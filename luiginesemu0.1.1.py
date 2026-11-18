#!python3.15
"""luigines emu 0.1.x — single-file NES emulator"""
from __future__ import annotations

import ctypes
import ctypes.util
import math
import os
import sys
import threading
import time
import tkinter as tk
from collections import deque
from tkinter import filedialog, messagebox

# =============================================================================
#  PALETTE - 64 NES colors (RGB) blue-tinted per request
# =============================================================================

_NES_PAL = (
    (0x66,0x66,0x66),(0x00,0x2A,0x88),(0x14,0x12,0xA7),(0x3B,0x00,0xA4),
    (0x5C,0x00,0x7E),(0x6E,0x00,0x40),(0x6C,0x06,0x00),(0x56,0x1D,0x00),
    (0x33,0x35,0x00),(0x0B,0x48,0x00),(0x00,0x52,0x00),(0x00,0x4F,0x08),
    (0x00,0x40,0x4D),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xAD,0xAD,0xAD),(0x15,0x5F,0xD9),(0x42,0x40,0xFF),(0x75,0x27,0xFE),
    (0xA0,0x1A,0xCC),(0xB7,0x1E,0x7B),(0xB5,0x31,0x20),(0x99,0x4E,0x00),
    (0x6B,0x6D,0x00),(0x38,0x87,0x00),(0x0C,0x93,0x00),(0x00,0x8F,0x32),
    (0x00,0x7C,0x8D),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xFF,0xFE,0xFF),(0x64,0xB0,0xFF),(0x92,0x90,0xFF),(0xC6,0x76,0xFF),
    (0xF3,0x6A,0xFF),(0xFE,0x6E,0xCC),(0xFE,0x81,0x70),(0xEA,0x9E,0x22),
    (0xBC,0xBE,0x00),(0x88,0xD8,0x00),(0x5C,0xE4,0x30),(0x45,0xE0,0x82),
    (0x48,0xCD,0xDE),(0x4F,0x4F,0x4F),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xFF,0xFE,0xFF),(0xC0,0xDF,0xFF),(0xD3,0xD2,0xFF),(0xE8,0xC8,0xFF),
    (0xFB,0xC2,0xFF),(0xFE,0xC4,0xEA),(0xFE,0xCC,0xC5),(0xF7,0xD8,0xA5),
    (0xE4,0xE5,0x94),(0xCF,0xEF,0x96),(0xBD,0xF4,0xAB),(0xB3,0xF3,0xCC),
    (0xB5,0xEB,0xF2),(0xB8,0xB8,0xB8),(0x00,0x00,0x00),(0x00,0x00,0x00),
)


def _blue_tint(rgb):
    r, g, b = rgb
    r = int(r * 0.55)
    g = int(g * 0.75)
    b = min(255, int(b * 1.10) + 35)
    return (r, g, b)


NES_PALETTE_RGB = tuple(_blue_tint(c) for c in _NES_PAL)
NES_PALETTE_HEX = tuple("#%02x%02x%02x" % c for c in NES_PALETTE_RGB)
NES_PALETTE_BYTES = tuple(bytes(c) for c in NES_PALETTE_RGB)


# =============================================================================
#  iNES / NES 2.0 loader  - accepts every valid header
# =============================================================================

class INESHeader:
    __slots__ = ("prg_banks", "chr_banks", "mapper", "mirroring", "battery",
                 "trainer", "four_screen", "is_nes2", "submapper", "prg_ram",
                 "tv_system", "filename", "title")

    def __init__(self, data, filename=""):
        if len(data) < 16 or data[0:4] != b"NES\x1a":
            raise ValueError("Not a valid iNES file (missing NES<EOF> magic)")
        self.filename = filename
        self.title = os.path.basename(filename) if filename else "untitled"
        self.prg_banks = data[4]
        self.chr_banks = data[5]
        f6, f7 = data[6], data[7]
        self.mirroring = "vertical" if (f6 & 1) else "horizontal"
        self.battery = bool(f6 & 2)
        self.trainer = bool(f6 & 4)
        self.four_screen = bool(f6 & 8)
        self.is_nes2 = ((f7 >> 2) & 3) == 2
        if self.is_nes2:
            mapper_lo = (f6 >> 4) | (f7 & 0xF0)
            mapper_hi = data[8] & 0x0F
            self.mapper = mapper_lo | (mapper_hi << 8)
            self.submapper = (data[8] >> 4) & 0x0F
            prg_hi = data[9] & 0x0F
            chr_hi = (data[9] >> 4) & 0x0F
            if prg_hi != 0xF:
                self.prg_banks |= (prg_hi << 8)
            if chr_hi != 0xF:
                self.chr_banks |= (chr_hi << 8)
            self.prg_ram = (data[10] & 0x0F) and (64 << (data[10] & 0x0F)) or 0
            self.tv_system = "PAL" if (data[12] & 1) else "NTSC"
        else:
            self.mapper = (f6 >> 4) | (f7 & 0xF0)
            self.submapper = 0
            self.prg_ram = data[8] * 8192 if data[8] else 8192
            self.tv_system = "PAL" if (data[9] & 1) else "NTSC"


class ROM:
    def __init__(self, path):
        with open(path, "rb") as f:
            data = f.read()
        self.header = INESHeader(data, path)
        off = 16
        if self.header.trainer:
            self.trainer = data[off:off + 512]
            off += 512
        else:
            self.trainer = b""
        prg_size = self.header.prg_banks * 16 * 1024
        chr_size = self.header.chr_banks * 8 * 1024
        self.prg = bytearray(data[off:off + prg_size])
        if len(self.prg) < prg_size:
            self.prg.extend(bytes(prg_size - len(self.prg)))
        off += prg_size
        if chr_size > 0:
            self.chr = bytearray(data[off:off + chr_size])
            if len(self.chr) < chr_size:
                self.chr.extend(bytes(chr_size - len(self.chr)))
        else:
            self.chr = bytearray(8192)
        self.has_chr_ram = chr_size == 0


# =============================================================================
#  Mappers  -  0 (NROM), 1 (MMC1), 2 (UNROM), 3 (CNROM), 4 (MMC3),
#              7 (AOROM), 11 (Color Dreams), 66 (GxROM), 71 (Camerica)
# =============================================================================

class Mapper:
    def __init__(self, rom):
        self.rom = rom
        self.mirroring = rom.header.mirroring
        self.prg_ram = bytearray(rom.header.prg_ram or 8192)
        self.irq_pending = False

    def cpu_read(self, addr): return 0
    def cpu_write(self, addr, val): pass
    def ppu_read(self, addr): return self.rom.chr[addr % len(self.rom.chr)]
    def ppu_write(self, addr, val):
        if self.rom.has_chr_ram:
            self.rom.chr[addr % len(self.rom.chr)] = val
    def scanline_tick(self): pass


class NROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.mask = 0x3FFF if rom.header.prg_banks == 1 else 0x7FFF
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        return self.rom.prg[(addr - 0x8000) & self.mask]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val


class MMC1(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.shift = 0x10
        self.control = 0x0C
        self.chr0 = 0
        self.chr1 = 0
        self.prg_bank = 0
        self._update()
    def _update(self):
        mode = (self.control >> 2) & 3
        cmode = (self.control >> 4) & 1
        banks = max(1, self.rom.header.prg_banks)
        if mode in (0, 1):
            b = (self.prg_bank & 0x0E) % banks
            self.prg_off0 = b * 16384
            self.prg_off1 = ((b + 1) % banks) * 16384
        elif mode == 2:
            self.prg_off0 = 0
            self.prg_off1 = ((self.prg_bank & 0x0F) % banks) * 16384
        else:
            self.prg_off0 = ((self.prg_bank & 0x0F) % banks) * 16384
            self.prg_off1 = (banks - 1) * 16384
        if cmode == 0:
            self.chr_off0 = (self.chr0 & 0x1E) * 4096
            self.chr_off1 = self.chr_off0 + 4096
        else:
            self.chr_off0 = self.chr0 * 4096
            self.chr_off1 = self.chr1 * 4096
        m = self.control & 3
        self.mirroring = ("one-screen-lo", "one-screen-hi", "vertical", "horizontal")[m]
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        if addr < 0xC000:
            return self.rom.prg[(self.prg_off0 + (addr - 0x8000)) % len(self.rom.prg)]
        return self.rom.prg[(self.prg_off1 + (addr - 0xC000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
            return
        if val & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            self._update()
            return
        complete = self.shift & 1
        self.shift = (self.shift >> 1) | ((val & 1) << 4)
        if complete:
            reg = (addr >> 13) & 3
            v = self.shift
            self.shift = 0x10
            if reg == 0: self.control = v
            elif reg == 1: self.chr0 = v
            elif reg == 2: self.chr1 = v
            else: self.prg_bank = v
            self._update()
    def ppu_read(self, addr):
        chr_data = self.rom.chr
        if addr < 0x1000:
            return chr_data[(self.chr_off0 + addr) % len(chr_data)]
        return chr_data[(self.chr_off1 + (addr - 0x1000)) % len(chr_data)]
    def ppu_write(self, addr, val):
        if self.rom.has_chr_ram:
            self.rom.chr[addr % len(self.rom.chr)] = val


class UNROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.bank = 0
        self.last = (rom.header.prg_banks - 1) * 16384
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        if addr < 0xC000:
            return self.rom.prg[(self.bank * 16384 + (addr - 0x8000)) % len(self.rom.prg)]
        return self.rom.prg[(self.last + (addr - 0xC000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
        elif addr >= 0x8000:
            self.bank = val & 0x0F


class CNROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.chr_bank = 0
        self.mask = 0x3FFF if rom.header.prg_banks == 1 else 0x7FFF
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        return self.rom.prg[(addr - 0x8000) & self.mask]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
        elif addr >= 0x8000:
            self.chr_bank = val & 0x03
    def ppu_read(self, addr):
        return self.rom.chr[(self.chr_bank * 8192 + addr) % len(self.rom.chr)]


class AOROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.bank = 0
        self.mirroring = "one-screen-lo"
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        return self.rom.prg[(self.bank * 32768 + (addr - 0x8000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
        elif addr >= 0x8000:
            self.bank = val & 0x07
            self.mirroring = "one-screen-hi" if (val & 0x10) else "one-screen-lo"


class GxROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.prg_bank = 0
        self.chr_bank = 0
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        return self.rom.prg[(self.prg_bank * 32768 + (addr - 0x8000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
        elif addr >= 0x8000:
            self.prg_bank = (val >> 4) & 3
            self.chr_bank = val & 3
    def ppu_read(self, addr):
        return self.rom.chr[(self.chr_bank * 8192 + addr) % len(self.rom.chr)]


class ColorDreams(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.prg_bank = 0
        self.chr_bank = 0
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        return self.rom.prg[(self.prg_bank * 32768 + (addr - 0x8000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if addr >= 0x8000:
            self.prg_bank = val & 3
            self.chr_bank = (val >> 4) & 0x0F
    def ppu_read(self, addr):
        return self.rom.chr[(self.chr_bank * 8192 + addr) % len(self.rom.chr)]


class Camerica(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.bank = 0
        self.last = (rom.header.prg_banks - 1) * 16384
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        if addr < 0xC000:
            return self.rom.prg[(self.bank * 16384 + (addr - 0x8000)) % len(self.rom.prg)]
        return self.rom.prg[(self.last + (addr - 0xC000)) % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0xC000 <= addr:
            self.bank = val & 0x0F


class MMC3(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.bank_select = 0
        self.banks = [0, 1, 0, 1, 0, 1, 0, 1]
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enable = False
        self.prg_banks_count = max(1, rom.header.prg_banks * 2)
        self._update()
    def _update(self):
        last = self.prg_banks_count - 1
        if self.bank_select & 0x40:
            self.prg_off = [last - 1, self.banks[7] & 0x3F, self.banks[6] & 0x3F, last]
        else:
            self.prg_off = [self.banks[6] & 0x3F, self.banks[7] & 0x3F, last - 1, last]
        if self.bank_select & 0x80:
            self.chr_off = [self.banks[2], self.banks[3], self.banks[4], self.banks[5],
                            self.banks[0] & 0xFE, (self.banks[0] & 0xFE) + 1,
                            self.banks[1] & 0xFE, (self.banks[1] & 0xFE) + 1]
        else:
            self.chr_off = [self.banks[0] & 0xFE, (self.banks[0] & 0xFE) + 1,
                            self.banks[1] & 0xFE, (self.banks[1] & 0xFE) + 1,
                            self.banks[2], self.banks[3], self.banks[4], self.banks[5]]
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) % len(self.prg_ram)]
        idx = (addr - 0x8000) >> 13
        off = self.prg_off[idx] * 8192 + ((addr - 0x8000) & 0x1FFF)
        return self.rom.prg[off % len(self.rom.prg)]
    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) % len(self.prg_ram)] = val
            return
        if addr < 0xA000:
            if addr & 1:
                self.banks[self.bank_select & 7] = val
            else:
                self.bank_select = val
            self._update()
        elif addr < 0xC000:
            if not (addr & 1):
                self.mirroring = "horizontal" if (val & 1) else "vertical"
        elif addr < 0xE000:
            if addr & 1:
                self.irq_reload = True
            else:
                self.irq_latch = val
        else:
            self.irq_enable = bool(addr & 1)
            if not self.irq_enable:
                self.irq_pending = False
    def ppu_read(self, addr):
        idx = (addr >> 10) & 7
        off = self.chr_off[idx] * 1024 + (addr & 0x3FF)
        return self.rom.chr[off % len(self.rom.chr)]
    def ppu_write(self, addr, val):
        if self.rom.has_chr_ram:
            idx = (addr >> 10) & 7
            off = self.chr_off[idx] * 1024 + (addr & 0x3FF)
            self.rom.chr[off % len(self.rom.chr)] = val
    def scanline_tick(self):
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter -= 1
        if self.irq_counter == 0 and self.irq_enable:
            self.irq_pending = True


_MAPPER_TABLE = {
    0: NROM, 1: MMC1, 2: UNROM, 3: CNROM, 4: MMC3,
    7: AOROM, 11: ColorDreams, 66: GxROM, 71: Camerica,
}


def make_mapper(rom):
    cls = _MAPPER_TABLE.get(rom.header.mapper)
    if cls is None:
        return NROM(rom)
    return cls(rom)


# =============================================================================
#  PPU & APU — picture + native 2A03 audio synthesis (no audio files)
# =============================================================================

AUDIO_FILES = False
AUDIO_ENABLED = True
SAMPLE_RATE = 48000
CPU_HZ_NTSC = 1789773.0
PPU_SCANLINES = 262
PPU_DOTS_PER_LINE = 341

# Engine timing — NTSC core; display locked to 60.00 Hz in the GUI loop.
TARGET_FPS = 60.0
FRAME_SEC = 1.0 / TARGET_FPS
NTSC_CPU_CYCLES_PER_FRAME = PPU_SCANLINES * (PPU_DOTS_PER_LINE / 3.0)
NTSC_CYCLES_PER_SCANLINE = NTSC_CPU_CYCLES_PER_FRAME / PPU_SCANLINES
# The GUI intentionally runs at exactly 60.00 FPS.  Sampling against the
# emulated clock keeps the native audio device fed with exactly 800 samples per
# displayed frame, avoiding the slow underrun that occurs when 60.00 Hz video
# is paired with the NES's 60.0988 Hz crystal rate.
EMULATED_CPU_HZ = NTSC_CPU_CYCLES_PER_FRAME * TARGET_FPS

_PATTERN_ROW_CACHE = {}
_IDENTITY_TRANSLATION = bytes(range(256))


def _decode_pattern_row(lo, hi):
    """Expand two NES bitplanes once, then reuse the eight decoded pixels."""
    key = (lo << 8) | hi
    row = _PATTERN_ROW_CACHE.get(key)
    if row is None:
        row = bytes(
            ((lo >> bit) & 1) | (((hi >> bit) & 1) << 1)
            for bit in range(7, -1, -1)
        )
        if len(_PATTERN_ROW_CACHE) >= 8192:
            _PATTERN_ROW_CACHE.clear()
        _PATTERN_ROW_CACHE[key] = row
    return row


class PPU:
    def __init__(self, mapper):
        self.mapper = mapper
        self.apu = None
        self.vram = bytearray(2048)
        self.palette = bytearray(32)
        self.oam = bytearray(256)
        self.framebuffer = bytearray(256 * 240)
        self.scanline = 0
        self.dot = 0
        self.frame = 0
        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_addr = 0
        self.v = 0
        self.t = 0
        self.x = 0
        self.w = 0
        self.buffer = 0
        self.nmi = False
        self.odd_frame = False
        self._bg_lut_key = None
        self._bg_luts = None
        self._colored_row_cache = {}
        init = [0x09,0x01,0x00,0x01,0x00,0x02,0x02,0x0D,
                0x08,0x10,0x08,0x24,0x00,0x00,0x04,0x2C,
                0x09,0x01,0x34,0x03,0x00,0x04,0x00,0x14,
                0x00,0x00,0x00,0x05,0x00,0x00,0x00,0x00]
        for i, v in enumerate(init):
            self.palette[i] = v

    def _background_luts(self):
        key = bytes(self.palette[:16])
        if key != self._bg_lut_key:
            universal = self.palette[0] & 0x3F
            luts = []
            for pal_hi in (0, 4, 8, 12):
                lut = bytearray(_IDENTITY_TRANSLATION)
                lut[0] = universal
                lut[1] = self.palette[pal_hi | 1] & 0x3F
                lut[2] = self.palette[pal_hi | 2] & 0x3F
                lut[3] = self.palette[pal_hi | 3] & 0x3F
                luts.append(bytes(lut))
            self._bg_lut_key = key
            self._bg_luts = tuple(luts)
            self._colored_row_cache.clear()
        return self._bg_luts

    def _mirror_addr(self, addr):
        addr &= 0x0FFF
        m = self.mapper.mirroring
        if m == "horizontal":
            if addr < 0x0400: return addr
            if addr < 0x0800: return addr - 0x0400
            if addr < 0x0C00: return addr - 0x0400
            return addr - 0x0800
        if m == "vertical":
            return addr & 0x07FF
        if m == "one-screen-lo":
            return addr & 0x03FF
        if m == "one-screen-hi":
            return (addr & 0x03FF) | 0x0400
        return addr & 0x07FF

    def ppu_read(self, addr):
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.mapper.ppu_read(addr)
        if addr < 0x3F00:
            return self.vram[self._mirror_addr(addr)]
        a = addr & 0x1F
        if a in (0x10, 0x14, 0x18, 0x1C):
            a -= 0x10
        return self.palette[a] & 0x3F

    def ppu_write(self, addr, val):
        addr &= 0x3FFF
        if addr < 0x2000:
            self.mapper.ppu_write(addr, val)
        elif addr < 0x3F00:
            self.vram[self._mirror_addr(addr)] = val
        else:
            a = addr & 0x1F
            if a in (0x10, 0x14, 0x18, 0x1C):
                a -= 0x10
            self.palette[a] = val & 0x3F

    def reg_read(self, reg):
        reg &= 7
        if reg == 2:
            v = self.status
            self.status &= 0x7F
            self.w = 0
            return v
        if reg == 4:
            return self.oam[self.oam_addr]
        if reg == 7:
            addr = self.v & 0x3FFF
            if addr < 0x3F00:
                ret = self.buffer
                self.buffer = self.ppu_read(addr)
            else:
                ret = self.ppu_read(addr)
                self.buffer = self.ppu_read(addr - 0x1000)
            self.v = (self.v + (32 if (self.ctrl & 4) else 1)) & 0x7FFF
            return ret
        return 0

    def reg_write(self, reg, val):
        reg &= 7
        if reg == 0:
            self.ctrl = val
            self.t = (self.t & 0xF3FF) | ((val & 3) << 10)
        elif reg == 1:
            self.mask = val
        elif reg == 3:
            self.oam_addr = val
        elif reg == 4:
            self.oam[self.oam_addr] = val
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif reg == 5:
            if self.w == 0:
                self.t = (self.t & 0xFFE0) | (val >> 3)
                self.x = val & 7
                self.w = 1
            else:
                self.t = (self.t & 0x8FFF) | ((val & 7) << 12)
                self.t = (self.t & 0xFC1F) | ((val & 0xF8) << 2)
                self.w = 0
        elif reg == 6:
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((val & 0x3F) << 8)
                self.w = 1
            else:
                self.t = (self.t & 0xFF00) | val
                self.v = self.t
                self.w = 0
        elif reg == 7:
            self.ppu_write(self.v & 0x3FFF, val)
            self.v = (self.v + (32 if (self.ctrl & 4) else 1)) & 0x7FFF

    def oam_dma_write(self, data):
        a = self.oam_addr
        for b in data:
            self.oam[a] = b
            a = (a + 1) & 0xFF

    def _render_scanline(self, y):
        bg_color = self.palette[0] & 0x3F
        base = y * 256
        row = bytearray((bg_color,)) * 256
        if not (self.mask & 0x18):
            self.framebuffer[base:base + 256] = row
            return
        nt_base = 0x2000 + ((self.ctrl & 3) << 10)
        pt_base = 0x1000 if (self.ctrl & 0x10) else 0
        line = y
        tile_y = line >> 3
        fine_y = line & 7
        bg_enabled = bool(self.mask & 0x08)
        sp_enabled = bool(self.mask & 0x10)
        if bg_enabled:
            mapper = self.mapper
            pattern_read = mapper.ppu_read
            vram = self.vram
            nt_row = self._mirror_addr(nt_base + tile_y * 32)
            at_row = self._mirror_addr(
                (nt_base | 0x3C0) + (tile_y >> 2) * 8)
            color_luts = self._background_luts()
            for tx in range(32):
                tile_idx = vram[nt_row + tx]
                at = vram[at_row + (tx >> 2)]
                shift = ((tile_y & 2) << 1) | (tx & 2)
                pal_hi = ((at >> shift) & 3) << 2
                pt_addr = pt_base + tile_idx * 16 + fine_y
                lo = pattern_read(pt_addr)
                hi = pattern_read(pt_addr + 8)
                sx_base = tx * 8
                cache_key = (lo << 10) | (hi << 2) | (pal_hi >> 2)
                colored = self._colored_row_cache.get(cache_key)
                if colored is None:
                    colored = _decode_pattern_row(lo, hi).translate(
                        color_luts[pal_hi >> 2])
                    if len(self._colored_row_cache) >= 16384:
                        self._colored_row_cache.clear()
                    self._colored_row_cache[cache_key] = colored
                row[sx_base:sx_base + 8] = colored
        if sp_enabled:
            sp_pt = 0x1000 if (self.ctrl & 0x08) else 0
            sp_h = 16 if (self.ctrl & 0x20) else 8
            count = 0
            for i in range(0, 256, 4):
                sy = self.oam[i]
                if sy >= 0xEF:
                    continue
                dy = line - sy
                if dy < 0 or dy >= sp_h:
                    continue
                if count >= 8:
                    self.status |= 0x20
                    break
                count += 1
                tile = self.oam[i + 1]
                attr = self.oam[i + 2]
                sx = self.oam[i + 3]
                pal_hi = ((attr & 3) << 2) | 0x10
                flip_h = bool(attr & 0x40)
                flip_v = bool(attr & 0x80)
                behind = bool(attr & 0x20)
                if sp_h == 16:
                    pt = (tile & 1) * 0x1000
                    t = tile & 0xFE
                    fy = dy
                    if flip_v:
                        fy = 15 - fy
                    if fy >= 8:
                        t += 1
                        fy -= 8
                    pt_addr = pt + t * 16 + fy
                else:
                    fy = dy if not flip_v else (7 - dy)
                    pt_addr = sp_pt + tile * 16 + fy
                lo = self.mapper.ppu_read(pt_addr)
                hi = self.mapper.ppu_read(pt_addr + 8)
                pattern = _decode_pattern_row(lo, hi)
                if flip_h:
                    pattern = pattern[::-1]
                for px, p in enumerate(pattern):
                    if p == 0:
                        continue
                    fx = sx + px
                    if fx >= 256:
                        break
                    if behind and bg_enabled:
                        if row[fx] != (self.palette[0] & 0x3F):
                            continue
                    row[fx] = self.palette[pal_hi | p] & 0x3F
                if i == 0 and bg_enabled and not (self.status & 0x40):
                    self.status |= 0x40
        self.framebuffer[base:base + 256] = row

    def step_scanline(self):
        if 0 <= self.scanline < 240:
            self._render_scanline(self.scanline)
            self.mapper.scanline_tick()
        elif self.scanline == 241:
            self.status |= 0x80
            if self.ctrl & 0x80:
                self.nmi = True
        elif self.scanline == 261:
            self.status &= 0x1F
        self.scanline += 1
        if self.scanline > 261:
            self.scanline = 0
            self.frame += 1
            self.odd_frame = not self.odd_frame
            if self.apu is not None:
                self.apu.on_ppu_frame(self.frame)


# --- APU (2A03 audio synthesis) ---

_LENGTH_TABLE = (
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
)

_NOISE_PERIOD_NTSC = (
    4, 8, 16, 32, 64, 96, 128, 160,
    202, 254, 380, 508, 762, 1016, 2034, 4068,
)

_DMC_RATE_NTSC = (
    428, 380, 340, 320, 286, 254, 226, 214, 190, 160, 142, 128, 106, 84, 72, 54,
)

_DUTY_SEQ = (
    (0, 1, 0, 0, 0, 0, 0, 0),
    (0, 1, 1, 0, 0, 0, 0, 0),
    (0, 1, 1, 1, 1, 0, 0, 0),
    (1, 0, 0, 1, 1, 1, 1, 1),
)

# CPU-cycle positions of the 2A03 frame sequencer.  Channel behavior and the
# lookup tables here were cross-checked against FCEUX's src/sound.cpp; this is
# a clean Python implementation rather than embedded FCEUX/C++ code.
_FRAME_STEPS_4 = (
    (3729, True, False),
    (7457, True, True),
    (11186, True, False),
    (14915, True, True),
)
_FRAME_STEPS_5 = (
    (3729, True, False),
    (7457, True, True),
    (11186, True, False),
    (14915, False, False),
    (18641, True, True),
)


class _Pulse:
    __slots__ = (
        "enabled", "channel", "timer", "timer_period", "duty", "duty_step",
        "length_counter", "length_halt", "volume", "constant_volume",
        "envelope_loop", "envelope_start", "envelope_divider", "envelope_counter",
        "sweep_enabled", "sweep_period", "sweep_negate", "sweep_shift",
        "sweep_reload", "sweep_divider", "sweep_counter", "target_period",
    )

    def __init__(self, channel):
        self.channel = channel
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.duty = 0
        self.duty_step = 0
        self.length_counter = 0
        self.length_halt = False
        self.volume = 0
        self.constant_volume = False
        self.envelope_loop = False
        self.envelope_start = False
        self.envelope_divider = 0
        self.envelope_counter = 0
        self.sweep_enabled = False
        self.sweep_period = 0
        self.sweep_negate = False
        self.sweep_shift = 0
        self.sweep_reload = False
        self.sweep_divider = 0
        self.sweep_counter = 0
        self.target_period = 0

    def write_reg0(self, val):
        self.duty = (val >> 6) & 3
        self.length_halt = bool(val & 0x20)
        self.envelope_loop = bool(val & 0x20)
        self.constant_volume = bool(val & 0x10)
        self.volume = val & 0x0F

    def write_reg1(self, val):
        self.sweep_enabled = bool(val & 0x80)
        self.sweep_period = (val >> 4) & 7
        self.sweep_negate = bool(val & 0x08)
        self.sweep_shift = val & 7
        self.sweep_reload = True
        self._update_target()

    def write_reg2(self, val):
        self.timer_period = (self.timer_period & 0x700) | val
        self._update_target()

    def write_reg3(self, val):
        self.timer_period = (self.timer_period & 0xFF) | ((val & 7) << 8)
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.duty_step = 0
        self.timer = 0
        self.envelope_start = True
        self._update_target()

    def _update_target(self):
        change = self.timer_period >> self.sweep_shift
        if self.sweep_negate:
            if self.channel == 0:
                change = -change - 1
            else:
                change = -change
        self.target_period = self.timer_period + change

    def clock_timer(self, cycles=1):
        period = (self.timer_period + 1) * 2
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        self.duty_step = (self.duty_step + steps) & 7

    def clock_envelope(self):
        if self.envelope_start:
            self.envelope_start = False
            self.envelope_counter = 15
            self.envelope_divider = self.volume
        elif self.envelope_divider:
            self.envelope_divider -= 1
        else:
            self.envelope_divider = self.volume
            if self.envelope_counter:
                self.envelope_counter -= 1
            elif self.envelope_loop:
                self.envelope_counter = 15

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def clock_sweep(self):
        if self.sweep_divider == 0:
            if self.sweep_enabled and self.sweep_shift and self.timer_period >= 8:
                if 0 < self.target_period <= 0x7FF:
                    self.timer_period = self.target_period
                    self._update_target()
        if self.sweep_divider == 0 or self.sweep_reload:
            self.sweep_divider = self.sweep_period
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def output(self):
        if not self.enabled or not self.length_counter or self.timer_period < 8:
            return 0
        if self.sweep_enabled and not (0 <= self.target_period <= 0x7FF):
            return 0
        seq = _DUTY_SEQ[self.duty][self.duty_step]
        if not seq:
            return 0
        if self.constant_volume:
            return self.volume
        return self.envelope_counter


class _Triangle:
    __slots__ = (
        "enabled", "timer", "timer_period", "length_counter", "length_halt",
        "linear_counter", "linear_reload_value", "linear_reload_flag",
        "control_flag", "step",
    )

    def __init__(self):
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.length_counter = 0
        self.length_halt = False
        self.linear_counter = 0
        self.linear_reload_value = 0
        self.linear_reload_flag = False
        self.control_flag = False
        self.step = 0

    def write_reg0(self, val):
        self.control_flag = bool(val & 0x80)
        self.length_halt = self.control_flag
        self.linear_reload_value = val & 0x7F

    def write_reg2(self, val):
        self.timer_period = (self.timer_period & 0x700) | val

    def write_reg3(self, val):
        self.timer_period = (self.timer_period & 0xFF) | ((val & 7) << 8)
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.linear_reload_flag = True

    def clock_timer(self, cycles=1):
        period = self.timer_period + 1
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        if self.timer_period >= 2 and self.linear_counter and self.length_counter:
            self.step = (self.step + steps) & 31

    def clock_linear(self):
        if self.linear_reload_flag:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control_flag:
            self.linear_reload_flag = False

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def output(self):
        if not self.enabled or not self.length_counter or not self.linear_counter:
            return 0
        if self.timer_period < 2:
            return 7
        step = self.step
        if step < 16:
            return step
        return 31 - step


class _Noise:
    __slots__ = (
        "enabled", "timer", "timer_period", "mode", "shift", "length_counter",
        "length_halt", "volume", "constant_volume", "envelope_loop",
        "envelope_start", "envelope_divider", "envelope_counter",
    )

    def __init__(self):
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.mode = 0
        self.shift = 1
        self.length_counter = 0
        self.length_halt = False
        self.volume = 0
        self.constant_volume = False
        self.envelope_loop = False
        self.envelope_start = False
        self.envelope_divider = 0
        self.envelope_counter = 0

    def write_reg0(self, val):
        self.length_halt = bool(val & 0x20)
        self.envelope_loop = bool(val & 0x20)
        self.constant_volume = bool(val & 0x10)
        self.volume = val & 0x0F

    def write_reg2(self, val):
        self.mode = (val >> 7) & 1
        self.timer_period = _NOISE_PERIOD_NTSC[val & 0x0F]

    def write_reg3(self, val):
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.envelope_start = True

    def clock_timer(self, cycles=1):
        period = max(1, self.timer_period)
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        tap = 6 if self.mode else 1
        for _ in range(steps):
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)

    def clock_envelope(self):
        if self.envelope_start:
            self.envelope_start = False
            self.envelope_counter = 15
            self.envelope_divider = self.volume
        elif self.envelope_divider:
            self.envelope_divider -= 1
        else:
            self.envelope_divider = self.volume
            if self.envelope_counter:
                self.envelope_counter -= 1
            elif self.envelope_loop:
                self.envelope_counter = 15

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def output(self):
        if not self.enabled or not self.length_counter or (self.shift & 1):
            return 0
        if self.constant_volume:
            return self.volume
        return self.envelope_counter


class _DMC:
    __slots__ = (
        "enabled", "irq_enabled", "loop", "rate_index", "timer", "rate_period",
        "output_level", "sample_addr", "sample_length", "current_addr",
        "bytes_remaining", "shift", "bits_remaining", "silence", "irq_pending",
        "sample_buffer", "sample_buffer_empty", "bus",
    )

    def __init__(self):
        self.bus = None
        self.reset()

    def reset(self):
        self.enabled = False
        self.irq_enabled = False
        self.loop = False
        self.rate_index = 0
        self.timer = 0
        self.rate_period = _DMC_RATE_NTSC[0]
        self.output_level = 0
        self.sample_addr = 0
        self.sample_length = 0
        self.current_addr = 0
        self.bytes_remaining = 0
        self.shift = 0
        self.bits_remaining = 0
        self.silence = True
        self.irq_pending = False
        self.sample_buffer = 0
        self.sample_buffer_empty = True

    def write_reg0(self, val):
        self.irq_enabled = bool(val & 0x80)
        self.loop = bool(val & 0x40)
        self.rate_index = val & 0x0F
        self.rate_period = _DMC_RATE_NTSC[self.rate_index]
        if not self.irq_enabled:
            self.irq_pending = False

    def write_reg1(self, val):
        self.output_level = val & 0x7F

    def write_reg2(self, val):
        self.sample_addr = 0xC000 | (val << 6)

    def write_reg3(self, val):
        self.sample_length = (val << 4) | 1

    def start(self):
        if not self.bytes_remaining:
            self.current_addr = self.sample_addr
            self.bytes_remaining = self.sample_length
        self._fill_sample_buffer()

    def clock_timer(self, cycles=1):
        if self.sample_buffer_empty and self.bytes_remaining:
            self._fill_sample_buffer()
        period = max(1, self.rate_period)
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        for _ in range(steps):
            if not self.silence:
                if self.shift & 1:
                    if self.output_level <= 125:
                        self.output_level += 2
                elif self.output_level >= 2:
                    self.output_level -= 2
                self.shift >>= 1
            if self.bits_remaining:
                self.bits_remaining -= 1
            if not self.bits_remaining:
                self.bits_remaining = 8
                if self.sample_buffer_empty:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift = self.sample_buffer
                    self.sample_buffer_empty = True
                self._fill_sample_buffer()

    def _fill_sample_buffer(self):
        if not self.enabled or not self.sample_buffer_empty:
            return
        if not self.bytes_remaining:
            return
        if self.bus is not None:
            self.sample_buffer = self.bus.read(self.current_addr)
            if hasattr(self.bus, "dma_stall"):
                self.bus.dma_stall += 4
        else:
            self.sample_buffer = 0
        self.sample_buffer_empty = False
        self.current_addr = 0x8000 if self.current_addr == 0xFFFF else self.current_addr + 1
        self.bytes_remaining -= 1
        if not self.bytes_remaining:
            if self.loop:
                self.current_addr = self.sample_addr
                self.bytes_remaining = self.sample_length
            else:
                if self.irq_enabled:
                    self.irq_pending = True

    def output(self):
        # $4011 is a direct DAC load, so its level remains in the mixer even
        # when the DMC sample reader is disabled through $4015.
        return self.output_level


def _mix_channels(p1, p2, tri, noise, dmc):
    pulse = p1 + p2
    if pulse:
        pulse_out = 95.52 / (8128.0 / pulse + 100.0)
    else:
        pulse_out = 0.0
    tnd_input = tri / 8227.0 + noise / 12241.0 + dmc / 22638.0
    if tnd_input:
        tnd_out = 159.79 / (1.0 / tnd_input + 100.0)
    else:
        tnd_out = 0.0
    return pulse_out + tnd_out


class APU:
    def __init__(self):
        self.bus = None
        self.audio = None
        self.reg = bytearray(0x18)
        self.pulse1 = _Pulse(0)
        self.pulse2 = _Pulse(1)
        self.triangle = _Triangle()
        self.noise = _Noise()
        self.dmc = _DMC()
        self.frame_mode = 0
        self.frame_irq_inhibit = False
        self.frame_irq_pending = False
        self.frame_step = 0
        self.frame_counter = 0
        self.frame_reset_delay = 0
        self.cpu_cycles = 0
        self._pending_cycles = 0
        self._batch_cycles = 32
        self.sample_accum = 0.0
        self.cycles_per_sample = EMULATED_CPU_HZ / SAMPLE_RATE
        self._sample_count = 0
        self._filter_in = 0.0
        self._filter_high = 0.0
        self._filter_low = 0.0
        self._high_pass_r = math.exp(-2.0 * math.pi * 90.0 / SAMPLE_RATE)
        self._low_pass_a = 1.0 - math.exp(-2.0 * math.pi * 14000.0 / SAMPLE_RATE)
        self._reset_channels()

    def _reset_channels(self):
        self.pulse1.reset()
        self.pulse2.reset()
        self.triangle.reset()
        self.noise.reset()
        self.dmc.reset()
        self.dmc.bus = self.bus

    def write(self, addr, val):
        self._flush_pending()
        val &= 0xFF
        if addr == 0x4017:
            self.frame_irq_inhibit = bool(val & 0x40)
            self.frame_mode = bool(val & 0x80)
            if self.frame_irq_inhibit:
                self.frame_irq_pending = False
            # The hardware applies a $4017 reset three or four CPU cycles
            # later depending on phase.  Keeping the delay prevents envelope
            # clicks in games that rewrite the frame counter mid-note.
            self.frame_reset_delay = 3 if (self.cpu_cycles & 1) else 4
            return
        addr -= 0x4000
        if 0 <= addr < len(self.reg):
            self.reg[addr] = val
        if addr == 0x15:
            self.pulse1.enabled = bool(val & 0x01)
            self.pulse2.enabled = bool(val & 0x02)
            self.triangle.enabled = bool(val & 0x04)
            self.noise.enabled = bool(val & 0x08)
            self.dmc.enabled = bool(val & 0x10)
            if not self.pulse1.enabled:
                self.pulse1.length_counter = 0
            if not self.pulse2.enabled:
                self.pulse2.length_counter = 0
            if not self.triangle.enabled:
                self.triangle.length_counter = 0
            if not self.noise.enabled:
                self.noise.length_counter = 0
            self.dmc.irq_pending = False
            if val & 0x10:
                self.dmc.start()
            else:
                self.dmc.bytes_remaining = 0
            return
        if addr <= 0x03:
            (self.pulse1.write_reg0, self.pulse1.write_reg1,
             self.pulse1.write_reg2, self.pulse1.write_reg3)[addr](val)
        elif addr <= 0x07:
            off = addr - 4
            (self.pulse2.write_reg0, self.pulse2.write_reg1,
             self.pulse2.write_reg2, self.pulse2.write_reg3)[off](val)
        elif addr <= 0x0B:
            off = addr - 8
            if off == 0:
                self.triangle.write_reg0(val)
            elif off == 2:
                self.triangle.write_reg2(val)
            elif off == 3:
                self.triangle.write_reg3(val)
        elif addr <= 0x0F:
            off = addr - 0x0C
            if off == 0:
                self.noise.write_reg0(val)
            elif off == 2:
                self.noise.write_reg2(val)
            elif off == 3:
                self.noise.write_reg3(val)
        elif addr <= 0x13:
            off = addr - 0x10
            (self.dmc.write_reg0, self.dmc.write_reg1,
             self.dmc.write_reg2, self.dmc.write_reg3)[off](val)

    def read_status(self):
        self._flush_pending()
        status = 0
        if self.pulse1.length_counter:
            status |= 0x01
        if self.pulse2.length_counter:
            status |= 0x02
        if self.triangle.length_counter:
            status |= 0x04
        if self.noise.length_counter:
            status |= 0x08
        if self.dmc.bytes_remaining:
            status |= 0x10
        if self.frame_irq_pending:
            status |= 0x40
        if self.dmc.irq_pending:
            status |= 0x80
        self.frame_irq_pending = False
        return status

    def _quarter_frame(self):
        self.pulse1.clock_envelope()
        self.pulse2.clock_envelope()
        self.triangle.clock_linear()
        self.noise.clock_envelope()

    def _half_frame(self):
        self.pulse1.clock_length()
        self.pulse2.clock_length()
        self.triangle.clock_length()
        self.noise.clock_length()
        self.pulse1.clock_sweep()
        self.pulse2.clock_sweep()

    def _frame_sequencer(self):
        steps = _FRAME_STEPS_5 if self.frame_mode else _FRAME_STEPS_4
        while self.frame_step < len(steps):
            cycle, quarter, half = steps[self.frame_step]
            if self.frame_counter < cycle:
                break
            if quarter:
                self._quarter_frame()
            if half:
                self._half_frame()
            if (not self.frame_mode and self.frame_step == 3
                    and not self.frame_irq_inhibit):
                self.frame_irq_pending = True
            self.frame_step += 1
            if self.frame_step >= len(steps):
                self.frame_counter = max(0, self.frame_counter - cycle)
                self.frame_step = 0
                break

    def _emit_sample(self):
        if not AUDIO_ENABLED or self.audio is None:
            return
        if AUDIO_FILES:
            return
        mixed = _mix_channels(
            self.pulse1.output(), self.pulse2.output(),
            self.triangle.output(), self.noise.output(), self.dmc.output(),
        )
        # FCEUX also filters the raw nonlinear APU mix.  A lightweight
        # high-pass/low-pass pair removes the DAC's DC offset and ultrasonic
        # stair-stepping before feeding the native PCM backend.
        high = mixed - self._filter_in + self._high_pass_r * self._filter_high
        self._filter_in = mixed
        self._filter_high = high
        self._filter_low += self._low_pass_a * (high - self._filter_low)
        self.audio.push(self._filter_low)
        self._sample_count += 1

    def on_ppu_frame(self, ppu_frame):
        """PPU hook retained for mapper/debug compatibility; audio is CPU-clocked."""
        self._flush_pending()

    def _flush_pending(self):
        cycles = self._pending_cycles
        if not cycles:
            return
        self._pending_cycles = 0
        # CPU writes are instruction-granular in this compact emulator, so the
        # five timers can safely advance as a batch here.  This preserves the
        # channel phase while avoiding ~1.8 million Python loop iterations/s.
        if self.pulse1.enabled:
            self.pulse1.clock_timer(cycles)
        if self.pulse2.enabled:
            self.pulse2.clock_timer(cycles)
        if self.triangle.enabled:
            self.triangle.clock_timer(cycles)
        if self.noise.enabled:
            self.noise.clock_timer(cycles)
        if self.dmc.enabled or not self.dmc.silence:
            self.dmc.clock_timer(cycles)
        self.sample_accum += cycles

        if self.frame_reset_delay:
            delay = self.frame_reset_delay
            self.frame_reset_delay -= cycles
            if self.frame_reset_delay <= 0:
                self.frame_reset_delay = 0
                self.frame_counter = 0
                self.frame_step = 0
                if self.frame_mode:
                    self._quarter_frame()
                    self._half_frame()
                self.frame_counter = max(0, cycles - delay)
                if self.frame_counter:
                    self._frame_sequencer()
        else:
            self.frame_counter += cycles
            steps = _FRAME_STEPS_5 if self.frame_mode else _FRAME_STEPS_4
            if self.frame_counter >= steps[self.frame_step][0]:
                self._frame_sequencer()

        if self.sample_accum >= self.cycles_per_sample:
            sample_count = int(self.sample_accum / self.cycles_per_sample)
            self.sample_accum -= sample_count * self.cycles_per_sample
            if self.audio is not None:
                for _ in range(sample_count):
                    self._emit_sample()

    def clock(self, cycles=1):
        cycles = max(0, int(cycles))
        if not cycles:
            return
        self.cpu_cycles += cycles
        if cycles >= self._batch_cycles:
            remaining = cycles
            while remaining:
                room = self._batch_cycles - self._pending_cycles
                step = min(remaining, room)
                self._pending_cycles += step
                remaining -= step
                if self._pending_cycles >= self._batch_cycles:
                    self._flush_pending()
            if (self.frame_reset_delay
                    and self._pending_cycles >= self.frame_reset_delay):
                self._flush_pending()
            return
        self._pending_cycles += cycles
        if (self._pending_cycles >= self._batch_cycles
                or (self.frame_reset_delay
                    and self._pending_cycles >= self.frame_reset_delay)):
            self._flush_pending()

    def irq_pending(self):
        self._flush_pending()
        return self.frame_irq_pending or self.dmc.irq_pending


class _LegacyWinMMAudioStream:
    """PCM output via WinMM waveOut on Windows."""

    _CHUNK = 512
    _POOL = 4
    _MIN_START = 64
    WHDR_DONE = 0x00000001
    AUDIO_GAIN = 5.0

    def __init__(self, rate=SAMPLE_RATE):
        self.rate = rate
        self._queue = deque(maxlen=32768)
        self._lock = threading.Lock()
        self._alive = False
        self._hwo = None
        self._winmm = None
        self._pool = []
        self._pool_free = set()
        self._due_at = {}
        self._WAVEHDR = None
        self._play_thread = None
        self._running = False

    @property
    def active(self):
        return self._running and self._hwo is not None

    def status(self):
        if not AUDIO_ENABLED:
            return "audio off"
        if self.active:
            return f"audio on ({self.rate} Hz)"
        return "audio unavailable"

    def start(self):
        if not AUDIO_ENABLED or self._running:
            return
        self._alive = True
        self._running = True
        if sys.platform == "win32":
            self._open_winmm()
        if self._play_thread is None or not self._play_thread.is_alive():
            self._play_thread = threading.Thread(target=self._play_loop, daemon=True)
            self._play_thread.start()

    def push(self, sample):
        if not self._running:
            return
        amp = max(-1.0, min(1.0, sample * self.AUDIO_GAIN))
        with self._lock:
            self._queue.append(amp)

    def stop(self):
        self._alive = False
        self._running = False
        if self._hwo is not None and self._winmm is not None:
            try:
                self._winmm.waveOutReset(self._hwo)
            except (AttributeError, OSError):
                pass

    @staticmethod
    def _win_pump():
        if sys.platform != "win32":
            return
        try:
            user32 = ctypes.windll.user32
        except (AttributeError, OSError):
            return
        class _MSG(ctypes.Structure):
            _fields_ = [
                ("hwnd", ctypes.c_void_p),
                ("message", ctypes.c_uint),
                ("wParam", ctypes.c_size_t),
                ("lParam", ctypes.c_size_t),
                ("time", ctypes.c_uint),
                ("pt_x", ctypes.c_long),
                ("pt_y", ctypes.c_long),
            ]
        msg = _MSG()
        while user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 1):
            user32.TranslateMessage(ctypes.byref(msg))
            user32.DispatchMessageW(ctypes.byref(msg))

    def _open_winmm(self):
        if self._hwo is not None:
            return
        try:
            winmm = ctypes.windll.winmm
        except (AttributeError, OSError):
            return
        class WAVEFORMATEX(ctypes.Structure):
            _fields_ = [
                ("wFormatTag", ctypes.c_uint16),
                ("nChannels", ctypes.c_uint16),
                ("nSamplesPerSec", ctypes.c_uint32),
                ("nAvgBytesPerSec", ctypes.c_uint32),
                ("nBlockAlign", ctypes.c_uint16),
                ("wBitsPerSample", ctypes.c_uint16),
                ("cbSize", ctypes.c_uint16),
            ]
        fmt = WAVEFORMATEX(1, 1, self.rate, self.rate * 2, 2, 16, 0)
        hwo = ctypes.c_void_p()
        if winmm.waveOutOpen(ctypes.byref(hwo), 0xFFFFFFFF, ctypes.byref(fmt),
                             0, 0, 0) != 0:
            return
        self._hwo = hwo
        self._winmm = winmm
        try:
            winmm.waveOutSetVolume(self._hwo, 0xFFFFFFFF)
            winmm.waveOutRestart(self._hwo)
        except (AttributeError, OSError):
            pass
        class WAVEHDR(ctypes.Structure):
            _fields_ = [
                ("lpData", ctypes.c_char_p),
                ("dwBufferLength", ctypes.c_uint32),
                ("dwBytesRecorded", ctypes.c_uint32),
                ("dwUser", ctypes.c_size_t),
                ("dwFlags", ctypes.c_uint32),
                ("dwLoops", ctypes.c_uint32),
                ("lpNext", ctypes.c_void_p),
                ("reserved", ctypes.c_size_t),
            ]
        self._WAVEHDR = WAVEHDR
        self._pool.clear()
        self._pool_free.clear()
        self._due_at.clear()
        for i in range(self._POOL):
            buf = ctypes.create_string_buffer(self._CHUNK * 2)
            hdr = WAVEHDR()
            hdr.lpData = ctypes.cast(buf, ctypes.c_char_p)
            hdr.dwBufferLength = self._CHUNK * 2
            hdr.dwFlags = 0
            self._pool.append((buf, hdr))
            self._pool_free.add(i)

    def _release_buffer(self, idx):
        if idx in self._pool_free:
            return
        _, hdr = self._pool[idx]
        winmm = self._winmm
        if hdr.dwFlags & 0x00000002:  # WHDR_PREPARED
            winmm.waveOutUnprepareHeader(self._hwo, ctypes.byref(hdr),
                                         ctypes.sizeof(hdr))
        hdr.dwFlags = 0
        self._pool_free.add(idx)
        self._due_at.pop(idx, None)

    def _reap_done(self):
        now = time.perf_counter()
        for i in range(self._POOL):
            if i in self._pool_free:
                continue
            _, hdr = self._pool[i]
            if hdr.dwFlags & self.WHDR_DONE or now >= self._due_at.get(i, 0):
                self._release_buffer(i)

    def _play_loop(self):
        if self._hwo is None:
            while self._alive:
                with self._lock:
                    while self._queue:
                        self._queue.popleft()
                time.sleep(0.02)
            return
        winmm = self._winmm
        chunk_sec = self._CHUNK / self.rate
        while self._alive:
            self._win_pump()
            self._reap_done()
            with self._lock:
                n = len(self._queue)
            if n < self._MIN_START or not self._pool_free:
                time.sleep(0.001)
                continue
            take = min(self._CHUNK, n)
            idx = min(self._pool_free)
            self._pool_free.remove(idx)
            buf, hdr = self._pool[idx]
            with self._lock:
                samples = [self._queue.popleft() for _ in range(take)]
            pcm = bytearray(self._CHUNK * 2)
            for i, s in enumerate(samples):
                val = int(max(-32768, min(32767, s * 32767)))
                pcm[i * 2] = val & 0xFF
                pcm[i * 2 + 1] = (val >> 8) & 0xFF
            ctypes.memmove(buf, bytes(pcm), self._CHUNK * 2)
            hdr.dwBufferLength = self._CHUNK * 2
            hdr.dwFlags = 0
            if winmm.waveOutPrepareHeader(self._hwo, ctypes.byref(hdr),
                                          ctypes.sizeof(hdr)) != 0:
                self._pool_free.add(idx)
                time.sleep(0.001)
                continue
            if winmm.waveOutWrite(self._hwo, ctypes.byref(hdr),
                                  ctypes.sizeof(hdr)) != 0:
                self._release_buffer(idx)
                time.sleep(0.001)
                continue
            self._due_at[idx] = time.perf_counter() + chunk_sec + 0.005


class AudioStream:
    """Low-latency mono PCM using only native OS APIs and ctypes."""

    _CHUNK = 512
    _POOL = 6
    _MIN_START = 768
    _MAX_LATENCY = SAMPLE_RATE // 5
    WHDR_DONE = 0x00000001
    WHDR_PREPARED = 0x00000002
    AUDIO_GAIN = 2.0

    def __init__(self, rate=SAMPLE_RATE):
        self.rate = rate
        self._queue = deque(maxlen=rate // 2)
        self._lock = threading.Lock()
        self._alive = False
        self._running = False
        self._backend = "none"
        self._play_thread = None
        self._winmm = None
        self._hwo = None
        self._pool = []
        self._pool_free = set()
        self._coreaudio = None
        self._audio_queue = None
        self._coreaudio_callback = None
        self._core_buffers = []
        self._alsa = None
        self._alsa_pcm = None
        self._alsa_error_handler = None

    @property
    def active(self):
        return self._running and self._backend != "none"

    def status(self):
        if not AUDIO_ENABLED:
            return "audio off"
        if self.active:
            names = {"winmm": "WinMM", "coreaudio": "CoreAudio", "alsa": "ALSA"}
            return f"audio on ({names.get(self._backend, self._backend)}, {self.rate} Hz)"
        return "audio unavailable"

    def start(self):
        if not AUDIO_ENABLED or self.active:
            return
        self._alive = True
        if sys.platform == "win32":
            self._open_winmm()
        elif sys.platform == "darwin":
            self._open_coreaudio()
        elif sys.platform.startswith("linux"):
            self._open_alsa()
        if self._backend == "none":
            self._alive = False
            return
        self._running = True
        if self._backend in ("winmm", "alsa"):
            self._play_thread = threading.Thread(
                target=self._play_loop, name="luigines-audio", daemon=True)
            self._play_thread.start()

    def push(self, sample):
        if not self.active:
            return
        amp = max(-1.0, min(1.0, sample * self.AUDIO_GAIN))
        with self._lock:
            self._queue.append(amp)

    def _take_pcm(self, frames):
        with self._lock:
            if len(self._queue) > self._MAX_LATENCY:
                trim_to = self._MIN_START + self._CHUNK
                for _ in range(len(self._queue) - trim_to):
                    self._queue.popleft()
            take = min(frames, len(self._queue))
            samples = [self._queue.popleft() for _ in range(take)]
        pcm = bytearray(frames * 2)
        for i, sample in enumerate(samples):
            value = int(max(-32768, min(32767, sample * 32767.0)))
            pcm[i * 2] = value & 0xFF
            pcm[i * 2 + 1] = (value >> 8) & 0xFF
        return bytes(pcm)

    def stop(self):
        self._alive = False
        self._running = False
        if self._backend == "winmm" and self._winmm is not None and self._hwo:
            self._winmm.waveOutReset(self._hwo)
        elif self._backend == "alsa" and self._alsa is not None and self._alsa_pcm:
            self._alsa.snd_pcm_drop(self._alsa_pcm)
        elif self._backend == "coreaudio" and self._coreaudio is not None and self._audio_queue:
            self._coreaudio.AudioQueueStop(self._audio_queue, True)
        if (self._play_thread is not None
                and self._play_thread is not threading.current_thread()):
            self._play_thread.join(timeout=0.5)
        if self._backend == "winmm":
            self._close_winmm()
        elif self._backend == "coreaudio":
            self._close_coreaudio()
        elif self._backend == "alsa":
            self._close_alsa()
        with self._lock:
            self._queue.clear()
        self._backend = "none"

    # -- Windows: waveOut -------------------------------------------------

    def _open_winmm(self):
        try:
            winmm = ctypes.windll.winmm
        except (AttributeError, OSError):
            return

        class WAVEFORMATEX(ctypes.Structure):
            _fields_ = [
                ("wFormatTag", ctypes.c_uint16), ("nChannels", ctypes.c_uint16),
                ("nSamplesPerSec", ctypes.c_uint32),
                ("nAvgBytesPerSec", ctypes.c_uint32),
                ("nBlockAlign", ctypes.c_uint16), ("wBitsPerSample", ctypes.c_uint16),
                ("cbSize", ctypes.c_uint16),
            ]

        class WAVEHDR(ctypes.Structure):
            _fields_ = [
                ("lpData", ctypes.c_void_p), ("dwBufferLength", ctypes.c_uint32),
                ("dwBytesRecorded", ctypes.c_uint32), ("dwUser", ctypes.c_size_t),
                ("dwFlags", ctypes.c_uint32), ("dwLoops", ctypes.c_uint32),
                ("lpNext", ctypes.c_void_p), ("reserved", ctypes.c_size_t),
            ]

        winmm.waveOutOpen.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_uint,
                                      ctypes.POINTER(WAVEFORMATEX), ctypes.c_void_p,
                                      ctypes.c_void_p, ctypes.c_uint]
        winmm.waveOutPrepareHeader.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutWrite.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutUnprepareHeader.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutReset.argtypes = [ctypes.c_void_p]
        winmm.waveOutClose.argtypes = [ctypes.c_void_p]
        fmt = WAVEFORMATEX(1, 1, self.rate, self.rate * 2, 2, 16, 0)
        handle = ctypes.c_void_p()
        if winmm.waveOutOpen(ctypes.byref(handle), 0xFFFFFFFF, ctypes.byref(fmt),
                             None, None, 0) != 0:
            return
        self._winmm = winmm
        self._hwo = handle
        self._pool = []
        self._pool_free = set(range(self._POOL))
        for _ in range(self._POOL):
            buf = ctypes.create_string_buffer(self._CHUNK * 2)
            hdr = WAVEHDR(ctypes.cast(buf, ctypes.c_void_p), self._CHUNK * 2,
                          0, 0, 0, 0, None, 0)
            self._pool.append((buf, hdr))
        self._backend = "winmm"

    def _release_winmm_buffer(self, idx):
        if idx in self._pool_free:
            return
        _, hdr = self._pool[idx]
        if hdr.dwFlags & self.WHDR_PREPARED:
            self._winmm.waveOutUnprepareHeader(
                self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr))
        hdr.dwFlags = 0
        self._pool_free.add(idx)

    def _reap_winmm(self):
        for idx, (_, hdr) in enumerate(self._pool):
            if idx not in self._pool_free and hdr.dwFlags & self.WHDR_DONE:
                self._release_winmm_buffer(idx)

    def _winmm_loop(self):
        while self._alive:
            self._reap_winmm()
            with self._lock:
                ready = len(self._queue) >= self._MIN_START
            if not ready or not self._pool_free:
                time.sleep(0.001)
                continue
            idx = min(self._pool_free)
            self._pool_free.remove(idx)
            buf, hdr = self._pool[idx]
            pcm = self._take_pcm(self._CHUNK)
            ctypes.memmove(buf, pcm, len(pcm))
            hdr.dwBufferLength = len(pcm)
            hdr.dwFlags = 0
            if self._winmm.waveOutPrepareHeader(
                    self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr)) != 0:
                self._pool_free.add(idx)
                continue
            if self._winmm.waveOutWrite(
                    self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr)) != 0:
                self._release_winmm_buffer(idx)

    def _close_winmm(self):
        if self._winmm is None or not self._hwo:
            return
        self._winmm.waveOutReset(self._hwo)
        for idx in range(len(self._pool)):
            self._release_winmm_buffer(idx)
        self._winmm.waveOutClose(self._hwo)
        self._hwo = None
        self._winmm = None
        self._pool.clear()

    # -- macOS: AudioQueue ------------------------------------------------

    def _open_coreaudio(self):
        try:
            audio = ctypes.CDLL(
                "/System/Library/Frameworks/AudioToolbox.framework/AudioToolbox")
        except OSError:
            return

        class AudioStreamBasicDescription(ctypes.Structure):
            _fields_ = [
                ("mSampleRate", ctypes.c_double), ("mFormatID", ctypes.c_uint32),
                ("mFormatFlags", ctypes.c_uint32), ("mBytesPerPacket", ctypes.c_uint32),
                ("mFramesPerPacket", ctypes.c_uint32), ("mBytesPerFrame", ctypes.c_uint32),
                ("mChannelsPerFrame", ctypes.c_uint32), ("mBitsPerChannel", ctypes.c_uint32),
                ("mReserved", ctypes.c_uint32),
            ]

        class AudioQueueBuffer(ctypes.Structure):
            _fields_ = [
                ("mAudioDataBytesCapacity", ctypes.c_uint32),
                ("mAudioData", ctypes.c_void_p),
                ("mAudioDataByteSize", ctypes.c_uint32),
                ("mUserData", ctypes.c_void_p),
                ("mPacketDescriptionCapacity", ctypes.c_uint32),
                ("mPacketDescriptions", ctypes.c_void_p),
            ]

        buffer_ref = ctypes.POINTER(AudioQueueBuffer)
        callback_type = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_void_p, buffer_ref)
        audio.AudioQueueNewOutput.argtypes = [
            ctypes.POINTER(AudioStreamBasicDescription), callback_type,
            ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint32,
            ctypes.POINTER(ctypes.c_void_p),
        ]
        audio.AudioQueueAllocateBuffer.argtypes = [
            ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(buffer_ref)]
        audio.AudioQueueEnqueueBuffer.argtypes = [
            ctypes.c_void_p, buffer_ref, ctypes.c_uint32, ctypes.c_void_p]
        audio.AudioQueueStart.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        audio.AudioQueueStop.argtypes = [ctypes.c_void_p, ctypes.c_ubyte]
        audio.AudioQueueDispose.argtypes = [ctypes.c_void_p, ctypes.c_ubyte]

        def fill_buffer(_user, queue, buffer):
            if not self._alive:
                return
            pcm = self._take_pcm(self._CHUNK)
            ctypes.memmove(buffer.contents.mAudioData, pcm, len(pcm))
            buffer.contents.mAudioDataByteSize = len(pcm)
            audio.AudioQueueEnqueueBuffer(queue, buffer, 0, None)

        callback = callback_type(fill_buffer)
        # 'lpcm', signed integer, packed, native-endian mono 16-bit.
        fmt = AudioStreamBasicDescription(
            float(self.rate), 0x6C70636D, 0x0C, 2, 1, 2, 1, 16, 0)
        queue = ctypes.c_void_p()
        if audio.AudioQueueNewOutput(
                ctypes.byref(fmt), callback, None, None, None, 0,
                ctypes.byref(queue)) != 0:
            return
        self._coreaudio = audio
        self._audio_queue = queue
        self._coreaudio_callback = callback
        self._core_buffers = []
        for _ in range(self._POOL):
            buffer = buffer_ref()
            if audio.AudioQueueAllocateBuffer(
                    queue, self._CHUNK * 2, ctypes.byref(buffer)) != 0:
                self._close_coreaudio()
                return
            self._core_buffers.append(buffer)
            fill_buffer(None, queue, buffer)
        if audio.AudioQueueStart(queue, None) != 0:
            self._close_coreaudio()
            return
        self._backend = "coreaudio"

    def _close_coreaudio(self):
        if self._coreaudio is not None and self._audio_queue:
            self._coreaudio.AudioQueueStop(self._audio_queue, True)
            self._coreaudio.AudioQueueDispose(self._audio_queue, True)
        self._audio_queue = None
        self._coreaudio = None
        self._coreaudio_callback = None
        self._core_buffers.clear()

    # -- Linux: ALSA ------------------------------------------------------

    def _open_alsa(self):
        name = ctypes.util.find_library("asound") or "libasound.so.2"
        try:
            alsa = ctypes.CDLL(name)
        except OSError:
            return
        error_type = ctypes.CFUNCTYPE(
            None, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
            ctypes.c_int, ctypes.c_char_p)
        self._alsa_error_handler = error_type(lambda *_args: None)
        try:
            alsa.snd_lib_error_set_handler(self._alsa_error_handler)
        except AttributeError:
            pass
        alsa.snd_pcm_open.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_char_p,
                                      ctypes.c_int, ctypes.c_int]
        alsa.snd_pcm_set_params.argtypes = [ctypes.c_void_p, ctypes.c_int,
                                            ctypes.c_int, ctypes.c_uint,
                                            ctypes.c_uint, ctypes.c_int,
                                            ctypes.c_uint]
        alsa.snd_pcm_writei.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong]
        alsa.snd_pcm_writei.restype = ctypes.c_long
        alsa.snd_pcm_recover.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
        alsa.snd_pcm_drop.argtypes = [ctypes.c_void_p]
        alsa.snd_pcm_close.argtypes = [ctypes.c_void_p]
        pcm = ctypes.c_void_p()
        if alsa.snd_pcm_open(ctypes.byref(pcm), b"default", 0, 0) < 0:
            return
        # S16_LE=2, RW_INTERLEAVED=3, mono, 80 ms hardware latency.
        if alsa.snd_pcm_set_params(pcm, 2, 3, 1, self.rate, 1, 80000) < 0:
            alsa.snd_pcm_close(pcm)
            return
        self._alsa = alsa
        self._alsa_pcm = pcm
        self._backend = "alsa"

    def _alsa_loop(self):
        while self._alive:
            with self._lock:
                ready = len(self._queue) >= self._MIN_START
            if not ready:
                time.sleep(0.001)
                continue
            pcm = self._take_pcm(self._CHUNK)
            data = ctypes.create_string_buffer(pcm)
            result = self._alsa.snd_pcm_writei(
                self._alsa_pcm, ctypes.cast(data, ctypes.c_void_p), self._CHUNK)
            if result < 0:
                self._alsa.snd_pcm_recover(self._alsa_pcm, int(result), 1)

    def _close_alsa(self):
        if self._alsa is not None and self._alsa_pcm:
            self._alsa.snd_pcm_drop(self._alsa_pcm)
            self._alsa.snd_pcm_close(self._alsa_pcm)
        self._alsa_pcm = None
        self._alsa = None
        self._alsa_error_handler = None

    def _play_loop(self):
        if self._backend == "winmm":
            self._winmm_loop()
        elif self._backend == "alsa":
            self._alsa_loop()


# =============================================================================
#  Controller
# =============================================================================

class Controller:
    BTN_A      = 0x01
    BTN_B      = 0x02
    BTN_SELECT = 0x04
    BTN_START  = 0x08
    BTN_UP     = 0x10
    BTN_DOWN   = 0x20
    BTN_LEFT   = 0x40
    BTN_RIGHT  = 0x80
    def __init__(self):
        self.state = 0
        self.shift = 0
        self.strobe = False
    def set_strobe(self, val):
        old = self.strobe
        self.strobe = bool(val & 1)
        if old and not self.strobe:
            self.shift = self.state
    def read(self):
        if self.strobe:
            return self.state & 1
        v = self.shift & 1
        self.shift = (self.shift >> 1) | 0x80
        return v


# =============================================================================
#  CPU bus
# =============================================================================

class Bus:
    def __init__(self, mapper, ppu, apu, pad1, pad2):
        self.ram = bytearray(2048)
        self.mapper = mapper
        self.ppu = ppu
        self.apu = apu
        self.pad1 = pad1
        self.pad2 = pad2
        self.dma_stall = 0
        self.cpu = None

    def read(self, addr):
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x07FF]
        if addr < 0x4000:
            return self.ppu.reg_read(addr & 7)
        if addr == 0x4015:
            return self.apu.read_status()
        if addr == 0x4016:
            return 0x40 | self.pad1.read()
        if addr == 0x4017:
            return 0x40 | self.pad2.read()
        if addr < 0x4018:
            return 0
        return self.mapper.cpu_read(addr)

    def write(self, addr, val):
        addr &= 0xFFFF
        val &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x07FF] = val
        elif addr < 0x4000:
            self.ppu.reg_write(addr & 7, val)
        elif addr == 0x4014:
            page = val << 8
            data = bytes(self.read(page + i) for i in range(256))
            self.ppu.oam_dma_write(data)
            self.dma_stall += 513
        elif addr == 0x4016:
            self.pad1.set_strobe(val)
            self.pad2.set_strobe(val)
        elif addr < 0x4018:
            self.apu.write(addr, val)
        else:
            self.mapper.cpu_write(addr, val)


# =============================================================================
#  6502 CPU
# =============================================================================

class CPU:
    FLAG_C = 0x01
    FLAG_Z = 0x02
    FLAG_I = 0x04
    FLAG_D = 0x08
    FLAG_B = 0x10
    FLAG_U = 0x20
    FLAG_V = 0x40
    FLAG_N = 0x80

    def __init__(self, bus):
        self.bus = bus
        bus.cpu = self
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.p = 0x24
        self.pc = 0
        self.cycles = 0
        self.pending_nmi = False
        self.pending_irq = False
        self._build_table()

    def reset(self):
        lo = self.bus.read(0xFFFC)
        hi = self.bus.read(0xFFFD)
        self.pc = (hi << 8) | lo
        self.sp = 0xFD
        self.p = 0x24
        self.cycles = 7

    def _read(self, addr):
        addr &= 0xFFFF
        if addr >= 0x8000:
            return self.bus.mapper.cpu_read(addr) & 0xFF
        return self.bus.read(addr) & 0xFF
    def _write(self, addr, val): self.bus.write(addr, val & 0xFF)
    def _read16(self, addr):
        return self._read(addr) | (self._read((addr + 1) & 0xFFFF) << 8)
    def _read16_bug(self, addr):
        a2 = (addr & 0xFF00) | ((addr + 1) & 0xFF)
        return self._read(addr) | (self._read(a2) << 8)
    def _push(self, val):
        self._write(0x100 | self.sp, val)
        self.sp = (self.sp - 1) & 0xFF
    def _pull(self):
        self.sp = (self.sp + 1) & 0xFF
        return self._read(0x100 | self.sp)
    def _push16(self, val):
        self._push((val >> 8) & 0xFF)
        self._push(val & 0xFF)
    def _pull16(self):
        lo = self._pull()
        hi = self._pull()
        return (hi << 8) | lo
    def _set_zn(self, v):
        v &= 0xFF
        self.p = (self.p & ~(self.FLAG_Z | self.FLAG_N))
        if v == 0: self.p |= self.FLAG_Z
        if v & 0x80: self.p |= self.FLAG_N

    def nmi(self): self.pending_nmi = True

    def _do_nmi(self):
        self._push16(self.pc)
        self._push((self.p | 0x20) & ~self.FLAG_B)
        self.p |= self.FLAG_I
        self.pc = self._read(0xFFFA) | (self._read(0xFFFB) << 8)
        self.cycles += 7

    def _do_irq(self):
        self._push16(self.pc)
        self._push((self.p | 0x20) & ~self.FLAG_B)
        self.p |= self.FLAG_I
        self.pc = self._read(0xFFFE) | (self._read(0xFFFF) << 8)
        self.cycles += 7

    # Addressing modes
    def _am_imm(self):
        a = self.pc; self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zp(self):
        a = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zpx(self):
        a = (self._read(self.pc) + self.x) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zpy(self):
        a = (self._read(self.pc) + self.y) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_abs(self):
        a = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF; return a, 0
    def _am_absx(self, write=False):
        base = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        a = (base + self.x) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_absy(self, write=False):
        base = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        a = (base + self.y) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_ind(self):
        ptr = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        return self._read16_bug(ptr), 0
    def _am_indx(self):
        zp = (self._read(self.pc) + self.x) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF
        return self._read(zp) | (self._read((zp + 1) & 0xFF) << 8), 0
    def _am_indy(self, write=False):
        zp = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        base = self._read(zp) | (self._read((zp + 1) & 0xFF) << 8)
        a = (base + self.y) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_rel(self):
        d = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        if d & 0x80: d -= 0x100
        return (self.pc + d) & 0xFFFF, 0

    # Ops
    def _op_adc(self, a):
        m = self._read(a); c = self.p & 1
        r = self.a + m + c
        v = (~(self.a ^ m) & (self.a ^ r)) & 0x80
        self.p = (self.p & ~(self.FLAG_C | self.FLAG_V)) | (1 if r > 0xFF else 0) | (self.FLAG_V if v else 0)
        self.a = r & 0xFF
        self._set_zn(self.a)
    def _op_sbc(self, a):
        m = self._read(a) ^ 0xFF; c = self.p & 1
        r = self.a + m + c
        v = (~(self.a ^ m) & (self.a ^ r)) & 0x80
        self.p = (self.p & ~(self.FLAG_C | self.FLAG_V)) | (1 if r > 0xFF else 0) | (self.FLAG_V if v else 0)
        self.a = r & 0xFF
        self._set_zn(self.a)
    def _op_and(self, a): self.a &= self._read(a); self._set_zn(self.a)
    def _op_ora(self, a): self.a |= self._read(a); self._set_zn(self.a)
    def _op_eor(self, a): self.a ^= self._read(a); self._set_zn(self.a)
    def _op_asl_a(self):
        self.p = (self.p & ~1) | ((self.a >> 7) & 1)
        self.a = (self.a << 1) & 0xFF; self._set_zn(self.a)
    def _op_asl(self, a):
        m = self._read(a)
        self.p = (self.p & ~1) | ((m >> 7) & 1)
        m = (m << 1) & 0xFF; self._write(a, m); self._set_zn(m)
    def _op_lsr_a(self):
        self.p = (self.p & ~1) | (self.a & 1); self.a >>= 1; self._set_zn(self.a)
    def _op_lsr(self, a):
        m = self._read(a)
        self.p = (self.p & ~1) | (m & 1); m >>= 1; self._write(a, m); self._set_zn(m)
    def _op_rol_a(self):
        c = self.p & 1
        self.p = (self.p & ~1) | ((self.a >> 7) & 1)
        self.a = ((self.a << 1) | c) & 0xFF; self._set_zn(self.a)
    def _op_rol(self, a):
        m = self._read(a); c = self.p & 1
        self.p = (self.p & ~1) | ((m >> 7) & 1)
        m = ((m << 1) | c) & 0xFF; self._write(a, m); self._set_zn(m)
    def _op_ror_a(self):
        c = (self.p & 1) << 7
        self.p = (self.p & ~1) | (self.a & 1)
        self.a = (self.a >> 1) | c; self._set_zn(self.a)
    def _op_ror(self, a):
        m = self._read(a); c = (self.p & 1) << 7
        self.p = (self.p & ~1) | (m & 1)
        m = (m >> 1) | c; self._write(a, m); self._set_zn(m)
    def _op_bit(self, a):
        m = self._read(a); r = self.a & m
        self.p = (self.p & ~(self.FLAG_Z | self.FLAG_N | self.FLAG_V))
        if r == 0: self.p |= self.FLAG_Z
        self.p |= (m & 0xC0)
    def _op_cmp(self, reg, a):
        m = self._read(a); r = reg - m
        self.p = (self.p & ~1) | (1 if reg >= m else 0)
        self._set_zn(r & 0xFF)
    def _branch(self, cond, target):
        if not cond: return 0
        extra = 2 if (target & 0xFF00) != (self.pc & 0xFF00) else 1
        self.pc = target
        return extra

    def _build_table(self):
        T = [None] * 256
        def op(c, fn, cy): T[c] = (fn, cy)

        op(0x69, lambda: (self._op_adc(self._am_imm()[0]), 0)[1], 2)
        op(0x65, lambda: (self._op_adc(self._am_zp()[0]), 0)[1], 3)
        op(0x75, lambda: (self._op_adc(self._am_zpx()[0]), 0)[1], 4)
        op(0x6D, lambda: (self._op_adc(self._am_abs()[0]), 0)[1], 4)
        op(0x7D, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x79, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x61, lambda: (self._op_adc(self._am_indx()[0]), 0)[1], 6)
        op(0x71, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xE9, lambda: (self._op_sbc(self._am_imm()[0]), 0)[1], 2)
        op(0xEB, lambda: (self._op_sbc(self._am_imm()[0]), 0)[1], 2)
        op(0xE5, lambda: (self._op_sbc(self._am_zp()[0]), 0)[1], 3)
        op(0xF5, lambda: (self._op_sbc(self._am_zpx()[0]), 0)[1], 4)
        op(0xED, lambda: (self._op_sbc(self._am_abs()[0]), 0)[1], 4)
        op(0xFD, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xF9, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xE1, lambda: (self._op_sbc(self._am_indx()[0]), 0)[1], 6)
        op(0xF1, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x29, lambda: (self._op_and(self._am_imm()[0]), 0)[1], 2)
        op(0x25, lambda: (self._op_and(self._am_zp()[0]), 0)[1], 3)
        op(0x35, lambda: (self._op_and(self._am_zpx()[0]), 0)[1], 4)
        op(0x2D, lambda: (self._op_and(self._am_abs()[0]), 0)[1], 4)
        op(0x3D, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x39, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x21, lambda: (self._op_and(self._am_indx()[0]), 0)[1], 6)
        op(0x31, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x09, lambda: (self._op_ora(self._am_imm()[0]), 0)[1], 2)
        op(0x05, lambda: (self._op_ora(self._am_zp()[0]), 0)[1], 3)
        op(0x15, lambda: (self._op_ora(self._am_zpx()[0]), 0)[1], 4)
        op(0x0D, lambda: (self._op_ora(self._am_abs()[0]), 0)[1], 4)
        op(0x1D, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x19, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x01, lambda: (self._op_ora(self._am_indx()[0]), 0)[1], 6)
        op(0x11, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x49, lambda: (self._op_eor(self._am_imm()[0]), 0)[1], 2)
        op(0x45, lambda: (self._op_eor(self._am_zp()[0]), 0)[1], 3)
        op(0x55, lambda: (self._op_eor(self._am_zpx()[0]), 0)[1], 4)
        op(0x4D, lambda: (self._op_eor(self._am_abs()[0]), 0)[1], 4)
        op(0x5D, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x59, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x41, lambda: (self._op_eor(self._am_indx()[0]), 0)[1], 6)
        op(0x51, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x0A, lambda: (self._op_asl_a(), 0)[1], 2)
        op(0x06, lambda: (self._op_asl(self._am_zp()[0]), 0)[1], 5)
        op(0x16, lambda: (self._op_asl(self._am_zpx()[0]), 0)[1], 6)
        op(0x0E, lambda: (self._op_asl(self._am_abs()[0]), 0)[1], 6)
        op(0x1E, lambda: (self._op_asl(self._am_absx(True)[0]), 0)[1], 7)
        op(0x4A, lambda: (self._op_lsr_a(), 0)[1], 2)
        op(0x46, lambda: (self._op_lsr(self._am_zp()[0]), 0)[1], 5)
        op(0x56, lambda: (self._op_lsr(self._am_zpx()[0]), 0)[1], 6)
        op(0x4E, lambda: (self._op_lsr(self._am_abs()[0]), 0)[1], 6)
        op(0x5E, lambda: (self._op_lsr(self._am_absx(True)[0]), 0)[1], 7)
        op(0x2A, lambda: (self._op_rol_a(), 0)[1], 2)
        op(0x26, lambda: (self._op_rol(self._am_zp()[0]), 0)[1], 5)
        op(0x36, lambda: (self._op_rol(self._am_zpx()[0]), 0)[1], 6)
        op(0x2E, lambda: (self._op_rol(self._am_abs()[0]), 0)[1], 6)
        op(0x3E, lambda: (self._op_rol(self._am_absx(True)[0]), 0)[1], 7)
        op(0x6A, lambda: (self._op_ror_a(), 0)[1], 2)
        op(0x66, lambda: (self._op_ror(self._am_zp()[0]), 0)[1], 5)
        op(0x76, lambda: (self._op_ror(self._am_zpx()[0]), 0)[1], 6)
        op(0x6E, lambda: (self._op_ror(self._am_abs()[0]), 0)[1], 6)
        op(0x7E, lambda: (self._op_ror(self._am_absx(True)[0]), 0)[1], 7)
        op(0x24, lambda: (self._op_bit(self._am_zp()[0]), 0)[1], 3)
        op(0x2C, lambda: (self._op_bit(self._am_abs()[0]), 0)[1], 4)

        def _lda(a): self.a = self._read(a); self._set_zn(self.a)
        def _ldx(a): self.x = self._read(a); self._set_zn(self.x)
        def _ldy(a): self.y = self._read(a); self._set_zn(self.y)
        op(0xA9, lambda: (_lda(self._am_imm()[0]), 0)[1], 2)
        op(0xA5, lambda: (_lda(self._am_zp()[0]), 0)[1], 3)
        op(0xB5, lambda: (_lda(self._am_zpx()[0]), 0)[1], 4)
        op(0xAD, lambda: (_lda(self._am_abs()[0]), 0)[1], 4)
        op(0xBD, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xB9, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xA1, lambda: (_lda(self._am_indx()[0]), 0)[1], 6)
        op(0xB1, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xA2, lambda: (_ldx(self._am_imm()[0]), 0)[1], 2)
        op(0xA6, lambda: (_ldx(self._am_zp()[0]), 0)[1], 3)
        op(0xB6, lambda: (_ldx(self._am_zpy()[0]), 0)[1], 4)
        op(0xAE, lambda: (_ldx(self._am_abs()[0]), 0)[1], 4)
        op(0xBE, lambda: (lambda r: (_ldx(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xA0, lambda: (_ldy(self._am_imm()[0]), 0)[1], 2)
        op(0xA4, lambda: (_ldy(self._am_zp()[0]), 0)[1], 3)
        op(0xB4, lambda: (_ldy(self._am_zpx()[0]), 0)[1], 4)
        op(0xAC, lambda: (_ldy(self._am_abs()[0]), 0)[1], 4)
        op(0xBC, lambda: (lambda r: (_ldy(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x85, lambda: (self._write(self._am_zp()[0], self.a), 0)[1], 3)
        op(0x95, lambda: (self._write(self._am_zpx()[0], self.a), 0)[1], 4)
        op(0x8D, lambda: (self._write(self._am_abs()[0], self.a), 0)[1], 4)
        op(0x9D, lambda: (self._write(self._am_absx(True)[0], self.a), 0)[1], 5)
        op(0x99, lambda: (self._write(self._am_absy(True)[0], self.a), 0)[1], 5)
        op(0x81, lambda: (self._write(self._am_indx()[0], self.a), 0)[1], 6)
        op(0x91, lambda: (self._write(self._am_indy(True)[0], self.a), 0)[1], 6)
        op(0x86, lambda: (self._write(self._am_zp()[0], self.x), 0)[1], 3)
        op(0x96, lambda: (self._write(self._am_zpy()[0], self.x), 0)[1], 4)
        op(0x8E, lambda: (self._write(self._am_abs()[0], self.x), 0)[1], 4)
        op(0x84, lambda: (self._write(self._am_zp()[0], self.y), 0)[1], 3)
        op(0x94, lambda: (self._write(self._am_zpx()[0], self.y), 0)[1], 4)
        op(0x8C, lambda: (self._write(self._am_abs()[0], self.y), 0)[1], 4)

        def _tax(): self.x = self.a; self._set_zn(self.x)
        def _tay(): self.y = self.a; self._set_zn(self.y)
        def _txa(): self.a = self.x; self._set_zn(self.a)
        def _tya(): self.a = self.y; self._set_zn(self.a)
        def _tsx(): self.x = self.sp; self._set_zn(self.x)
        def _txs(): self.sp = self.x
        op(0xAA, lambda: (_tax(), 0)[1], 2)
        op(0xA8, lambda: (_tay(), 0)[1], 2)
        op(0x8A, lambda: (_txa(), 0)[1], 2)
        op(0x98, lambda: (_tya(), 0)[1], 2)
        op(0xBA, lambda: (_tsx(), 0)[1], 2)
        op(0x9A, lambda: (_txs(), 0)[1], 2)

        op(0x48, lambda: (self._push(self.a), 0)[1], 3)
        op(0x08, lambda: (self._push(self.p | 0x30), 0)[1], 3)
        def _pla():
            self.a = self._pull(); self._set_zn(self.a)
        op(0x68, lambda: (_pla(), 0)[1], 4)
        def _plp(): self.p = (self._pull() & ~0x10) | 0x20
        op(0x28, lambda: (_plp(), 0)[1], 4)

        def _inc(a): m = (self._read(a) + 1) & 0xFF; self._write(a, m); self._set_zn(m)
        def _dec(a): m = (self._read(a) - 1) & 0xFF; self._write(a, m); self._set_zn(m)
        op(0xE6, lambda: (_inc(self._am_zp()[0]), 0)[1], 5)
        op(0xF6, lambda: (_inc(self._am_zpx()[0]), 0)[1], 6)
        op(0xEE, lambda: (_inc(self._am_abs()[0]), 0)[1], 6)
        op(0xFE, lambda: (_inc(self._am_absx(True)[0]), 0)[1], 7)
        op(0xC6, lambda: (_dec(self._am_zp()[0]), 0)[1], 5)
        op(0xD6, lambda: (_dec(self._am_zpx()[0]), 0)[1], 6)
        op(0xCE, lambda: (_dec(self._am_abs()[0]), 0)[1], 6)
        op(0xDE, lambda: (_dec(self._am_absx(True)[0]), 0)[1], 7)
        def _inx(): self.x = (self.x + 1) & 0xFF; self._set_zn(self.x)
        def _dex(): self.x = (self.x - 1) & 0xFF; self._set_zn(self.x)
        def _iny(): self.y = (self.y + 1) & 0xFF; self._set_zn(self.y)
        def _dey(): self.y = (self.y - 1) & 0xFF; self._set_zn(self.y)
        op(0xE8, lambda: (_inx(), 0)[1], 2)
        op(0xCA, lambda: (_dex(), 0)[1], 2)
        op(0xC8, lambda: (_iny(), 0)[1], 2)
        op(0x88, lambda: (_dey(), 0)[1], 2)

        op(0xC9, lambda: (self._op_cmp(self.a, self._am_imm()[0]), 0)[1], 2)
        op(0xC5, lambda: (self._op_cmp(self.a, self._am_zp()[0]), 0)[1], 3)
        op(0xD5, lambda: (self._op_cmp(self.a, self._am_zpx()[0]), 0)[1], 4)
        op(0xCD, lambda: (self._op_cmp(self.a, self._am_abs()[0]), 0)[1], 4)
        op(0xDD, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xD9, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xC1, lambda: (self._op_cmp(self.a, self._am_indx()[0]), 0)[1], 6)
        op(0xD1, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xE0, lambda: (self._op_cmp(self.x, self._am_imm()[0]), 0)[1], 2)
        op(0xE4, lambda: (self._op_cmp(self.x, self._am_zp()[0]), 0)[1], 3)
        op(0xEC, lambda: (self._op_cmp(self.x, self._am_abs()[0]), 0)[1], 4)
        op(0xC0, lambda: (self._op_cmp(self.y, self._am_imm()[0]), 0)[1], 2)
        op(0xC4, lambda: (self._op_cmp(self.y, self._am_zp()[0]), 0)[1], 3)
        op(0xCC, lambda: (self._op_cmp(self.y, self._am_abs()[0]), 0)[1], 4)

        op(0x10, lambda: self._branch(not (self.p & self.FLAG_N), self._am_rel()[0]), 2)
        op(0x30, lambda: self._branch(bool(self.p & self.FLAG_N), self._am_rel()[0]), 2)
        op(0x50, lambda: self._branch(not (self.p & self.FLAG_V), self._am_rel()[0]), 2)
        op(0x70, lambda: self._branch(bool(self.p & self.FLAG_V), self._am_rel()[0]), 2)
        op(0x90, lambda: self._branch(not (self.p & self.FLAG_C), self._am_rel()[0]), 2)
        op(0xB0, lambda: self._branch(bool(self.p & self.FLAG_C), self._am_rel()[0]), 2)
        op(0xD0, lambda: self._branch(not (self.p & self.FLAG_Z), self._am_rel()[0]), 2)
        op(0xF0, lambda: self._branch(bool(self.p & self.FLAG_Z), self._am_rel()[0]), 2)

        def _jmp_abs():
            self.pc = self._am_abs()[0]
        def _jmp_ind():
            self.pc = self._am_ind()[0]
        def _jsr():
            a = self._am_abs()[0]
            self._push16((self.pc - 1) & 0xFFFF)
            self.pc = a
        def _rts():
            self.pc = (self._pull16() + 1) & 0xFFFF
        def _rti():
            self.p = (self._pull() & ~0x10) | 0x20
            self.pc = self._pull16()
        op(0x4C, lambda: (_jmp_abs(), 0)[1], 3)
        op(0x6C, lambda: (_jmp_ind(), 0)[1], 5)
        op(0x20, lambda: (_jsr(), 0)[1], 6)
        op(0x60, lambda: (_rts(), 0)[1], 6)
        op(0x40, lambda: (_rti(), 0)[1], 6)

        def _clc(): self.p &= ~self.FLAG_C
        def _sec(): self.p |= self.FLAG_C
        def _cli(): self.p &= ~self.FLAG_I
        def _sei(): self.p |= self.FLAG_I
        def _clv(): self.p &= ~self.FLAG_V
        def _cld(): self.p &= ~self.FLAG_D
        def _sed(): self.p |= self.FLAG_D
        op(0x18, lambda: (_clc(), 0)[1], 2)
        op(0x38, lambda: (_sec(), 0)[1], 2)
        op(0x58, lambda: (_cli(), 0)[1], 2)
        op(0x78, lambda: (_sei(), 0)[1], 2)
        op(0xB8, lambda: (_clv(), 0)[1], 2)
        op(0xD8, lambda: (_cld(), 0)[1], 2)
        op(0xF8, lambda: (_sed(), 0)[1], 2)

        # NOPs (official + common unofficial)
        for c in (0xEA, 0x1A, 0x3A, 0x5A, 0x7A, 0xDA, 0xFA):
            op(c, lambda: 0, 2)
        for c in (0x80, 0x82, 0x89, 0xC2, 0xE2):
            op(c, lambda: (self._am_imm(), 0)[1], 2)
        for c in (0x04, 0x44, 0x64):
            op(c, lambda: (self._am_zp(), 0)[1], 3)
        for c in (0x14, 0x34, 0x54, 0x74, 0xD4, 0xF4):
            op(c, lambda: (self._am_zpx(), 0)[1], 4)
        op(0x0C, lambda: (self._am_abs(), 0)[1], 4)
        for c in (0x1C, 0x3C, 0x5C, 0x7C, 0xDC, 0xFC):
            op(c, lambda: (lambda r: r[1])(self._am_absx()), 4)

        def _brk():
            self.pc = (self.pc + 1) & 0xFFFF
            self._push16(self.pc)
            self._push(self.p | 0x30)
            self.p |= self.FLAG_I
            self.pc = self._read(0xFFFE) | (self._read(0xFFFF) << 8)
        op(0x00, lambda: (_brk(), 0)[1], 7)

        self._table = T

    def step(self):
        apu = self.bus.apu
        if self.pending_nmi:
            self.pending_nmi = False
            self._do_nmi()
            apu.clock(7)
            return 7
        if self.pending_irq and not (self.p & self.FLAG_I):
            self.pending_irq = False
            self._do_irq()
            apu.clock(7)
            return 7
        if self.bus.dma_stall:
            stalled = self.bus.dma_stall
            self.bus.dma_stall = 0
            self.cycles += stalled
            apu.clock(stalled)
            return stalled
        bus = self.bus
        if self.pc >= 0x8000:
            opcode = bus.mapper.cpu_read(self.pc) & 0xFF
        else:
            opcode = bus.read(self.pc) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF

        # Hot-path official opcodes.  Keeping these directly in the dispatch
        # loop avoids several lambda/addressing-mode calls for the operations
        # that dominate commercial NES games; uncommon and unofficial opcodes
        # still use the complete table below.
        code_read = bus.mapper.cpu_read if self.pc >= 0x8000 else bus.read
        cy = 0
        if opcode == 0x4C:  # JMP absolute
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (hi << 8) | lo
            cy = 3
        elif opcode == 0xEA:  # NOP
            cy = 2
        elif opcode in (0xA9, 0xA2, 0xA0):  # LDA/LDX/LDY immediate
            value = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xA9:
                self.a = value
            elif opcode == 0xA2:
                self.x = value
            else:
                self.y = value
            self._set_zn(value)
            cy = 2
        elif opcode in (0xA5, 0xB5):  # LDA zp/zp,X
            addr = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xB5:
                addr = (addr + self.x) & 0xFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 4 if opcode == 0xB5 else 3
        elif opcode in (0xAD, 0xBD, 0xB9):  # LDA abs/abs,X/abs,Y
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            base = (hi << 8) | lo
            index = self.x if opcode == 0xBD else (self.y if opcode == 0xB9 else 0)
            addr = (base + index) & 0xFFFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 4 + (1 if opcode != 0xAD and (base ^ addr) & 0xFF00 else 0)
        elif opcode == 0xB1:  # LDA (zp),Y
            zp = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            base = bus.read(zp) | (bus.read((zp + 1) & 0xFF) << 8)
            addr = (base + self.y) & 0xFFFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 5 + (1 if (base ^ addr) & 0xFF00 else 0)
        elif opcode in (0x85, 0x95):  # STA zp/zp,X
            addr = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x95:
                addr = (addr + self.x) & 0xFF
            bus.write(addr, self.a)
            cy = 4 if opcode == 0x95 else 3
        elif opcode in (0x8D, 0x9D, 0x99):  # STA abs/abs,X/abs,Y
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            index = self.x if opcode == 0x9D else (self.y if opcode == 0x99 else 0)
            bus.write(((hi << 8) | lo) + index & 0xFFFF, self.a)
            cy = 5 if opcode != 0x8D else 4
        elif opcode == 0x91:  # STA (zp),Y
            zp = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            addr = (bus.read(zp) | (bus.read((zp + 1) & 0xFF) << 8)) + self.y
            bus.write(addr & 0xFFFF, self.a)
            cy = 6
        elif opcode in (0xE8, 0xCA, 0xC8, 0x88):
            if opcode == 0xE8:
                self.x = (self.x + 1) & 0xFF
                value = self.x
            elif opcode == 0xCA:
                self.x = (self.x - 1) & 0xFF
                value = self.x
            elif opcode == 0xC8:
                self.y = (self.y + 1) & 0xFF
                value = self.y
            else:
                self.y = (self.y - 1) & 0xFF
                value = self.y
            self._set_zn(value)
            cy = 2
        elif opcode in (0xAA, 0x8A, 0xA8, 0x98, 0xBA, 0x9A):
            if opcode == 0xAA:
                self.x = self.a; value = self.x
            elif opcode == 0x8A:
                self.a = self.x; value = self.a
            elif opcode == 0xA8:
                self.y = self.a; value = self.y
            elif opcode == 0x98:
                self.a = self.y; value = self.a
            elif opcode == 0xBA:
                self.x = self.sp; value = self.x
            else:
                self.sp = self.x; value = None
            if value is not None:
                self._set_zn(value)
            cy = 2
        elif opcode in (0x09, 0x29, 0x49, 0x69, 0xE9, 0xC9, 0xE0, 0xC0):
            operand_addr = self.pc
            value = code_read(operand_addr)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x09:
                self.a |= value; self._set_zn(self.a)
            elif opcode == 0x29:
                self.a &= value; self._set_zn(self.a)
            elif opcode == 0x49:
                self.a ^= value; self._set_zn(self.a)
            elif opcode == 0x69:
                self._op_adc(operand_addr)
            elif opcode == 0xE9:
                self._op_sbc(operand_addr)
            elif opcode == 0xC9:
                self._op_cmp(self.a, operand_addr)
            elif opcode == 0xE0:
                self._op_cmp(self.x, operand_addr)
            else:
                self._op_cmp(self.y, operand_addr)
            cy = 2
        elif opcode in (0x10, 0x30, 0x50, 0x70, 0x90, 0xB0, 0xD0, 0xF0):
            offset = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            condition = (
                not (self.p & self.FLAG_N) if opcode == 0x10 else
                bool(self.p & self.FLAG_N) if opcode == 0x30 else
                not (self.p & self.FLAG_V) if opcode == 0x50 else
                bool(self.p & self.FLAG_V) if opcode == 0x70 else
                not (self.p & self.FLAG_C) if opcode == 0x90 else
                bool(self.p & self.FLAG_C) if opcode == 0xB0 else
                not (self.p & self.FLAG_Z) if opcode == 0xD0 else
                bool(self.p & self.FLAG_Z)
            )
            cy = 2
            if condition:
                old_pc = self.pc
                signed = offset - 256 if offset & 0x80 else offset
                self.pc = (self.pc + signed) & 0xFFFF
                cy += 1 + (1 if (old_pc ^ self.pc) & 0xFF00 else 0)
        elif opcode in (0x18, 0x38, 0x58, 0x78, 0xB8, 0xD8, 0xF8):
            if opcode == 0x18: self.p &= ~self.FLAG_C
            elif opcode == 0x38: self.p |= self.FLAG_C
            elif opcode == 0x58: self.p &= ~self.FLAG_I
            elif opcode == 0x78: self.p |= self.FLAG_I
            elif opcode == 0xB8: self.p &= ~self.FLAG_V
            elif opcode == 0xD8: self.p &= ~self.FLAG_D
            else: self.p |= self.FLAG_D
            cy = 2
        elif opcode == 0x20:  # JSR
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self._push16((self.pc + 1) & 0xFFFF)
            self.pc = (hi << 8) | lo
            cy = 6
        elif opcode == 0x60:  # RTS
            self.pc = (self._pull16() + 1) & 0xFFFF
            cy = 6

        if cy:
            self.cycles += cy
            apu.clock(cy)
            return cy
        entry = self._table[opcode]
        if entry is None:
            self.cycles += 2
            apu.clock(2)
            return 2
        fn, base_cy = entry
        extra = fn() or 0
        cy = base_cy + extra
        self.cycles += cy
        apu.clock(cy)
        return cy


# =============================================================================
#  Engine — NES system (NTSC CPU / PPU / APU core)
# =============================================================================

class NES:
    def __init__(self, rom_path, audio=None):
        self.rom = ROM(rom_path)
        self.mapper = make_mapper(self.rom)
        self.ppu = PPU(self.mapper)
        self.apu = APU()
        self.pad1 = Controller()
        self.pad2 = Controller()
        self.bus = Bus(self.mapper, self.ppu, self.apu, self.pad1, self.pad2)
        self.apu.bus = self.bus
        self.apu.dmc.bus = self.bus
        self.apu.audio = audio
        self.ppu.apu = self.apu
        self.cpu = CPU(self.bus)
        self.cpu.reset()
        self.ppu.scanline = 0
        self._cpu_target = float(self.cpu.cycles)

    def run_frame(self):
        cycles_per_scanline = NTSC_CYCLES_PER_SCANLINE
        ppu = self.ppu
        cpu = self.cpu
        mapper = self.mapper
        apu = self.apu
        for _ in range(PPU_SCANLINES):
            self._cpu_target += cycles_per_scanline
            while cpu.cycles < self._cpu_target:
                cpu.step()
                if (mapper.irq_pending or apu.frame_irq_pending
                        or apu.dmc.irq_pending):
                    cpu.pending_irq = True
                    mapper.irq_pending = False
            ppu.step_scanline()
            if ppu.nmi:
                ppu.nmi = False
                cpu.nmi()


# =============================================================================
#  Tkinter GUI — luigines emu 0.1.x (File/CPU/Options/Help, viewport, status)
# =============================================================================

SCALE = 2
SCREEN_W = 256
SCREEN_H = 240
APP_VERSION = "0.1.x"
WINDOW_TITLE = "luigines emu 0.1.x"

KEYMAP_P1 = {
    "x": Controller.BTN_A,
    "X": Controller.BTN_A,
    "z": Controller.BTN_B,
    "Z": Controller.BTN_B,
    "Return": Controller.BTN_START,
    "Shift_R": Controller.BTN_SELECT,
    "Shift_L": Controller.BTN_SELECT,
    "Up": Controller.BTN_UP,
    "Down": Controller.BTN_DOWN,
    "Left": Controller.BTN_LEFT,
    "Right": Controller.BTN_RIGHT,
    "w": Controller.BTN_UP, "W": Controller.BTN_UP,
    "s": Controller.BTN_DOWN, "S": Controller.BTN_DOWN,
    "a": Controller.BTN_LEFT, "A": Controller.BTN_LEFT,
    "d": Controller.BTN_RIGHT, "D": Controller.BTN_RIGHT,
}


class EmuApp:
    # Classic Windows-style chrome; game viewport stays black.
    BG = "#d4d0c8"
    VIEWPORT_BG = "#000000"
    STATUS_BG = "#d4d0c8"
    STATUS_FG = "#000000"

    def __init__(self, root, rom_path=None):
        self.root = root
        self.root.title(WINDOW_TITLE)
        self.root.configure(bg=self.BG)
        self.root.minsize(SCREEN_W * SCALE + 8, SCREEN_H * SCALE + 64)
        self.nes = None
        self.running = False
        self.paused = False
        self.audio = None
        self.fps = 0.0
        self._fps_frames = 0
        self._fps_t0 = time.perf_counter()
        self._frame_clock = time.perf_counter() + FRAME_SEC
        self._build_menu()
        self._build_widgets()
        self._bind_keys()
        self.root.update_idletasks()
        if AUDIO_ENABLED:
            self.audio = AudioStream()
            self.audio.start()
        self.root.protocol("WM_DELETE_WINDOW", self._quit)
        if rom_path and os.path.isfile(rom_path):
            self._open(rom_path)
        else:
            self._show_splash()
        self._schedule_frame()

    def _build_menu(self):
        menubar = tk.Menu(self.root)

        m_file = tk.Menu(menubar, tearoff=0)
        m_file.add_command(label="Open ROM...", command=self._open_dialog,
                           accelerator="Ctrl+O")
        m_file.add_command(label="Close ROM", command=self._close_rom)
        m_file.add_separator()
        m_file.add_command(label="Exit", command=self._quit, accelerator="Alt+F4")
        menubar.add_cascade(label="File", menu=m_file)

        m_cpu = tk.Menu(menubar, tearoff=0)
        m_cpu.add_command(label="Reset", command=self._reset, accelerator="Ctrl+R")
        m_cpu.add_command(label="Power Cycle", command=self._power_cycle)
        m_cpu.add_separator()
        m_cpu.add_command(label="Pause", command=self._toggle_pause, accelerator="P")
        menubar.add_cascade(label="CPU", menu=m_cpu)

        m_opt = tk.Menu(menubar, tearoff=0)
        m_opt.add_command(label=f"Zoom {SCALE}x (fixed)", state="disabled")
        m_opt.add_command(label="Display... 256x240 NTSC", state="disabled")
        audio_cfg = (f"Sound... 2A03 {SAMPLE_RATE} Hz"
                     if AUDIO_ENABLED and not AUDIO_FILES else "Sound... off")
        m_opt.add_command(label=audio_cfg, state="disabled")
        m_opt.add_separator()
        m_opt.add_command(label=f"Speed... locked {TARGET_FPS:.0f} FPS",
                          state="disabled")
        m_opt.add_command(label="Input... keyboard", state="disabled")
        menubar.add_cascade(label="Options", menu=m_opt)

        m_help = tk.Menu(menubar, tearoff=0)
        m_help.add_command(label="Controls", command=self._controls_help)
        m_help.add_separator()
        m_help.add_command(label="About luigines", command=self._about)
        menubar.add_cascade(label="Help", menu=m_help)

        self.root.config(menu=menubar)

    def _build_widgets(self):
        # Status bar first so the viewport fills remaining space above it.
        status_frame = tk.Frame(self.root, bg=self.STATUS_BG, bd=1, relief="sunken")
        status_frame.pack(side="bottom", fill="x")
        self.status_var = tk.StringVar(value="No ROM loaded.")
        tk.Label(status_frame, textvariable=self.status_var, anchor="w",
                 bg=self.STATUS_BG, fg=self.STATUS_FG,
                 font=("TkDefaultFont", 9)).pack(
                     side="left", fill="x", expand=True, padx=4, pady=1)
        self.status_fps_var = tk.StringVar(value="--- fps")
        tk.Label(status_frame, textvariable=self.status_fps_var, anchor="e",
                 bg=self.STATUS_BG, fg=self.STATUS_FG,
                 font=("TkDefaultFont", 9)).pack(side="right", padx=4, pady=1)

        cw = SCREEN_W * SCALE
        ch = SCREEN_H * SCALE
        self.canvas = tk.Canvas(self.root, width=cw, height=ch,
                                bg=self.VIEWPORT_BG, highlightthickness=0, bd=0)
        self.canvas.pack(side="top", fill="both", expand=True)
        self.photo = tk.PhotoImage(width=cw, height=ch)
        self.canvas_img = self.canvas.create_image(0, 0, image=self.photo,
                                                   anchor="nw")

    def _bind_keys(self):
        self.root.bind("<KeyPress>",   self._on_key_down)
        self.root.bind("<KeyRelease>", self._on_key_up)
        self.root.bind("<Control-o>",  lambda e: self._open_dialog())
        self.root.bind("<Control-O>",  lambda e: self._open_dialog())
        self.root.bind("<Control-r>",  lambda e: self._reset())
        self.root.bind("<Control-R>",  lambda e: self._reset())
        self.root.bind("<KeyPress-p>", lambda e: self._toggle_pause())
        self.root.bind("<Pause>",      lambda e: self._toggle_pause())

    def _on_key_down(self, ev):
        bit = KEYMAP_P1.get(ev.keysym)
        if bit is not None and self.nes is not None:
            self.nes.pad1.state |= bit

    def _on_key_up(self, ev):
        bit = KEYMAP_P1.get(ev.keysym)
        if bit is not None and self.nes is not None:
            self.nes.pad1.state &= ~bit & 0xFF

    def _show_splash(self):
        cw = SCREEN_W * SCALE
        ch = SCREEN_H * SCALE
        self.photo.put("#000000", to=(0, 0, cw, ch))
        self.canvas.delete("splash")
        self.canvas.create_text(cw // 2, ch // 2 - 12, anchor="center",
                                text=WINDOW_TITLE, fill="#c0c0c0",
                                font=("TkDefaultFont", 16, "bold"), tags="splash")
        self.canvas.create_text(cw // 2, ch // 2 + 14, anchor="center",
                                text="File > Open ROM... to begin",
                                fill="#808080", font=("TkDefaultFont", 10),
                                tags="splash")

    def _hide_splash(self):
        self.canvas.delete("splash")

    def _rom_display_name(self, path):
        name = os.path.splitext(os.path.basename(path))[0]
        return name.replace("_", " ").replace(".", " ")

    def _open_dialog(self):
        path = filedialog.askopenfilename(
            title="Open NES ROM",
            filetypes=[("NES iNES ROM", "*.nes"), ("All files", "*.*")])
        if path:
            self._open(path)

    def _open(self, path):
        if self.audio is None and AUDIO_ENABLED:
            self.audio = AudioStream()
        if self.audio is not None:
            self.audio.start()
        try:
            nes = NES(path, self.audio)
        except Exception as e:
            messagebox.showerror("luigines",
                                 f"Failed to load ROM:\n{path}\n\n{e}")
            return
        self.nes = nes
        self.running = True
        self.paused = False
        self._fps_frames = 0
        self._fps_t0 = time.perf_counter()
        self._frame_clock = time.perf_counter() + FRAME_SEC
        self._hide_splash()
        self.status_var.set(f"{self._rom_display_name(path)} initialized")
        self.status_fps_var.set("--- fps")
        self.root.title(WINDOW_TITLE)

    def _close_rom(self):
        if self.nes and self.nes.apu:
            self.nes.apu.audio = None
        if self.nes and self.nes.ppu:
            self.nes.ppu.apu = None
        self.nes = None
        self.running = False
        self.status_var.set("No ROM loaded.")
        self.status_fps_var.set("--- fps")
        self.root.title(WINDOW_TITLE)
        self._show_splash()

    def _reset(self):
        if self.nes:
            self.nes.cpu.reset()
            self.nes._cpu_target = float(self.nes.cpu.cycles)
            self.nes.ppu.scanline = 0
            if self.audio and self.nes.apu:
                self.nes.apu.audio = self.audio

    def _power_cycle(self):
        if self.nes:
            path = self.nes.rom.header.filename
            self._open(path)

    def _toggle_pause(self):
        if not self.nes:
            return
        self.paused = not self.paused
        s = self.status_var.get().replace("  [paused]", "")
        if self.paused:
            s += "  [paused]"
        self.status_var.set(s)

    def _about(self):
        messagebox.showinfo(
            "About luigines",
            f"{WINDOW_TITLE}\n"
            f"Single-file NES emulator, Python {sys.version.split()[0]}\n\n"
            "Menus: File, CPU, Options, Help.\n"
            f"Display locked at {TARGET_FPS:.0f} FPS NTSC.\n"
            "PPU: 256x240. APU: cycle-driven 2A03 synthesis.\n"
            "Mappers: 0, 1, 2, 3, 4, 7, 11, 66, 71.")

    def _controls_help(self):
        messagebox.showinfo(
            "Controls",
            "D-Pad  : Arrow keys (or WASD)\n"
            "A      : X\n"
            "B      : Z\n"
            "Start  : Enter\n"
            "Select : Shift\n\n"
            "Pause  : P  (or Pause key)\n"
            "Reset  : Ctrl+R\n"
            "Open   : Ctrl+O")

    def _quit(self):
        self.running = False
        if self.audio:
            self.audio.stop()
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def _schedule_frame(self):
        self.root.after(1, self._frame_tick)

    def _update_fps(self, frames=1):
        self._fps_frames += frames
        dt = time.perf_counter() - self._fps_t0
        if dt >= 1.0:
            self.fps = self._fps_frames / dt
            self._fps_frames = 0
            self._fps_t0 = time.perf_counter()
            self.status_fps_var.set(f"{self.fps:.0f} fps")

    def _frame_tick(self):
        now = time.perf_counter()
        if not (self.nes and self.running and not self.paused):
            self._frame_clock = now + FRAME_SEC
            self.root.after(max(1, math.ceil(FRAME_SEC * 1000)), self._frame_tick)
            return
        if now < self._frame_clock:
            delay = self._frame_clock - now
            self.root.after(max(1, math.ceil(delay * 1000)), self._frame_tick)
            return

        frames = 0
        try:
            # Catch up one hidden frame after a small OS/UI scheduling hiccup,
            # then blit once.  This keeps CPU/APU time at 60 Hz without letting
            # a delayed Tk callback create an ever-growing audio backlog.
            while frames < 2 and now >= self._frame_clock:
                self.nes.run_frame()
                frames += 1
                self._frame_clock += FRAME_SEC
                now = time.perf_counter()
            self._blit()
            self._update_fps(frames)
        except Exception as e:
            self.running = False
            self.status_var.set(f"emulation error: {e}")
        now = time.perf_counter()
        if now - self._frame_clock > FRAME_SEC * 2:
            self._frame_clock = now + FRAME_SEC
        delay = max(0.0, self._frame_clock - now)
        self.root.after(max(1, math.ceil(delay * 1000)), self._frame_tick)

    def _blit(self):
        if self.nes is None:
            return
        fb = self.nes.ppu.framebuffer
        try:
            rgb = b"".join(NES_PALETTE_BYTES[pixel & 0x3F] for pixel in fb)
            ppm = b"P6\n256 240\n255\n" + rgb
            tmp = tk.PhotoImage(data=ppm, format="PPM")
            self.photo = tmp.zoom(SCALE, SCALE)
            self.canvas.itemconfig(self.canvas_img, image=self.photo)
        except tk.TclError:
            # Conservative fallback for Tk builds without binary PPM support.
            pal = NES_PALETTE_HEX
            rows = []
            for y in range(SCREEN_H):
                off = y * SCREEN_W
                rows.append("{" + " ".join(
                    pal[fb[off + x] & 0x3F] for x in range(SCREEN_W)) + "}")
            tmp = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
            tmp.put(" ".join(rows))
            self.photo = tmp.zoom(SCALE, SCALE)
            self.canvas.itemconfig(self.canvas_img, image=self.photo)


def main():
    if sys.version_info < (3, 14):
        print(f"{WINDOW_TITLE} requires Python 3.14+, got {sys.version}",
              file=sys.stderr)
        return 1
    rom = sys.argv[1] if len(sys.argv) > 1 else None
    root = tk.Tk()
    EmuApp(root, rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
