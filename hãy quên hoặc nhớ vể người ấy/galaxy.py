# -*- coding: utf-8 -*-
"""
THIÊN HÀ ANDROMEDA + TRÌNH PHÁT NHẠC
------------------------------------
Cài:   python -m pip install pygame numpy mutagen     (mutagen không bắt buộc, nhưng giúp đọc tên bài/ca sĩ)
Chạy:  python galaxy.py          (chạy ngầm, không hiện console: pythonw galaxy.py)

Nhạc:  bỏ file .mp3 / .ogg / .wav / .flac vào thư mục "music" nằm cạnh file này,
       hoặc kéo thả file nhạc vào cửa sổ (chương trình tự chép vào thư mục music).

Lời:   chữ chỉ hiện khi giọng bắt đầu hát (đoạn nhạc dạo thì không có chữ), sáng dần theo nhịp hát,
       rồi trôi xuống và mờ đi. Lấy lời từ (theo thứ tự):
         1) file .lrc cùng tên với bài hát, nằm cạnh bài hát  (vd. "Lac Troi.mp3" + "Lac Troi.lrc")
         2) lời có mốc thời gian nhúng sẵn trong file nhạc
         3) tự tìm trên lrclib.net theo tên bài/ca sĩ rồi lưu lại thành .lrc (tắt: AUTO_FETCH_LYRICS = False)
       Thả file .lrc vào cửa sổ để gắn cho bài đang chọn.

Phím:  Space       phát / tạm dừng
       N hoặc →    bài sau            P hoặc ←   bài trước
       ↑ / ↓       âm lượng           S          phát ngẫu nhiên
       R           lặp lại một bài (hết bài thì phát lại đúng bài đó)
       H           ẩn / hiện thanh nhạc          L          ẩn / hiện lời bài hát
       (hai nút icon ở mép phải màn hình làm đúng việc của H và L: ♫ = lời bài hát, ▶ = thanh nhạc;
        di chuột là hiện, đứng yên vài giây thì tự mờ đi; chương trình nhớ lần sau)
       F           toàn màn hình                 Esc        thoát
Chuột: bấm nút trên thanh nhạc, bấm lên thanh tiến trình để tua, lăn chuột chỉnh âm lượng.
       Thanh nhạc tự mờ đi sau vài giây không động chuột.
"""
import bisect
import json
import math
import os
import random
import re
import shutil
import sys
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request

import numpy as np
import pygame

# ----------------------------------------------------------------------------
# CẤU HÌNH (chỉnh ở đây)
# ----------------------------------------------------------------------------
BASE = os.path.dirname(os.path.abspath(__file__))
MUSIC_DIR = os.path.join(BASE, "music")
STATE_FILE = os.path.join(BASE, "galaxy_state.json")
EXTS = (".mp3", ".ogg", ".wav", ".flac")

W, H = 1280, 720          # kích thước cửa sổ
SCALE = 2                 # 2 = nhẹ + mịn; 1 = nét nhất nhưng nặng; 3 = rất nhẹ
BW, BH = W // SCALE, H // SCALE
FPS = 60
AUTOPLAY = True           # tự phát nhạc khi mở
AUTO_FETCH_LYRICS = True  # tự tìm lời trên lrclib.net khi bài chưa có file .lrc (False = chỉ dùng file .lrc có sẵn)
LYRIC_LEAD = 0.10         # lời hiện sớm hơn tiếng một chút (giây); tăng nếu thấy lời bị trễ
LYRIC_FONT = "timesnewroman,times new roman,liberationserif,dejavuserif,freeserif"   # font lời bài hát (Times New Roman, có font dự phòng)
LYRIC_BOLD = True         # chữ đậm cho dễ đọc trên nền ảnh; False = chữ thường, thanh mảnh hơn
LYRIC_SIZE = 22           # cỡ chữ lời bài hát: 18-24 = nhỏ gọn để ngắm hình (Times New Roman trông nhỏ hơn font thường); 30 = to
DOCK_IDLE_ALPHA = 0.0     # nút icon bên phải khi không động chuột: 0 = ẩn hẳn, 0.25 = luôn mờ mờ
LYRIC_PREVIEW = False     # False = chữ chỉ hiện khi giọng bắt đầu hát (không hiện trước); True = hiện mờ các câu sắp hát
LYRIC_GAP = 3.5           # nghỉ hát lâu hơn số giây này (nhạc dạo...) thì chữ câu vừa hát tự mờ đi và biến mất
METEOR_EVERY = (2.2, 6.5) # sao băng xuất hiện cách nhau ngẫu nhiên trong khoảng này (giây); tăng số để thưa hơn
SPIN = 0.045              # tốc độ xoay thiên hà (rad/giây)

BG_COLOR = (3, 4, 9)


# ----------------------------------------------------------------------------
# THIÊN HÀ
# ----------------------------------------------------------------------------
def arm_angle(r):
    """Góc của nhánh xoắn ốc theo bán kính."""
    return 3.0 * np.log1p(6.0 * r)


def blur(a):
    """Làm mờ nhẹ 3 điểm theo cả hai trục (a: (BW,BH) hoặc (BW,BH,3))."""
    b = a.copy()
    b[1:-1] = (a[:-2] + a[1:-1] + a[2:]) * (1.0 / 3.0)
    c = b.copy()
    c[:, 1:-1] = (b[:, :-2] + b[:, 1:-1] + b[:, 2:]) * (1.0 / 3.0)
    return c


class Galaxy:
    def __init__(self):
        rng = np.random.default_rng(2024)
        tilt = 0.30                                   # cos(độ nghiêng): nhỏ = dẹt hơn
        self.ci, self.si = tilt, math.sqrt(1 - tilt * tilt)
        ang = math.radians(33)                        # góc nghiêng trục dài
        self.ca, self.sa = math.cos(ang), math.sin(ang)
        self.cx, self.cy, self.R = BW * 0.50, BH * 0.47, BW * 0.45

        # ---- đĩa sao (nhánh xoắn ốc + nền đĩa) ----
        n = 150000
        r = rng.gamma(2.0, 0.25, int(n * 1.6))              # đĩa mũ: mật độ ~ exp(-r/h)
        r = r[r < 1.0][:n]
        n = len(r)
        in_arm = rng.random(n) < 0.70 * np.minimum(1.0, r / 0.30)     # gần tâm thì mịn, không xoáy
        k = rng.integers(0, 2, n)
        th = np.where(
            in_arm,
            arm_angle(r) + k * math.pi + rng.normal(0, 1, n) * (0.16 + 0.22 * r),
            rng.uniform(0, 2 * math.pi, n),
        )
        x, y = r * np.cos(th), r * np.sin(th)
        z = rng.normal(0, 0.01, n)
        t = np.clip(r / 0.95, 0, 1) ** 0.9
        core = np.array([1.0, 0.80, 0.52])
        outer = np.array([0.52, 0.66, 1.0])
        col = core[None, :] * (1 - t)[:, None] + outer[None, :] * t[:, None]
        col *= 1 + 0.10 * rng.normal(size=(n, 1))
        pink = in_arm & (r > 0.3) & (rng.random(n) < 0.04)       # vùng HII hồng
        col[pink] = [1.0, 0.50, 0.60]
        w = 0.030 * (1 + 1.3 * in_arm)
        w = w * np.where(rng.random(n) < 0.015, 5.0, 1.0)         # vài sao sáng
        wd = np.clip(col, 0, None) * w[:, None]

        # ---- sao "nét": vẽ từng điểm ở độ phân giải đầy đủ, như ảnh thật (điểm sắc trên nền sương) ----
        sh = rng.random(n) < 0.16
        ns = int(sh.sum())
        bri = np.clip(rng.pareto(1.6, ns) * 0.16 + 0.10, 0.10, 0.85)
        scol = np.clip(col[sh], 0, 1) * 0.78 + 0.22                # pha chút trắng cho điểm sao sắc
        self.SX = x[sh].astype(np.float32)
        self.SY = y[sh].astype(np.float32)
        self.SC = (scol * bri[:, None] * 255.0).astype(np.float32)
        keep = ~sh
        x, y, z, wd = x[keep], y[keep], z[keep], wd[keep]

        # ---- lõi (bulge) hình cầu dẹt ----
        nb = 50000
        u = rng.random(nb)
        rb = 0.10 / np.sqrt(u ** (-2 / 3) - 1)
        rb = rb[rb < 0.55]
        nb = len(rb)
        v = rng.normal(size=(nb, 3))
        v /= np.linalg.norm(v, axis=1, keepdims=True)
        bx, by, bz = rb * v[:, 0], rb * v[:, 1], rb * v[:, 2] * 0.75
        bcol = np.array([1.0, 0.85, 0.58])[None, :] * (1 + 0.08 * rng.normal(size=(nb, 1)))
        wb = np.clip(bcol, 0, None) * 0.030

        f32 = np.float32
        self.X = np.concatenate([x, bx]).astype(f32)
        self.Y = np.concatenate([y, by]).astype(f32)
        self.Z = np.concatenate([z, bz]).astype(f32)
        wall = np.concatenate([wd, wb], axis=0)
        self.WR = np.ascontiguousarray(wall[:, 0], dtype=f32)
        self.WG = np.ascontiguousarray(wall[:, 1], dtype=f32)
        self.WB = np.ascontiguousarray(wall[:, 2], dtype=f32)

        # ---- bụi: nằm lệch về phía trong của nhánh ----
        m = 40000
        dr = rng.normal(0.55, 0.20, int(m * 1.3))
        dr = dr[(dr > 0.16) & (dr < 0.95)][:m]
        m = len(dr)
        dth = arm_angle(dr) + rng.integers(0, 2, m) * math.pi - 0.20 + rng.normal(0, 1, m) * (0.05 + 0.05 * dr)
        ring = rng.random(m) < 0.22                          # vòng bụi quanh đĩa
        dr = np.where(ring, rng.normal(0.60, 0.035, m), dr)
        dth = np.where(ring, rng.uniform(0, 2 * math.pi, m), dth)
        self.DX = (dr * np.cos(dth)).astype(f32)
        self.DY = (dr * np.sin(dth)).astype(f32)
        self.DW = rng.lognormal(0.0, 0.7, m).astype(f32)     # bụi vón cục -> dải tối có khối
        self.dust_w = np.float32(0.15)
        self.dust_k = np.array([0.85, 1.10, 1.55], dtype=f32)     # bụi đỏ hoá ánh sáng xanh

        # ---- lớp tĩnh: quầng sáng đĩa + lõi + thiên hà vệ tinh ----
        gx, gy = np.meshgrid(np.arange(BW, dtype=f32), np.arange(BH, dtype=f32), indexing="ij")
        dx, dy = gx - self.cx, gy - self.cy
        uu = dx * self.ca - dy * self.sa
        vv = dx * self.sa + dy * self.ca
        rho = np.sqrt((uu / self.R) ** 2 + (vv / (self.R * self.ci)) ** 2)
        tt = np.clip(rho / 0.9, 0, 1)[..., None]
        halo_col = core[None, None, :] * (1 - tt) + outer[None, None, :] * tt
        base = 0.10 * np.exp(-rho / 0.36)[..., None] * halo_col
        d = np.sqrt(uu ** 2 + (vv / 0.8) ** 2) / self.R
        core_glow = 0.38 / (1 + (d / 0.032) ** 2) + 0.20 * np.exp(-(d / 0.15) ** 2)
        base = base + core_glow[..., None] * np.array([1.0, 0.86, 0.62])[None, None, :]
        # thiên hà vệ tinh nhỏ (giống M32 trong ảnh mẫu)
        mx, my = self.cx + BW * 0.095, self.cy + BH * 0.17
        dd = np.sqrt((gx - mx) ** 2 + ((gy - my) * 1.25) ** 2)
        m32 = 0.55 * np.exp(-(dd / 3.0) ** 2) + 0.13 * np.exp(-(dd / 9.0) ** 2)
        base = base + m32[..., None] * np.array([1.0, 0.92, 0.75])[None, None, :]
        self.base = base.astype(f32)
        self.gain = 1.3

        self.buf = pygame.Surface((BW, BH)).convert()
        self.out = pygame.Surface((W, H)).convert()

    def frame(self, t):
        phi = t * SPIN
        c, s = math.cos(phi), math.sin(phi)
        xr = self.X * c - self.Y * s
        yr = self.X * s + self.Y * c
        yt = yr * self.ci + self.Z * self.si
        sx = (xr * self.ca + yt * self.sa) * self.R + self.cx
        sy = (-xr * self.sa + yt * self.ca) * self.R + self.cy
        ix = sx.astype(np.int32)
        iy = sy.astype(np.int32)
        size = BW * BH
        ok = (sx >= 0) & (sx < BW) & (sy >= 0) & (sy < BH)       # sao ngoài khung thì bỏ, không dồn vào mép
        idx = np.where(ok, ix * BH + iy, size)
        D = np.empty((BW, BH, 3), np.float32)
        D[..., 0] = np.bincount(idx, weights=self.WR, minlength=size + 1)[:size].reshape(BW, BH)
        D[..., 1] = np.bincount(idx, weights=self.WG, minlength=size + 1)[:size].reshape(BW, BH)
        D[..., 2] = np.bincount(idx, weights=self.WB, minlength=size + 1)[:size].reshape(BW, BH)
        D = blur(D) + self.base

        # bụi
        c2, s2 = c, s
        dxr = self.DX * c2 - self.DY * s2
        dyr = (self.DX * s2 + self.DY * c2) * self.ci
        fsx = (dxr * self.ca + dyr * self.sa) * self.R + self.cx
        fsy = (-dxr * self.sa + dyr * self.ca) * self.R + self.cy
        dok = (fsx >= 0) & (fsx < BW) & (fsy >= 0) & (fsy < BH)
        didx = np.where(dok, fsx.astype(np.int32) * BH + fsy.astype(np.int32), size)
        dust = np.bincount(didx, weights=self.DW, minlength=size + 1)[:size].reshape(BW, BH).astype(np.float32)
        dust = blur(blur(dust)) * self.dust_w
        D *= np.exp(-dust[..., None] * self.dust_k)

        img = 1.0 - np.exp(-D * self.gain)
        arr = (img * 255.0).astype(np.uint8)
        pygame.surfarray.blit_array(self.buf, arr)
        pygame.transform.smoothscale(self.buf, (W, H), self.out)

        # sao nét ở độ phân giải đầy đủ (bụi che bớt ở dải tối)
        xr = self.SX * c - self.SY * s
        yr = (self.SX * s + self.SY * c) * self.ci
        fx = ((xr * self.ca + yr * self.sa) * self.R + self.cx) * SCALE
        fy = ((-xr * self.sa + yr * self.ca) * self.R + self.cy) * SCALE
        okk = (fx >= 0) & (fx < W) & (fy >= 0) & (fy < H)
        xs = fx[okk].astype(np.int32)
        ys = fy[okk].astype(np.int32)
        dv = dust[xs // SCALE, ys // SCALE]
        add = self.SC[okk] * np.exp(-dv[:, None] * self.dust_k)
        px = pygame.surfarray.pixels3d(self.out)
        px[xs, ys] = np.minimum(255.0, px[xs, ys].astype(np.float32) + add).astype(np.uint8)
        del px
        return self.out


# ----------------------------------------------------------------------------
# BẦU TRỜI SAO: sao nháy, sao lóe sáng, sao băng
# ----------------------------------------------------------------------------
TINTS = np.array([[1.0, 1.0, 1.0], [0.80, 0.88, 1.0], [1.0, 0.82, 0.62], [1.0, 0.55, 0.45]])
TINT_P = [0.45, 0.30, 0.20, 0.05]


def glow_array(radius, spikes=False):
    """Độ sáng 0..1 của một ngôi sao có quầng (tuỳ chọn có bốn tia)."""
    size = radius * 2 + 1
    ax = np.arange(size) - radius
    gx, gy = np.meshgrid(ax, ax, indexing="ij")
    d = np.sqrt(gx ** 2 + gy ** 2) / radius
    a = (np.exp(-(d * 3.2) ** 2) * 0.9 + np.exp(-d * 5.0) * 0.25) * (d <= 1.0)
    if spikes:
        sp = (np.exp(-np.abs(gx) / (radius * 0.55)) * np.exp(-(gy / 1.1) ** 2)
              + np.exp(-np.abs(gy) / (radius * 0.55)) * np.exp(-(gx / 1.1) ** 2))
        sp *= np.clip(1 - np.maximum(np.abs(gx), np.abs(gy)) / radius, 0, 1)
        a = a + 0.55 * sp
    return np.clip(a, 0, 1)


def star_surface(a, color, k):
    rgb = (a[..., None] * (np.array(color, dtype=float) * k)[None, None, :]).clip(0, 255).astype(np.uint8)
    return pygame.surfarray.make_surface(rgb).convert()


class Sky:
    LEVELS = 6

    def __init__(self):
        rng = np.random.default_rng(99)
        self.rng = np.random.default_rng()               # ngẫu nhiên lúc chạy (sao băng, sao lóe)

        # --- bầu trời sao: TẤT CẢ các điểm sao đều nhấp nháy, mỗi sao một nhịp và một biên độ riêng ---
        n1, n2 = 9000, 750                                # điểm nhỏ 1 px; sao vừa dạng khối 2x2
        x1, y1 = rng.integers(2, W - 2, n1), rng.integers(2, H - 2, n1)
        b1 = np.clip(rng.pareto(1.8, n1) * 28 + 24, 24, 200)
        x2, y2 = rng.integers(2, W - 3, n2), rng.integers(2, H - 3, n2)
        b2 = rng.integers(110, 230, n2).astype(float)
        offs = np.array([[0, 0], [1, 0], [0, 1], [1, 1]])
        self.sx = np.concatenate([x1, (x2[:, None] + offs[:, 0]).ravel()])
        self.sy = np.concatenate([y1, (y2[:, None] + offs[:, 1]).ravel()])
        bright = np.concatenate([b1, np.repeat(b2, 4)])
        grp = np.concatenate([np.arange(n1), n1 + np.repeat(np.arange(n2), 4)])   # 4 điểm của một sao vừa chung nhịp
        total = n1 + n2
        tint = TINTS[rng.choice(4, total, p=TINT_P)]
        steady = rng.random(total) < 0.22                 # một phần sao nháy nhẹ để nền không quá "sôi"
        amp = np.where(steady, rng.uniform(0.05, 0.25, total), rng.uniform(0.45, 1.0, total))
        f1, f2 = rng.uniform(1.5, 7.0, total), rng.uniform(3.0, 12.0, total)     # rad/giây: chu kỳ nháy khoảng 0,5 đến 4 giây
        p1, p2 = rng.uniform(0, 6.28, total), rng.uniform(0, 6.28, total)
        self.scol = (tint[grp] * bright[:, None]).astype(np.float32)
        self.samp, self.sf1, self.sf2 = amp[grp].astype(np.float32), f1[grp], f2[grp]
        self.sp1, self.sp2 = p1[grp], p2[grp]
        # sao sáng và nháy mạnh: lúc đỉnh sáng thì lóe thành hình chữ thập nhỏ
        spk = np.flatnonzero((grp < n1) & (amp[grp] > 0.5) & (bright > 85))[:1400]
        self.spk = spk
        self.spn = [(self.sx[spk] + dx, self.sy[spk] + dy) for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1))]
        self.base = np.array(BG_COLOR, np.float32)

        # --- sao có quầng: nhấp nháy liên tục; sao có tia thỉnh thoảng lóe sáng ---
        levels = np.linspace(0.28, 1.0, self.LEVELS)
        self.glow = []
        self.flare_src = []
        for count, rr, cr, spikes in ((140, (4, 10), (150, 235), False), (24, (16, 28), (200, 255), True)):
            for _ in range(count):
                x, y = int(rng.integers(0, W)), int(rng.integers(0, H))
                rad = int(rng.integers(*rr))
                tint = TINTS[rng.choice(4, p=TINT_P)] if not spikes else TINTS[rng.choice(3, p=[0.45, 0.35, 0.20])]
                col = tint * rng.integers(*cr)
                arr = glow_array(rad, spikes)
                surfs = [star_surface(arr, col, k) for k in levels]
                self.glow.append((x, y, rad, surfs, float(rng.uniform(0.7, 3.0)), float(rng.uniform(0, 6.28)),
                                  float(rng.uniform(2.0, 6.0)), float(rng.uniform(0, 6.28))))
                if spikes:
                    r2 = int(rad * 1.9)
                    arr2 = glow_array(r2, True)
                    flare = [star_surface(arr2, np.minimum(255, col * 1.15), k) for k in np.linspace(0.2, 1.0, 5)]
                    self.flare_src.append((x, y, r2, flare))

        self.flares = []
        self.next_flare = 1.2
        self.meteors = []
        self.next_meteor = 2.0

    # ---------------- sao băng ----------------
    @staticmethod
    def _tail(L, thick):
        h = 13
        x = np.arange(L, dtype=np.float32)[:, None]
        y = (np.arange(h, dtype=np.float32) - h // 2)[None, :]
        u = x / (L - 1)
        sigma = (0.25 + 1.5 * u) * thick
        a = (u ** 2.2) * np.exp(-(y / sigma) ** 2)
        a = np.clip(a + 0.9 * np.exp(-(((x - (L - 1)) / 5.0) ** 2 + (y / 3.0) ** 2)), 0, 1)
        ramp = (u ** 3)[..., None]                       # đuôi xanh nhạt, đầu trắng
        col = np.concatenate([150 + 105 * ramp, 190 + 65 * ramp, np.full_like(ramp, 255.0)], axis=2)
        rgb = (a[..., None] * col).clip(0, 255).astype(np.uint8)[:, :, :]
        return pygame.surfarray.make_surface(rgb.reshape(L, h, 3)).convert()

    def spawn_meteor(self, t0):
        r = self.rng
        sign = 1 if r.random() < 0.5 else -1
        ang = math.radians(float(r.uniform(16, 40)))
        speed = float(r.uniform(800, 1400))
        dist = float(r.uniform(450, 900))
        dur = dist / speed
        L = int(r.uniform(150, 300))
        x0 = float(r.uniform(0.05, 0.65) * W) if sign > 0 else float(r.uniform(0.35, 0.95) * W)
        y0 = float(r.uniform(0.0, 0.5) * H)
        vx, vy = sign * math.cos(ang) * speed, math.sin(ang) * speed
        theta = math.atan2(vy, vx)
        rot = pygame.transform.rotate(self._tail(L, float(r.uniform(0.8, 1.2))), -math.degrees(theta))
        self.meteors.append([t0, dur, x0, y0, vx, vy, theta, L, rot, float(r.uniform(0.65, 1.0))])

    # ---------------- vẽ ----------------
    def draw_back(self, scr, t):
        """Nền + sao nháy + sao có quầng (vẽ trước khi cộng thiên hà)."""
        scr.fill(BG_COLOR)
        u = 0.5 + 0.25 * np.sin(t * self.sf1 + self.sp1) + 0.25 * np.sin(t * self.sf2 + self.sp2)   # 0..1, hai nhịp chồng nhau -> nháy không đều
        tw = 1.0 - self.samp * (1.0 - u)
        px = pygame.surfarray.pixels3d(scr)
        px[self.sx, self.sy] = np.minimum(self.base + self.scol * tw[:, None], 255).astype(np.uint8)
        g = np.clip((tw[self.spk] - 0.80) / 0.20, 0.0, 1.0) ** 2 * 0.55
        on = g > 0.03
        if on.any():
            cs = np.minimum(self.base + self.scol[self.spk][on] * g[on][:, None], 255).astype(np.uint8)
            for nx, ny in self.spn:
                px[nx[on], ny[on]] = cs
        del px

        L = self.LEVELS
        for x, y, rad, surfs, f1, p1, f2, p2 in self.glow:
            k = 0.62 + 0.38 * (0.6 * math.sin(t * f1 + p1) + 0.4 * math.sin(t * f2 + p2))
            li = int(min(max((k - 0.24) / 0.76, 0.0), 0.999) * L)
            scr.blit(surfs[li], (x - rad, y - rad), special_flags=pygame.BLEND_ADD)

        if t >= self.next_flare and self.flare_src:
            self.flares.append([int(self.rng.integers(0, len(self.flare_src))), t, float(self.rng.uniform(0.7, 1.3))])
            self.next_flare = t + float(self.rng.uniform(1.2, 3.8))
        keep = []
        for fl in self.flares:
            i, f0, dur = fl
            u = (t - f0) / dur
            if u >= 1.0:
                continue
            x, y, rad, surfs = self.flare_src[i]
            env = math.sin(math.pi * max(u, 0.0)) ** 1.5
            scr.blit(surfs[min(4, int(env * 5))], (x - rad, y - rad), special_flags=pygame.BLEND_ADD)
            keep.append(fl)
        self.flares = keep

    def draw_front(self, scr, t):
        """Sao băng (vẽ sau thiên hà để luôn nằm trên cùng)."""
        if t >= self.next_meteor and len(self.meteors) < 5:
            self.spawn_meteor(t)
            if self.rng.random() < 0.18:                  # thỉnh thoảng một cặp sao băng liền nhau
                self.spawn_meteor(t + float(self.rng.uniform(0.12, 0.4)))
            self.next_meteor = t + float(self.rng.uniform(*METEOR_EVERY))
        live = []
        for m in self.meteors:
            t0, dur, x0, y0, vx, vy, theta, L, img, bright = m
            u = (t - t0) / dur
            if u >= 1.0:
                continue
            live.append(m)
            if u < 0.0:
                continue
            e = max(0.0, min(1.0, u / 0.10, (1.0 - u) / 0.45)) * bright
            v = int(255 * e)
            if v < 4:
                continue
            tau = t - t0
            hx, hy = x0 + vx * tau, y0 + vy * tau
            cx, cy = hx - math.cos(theta) * L / 2, hy - math.sin(theta) * L / 2
            w, h = img.get_size()
            if v < 255:
                img = img.copy()
                img.fill((v, v, v), special_flags=pygame.BLEND_MULT)
            scr.blit(img, (int(cx - w / 2), int(cy - h / 2)), special_flags=pygame.BLEND_ADD)
        self.meteors = live


# ----------------------------------------------------------------------------
# TRÌNH PHÁT NHẠC
# ----------------------------------------------------------------------------
class Player:
    def __init__(self, audio_ok):
        self.audio_ok = audio_ok
        self.tracks = []
        self.i = -1
        self.playing = False
        self.paused = False
        self.shuffle = False
        self.volume = 0.6
        self.offset = 0.0
        self.t_play = 0.0
        self.lengths = {}
        self.error = ""
        self.last_name = ""
        self.repeat = False                               # True = hết bài thì phát lại đúng bài đó
        self.extra = {}                                   # cài đặt giao diện cần nhớ: lời bật/tắt, thanh nhạc bật/tắt
        self.load_state()
        self.scan()
        if self.last_name:
            for j, p in enumerate(self.tracks):
                if os.path.basename(p) == self.last_name:
                    self.i = j
        self.apply_volume()

    # -- lưu / đọc trạng thái nhỏ (âm lượng, ngẫu nhiên, bài cuối) --
    def load_state(self):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                s = json.load(f)
            self.volume = float(s.get("volume", 0.6))
            self.shuffle = bool(s.get("shuffle", False))
            self.last_name = s.get("last", "")
            self.repeat = bool(s.get("repeat", False))
            self.extra = {k: bool(s[k]) for k in ("lyrics", "bar") if k in s}
        except Exception:
            pass

    def save_state(self):
        try:
            last = os.path.basename(self.tracks[self.i]) if 0 <= self.i < len(self.tracks) else ""
            with open(STATE_FILE, "w", encoding="utf-8") as f:
                json.dump({"volume": self.volume, "shuffle": self.shuffle, "repeat": self.repeat, "last": last,
                           **self.extra}, f)
        except Exception:
            pass

    def scan(self):
        cur = self.tracks[self.i] if 0 <= self.i < len(self.tracks) else None
        try:
            names = sorted(os.listdir(MUSIC_DIR), key=str.lower)
        except OSError:
            names = []
        self.tracks = [os.path.join(MUSIC_DIR, f) for f in names if f.lower().endswith(EXTS)]
        if cur in self.tracks:
            self.i = self.tracks.index(cur)
        else:
            self.i = 0 if self.tracks else -1

    def title(self):
        if self.i < 0:
            return ""
        return os.path.splitext(os.path.basename(self.tracks[self.i]))[0].replace("_", " ")

    def apply_volume(self):
        self.volume = min(1.0, max(0.0, self.volume))
        if self.audio_ok:
            try:
                pygame.mixer.music.set_volume(self.volume)
            except pygame.error:
                pass

    def length(self):
        if self.i < 0:
            return 0.0
        p = self.tracks[self.i]
        if p not in self.lengths:
            self.lengths[p] = 0.0
            threading.Thread(target=self._probe, args=(p,), daemon=True).start()
        return self.lengths[p]

    def _probe(self, p):
        L = 0.0
        try:
            from mutagen import File as MFile
            f = MFile(p)
            if f is not None and f.info is not None:
                L = float(f.info.length)
        except Exception:
            pass
        if L <= 0:
            try:
                L = float(pygame.mixer.Sound(p).get_length())
            except Exception:
                L = 0.0
        self.lengths[p] = L

    def play(self, i, start=0.0, _tries=0):
        if not self.tracks or not self.audio_ok:
            return
        self.i = i % len(self.tracks)
        path = self.tracks[self.i]
        try:
            pygame.mixer.music.load(path)
            off = 0.0
            if start > 0:
                try:
                    pygame.mixer.music.play(start=start)
                    off = start
                except pygame.error:
                    pygame.mixer.music.play()
            else:
                pygame.mixer.music.play()
            self.offset = off
            self.playing, self.paused = True, False
            self.t_play = time.time()
            self.error = ""
        except pygame.error:
            self.error = "Không phát được: " + os.path.basename(path)
            self.playing = False
            if _tries < len(self.tracks) - 1:
                self.play(self.i + 1, 0.0, _tries + 1)

    def toggle(self):
        if not self.tracks or not self.audio_ok:
            return
        if not self.playing:
            self.play(self.i)
        elif self.paused:
            pygame.mixer.music.unpause()
            self.paused = False
        else:
            pygame.mixer.music.pause()
            self.paused = True

    def next(self):
        if not self.tracks:
            return
        if self.shuffle and len(self.tracks) > 1:
            j = self.i
            while j == self.i:
                j = random.randrange(len(self.tracks))
        else:
            j = self.i + 1
        self.play(j)

    def prev(self):
        if not self.tracks:
            return
        if self.pos() > 3 or len(self.tracks) < 2:
            self.play(self.i)
        else:
            self.play(self.i - 1)

    def pos(self):
        if not self.playing or not self.audio_ok:
            return 0.0
        try:
            ms = pygame.mixer.music.get_pos()
        except pygame.error:
            ms = 0
        p = self.offset + max(ms, 0) / 1000.0
        L = self.length()
        return min(p, L) if L > 0 else p

    def seek(self, frac):
        L = self.length()
        if L <= 0 or not self.playing:
            return
        was_paused = self.paused
        self.play(self.i, max(0.0, min(frac, 0.999)) * L)
        if was_paused and self.playing:
            pygame.mixer.music.pause()
            self.paused = True

    def add_file(self, path):
        if not path.lower().endswith(EXTS):
            return
        dst = os.path.join(MUSIC_DIR, os.path.basename(path))
        try:
            if os.path.abspath(path) != os.path.abspath(dst) and not os.path.exists(dst):
                shutil.copy2(path, dst)
        except OSError:
            self.error = "Không chép được file vào thư mục music"
            return
        self.scan()
        if dst in self.tracks:
            self.play(self.tracks.index(dst))

    def on_track_end(self):
        if self.playing and not self.paused and time.time() - self.t_play > 1.0:
            if self.repeat:
                self.play(self.i)                         # lặp lại một bài: phát lại đúng bài vừa hết
            else:
                self.next()


# ----------------------------------------------------------------------------
# LỜI BÀI HÁT
#   Nguồn (theo thứ tự): file .lrc cùng tên cạnh bài hát  ->  lời nhúng trong file nhạc
#                        ->  tự tìm trên lrclib.net (chỉ gửi tên bài / ca sĩ), lưu lại thành .lrc
# ----------------------------------------------------------------------------
LRC_TAG = re.compile(r"\[(\d{1,3}):(\d{1,2})(?:[.:](\d{1,3}))?\]")
WORD_TAG = re.compile(r"<\d{1,3}:\d{1,2}(?:[.:]\d{1,3})?>")
LRCLIB = "https://lrclib.net/api/"
EMPTY_LYRICS = ([], [], [], [])


def read_text(path):
    data = open(path, "rb").read()
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return data.decode("utf-16", errors="replace")
    for enc in ("utf-8-sig", "cp1258"):
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            pass
    return data.decode("latin-1", errors="replace")


def parse_lrc(text):
    """Nội dung .lrc -> (starts, ends, texts, durs). Rỗng nếu không có mốc thời gian."""
    offset = 0.0
    rows = []
    for raw in text.splitlines():
        raw = raw.strip().lstrip("﻿")
        if not raw:
            continue
        mo = re.match(r"\[offset:\s*([+-]?\d+)\s*\]", raw, re.I)
        if mo:
            offset = int(mo.group(1)) / 1000.0
            continue
        pos, stamps = 0, []
        while True:
            m = LRC_TAG.match(raw, pos)
            if not m:
                break
            frac = m.group(3)
            stamps.append(int(m.group(1)) * 60 + int(m.group(2)) + (int(frac) / 10 ** len(frac) if frac else 0.0))
            pos = m.end()
        if not stamps:
            continue
        txt = WORD_TAG.sub("", raw[pos:]).strip()
        for s in stamps:
            rows.append((s - offset, txt))
    rows.sort(key=lambda r: r[0])
    starts, ends, texts, durs = [], [], [], []
    for k, (s, txt) in enumerate(rows):
        if not txt:
            continue                                      # dòng trống chỉ dùng để đánh dấu hết câu trước
        nxt = rows[k + 1][0] if k + 1 < len(rows) else s + 6.0
        nxt = max(nxt, s + 0.3)
        est = max(1.2, 0.085 * len(txt) + 0.6)           # thời gian ước tính để hát hết câu
        starts.append(s)
        ends.append(nxt)
        texts.append(txt)
        durs.append(max(0.4, min((nxt - s) * 0.92, est)))
    return starts, ends, texts, durs


def clean_name(path):
    s = os.path.splitext(os.path.basename(path))[0].replace("_", " ")
    s = re.sub(r"[\(\[][^\)\]]*(official|lyrics?|mv|m/v|audio|video|hd|4k|karaoke)[^\)\]]*[\)\]]", "", s, flags=re.I)
    s = re.sub(r"^\s*\d{1,3}\s*[-._)]\s*", "", s)
    return re.sub(r"\s+", " ", s).strip(" -")


def guess_artist_title(path):
    artist = title = None
    try:
        import mutagen
        f = mutagen.File(path, easy=True)
        if f is not None and f.tags:
            a, t = f.tags.get("artist"), f.tags.get("title")
            artist = a[0] if a else None
            title = t[0] if t else None
        if not (artist or title):                      # một số định dạng (vd. wav) chỉ có thẻ ID3 thường
            tg = mutagen.File(path).tags
            if tg:
                fa, ft = tg.get("TPE1"), tg.get("TIT2")
                artist = str(fa.text[0]) if fa is not None and fa.text else None
                title = str(ft.text[0]) if ft is not None and ft.text else None
    except Exception:
        pass
    if not title:
        name = clean_name(path)
        if " - " in name:
            a, t = name.split(" - ", 1)
            artist, title = artist or a.strip(), t.strip()
        else:
            title = name
    return artist, title


def embedded_lyrics(path):
    """Lời nhúng trong file nhạc (cần mutagen). Chỉ nhận loại có mốc thời gian."""
    try:
        import mutagen
        tags = mutagen.File(path).tags
    except Exception:
        return None
    if not tags:
        return None
    out = []
    try:
        getall = getattr(tags, "getall", None)
        if getall:
            for fr in getall("USLT"):
                out.append(str(fr.text))
            for fr in getall("SYLT"):
                if getattr(fr, "format", 2) == 2:
                    out.append("\n".join("[%02d:%05.2f]%s" % (ms // 60000, (ms % 60000) / 1000.0, tx.strip())
                                         for tx, ms in fr.text))
        for key in ("LYRICS", "UNSYNCEDLYRICS", "lyrics", "\xa9lyr"):
            v = tags.get(key)
            if v:
                out.extend(str(x) for x in (v if isinstance(v, (list, tuple)) else [v]))
    except Exception:
        pass
    for s in out:
        if parse_lrc(s)[0]:
            return s
    return None


def lrclib_get(path, timeout=8):
    req = urllib.request.Request(LRCLIB + path, headers={"User-Agent": "GalaxyPlayer/1.0 (personal music wallpaper)"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def fetch_lrclib(path, duration):
    """Tìm lời có mốc thời gian trên lrclib.net. Trả về (text | None, 'ok' | 'missing' | 'offline')."""
    q = urllib.parse.quote
    artist, title = guess_artist_title(path)
    try:
        if artist and title and duration > 0:
            try:
                d = lrclib_get("get?artist_name=%s&track_name=%s&duration=%d" % (q(artist), q(title), round(duration)))
                if d.get("syncedLyrics"):
                    return d["syncedLyrics"], "ok"
            except urllib.error.HTTPError as e:
                if e.code != 404:
                    raise
        queries = []
        if artist and title:
            queries.append(artist + " " + title)
        queries.append(title or clean_name(path))
        if artist and title:
            queries.append(title)
        seen = set()
        for qs in queries:
            if qs in seen:
                continue
            seen.add(qs)
            res = lrclib_get("search?q=" + q(qs))
            cands = [r for r in res if r.get("syncedLyrics")]
            if duration > 0:
                cands = [r for r in cands if abs((r.get("duration") or 0) - duration) <= 7]
                cands.sort(key=lambda r: abs((r.get("duration") or 0) - duration))
            if cands:
                return cands[0]["syncedLyrics"], "ok"
    except (urllib.error.URLError, OSError, ValueError):
        return None, "offline"
    return None, "missing"


class Lyrics:
    def __init__(self):
        self.path = None
        self.data = EMPTY_LYRICS          # (starts, ends, texts, durs) — gán một lần, an toàn giữa các luồng
        self.status = "none"              # none | loading | ok | missing | offline
        self.status_t = 0.0
        self._token = 0

    def load(self, path, length_fn=None):
        self.path = path
        self._token += 1
        token = self._token
        self.data = EMPTY_LYRICS
        self.status, self.status_t = "none", time.time()
        if not path:
            return
        lrc = os.path.splitext(path)[0] + ".lrc"
        if os.path.isfile(lrc):
            try:
                if self._apply(parse_lrc(read_text(lrc)), token):
                    return
            except OSError:
                pass
        self.status = "loading"
        threading.Thread(target=self._worker, args=(path, lrc, token, length_fn), daemon=True).start()

    def attach(self, src, track, length_fn=None):
        """Người dùng thả file .lrc vào cửa sổ: gắn cho bài đang chọn."""
        if not track:
            return
        dst = os.path.splitext(track)[0] + ".lrc"
        try:
            if os.path.abspath(src) != os.path.abspath(dst):
                shutil.copy2(src, dst)
        except OSError:
            return
        self.load(track, length_fn)

    def _apply(self, parsed, token):
        if token != self._token or not parsed[0]:
            return False
        self.data = parsed
        self.status, self.status_t = "ok", time.time()
        return True

    def _finish(self, token, status):
        if token == self._token:
            self.status, self.status_t = status, time.time()

    def _worker(self, path, lrc, token, length_fn):
        try:
            txt = embedded_lyrics(path)
            if txt and self._apply(parse_lrc(txt), token):
                return
        except Exception:
            pass
        if not AUTO_FETCH_LYRICS:
            self._finish(token, "missing")
            return
        dur = 0.0
        for _ in range(12):                                # chờ tối đa ~2,4 giây để biết độ dài bài
            dur = length_fn(path) if length_fn else 0.0
            if dur > 0:
                break
            time.sleep(0.2)
        try:
            txt, st = fetch_lrclib(path, dur)
        except Exception:
            txt, st = None, "offline"
        if txt:
            parsed = parse_lrc(txt)
            if parsed[0]:
                try:
                    with open(lrc, "w", encoding="utf-8") as f:
                        f.write(txt)
                except OSError:
                    pass
                if self._apply(parsed, token):
                    return
            st = "missing"
        self._finish(token, st)


# Dòng càng xa dòng đang hát thì càng mờ và nhỏ. rel > 0: dòng sắp hát (phía trên), rel < 0: dòng đã hát (trôi xuống).
LYR_X = [-1.8, -1.0, 0.0, 1.0, 2.0, 2.8]
LYR_A = [0.0, 0.30, 1.0, 0.48, 0.16, 0.0]
LYR_S = [0.80, 0.88, 1.0, 0.90, 0.84, 0.80]
LYR_A_LIVE = [0.0, 0.30, 1.0, 0.0, 0.0, 0.0]       # không hiện trước: câu mới chỉ hiện (trượt từ trên xuống) khi bắt đầu hát


class LyricsView:
    def __init__(self):
        names = "segoeui,tahoma,arial,dejavusans,freesans"
        self.font = pygame.font.SysFont(LYRIC_FONT, LYRIC_SIZE, bold=LYRIC_BOLD)
        self.spacing = int(LYRIC_SIZE * 1.6)
        self.alpha_curve = LYR_A if LYRIC_PREVIEW else LYR_A_LIVE
        self.small = pygame.font.SysFont(names, 15)
        self.cache = {}
        self.cache_data = None
        self.fi = -1.0
        self.vis = 0.0
        self.on = True
        self.t_est = 0.0
        self.y0 = PY - 24 - self.spacing                   # dòng đang hát nằm ngay trên khung nhạc, chừa chỗ cho dòng vừa hát trôi xuống
        vh = 150                                           # dải tối nhẹ phía sau lời cho dễ đọc
        self.vig = pygame.Surface((W, vh), pygame.SRCALPHA)
        self.vig.fill((3, 4, 10, 255))
        al = pygame.surfarray.pixels_alpha(self.vig)
        al[:, :] = (np.linspace(0, 1, vh) ** 1.6 * 75).astype(np.uint8)[None, :]
        del al

    # --- đồng hồ mượt: get_pos của mixer nhích theo bước, nên tự nội suy giữa các lần cập nhật ---
    def clock(self, pos, playing, dt):
        if playing:
            self.t_est += dt
            err = pos - self.t_est
            self.t_est = pos if abs(err) > 0.4 else self.t_est + err * 0.12
        else:
            self.t_est = pos
        return self.t_est

    def _base(self, data, i):
        key = (i, 1.0)
        v = self.cache.get(key)
        if v is None:
            text = data[2][i]
            pad = 4
            dim_t = self.font.render(text, True, (176, 190, 232))
            br_t = self.font.render(text, True, (255, 255, 255))
            sh = self.font.render(text, True, (3, 5, 14))
            sh.set_alpha(185)
            tw, th = dim_t.get_size()
            size = (tw + pad * 2 + 4, th + pad * 2 + 4)
            dim = pygame.Surface(size, pygame.SRCALPHA)
            bright = pygame.Surface(size, pygame.SRCALPHA)
            for s in (dim, bright):
                for dx, dy in ((1, 2), (-1, 2), (1, 0), (-1, 0)):
                    s.blit(sh, (pad + dx, pad + dy))
            dim.blit(dim_t, (pad, pad))
            bright.blit(br_t, (pad, pad))
            maxw = int(W * 0.80)
            f = 1.0
            if size[0] > maxw:
                f = maxw / size[0]
                ns = (maxw, max(1, int(size[1] * f)))
                dim, bright = pygame.transform.smoothscale(dim, ns), pygame.transform.smoothscale(bright, ns)
            v = (dim, bright, tw * f, pad * f)
            self.cache[key] = v
        return v

    def _pair(self, data, i, sc):
        base = self._base(data, i)
        q = round(sc * 33) / 33.0
        if abs(q - 1.0) < 0.012:
            return base
        key = (i, q)
        v = self.cache.get(key)
        if v is None:
            dim, bright, tw, pad = base
            sz = (max(1, int(dim.get_width() * q)), max(1, int(dim.get_height() * q)))
            v = (pygame.transform.smoothscale(dim, sz), pygame.transform.smoothscale(bright, sz), tw * q, pad * q)
            if len(self.cache) > 80:
                self.cache = {k: x for k, x in self.cache.items() if k[1] == 1.0}
            self.cache[key] = v
        return v

    @staticmethod
    def _line_fade(data, i, tt):
        """Câu chỉ ở lại khi giọng còn hát. Hát liền mạch sang câu sau thì để câu trôi xuống tự nhiên;
        nếu sau câu này là khoảng lặng dài (nhạc dạo) thì mờ đi ngay khi hát xong."""
        starts, ends, texts, durs = data
        sung = starts[i] + durs[i]
        if i + 1 < len(starts) and starts[i + 1] - sung <= LYRIC_GAP:
            return 1.0
        f0 = min(ends[i] + 0.4, sung + 2.0)
        return max(0.0, min(1.0, 1.0 - (tt - f0) / 0.6))

    @staticmethod
    def _linked(data, i, idx):
        """Câu i còn nối liền (không bị nhạc dạo chen giữa) với câu đang hát idx không."""
        starts, ends, texts, durs = data
        for k in range(i, idx):
            if starts[k + 1] - (starts[k] + durs[k]) > LYRIC_GAP:
                return 0.0
        return 1.0

    def draw(self, scr, lyr, t, dt):
        data = lyr.data
        if data is not self.cache_data:                    # đổi bài / nạp lời mới
            self.cache.clear()
            self.cache_data = data
            self.fi = -1.0
        starts, ends, texts, durs = data
        n = len(starts)
        want = 1.0 if (self.on and n) else 0.0
        self.vis += (want - self.vis) * min(1.0, dt * 5.0)

        if n and self.vis > 0.01:
            tt = t + LYRIC_LEAD
            idx = bisect.bisect_right(starts, tt) - 1
            if abs(idx - self.fi) > 4.5:
                self.fi = float(idx)
            else:
                self.fi += (idx - self.fi) * (1.0 - math.exp(-dt * 7.5))
            lo = max(0, int(math.floor(self.fi)) - 2)
            hi = min(n, int(math.ceil(self.fi)) + 5)
            items, amax = [], 0.0
            cur_fade = self._line_fade(data, idx, tt) if idx >= 0 else 1.0
            for i in range(lo, hi):
                rel = i - self.fi
                a = float(np.interp(rel, LYR_X, self.alpha_curve)) * self.vis
                if i <= idx:
                    a *= self._line_fade(data, i, tt)
                    if i < idx:                              # các câu đã hát chỉ ở lại khi câu hiện tại còn hiện và không bị nhạc dạo chen giữa
                        a *= cur_fade * self._linked(data, i, idx)
                if a < 0.02:
                    continue
                items.append((i, rel, a))
                amax = max(amax, a)
            if items:                                        # dải tối nhẹ chỉ hiện cùng lúc với chữ
                vig = self.vig
                vig.set_alpha(int(255 * min(1.0, amax)))
                scr.blit(vig, (0, H - vig.get_height()))
            for i, rel, a in items:
                dim, bright, tw, pad = self._pair(data, i, float(np.interp(rel, LYR_X, LYR_S)))
                w, h = dim.get_size()
                pos = ((W - w) // 2, int(self.y0 - rel * self.spacing - h / 2))
                alpha = int(255 * a)
                dim.set_alpha(alpha)
                scr.blit(dim, pos)
                if i <= idx:                                 # dòng đang hát: sáng dần từ trái sang phải; dòng đã hát: sáng hẳn
                    p = 1.0 if i < idx else max(0.0, min(1.0, (tt - starts[i]) / durs[i]))
                    if p > 0.0:
                        bright.set_alpha(alpha)
                        if p >= 0.999:
                            scr.blit(bright, pos)
                        else:
                            scr.blit(bright, pos, area=pygame.Rect(0, 0, int(pad + tw * p) + 1, h))

        # dòng trạng thái nhỏ phía trên khung nhạc
        if self.on and lyr.status in ("loading", "missing", "offline"):
            age = time.time() - lyr.status_t
            a = 0.55 + 0.45 * math.sin(time.time() * 4.0) if lyr.status == "loading" else max(0.0, min(1.0, (7.0 - age) / 1.5))
            msg = {"loading": "Đang tìm lời bài hát…",
                   "missing": "Chưa có lời cho bài này. Thả file .lrc cùng tên vào cửa sổ hoặc thư mục music",
                   "offline": "Không kết nối được để tìm lời. Thả file .lrc cùng tên vào cửa sổ hoặc thư mục music"}[lyr.status]
            if a > 0.02:
                img = self.small.render(msg, True, (170, 183, 222))
                img.set_alpha(int(255 * a))
                scr.blit(img, ((W - img.get_width()) // 2, PY - 26))


# ----------------------------------------------------------------------------
# GIAO DIỆN THANH NHẠC (gọn + nét: hình vẽ ở độ phân giải gấp 3 rồi thu nhỏ, chữ vẽ trực tiếp)
# ----------------------------------------------------------------------------
PW, PH = 600, 66
PX, PY = (W - PW) // 2, H - PH - 22
SS = 3                      # hệ số siêu mẫu: viền, nút, thanh trượt mịn, không răng cưa


def fmt_time(s):
    s = int(max(0, s))
    return "%d:%02d" % (s // 60, s % 60)


def fit(font, text, maxw):
    if font.size(text)[0] <= maxw:
        return text
    while text and font.size(text + "…")[0] > maxw:
        text = text[:-1]
    return text + "…"


class UI:
    def __init__(self):
        names = "segoeui,tahoma,arial,dejavusans,freesans"
        self.f_title = pygame.font.SysFont(names, 17, bold=True)
        self.f_small = pygame.font.SysFont(names, 13)
        self.big = pygame.Surface((PW * SS, PH * SS), pygame.SRCALPHA)
        self.panel = pygame.Surface((PW, PH), pygame.SRCALPHA)
        o = (PX, PY)
        self.cy = 26

        def ctr(x, y, w, h):
            r = pygame.Rect(0, 0, w, h)
            r.center = (PX + x, PY + y)
            return r

        # vùng bấm (toạ độ màn hình)
        self.bar = pygame.Rect(18, 54, PW - 36, 4).move(o)
        self.bar_hit = self.bar.inflate(0, 18)
        self.prev_r = ctr(34, self.cy, 34, 34)
        self.play_r = ctr(76, self.cy, 40, 40)
        self.next_r = ctr(118, self.cy, 34, 34)
        self.shuf_r = ctr(PW - 172, self.cy, 30, 30)
        self.rep_r = ctr(PW - 208, self.cy, 32, 30)
        self.vol = pygame.Rect(PW - 124, self.cy - 2, 104, 4).move(o)
        self.vol_hit = self.vol.inflate(16, 22)
        self.panel_rect = pygame.Rect(PX, PY, PW, PH)
        self.title_rect = pygame.Rect(150, 7, 222, 22)

    def _title(self, surf, text, color):
        """Tên bài: dài quá thì chạy chữ qua lại thay vì cắt."""
        img = self.f_title.render(text, True, color)
        r = self.title_rect
        if img.get_width() <= r.w:
            surf.blit(img, r.topleft)
            return
        over = img.get_width() - r.w
        speed, wait = 45.0, 1.3
        d = over / speed
        tt = time.time() % (2 * (wait + d))
        if tt < wait:
            off = 0.0
        elif tt < wait + d:
            off = (tt - wait) * speed
        elif tt < 2 * wait + d:
            off = over
        else:
            off = over - (tt - 2 * wait - d) * speed
        surf.blit(img, r.topleft, area=pygame.Rect(int(off), 0, r.w, img.get_height()))

    def draw(self, scr, pl, alpha, seek_preview):
        if alpha <= 2:
            return
        S = SS
        b = self.big
        b.fill((9, 11, 24, 0))
        white, dim, accent = (244, 247, 255), (150, 163, 200), (130, 165, 255)
        track, dark = (50, 58, 90), (10, 14, 34)

        def R(x, y, w, h, col, rad=0, width=0):
            pygame.draw.rect(b, col, (round(x * S), round(y * S), round(w * S), round(h * S)),
                             round(width * S), border_radius=round(rad * S))

        def P(pts, col):
            pygame.draw.polygon(b, col, [(round(x * S), round(y * S)) for x, y in pts])

        def C(x, y, r, col):
            pygame.draw.circle(b, col, (round(x * S), round(y * S)), round(r * S))

        def L(pts, col, w):
            pygame.draw.lines(b, col, False, [(round(x * S), round(y * S)) for x, y in pts], max(1, round(w * S)))

        # nền + viền
        R(0, 0, PW, PH, (9, 11, 24, 240), rad=15)
        R(0.5, 0.5, PW - 1, PH - 1, (115, 132, 205, 210), rad=15, width=1)

        L_len = pl.length()
        frac = seek_preview if seek_preview is not None else (pl.pos() / L_len if L_len > 0 else 0.0)
        frac = max(0.0, min(1.0, frac))

        # thanh tiến trình
        bx, by, bw, bh = self.bar.x - PX, self.bar.y - PY, self.bar.w, self.bar.h
        R(bx, by, bw, bh, track, rad=2)
        if frac > 0:
            R(bx, by, max(4, bw * frac), bh, accent, rad=2)
        C(bx + bw * frac, by + bh / 2, 5.5, white)

        cy = self.cy
        # bài trước
        cx = 34
        R(cx - 9, cy - 8, 2.4, 16, white, rad=1)
        P([(cx + 8, cy - 8), (cx + 8, cy + 8), (cx - 6, cy)], white)
        # bài sau
        cx = 118
        R(cx + 6.6, cy - 8, 2.4, 16, white, rad=1)
        P([(cx - 8, cy - 8), (cx - 8, cy + 8), (cx + 6, cy)], white)
        # phát / dừng
        cx = 76
        C(cx, cy, 18, accent)
        if pl.playing and not pl.paused:
            R(cx - 6, cy - 8, 4.2, 16, dark, rad=1)
            R(cx + 1.8, cy - 8, 4.2, 16, dark, rad=1)
        else:
            P([(cx - 5, cy - 8.5), (cx - 5, cy + 8.5), (cx + 8.5, cy)], dark)

        # ngẫu nhiên
        sc = accent if pl.shuffle else dim
        sx = PW - 172
        L([(sx - 9, cy - 5), (sx - 3, cy - 5), (sx + 3, cy + 5), (sx + 7, cy + 5)], sc, 1.7)
        L([(sx - 9, cy + 5), (sx - 3, cy + 5), (sx + 3, cy - 5), (sx + 7, cy - 5)], sc, 1.7)
        P([(sx + 11, cy + 5), (sx + 6, cy + 1.5), (sx + 6, cy + 8.5)], sc)
        P([(sx + 11, cy - 5), (sx + 6, cy - 8.5), (sx + 6, cy - 1.5)], sc)

        # lặp lại một bài (hai mũi tên vòng + số 1)
        rc = accent if pl.repeat else dim
        rx = PW - 208
        x0, x1, y0, y1 = rx - 8, rx + 8, cy - 5, cy + 5
        L([(x0, cy + 1.5), (x0, y0), (x1 - 2.5, y0)], rc, 1.7)
        P([(x1 + 2.5, y0), (x1 - 2.5, y0 - 3.4), (x1 - 2.5, y0 + 3.4)], rc)
        L([(x1, cy - 1.5), (x1, y1), (x0 + 2.5, y1)], rc, 1.7)
        P([(x0 - 2.5, y1), (x0 + 2.5, y1 - 3.4), (x0 + 2.5, y1 + 3.4)], rc)
        L([(rx - 2.2, cy - 1.6), (rx + 0.6, cy - 3.2), (rx + 0.6, cy + 3.2)], rc, 1.5)

        # âm lượng
        vx = PW - 140
        P([(vx - 8, cy - 3), (vx - 4, cy - 3), (vx + 1, cy - 7), (vx + 1, cy + 7), (vx - 4, cy + 3), (vx - 8, cy + 3)], dim)
        if pl.volume > 0.04:
            pygame.draw.arc(b, dim, (round((vx + 1 - 5) * S), round((cy - 5) * S), round(10 * S), round(10 * S)),
                            -0.9, 0.9, round(1.5 * S))
        if pl.volume > 0.5:
            pygame.draw.arc(b, dim, (round((vx + 1 - 9) * S), round((cy - 9) * S), round(18 * S), round(18 * S)),
                            -0.9, 0.9, round(1.5 * S))
        vbx, vby, vbw, vbh = self.vol.x - PX, self.vol.y - PY, self.vol.w, self.vol.h
        R(vbx, vby, vbw, vbh, track, rad=2)
        R(vbx, vby, max(3, vbw * pl.volume), vbh, accent, rad=2)
        C(vbx + vbw * pl.volume, vby + vbh / 2, 5, white)

        # thu nhỏ về kích thước thật -> viền/nút mịn
        pygame.transform.smoothscale(b, (PW, PH), self.panel)
        p = self.panel

        # chữ vẽ trực tiếp ở độ phân giải thật nên rất nét
        if pl.i >= 0:
            self._title(p, pl.title(), white)
            if pl.error:
                sub, scol = pl.error, (255, 150, 140)
            else:
                pos = seek_preview * L_len if seek_preview is not None else pl.pos()
                sub = "%s / %s   ·   Bài %d/%d" % (fmt_time(pos), fmt_time(L_len) if L_len > 0 else "--:--",
                                                   pl.i + 1, len(pl.tracks))
                if pl.shuffle:
                    sub += "   ·   Ngẫu nhiên"
                scol = dim
        else:
            self._title(p, "Chưa có bài hát", dim)
            sub, scol = "Kéo thả file nhạc vào đây hoặc vào thư mục music", dim
        p.blit(self.f_small.render(fit(self.f_small, sub, self.title_rect.w + 6), True, scol), (150, 31))

        p.set_alpha(int(alpha))
        scr.blit(p, (PX, PY))


# ----------------------------------------------------------------------------
# NÚT ICON Ở MÉP PHẢI: ♫ bật/tắt lời bài hát, ▶ bật/tắt thanh nhạc
# ----------------------------------------------------------------------------
class Dock:
    SIZE, SS = 44, 4                                      # kích thước nút; hệ số siêu mẫu để nét vẽ mịn

    def __init__(self):
        self.font = pygame.font.SysFont("segoeui,tahoma,arial,dejavusans,freesans", 14)
        self.names = ("lyrics", "bar")
        self.tips = {"lyrics": "Lời bài hát  (L)", "bar": "Thanh nhạc  (H)"}
        cx, cy = W - 38, H // 2
        self.rects = {}
        for name, dy in (("lyrics", -30), ("bar", 30)):
            r = pygame.Rect(0, 0, self.SIZE, self.SIZE)
            r.center = (cx, cy + dy)
            self.rects[name] = r
        self.img = {(n, on, hov): self._make(n, on, hov)
                    for n in self.names for on in (True, False) for hov in (True, False)}

    # --- hình vẽ theo toạ độ 44x44, nhân hệ số SS rồi thu nhỏ ---
    def _pt(self, x, y):
        return (round(x * self.SS), round(y * self.SS))

    def _ellipse(self, cx, cy, rx, ry, ang):
        pts = []
        for a in np.linspace(0, 2 * math.pi, 32, endpoint=False):
            x, y = rx * math.cos(a), ry * math.sin(a)
            pts.append(self._pt(cx + x * math.cos(ang) - y * math.sin(ang), cy + x * math.sin(ang) + y * math.cos(ang)))
        return pts

    def _note(self, s, col):
        """Hai nốt móc nối nhau (♫)."""
        tilt = math.radians(-22)
        pygame.draw.polygon(s, col, self._ellipse(15.0, 30.0, 5.8, 4.3, tilt))
        pygame.draw.polygon(s, col, self._ellipse(29.0, 26.5, 5.8, 4.3, tilt))
        k = self.SS
        pygame.draw.rect(s, col, (round(19.4 * k), round(11 * k), round(2.6 * k), round(19 * k)))
        pygame.draw.rect(s, col, (round(33.4 * k), round(7.5 * k), round(2.6 * k), round(19 * k)))
        pygame.draw.polygon(s, col, [self._pt(19.4, 10.5), self._pt(36.0, 7.0), self._pt(36.0, 12.6), self._pt(19.4, 16.1)])

    def _player(self, s, col):
        """Khung máy phát: màn hình ở trên, nút phát ở dưới."""
        k = self.SS
        pygame.draw.rect(s, col, (7 * k, 7 * k, 30 * k, 30 * k), border_radius=5 * k)
        pygame.draw.rect(s, (0, 0, 0, 0), (11 * k, 11 * k, 22 * k, 14 * k), border_radius=3 * k)
        pygame.draw.polygon(s, (0, 0, 0, 0), [self._pt(18.2, 27.2), self._pt(18.2, 34.6), self._pt(25.6, 30.9)])   # nút phát khoét ra

    def _make(self, name, on, hover):
        S, k = self.SIZE, self.SS
        big = pygame.Surface((S * k, S * k), pygame.SRCALPHA)
        mid = (S * k // 2, S * k // 2)
        pygame.draw.circle(big, (30, 36, 72, 215) if hover else (8, 10, 24, 150), mid, S * k // 2 - k)
        pygame.draw.circle(big, (130, 148, 215, 160 if hover else 80), mid, S * k // 2 - k, k)
        glyph = pygame.Surface((S * k, S * k), pygame.SRCALPHA)
        col = (244, 247, 255, 255) if on else (112, 121, 152, 255)
        (self._note if name == "lyrics" else self._player)(glyph, col)
        if not on:                                        # tắt: gạch chéo
            a, b = self._pt(11, 33), self._pt(33, 11)
            pygame.draw.line(glyph, (0, 0, 0, 0), a, b, round(6.2 * k))
            pygame.draw.line(glyph, (176, 184, 212, 255), a, b, round(2.6 * k))
        big.blit(glyph, (0, 0))
        return pygame.transform.smoothscale(big, (S, S))

    def hit(self, pos):
        for n, r in self.rects.items():
            if r.collidepoint(pos):
                return n
        return None

    def draw(self, scr, state, hov, alpha):
        if alpha <= 0.02:
            return
        a = int(255 * min(1.0, alpha))
        for n in self.names:
            im = self.img[(n, bool(state[n]), n == hov)]
            im.set_alpha(a)
            scr.blit(im, self.rects[n])
        if hov:
            tip = self.font.render(self.tips[hov] + ("" if state[hov] else "  ·  đang tắt"), True, (225, 232, 255))
            pill = pygame.Surface((tip.get_width() + 22, 28), pygame.SRCALPHA)
            pygame.draw.rect(pill, (8, 10, 24, 225), pill.get_rect(), border_radius=14)
            pill.blit(tip, (11, (28 - tip.get_height()) // 2))
            pill.set_alpha(a)
            r = self.rects[hov]
            scr.blit(pill, (r.left - 10 - pill.get_width(), r.centery - 14))


# ----------------------------------------------------------------------------
# CHƯƠNG TRÌNH CHÍNH
# ----------------------------------------------------------------------------
def main():
    shot = None
    if "--shot" in sys.argv:
        shot = sys.argv[sys.argv.index("--shot") + 1]

    if sys.platform == "win32":
        # báo cho Windows biết chương trình tự xử lý DPI -> không bị phóng to làm mờ khi màn hình đặt 125%/150%
        try:
            import ctypes
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
            except Exception:
                ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

    os.makedirs(MUSIC_DIR, exist_ok=True)
    pygame.init()
    audio_ok = True
    try:
        if not pygame.mixer.get_init():
            pygame.mixer.init()
    except pygame.error:
        audio_ok = False

    screen = pygame.display.set_mode((W, H), pygame.SCALED)
    pygame.display.set_caption("Thiên hà Andromeda")
    clock = pygame.time.Clock()

    galaxy = Galaxy()
    sky = Sky()
    ui = UI()
    player = Player(audio_ok)
    lyr = Lyrics()
    view = LyricsView()
    dock = Dock()
    view.on = player.extra.get("lyrics", True)             # nhớ lần trước đã bật hay tắt lời
    length_fn = lambda p: player.lengths.get(p, 0.0)
    shot_lt = float(sys.argv[sys.argv.index("--lt") + 1]) if "--lt" in sys.argv else 0.0   # chỉ để chụp thử
    MUSIC_END = pygame.USEREVENT + 1
    if audio_ok:
        pygame.mixer.music.set_endevent(MUSIC_END)
    if AUTOPLAY and player.tracks and shot is None:
        player.play(player.i)

    t0 = time.time()
    if shot:
        sky.spawn_meteor(0.30)
        sky.spawn_meteor(0.38)
    dt = 1.0 / 60.0
    last_move = time.time()
    ui_alpha = 255.0
    ui_hidden = player.extra.get("bar", False)             # nhớ lần trước đã ẩn thanh nhạc hay chưa
    if ui_hidden:
        ui_alpha = 0.0                                      # đã ẩn từ lần trước: không nháy thanh nhạc lúc mở
    dock_alpha = 1.0
    dragging = None
    seek_preview = None
    cursor_vis = True
    running = True

    def vol_from_x(x):
        return (x - ui.vol.x) / ui.vol.w

    while running:
        now = time.time()
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                running = False
            elif e.type == MUSIC_END:
                player.on_track_end()
                last_move = now
            elif e.type == pygame.DROPFILE:
                if e.file.lower().endswith(".lrc"):
                    lyr.attach(e.file, player.tracks[player.i] if player.i >= 0 else None, length_fn)
                else:
                    player.add_file(e.file)
                last_move = now
            elif e.type == pygame.KEYDOWN:
                last_move = now
                k = e.key
                if k == pygame.K_ESCAPE:
                    running = False
                elif k == pygame.K_SPACE:
                    player.toggle()
                elif k in (pygame.K_n, pygame.K_RIGHT):
                    player.next()
                elif k in (pygame.K_p, pygame.K_LEFT):
                    player.prev()
                elif k == pygame.K_UP:
                    player.volume += 0.05
                    player.apply_volume()
                elif k == pygame.K_DOWN:
                    player.volume -= 0.05
                    player.apply_volume()
                elif k == pygame.K_s:
                    player.shuffle = not player.shuffle
                elif k == pygame.K_r:
                    player.repeat = not player.repeat
                elif k == pygame.K_h:
                    ui_hidden = not ui_hidden
                elif k == pygame.K_l:
                    view.on = not view.on
                elif k == pygame.K_f:
                    pygame.display.toggle_fullscreen()
            elif e.type == pygame.MOUSEWHEEL:
                last_move = now
                player.volume += 0.05 * e.y
                player.apply_volume()
            elif e.type == pygame.MOUSEMOTION:
                last_move = now
                if dragging == "vol":
                    player.volume = vol_from_x(e.pos[0])
                    player.apply_volume()
                elif dragging == "seek":
                    seek_preview = max(0.0, min(1.0, (e.pos[0] - ui.bar.x) / ui.bar.w))
            elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                last_move = now
                pos = e.pos
                name = dock.hit(pos)
                if name == "lyrics":
                    view.on = not view.on
                elif name == "bar":
                    ui_hidden = not ui_hidden
                elif ui_alpha < 40:
                    pass                                    # thanh nhạc đang ẩn: bấm vào chỗ đó không làm gì
                elif ui.vol_hit.collidepoint(pos):
                    dragging = "vol"
                    player.volume = vol_from_x(pos[0])
                    player.apply_volume()
                elif ui.bar_hit.collidepoint(pos) and player.i >= 0:
                    dragging = "seek"
                    seek_preview = max(0.0, min(1.0, (pos[0] - ui.bar.x) / ui.bar.w))
                elif ui.play_r.collidepoint(pos):
                    player.toggle()
                elif ui.next_r.collidepoint(pos):
                    player.next()
                elif ui.prev_r.collidepoint(pos):
                    player.prev()
                elif ui.shuf_r.collidepoint(pos):
                    player.shuffle = not player.shuffle
                elif ui.rep_r.collidepoint(pos):
                    player.repeat = not player.repeat
            elif e.type == pygame.MOUSEBUTTONUP and e.button == 1:
                if dragging == "seek" and seek_preview is not None:
                    player.seek(seek_preview)
                dragging = None
                seek_preview = None

        # vẽ cảnh
        t = now - t0
        sky.draw_back(screen, t)
        screen.blit(galaxy.frame(t), (0, 0), special_flags=pygame.BLEND_ADD)
        sky.draw_front(screen, t)

        # lời bài hát (đổi bài -> nạp lời mới)
        cur = player.tracks[player.i] if 0 <= player.i < len(player.tracks) else None
        if cur != lyr.path:
            lyr.load(cur, length_fn)
        player.length()
        lt = shot_lt if shot else view.clock(player.pos(), player.playing and not player.paused, dt)
        view.draw(screen, lyr, lt, dt)

        # thanh nhạc: tự mờ khi không động chuột
        near = ui.panel_rect.collidepoint(pygame.mouse.get_pos()) or dragging is not None
        show = (not ui_hidden) and (near or now - last_move < 4.0 or player.i < 0)
        target = 255.0 if show else 0.0
        ui_alpha += (target - ui_alpha) * 0.12
        ui.draw(screen, player, ui_alpha, seek_preview)

        # nút icon bên phải: hiện khi động chuột, tự mờ khi yên
        hov = dock.hit(pygame.mouse.get_pos())
        dock_target = 1.0 if (now - last_move < 4.0 or hov) else DOCK_IDLE_ALPHA
        dock_alpha += (dock_target - dock_alpha) * 0.12
        dock.draw(screen, {"lyrics": view.on, "bar": not ui_hidden}, hov, dock_alpha)

        want_cursor = (now - last_move < 4.0) or near or hov is not None
        if want_cursor != cursor_vis:
            pygame.mouse.set_visible(want_cursor)
            cursor_vis = want_cursor

        pygame.display.flip()
        if shot:
            if t > 0.5:
                pygame.image.save(screen, shot)
                running = False
        else:
            dt = min(clock.tick(FPS) / 1000.0, 0.1)

    player.extra = {"lyrics": view.on, "bar": ui_hidden}
    player.save_state()
    pygame.quit()


if __name__ == "__main__":
    try:
        main()
    except Exception:
        with open(os.path.join(BASE, "galaxy_error.log"), "w", encoding="utf-8") as f:
            f.write(traceback.format_exc())
        raise