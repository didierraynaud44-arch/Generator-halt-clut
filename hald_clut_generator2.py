#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
╔══════════════════════════════════════════════════════════════════════════════╗
║           HALD-CLUT GENERATOR PRO v2.0 — Créateur de LUTs Avancé            ║
║                                                                              ║
║  Fonctionnalités :                                                           ║
║    1. Extraction automatique de look (paire couleur+N&B → preset)           ║
║    2. Comparaison côte-à-côte avec séparateur déplaçable                    ║
║    3. Ajustement par zone (ombres/mi-tons/HL) avec courbes visuelles        ║
║    4. Export multi-format (PNG Hald-CLUT, .cube, .csp)                      ║
║    5. Batch processing (dossier entier)                                     ║
║    6. Synchronisation avec Nikon Picture Control Studio                     ║
║                                                                              ║
║  Dépendances : pip install pillow numpy                                     ║
╚══════════════════════════════════════════════════════════════════════════════╝
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser
from PIL import Image, ImageTk, ImageDraw
import numpy as np
import os
import sys
import threading
import time
import json
import argparse
import struct

try:
    import rawpy
    RAWPY_AVAILABLE = True
except ImportError:
    RAWPY_AVAILABLE = False

# Extensions de fichiers RAW d'appareil photo reconnues (nécessitent rawpy/libraw)
RAW_EXTENSIONS = {
    ".nef", ".cr2", ".cr3", ".arw", ".dng", ".raf", ".rw2",
    ".orf", ".pef", ".srw", ".raw", ".sr2", ".3fr", ".erf",
    ".kdc", ".mrw", ".nrw", ".raw", ".x3f"
}


# ═══════════════════════════════════════════════════════════════════════════════
# CONSTANTES
# ═══════════════════════════════════════════════════════════════════════════════

HALD_LEVEL = 12
HALD_SIDE = HALD_LEVEL ** 3
HALD_CUBE_SIZE = HALD_LEVEL ** 2
PREVIEW_MAX_SIZE = 900
SETTINGS_FILE = os.path.expanduser("~/.hald_clut_settings.json")
SYNC_MARKER_FILE = os.path.expanduser("~/.hald_clut_sync_path")
LAST_PRESETS_PATH_FILE = os.path.expanduser("~/.hald_clut_last_presets_path")


# ═══════════════════════════════════════════════════════════════════════════════
# MOTEUR DE TRAITEMENT
# ═══════════════════════════════════════════════════════════════════════════════

class ImageEngine:
    @staticmethod
    def rgb_to_hsv(rgb):
        r, g, b = rgb[..., 0], rgb[..., 1], rgb[..., 2]
        mx = np.max(rgb, axis=-1)
        mn = np.min(rgb, axis=-1)
        diff = mx - mn
        h = np.zeros_like(mx)
        s = np.zeros_like(mx)
        v = mx
        mask = mx != mn
        r_mask = (mx == r) & mask
        h[r_mask] = (60 * ((g[r_mask] - b[r_mask]) / diff[r_mask]) + 360) % 360
        g_mask = (mx == g) & mask
        h[g_mask] = (60 * ((b[g_mask] - r[g_mask]) / diff[g_mask]) + 120) % 360
        b_mask = (mx == b) & mask
        h[b_mask] = (60 * ((r[b_mask] - g[b_mask]) / diff[b_mask]) + 240) % 360
        s[mx > 0] = diff[mx > 0] / mx[mx > 0]
        return np.stack([h / 360.0, s, v], axis=-1)

    @staticmethod
    def hsv_to_rgb(hsv):
        h, s, v = hsv[..., 0], hsv[..., 1], hsv[..., 2]
        h = h * 360.0
        c = v * s
        x = c * (1 - np.abs((h / 60) % 2 - 1))
        m = v - c
        rgb = np.zeros_like(hsv)
        mask0 = (h < 60)
        rgb[mask0] = np.stack([c[mask0], x[mask0], np.zeros_like(c[mask0])], axis=-1)
        mask1 = (h >= 60) & (h < 120)
        rgb[mask1] = np.stack([x[mask1], c[mask1], np.zeros_like(c[mask1])], axis=-1)
        mask2 = (h >= 120) & (h < 180)
        rgb[mask2] = np.stack([np.zeros_like(c[mask2]), c[mask2], x[mask2]], axis=-1)
        mask3 = (h >= 180) & (h < 240)
        rgb[mask3] = np.stack([np.zeros_like(c[mask3]), x[mask3], c[mask3]], axis=-1)
        mask4 = (h >= 240) & (h < 300)
        rgb[mask4] = np.stack([x[mask4], np.zeros_like(c[mask4]), c[mask4]], axis=-1)
        mask5 = (h >= 300)
        rgb[mask5] = np.stack([c[mask5], np.zeros_like(c[mask5]), x[mask5]], axis=-1)
        return rgb + m[..., None]

    @staticmethod
    def get_luminance(rgb):
        return 0.2126 * rgb[..., 0] + 0.7152 * rgb[..., 1] + 0.0722 * rgb[..., 2]

    @classmethod
    def apply_all(cls, rgb, settings):
        rgb = rgb.astype(np.float32)
        temp = settings.get("wb_temperature", 0) / 100.0
        tint = settings.get("wb_tint", 0) / 100.0
        if temp != 0 or tint != 0:
            rgb = rgb.copy()
            rgb[..., 0] *= (1.0 + temp * 0.15)
            rgb[..., 2] *= (1.0 - temp * 0.15)
            rgb[..., 1] *= (1.0 + tint * 0.1)
            rgb[..., 0] *= (1.0 - tint * 0.05)
            rgb[..., 2] *= (1.0 - tint * 0.05)
        exp = settings.get("exposure", 0)
        if exp != 0:
            rgb = rgb * (2.0 ** (exp / 100.0 * 2.0))
        bp = settings.get("black_point", 0) / 255.0
        wp = settings.get("white_point", 255) / 255.0
        if bp != 0 or wp < 1.0:
            rgb = (rgb - bp) / (wp - bp)
        curve = settings.get("tone_curve", 0)
        if curve != 0:
            # Signe inversé : vers la droite (+) doit renforcer la courbe en S
            # (plus de contraste), vers la gauche (-) doit aplatir (plus linéaire).
            s = -curve / 100.0
            rgb = (rgb - 0.5) * (1.0 - s * 0.5) + 0.5
            rgb = np.clip(rgb, 0, 1)
            rgb = rgb + s * 0.3 * (rgb * (1 - rgb) * (2 * rgb - 1))
        cont = settings.get("contrast", 0)
        if cont != 0:
            rgb = (rgb - 0.5) * (1.0 + cont / 100.0) + 0.5
        bright = settings.get("brightness", 0)
        if bright != 0:
            rgb = rgb + bright / 100.0
        hl = settings.get("highlights", 0)
        sh = settings.get("shadows", 0)
        if hl != 0 or sh != 0:
            lum = cls.get_luminance(rgb)
            if sh != 0:
                shadow_mask = 1.0 - np.clip(lum * 2.0, 0, 1)
                rgb = rgb + shadow_mask[..., None] * (sh / 100.0 * 0.5)
            if hl != 0:
                highlight_mask = np.clip((lum - 0.5) * 2.0, 0, 1)
                rgb = rgb + highlight_mask[..., None] * (hl / 100.0 * 0.5)
        sat = settings.get("saturation", 0)
        if sat != 0:
            hsv = cls.rgb_to_hsv(np.clip(rgb, 0, 1))
            hsv[..., 1] = np.clip(hsv[..., 1] * (1.0 + sat / 100.0), 0, 1)
            rgb = cls.hsv_to_rgb(hsv)
        vib = settings.get("vibrance", 0)
        if vib != 0:
            hsv = cls.rgb_to_hsv(np.clip(rgb, 0, 1))
            s = hsv[..., 1]
            mask = 1.0 - s
            hsv[..., 1] = np.clip(s * (1.0 + (vib / 100.0) * mask), 0, 1)
            rgb = cls.hsv_to_rgb(hsv)
        hue = settings.get("hue", 0)
        if hue != 0:
            hsv = cls.rgb_to_hsv(np.clip(rgb, 0, 1))
            hsv[..., 0] = (hsv[..., 0] + hue / 360.0) % 1.0
            rgb = cls.hsv_to_rgb(hsv)
        dehaze = settings.get("dehaze", 0)
        if dehaze != 0:
            strength = dehaze / 100.0
            rgb = rgb.copy()
            rgb[..., 2] *= (1.0 - strength * 0.15)
            lum = cls.get_luminance(rgb)
            rgb = rgb + (rgb - lum[..., None]) * (strength * 0.2)
        cg_intensity = settings.get("color_grading_intensity", 0)
        if cg_intensity > 0:
            lum = cls.get_luminance(rgb)
            shadow_mask = np.clip(1.0 - lum * 2.0, 0, 1)
            mid_mask = 1.0 - np.abs(lum - 0.5) * 2.0
            high_mask = np.clip((lum - 0.5) * 2.0, 0, 1)
            grading = (shadow_mask[..., None] * np.array(settings.get("shadows_color", [0,0,0])) +
                       mid_mask[..., None] * np.array(settings.get("midtones_color", [0,0,0])) +
                       high_mask[..., None] * np.array(settings.get("highlights_color", [0,0,0])))
            rgb = rgb + grading * (cg_intensity / 100.0) * 0.3
        if settings.get("monochrome", False):
            w = np.array(settings.get("mono_weights", [0.33, 0.33, 0.34]))
            w = w / np.sum(w)
            gray = np.dot(rgb[..., :3], w)
            rgb = np.stack([gray, gray, gray], axis=-1)
        return np.clip(rgb, 0, 1)


# ═══════════════════════════════════════════════════════════════════════════════
# GÉNÉRATEUR HALD-CLUT
# ═══════════════════════════════════════════════════════════════════════════════

class HaldClutGenerator:
    def __init__(self):
        self.identity = None
        self.generate_identity()

    def generate_identity(self):
        side = HALD_SIDE
        cube = HALD_CUBE_SIZE
        indices = np.arange(side * side)
        r = (indices % cube).astype(np.float32) / (cube - 1)
        g = ((indices // cube) % cube).astype(np.float32) / (cube - 1)
        b = (indices // (cube * cube)).astype(np.float32) / (cube - 1)
        self.identity = np.stack([r, g, b], axis=-1).reshape(side, side, 3)

    def generate_processed(self, settings):
        flat = self.identity.reshape(-1, 3)
        processed = ImageEngine.apply_all(flat, settings)
        result = (processed * 255).astype(np.uint8).reshape(HALD_SIDE, HALD_SIDE, 3)
        return result

    def save(self, array, path, grayscale=False):
        if grayscale:
            gray = array[..., 0]
            img = Image.fromarray(gray, mode="L")
        else:
            img = Image.fromarray(array, mode="RGB")
        img.save(path, "PNG", optimize=True)
        return path


# ═══════════════════════════════════════════════════════════════════════════════
# EXPORT MULTI-FORMAT
# ═══════════════════════════════════════════════════════════════════════════════

class MultiFormatExporter:
    """Exporte un LUT en plusieurs formats standards."""

    @staticmethod
    def export_cube(hald_array, path, name="GeneratedLUT", grayscale=False):
        """Exporte en format .cube (DaVinci Resolve, Premiere Pro, etc.)"""
        if grayscale:
            data = hald_array[..., 0].astype(np.float32) / 255.0
            data = np.stack([data, data, data], axis=-1)
        else:
            data = hald_array.astype(np.float32) / 255.0

        side = HALD_SIDE
        cube_size = HALD_CUBE_SIZE

        with open(path, "w") as f:
            f.write(f"# Generated by Hald-CLUT Generator\n")
            f.write(f"# Name: {name}\n")
            f.write(f"# Dimensions: {cube_size}x{cube_size}x{cube_size}\n")
            f.write(f"LUT_3D_SIZE {cube_size}\n")
            f.write(f"\n")

            for b in range(cube_size):
                for g in range(cube_size):
                    for r in range(cube_size):
                        idx = r + g * side + b * side * side
                        x = idx % side
                        y = idx // side
                        if y < side and x < side:
                            px = data[y, x]
                            f.write(f"{px[0]:.6f} {px[1]:.6f} {px[2]:.6f}\n")
        return path

    @staticmethod
    def export_csp(hald_array, path, name="GeneratedLUT", grayscale=False):
        """Exporte en format .csp (Photoshop, After Effects)"""
        if grayscale:
            data = hald_array[..., 0].astype(np.float32) / 255.0
            data = np.stack([data, data, data], axis=-1)
        else:
            data = hald_array.astype(np.float32) / 255.0

        cube_size = HALD_CUBE_SIZE

        with open(path, "w") as f:
            f.write("CS\n")
            f.write("\n")
            f.write("LUT_3D_SIZE ")
            f.write(f"{cube_size}\n")
            f.write("\n")

            for b in range(cube_size):
                for g in range(cube_size):
                    for r in range(cube_size):
                        idx = r + g * HALD_SIDE + b * HALD_SIDE * HALD_SIDE
                        x = idx % HALD_SIDE
                        y = idx // HALD_SIDE
                        if y < HALD_SIDE and x < HALD_SIDE:
                            px = data[y, x]
                            f.write(f"{px[0]:.6f} {px[1]:.6f} {px[2]:.6f}\n")
        return path


# ═══════════════════════════════════════════════════════════════════════════════
# EXTRACTEUR AUTOMATIQUE DE LOOK (Fonctionnalité 1)
# ═══════════════════════════════════════════════════════════════════════════════

class LookExtractor:
    """Extrait un preset depuis une paire couleur + N&B."""

    @staticmethod
    def extract(color_path, bw_path, preset_name="Look Extrait"):
        color_img = Image.open(color_path).convert("RGB")
        bw_img = Image.open(bw_path).convert("L")
        bw_img = bw_img.resize(color_img.size, Image.LANCZOS)

        color_arr = np.array(color_img).astype(np.float32) / 255.0
        bw_arr = np.array(bw_img).astype(np.float32) / 255.0

        # 1. ESTIMATION DU MIXEUR MONOCHROME
        step = 15
        R = color_arr[::step, ::step, 0].flatten()
        G = color_arr[::step, ::step, 1].flatten()
        B = color_arr[::step, ::step, 2].flatten()
        Y = bw_arr[::step, ::step].flatten()

        A = np.column_stack([R, G, B])
        lambda_reg = 0.05
        AtA = A.T @ A
        AtA_reg = AtA + lambda_reg * np.eye(3)
        AtY = A.T @ Y
        weights = np.linalg.solve(AtA_reg, AtY)
        weights = np.clip(weights, 0.05, None)
        weights = weights / np.sum(weights)

        # 2. ANALYSE DE LA COURBE TONALE
        predicted = weights[0]*R + weights[1]*G + weights[2]*B

        # Contraste : pente à mi-ton
        mid_mask = (predicted > 0.4) & (predicted < 0.6)
        if np.sum(mid_mask) > 100:
            mid_in = predicted[mid_mask]
            mid_out = Y[mid_mask]
            slope = np.polyfit(mid_in, mid_out, 1)[0]
            contrast_est = (slope - 1.0) * 100
        else:
            contrast_est = 0

        # 3. POINTS NOIR ET BLANC
        bw_flat = bw_arr.flatten()
        black_point = np.percentile(bw_flat[bw_flat > 0.001], 2) * 255
        white_point = np.percentile(bw_flat[bw_flat < 0.999], 98) * 255

        # 4. OMBRES ET HL
        shadows_est = (np.mean(Y[predicted < 0.2]) - np.mean(predicted[predicted < 0.2])) * 100
        hl_est = (np.mean(Y[predicted > 0.8]) - np.mean(predicted[predicted > 0.8])) * 100

        # 5. COURBE S (analyse de la non-linéarité)
        predicted_full = color_arr[:,:,0]*weights[0] + color_arr[:,:,1]*weights[1] + color_arr[:,:,2]*weights[2]
        lum_full = predicted_full.flatten()
        bw_full = bw_arr.flatten()

        # Fit une parabole : y = ax² + bx + c
        # Si a > 0 → S-curve positive, si a < 0 → S-curve négative
        mid_mask_full = (lum_full > 0.2) & (lum_full < 0.8)
        if np.sum(mid_mask_full) > 1000:
            x = lum_full[mid_mask_full]
            y = bw_full[mid_mask_full]
            coeffs = np.polyfit(x, y, 2)
            curve_est = coeffs[0] * 200  # Normalisation approximative
        else:
            curve_est = 0

        # 6. LUMINOSITÉ GLOBALE
        brightness_est = (np.mean(bw_full) - np.mean(predicted_full)) * 100

        # Assembler le preset
        settings = {
            "wb_temperature": 0,
            "wb_tint": 0,
            "exposure": 0,
            "black_point": int(np.clip(black_point, 0, 50)),
            "white_point": int(np.clip(white_point, 200, 255)),
            "tone_curve": int(np.clip(curve_est, -50, 50)),
            "contrast": int(np.clip(contrast_est, -50, 80)),
            "brightness": int(np.clip(brightness_est, -30, 30)),
            "highlights": int(np.clip(hl_est, -50, 50)),
            "shadows": int(np.clip(shadows_est, -50, 50)),
            "saturation": -100,
            "vibrance": 0,
            "hue": 0,
            "dehaze": 0,
            "color_grading_intensity": 0,
            "monochrome": True,
            "mono_r": int(weights[0] * 100),
            "mono_g": int(weights[1] * 100),
            "mono_b": int(weights[2] * 100),
            "shadows_color": [0.0, 0.0, 0.0],
            "midtones_color": [0.0, 0.0, 0.0],
            "highlights_color": [0.0, 0.0, 0.0]
        }

        return {
            "name": preset_name,
            "description": f"Look extrait automatiquement depuis {os.path.basename(color_path)} et {os.path.basename(bw_path)}",
            "category": "Extrait automatique",
            "settings": settings
        }


# ═══════════════════════════════════════════════════════════════════════════════
# INTERFACE GRAPHIQUE PRINCIPALE
# ═══════════════════════════════════════════════════════════════════════════════

class App:
    def __init__(self, root):
        self.root = root
        self.root.title("Hald-CLUT Generator PRO v2.0 — 6 Fonctionnalités Avancées")
        self.root.geometry("1600x1050")
        self.root.minsize(1400, 900)

        self.source_image = None
        self.preview_image = None
        self.preview_tk = None
        self.hald_preview_tk = None
        self.hald_gen = HaldClutGenerator()
        self.preview_thread = None
        self.pending_preview = False
        self.before_after = False
        self.split_position = 0.5  # Position du séparateur (0-1)
        self.dragging_split = False

        self.settings = {
            "wb_temperature": tk.DoubleVar(value=0),
            "wb_tint": tk.DoubleVar(value=0),
            "exposure": tk.DoubleVar(value=0),
            "black_point": tk.DoubleVar(value=0),
            "white_point": tk.DoubleVar(value=255),
            "tone_curve": tk.DoubleVar(value=0),
            "contrast": tk.DoubleVar(value=0),
            "brightness": tk.DoubleVar(value=0),
            "highlights": tk.DoubleVar(value=0),
            "shadows": tk.DoubleVar(value=0),
            "saturation": tk.DoubleVar(value=0),
            "vibrance": tk.DoubleVar(value=0),
            "hue": tk.DoubleVar(value=0),
            "dehaze": tk.DoubleVar(value=0),
            "color_grading_intensity": tk.DoubleVar(value=0),
            "monochrome": tk.BooleanVar(value=False),
            "mono_r": tk.DoubleVar(value=33),
            "mono_g": tk.DoubleVar(value=33),
            "mono_b": tk.DoubleVar(value=34),
            "shadows_color": [0.0, 0.0, 0.0],
            "midtones_color": [0.0, 0.0, 0.0],
            "highlights_color": [0.0, 0.0, 0.0],
        }

        self.sync_path = None
        self.load_sync_path()

        self.setup_menu()
        self.setup_layout()
        self.setup_bindings()
        # Auto-restauration désactivée : le programme démarre toujours avec des
        # réglages à zéro plutôt que de recharger la dernière session utilisée.
        # (self.load_auto_settings() désactivé volontairement)
        self.show_welcome()

    # ─── MENU ───
    def setup_menu(self):
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Fichier", menu=file_menu)
        file_menu.add_command(label="📂 Charger image...", command=self.load_image, accelerator="Ctrl+O")
        file_menu.add_separator()
        file_menu.add_command(label="💾 Exporter Hald-CLUT", command=self.export_hald, accelerator="Ctrl+E")
        file_menu.add_command(label="📤 Exporter réglages", command=self.export_settings)
        file_menu.add_command(label="📥 Importer réglages", command=self.import_settings)
        file_menu.add_separator()
        file_menu.add_command(label="❌ Quitter", command=self.on_close, accelerator="Alt+F4")

        tools_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Outils", menu=tools_menu)
        tools_menu.add_command(label="🔍 Extraction de look (paire couleur+N&B)", command=self.open_extractor)
        tools_menu.add_command(label="📁 Batch processing (dossier)", command=self.open_batch)
        tools_menu.add_separator()
        tools_menu.add_command(label="🔗 Configurer synchro Studio", command=self.configure_sync)
        tools_menu.add_command(label="🔄 Synchroniser avec Studio", command=self.sync_to_studio)

        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Aide", menu=help_menu)
        help_menu.add_command(label="ℹ️ À propos", command=self.show_about)
        help_menu.add_command(label="📖 Raccourcis", command=self.show_docs)

    # ─── LAYOUT ───
    def setup_layout(self):
        self.main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        self.main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.left_frame = ttk.Frame(self.main_paned, width=400)
        self.main_paned.add(self.left_frame, weight=0)
        self.setup_controls_panel()

        self.right_frame = ttk.Frame(self.main_paned)
        self.main_paned.add(self.right_frame, weight=1)
        self.setup_preview_panel()

    def setup_controls_panel(self):
        canvas = tk.Canvas(self.left_frame, highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.left_frame, orient="vertical", command=canvas.yview)
        self.controls_container = ttk.Frame(canvas)
        self.controls_container.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.controls_container, anchor="nw", width=380)
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        ttk.Label(self.controls_container, text="🎛 RÉGLAGES", font=("Segoe UI", 14, "bold")).pack(pady=(10, 5))

        # ─── Sélecteur de Presets ───
        preset_frame = ttk.LabelFrame(self.controls_container, text=" Bibliothèque de Films ")
        preset_frame.pack(fill=tk.X, padx=10, pady=5)
        self.preset_var = tk.StringVar(value="— Choisir un preset —")
        self.preset_combo = ttk.Combobox(preset_frame, textvariable=self.preset_var, state="readonly", width=35)
        self.preset_combo.pack(fill=tk.X, padx=5, pady=5)
        self._load_presets()
        self.preset_combo.bind("<<ComboboxSelected>>", self.on_preset_selected)
        ttk.Button(preset_frame, text="📂 Charger presets.json", command=self.load_presets_file).pack(fill=tk.X, padx=5, pady=2)

        ttk.Separator(self.controls_container, orient=tk.HORIZONTAL).pack(fill=tk.X, padx=10, pady=5)

        # ─── Extraction de Look (Fonctionnalité 1) ───
        extract_frame = ttk.LabelFrame(self.controls_container, text=" 🔍 Extraction de Look ")
        extract_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Button(extract_frame, text="📸 Extraire depuis une paire couleur+N&B", command=self.open_extractor).pack(fill=tk.X, padx=5, pady=3)
        self.extract_status = ttk.Label(extract_frame, text="Aucune extraction", foreground="gray", font=("Segoe UI", 8))
        self.extract_status.pack(pady=2)

        ttk.Separator(self.controls_container, orient=tk.HORIZONTAL).pack(fill=tk.X, padx=10, pady=5)

        # ─── Balance des blancs ───
        self.add_section("Balance des blancs")
        self.add_slider("Température", self.settings["wb_temperature"], -100, 100, "Froid ← → Chaud")
        self.add_slider("Teinte", self.settings["wb_tint"], -100, 100, "Magenta ← → Vert")

        # ─── Tonalité ───
        self.add_section("Tonalité")
        self.add_slider("Exposition", self.settings["exposure"], -200, 200, "-2 EV ← → +2 EV")
        self.add_slider("Point noir", self.settings["black_point"], 0, 100, "0 ← → 100")
        self.add_slider("Point blanc", self.settings["white_point"], 155, 255, "155 ← → 255")
        self.add_slider("Courbe S", self.settings["tone_curve"], -100, 100, "Linéaire ← → S fort")

        # ─── Dynamique ───
        self.add_section("Dynamique")
        self.add_slider("Contraste", self.settings["contrast"], -100, 100, "-100 ← → +100")
        self.add_slider("Luminosité", self.settings["brightness"], -100, 100, "-100 ← → +100")
        self.add_slider("Hautes lumières", self.settings["highlights"], -100, 100, "-100 ← → +100")
        self.add_slider("Ombres", self.settings["shadows"], -100, 100, "-100 ← → +100")

        # ─── Couleur ───
        self.add_section("Couleur")
        self.add_slider("Saturation", self.settings["saturation"], -100, 100, "-100 ← → +100")
        self.add_slider("Vibrance", self.settings["vibrance"], -100, 100, "-100 ← → +100")
        self.add_slider("Teinte", self.settings["hue"], -180, 180, "-180° ← → +180°")
        self.add_slider("Déhaze", self.settings["dehaze"], 0, 100, "0 ← → 100")

        # ─── Monochrome ───
        self.add_section("Monochrome")
        mono_frame = ttk.Frame(self.controls_container)
        mono_frame.pack(fill=tk.X, padx=10, pady=2)
        ttk.Checkbutton(mono_frame, text="Activer le N&B", variable=self.settings["monochrome"], command=self.on_monochrome_toggle).pack(side=tk.LEFT)
        self.mono_label = ttk.Label(mono_frame, text="(export Grayscale)", foreground="gray")
        self.mono_label.pack(side=tk.LEFT, padx=10)
        self.add_slider("Rouge", self.settings["mono_r"], 0, 100, "")
        self.add_slider("Vert", self.settings["mono_g"], 0, 100, "")
        self.add_slider("Bleu", self.settings["mono_b"], 0, 100, "")

        # ─── Color Grading ───
        self.add_section("Color Grading")
        self.add_slider("Intensité", self.settings["color_grading_intensity"], 0, 100, "0% ← → 100%")
        cg_frame = ttk.Frame(self.controls_container)
        cg_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(cg_frame, text="Ombres:").grid(row=0, column=0, sticky=tk.W)
        self.shadows_btn = ttk.Button(cg_frame, text="⬛ Choisir", width=12, command=lambda: self.pick_color("shadows"))
        self.shadows_btn.grid(row=0, column=1, padx=5)
        ttk.Label(cg_frame, text="Tons moyens:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.midtones_btn = ttk.Button(cg_frame, text="⬛ Choisir", width=12, command=lambda: self.pick_color("midtones"))
        self.midtones_btn.grid(row=1, column=1, padx=5)
        ttk.Label(cg_frame, text="Hautes lumières:").grid(row=2, column=0, sticky=tk.W)
        self.highlights_btn = ttk.Button(cg_frame, text="⬛ Choisir", width=12, command=lambda: self.pick_color("highlights"))
        self.highlights_btn.grid(row=2, column=1, padx=5)

        # ─── Boutons d'action ───
        ttk.Separator(self.controls_container, orient=tk.HORIZONTAL).pack(fill=tk.X, padx=10, pady=15)
        btn_frame = ttk.Frame(self.controls_container)
        btn_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Button(btn_frame, text="🔄 Réinitialiser", command=self.reset_settings).pack(fill=tk.X, pady=2)
        ttk.Button(btn_frame, text="💾 Exporter Hald-CLUT", command=self.export_hald).pack(fill=tk.X, pady=2)
        ttk.Button(btn_frame, text="📦 Exporter multi-format", command=self.export_multi_format).pack(fill=tk.X, pady=2)
        ttk.Button(btn_frame, text="📁 Batch processing", command=self.open_batch).pack(fill=tk.X, pady=2)

        self.progress = ttk.Progressbar(self.controls_container, mode="determinate", maximum=100)
        self.progress.pack(fill=tk.X, padx=10, pady=5)
        self.progress.pack_forget()
        self.status_label = ttk.Label(self.controls_container, text="Prêt — Niveau 12 (1728×1728)", anchor=tk.W)
        self.status_label.pack(fill=tk.X, padx=10, pady=5)

    def setup_preview_panel(self):
        toolbar = ttk.Frame(self.right_frame)
        toolbar.pack(fill=tk.X, pady=5)
        ttk.Button(toolbar, text="📂 Charger image", command=self.load_image).pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="🔍 Avant/Après", command=self.toggle_before_after).pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="💾 Exporter LUT", command=self.export_hald).pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="📦 Multi-format", command=self.export_multi_format).pack(side=tk.LEFT, padx=5)
        self.mode_label = ttk.Label(toolbar, text="Mode: RGB", foreground="blue", font=("Segoe UI", 9, "bold"))
        self.mode_label.pack(side=tk.RIGHT, padx=10)

        preview_paned = ttk.PanedWindow(self.right_frame, orient=tk.VERTICAL)
        preview_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        img_frame = ttk.LabelFrame(preview_paned, text=" Aperçu image (cliquer-glisser le séparateur) ")
        preview_paned.add(img_frame, weight=3)
        self.preview_canvas = tk.Canvas(img_frame, bg="#1a1a1a", highlightthickness=0)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)

        hald_frame = ttk.LabelFrame(preview_paned, text=" Aperçu Hald-CLUT ")
        preview_paned.add(hald_frame, weight=1)
        self.hald_canvas = tk.Canvas(hald_frame, bg="#222", highlightthickness=0, height=180)
        self.hald_canvas.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)

        self.info_label = ttk.Label(self.right_frame, text="Aucune image chargée", anchor=tk.W)
        self.info_label.pack(fill=tk.X, padx=5, pady=2)

    def add_section(self, title):
        frame = ttk.Frame(self.controls_container)
        frame.pack(fill=tk.X, pady=(15, 2))
        ttk.Label(frame, text=title, font=("Segoe UI", 11, "bold")).pack(side=tk.LEFT)
        ttk.Separator(frame, orient=tk.HORIZONTAL).pack(fill=tk.X, expand=True, padx=10)

    def add_slider(self, label, var, min_val, max_val, hint):
        frame = ttk.Frame(self.controls_container)
        frame.pack(fill=tk.X, padx=10, pady=3)
        ttk.Label(frame, text=label, width=14).pack(side=tk.LEFT)
        scale = ttk.Scale(frame, from_=min_val, to=max_val, variable=var, orient=tk.HORIZONTAL, length=180, command=lambda _: self.trigger_preview())
        scale.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        val_label = ttk.Label(frame, text=f"{var.get():.0f}", width=5)
        val_label.pack(side=tk.LEFT)
        def update_label(*args):
            val_label.config(text=f"{var.get():.0f}")
        var.trace_add("write", update_label)
        if hint:
            ttk.Label(self.controls_container, text=hint, foreground="gray", font=("Segoe UI", 8)).pack(padx=10)

    # ─── BINDINGS ───
    def setup_bindings(self):
        self.root.bind("<Control-o>", lambda e: self.load_image())
        self.root.bind("<Control-e>", lambda e: self.export_hald())
        self.root.bind("<space>", lambda e: self.toggle_before_after())
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.preview_canvas.bind("<Configure>", lambda e: self.trigger_preview())
        # Séparateur déplaçable (Fonctionnalité 2)
        self.preview_canvas.bind("<Button-1>", self.on_canvas_click)
        self.preview_canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.preview_canvas.bind("<ButtonRelease-1>", self.on_canvas_release)

    def show_welcome(self):
        self.preview_canvas.delete("all")
        self.preview_canvas.create_text(
            self.preview_canvas.winfo_width() // 2 or 400,
            self.preview_canvas.winfo_height() // 2 or 300,
            text="📂 Chargez une image pour commencer\n(Ctrl+O)\n\n🔍 Glissez le séparateur pour comparer", 
            fill="white", font=("Segoe UI", 16), justify=tk.CENTER
        )
        self._draw_hald_preview()

    def show_about(self):
        messagebox.showinfo("À propos",
            "Hald-CLUT Generator PRO v2.0\n\n"
            "6 Fonctionnalités Avancées :\n"
            "1. Extraction automatique de look\n"
            "2. Comparaison côte-à-côte avec séparateur\n"
            "3. Ajustement par zone (ombres/mi-tons/HL)\n"
            "4. Export multi-format (PNG, .cube, .csp)\n"
            "5. Batch processing (dossier entier)\n"
            "6. Synchronisation avec Picture Control Studio")

    def show_docs(self):
        docs = """RACCOURCIS :
  Ctrl+O  Charger image
  Ctrl+E  Exporter Hald-CLUT
  Espace  Avant/Après
  Clic+glisser sur l'aperçu = déplacer le séparateur
  Alt+F4  Quitter

FONCTIONNALITÉS :
  1. Extraction : Outils → Extraction de look
  2. Séparateur : cliquer-glisser sur l'aperçu
  3. Zones : Color Grading (ombres/mi-tons/HL)
  4. Multi-format : bouton 📦 ou menu Fichier
  5. Batch : Outils → Batch processing
  6. Synchro : Outils → Configurer synchro Studio
"""
        messagebox.showinfo("Documentation", docs)

    def on_monochrome_toggle(self):
        if self.settings["monochrome"].get():
            self.mode_label.config(text="Mode: Grayscale (N&B)", foreground="gray")
            self.mono_label.config(text="(export Grayscale ✓)", foreground="green")
        else:
            self.mode_label.config(text="Mode: RGB", foreground="blue")
            self.mono_label.config(text="(export Grayscale)", foreground="gray")
        self.trigger_preview()

    def load_image(self):
        raw_patterns = " ".join(f"*{ext}" for ext in sorted(RAW_EXTENSIONS))
        filetypes = [
            ("Toutes images", f"*.png *.jpg *.jpeg *.tif *.tiff *.bmp {raw_patterns}"),
            ("Images standard", "*.png *.jpg *.jpeg *.tif *.tiff *.bmp"),
            ("RAW appareil photo", raw_patterns),
            ("Tous", "*.*"),
        ]
        path = filedialog.askopenfilename(title="Charger une image", filetypes=filetypes)
        if not path:
            return
        try:
            ext = os.path.splitext(path)[1].lower()
            loader_used = "?"
            if ext in RAW_EXTENSIONS:
                if not RAWPY_AVAILABLE:
                    messagebox.showerror(
                        "Bibliothèque manquante",
                        f"Extension détectée : {ext}\n\n"
                        "rawpy n'est pas disponible dans cet exécutable "
                        "(import échoué). Installe rawpy :\n\npip install rawpy\n\n"
                        "Puis recompile avec --include-package=rawpy."
                    )
                    return
                loader_used = "rawpy"
                self.status_label.config(text="Décodage du RAW en cours…")
                self.root.update_idletasks()
                with rawpy.imread(path) as raw:
                    rgb_array = raw.postprocess(
                        use_camera_wb=True,
                        no_auto_bright=True,
                        output_bps=8,
                    )
                self.source_image = Image.fromarray(rgb_array, mode="RGB")
            else:
                loader_used = "Pillow"
                self.source_image = Image.open(path).convert("RGB")
            self.source_path = path
            w, h = self.source_image.size
            ratio = min(PREVIEW_MAX_SIZE / w, PREVIEW_MAX_SIZE / h, 1.0)
            new_w, new_h = int(w * ratio), int(h * ratio)
            self.preview_image = self.source_image.resize((new_w, new_h), Image.LANCZOS)
            self.info_label.config(
                text=f"{os.path.basename(path)} — {w}×{h} px (aperçu {new_w}×{new_h}) "
                     f"[ext={ext}, loader={loader_used}]"
            )
            self.status_label.config(text="Image chargée")
            self.trigger_preview()
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible de charger l'image :\n{e}")

    def pick_color(self, target):
        color = colorchooser.askcolor(title=f"Couleur des {target}")[0]
        if color:
            r, g, b = [(c - 128) / 128.0 for c in color]
            self.settings[f"{target}_color"] = [r, g, b]
            hex_color = '#%02x%02x%02x' % tuple(int(c) for c in color)
            btn = getattr(self, f"{target}_btn")
            btn.config(text=hex_color)
            self.trigger_preview()

    def reset_settings(self):
        for key in ["wb_temperature", "wb_tint", "exposure", "black_point", "white_point",
                    "tone_curve", "contrast", "brightness", "highlights", "shadows",
                    "saturation", "vibrance", "hue", "dehaze", "color_grading_intensity"]:
            self.settings[key].set(0)
        self.settings["white_point"].set(255)
        self.settings["monochrome"].set(False)
        self.settings["mono_r"].set(33)
        self.settings["mono_g"].set(33)
        self.settings["mono_b"].set(34)
        self.settings["shadows_color"] = [0.0, 0.0, 0.0]
        self.settings["midtones_color"] = [0.0, 0.0, 0.0]
        self.settings["highlights_color"] = [0.0, 0.0, 0.0]
        for target in ["shadows", "midtones", "highlights"]:
            getattr(self, f"{target}_btn").config(text="⬛ Choisir")
        self.on_monochrome_toggle()
        self.trigger_preview()
        self.status_label.config(text="Réglages réinitialisés")

    def get_settings_dict(self):
        return {
            "wb_temperature": self.settings["wb_temperature"].get(),
            "wb_tint": self.settings["wb_tint"].get(),
            "exposure": self.settings["exposure"].get(),
            "black_point": self.settings["black_point"].get(),
            "white_point": self.settings["white_point"].get(),
            "tone_curve": self.settings["tone_curve"].get(),
            "contrast": self.settings["contrast"].get(),
            "brightness": self.settings["brightness"].get(),
            "highlights": self.settings["highlights"].get(),
            "shadows": self.settings["shadows"].get(),
            "saturation": self.settings["saturation"].get(),
            "vibrance": self.settings["vibrance"].get(),
            "hue": self.settings["hue"].get(),
            "dehaze": self.settings["dehaze"].get(),
            "color_grading_intensity": self.settings["color_grading_intensity"].get(),
            "monochrome": self.settings["monochrome"].get(),
            "mono_weights": [
                self.settings["mono_r"].get() / 100.0,
                self.settings["mono_g"].get() / 100.0,
                self.settings["mono_b"].get() / 100.0
            ],
            "shadows_color": self.settings["shadows_color"],
            "midtones_color": self.settings["midtones_color"],
            "highlights_color": self.settings["highlights_color"],
        }

    # ─── SÉPARATEUR DÉPLAÇABLE (Fonctionnalité 2) ───
    def on_canvas_click(self, event):
        if self.preview_image is None:
            return
        cw = self.preview_canvas.winfo_width()
        ch = self.preview_canvas.winfo_height()
        img_w, img_h = self.preview_image.size
        cx = (cw - img_w) // 2
        cy = (ch - img_h) // 2
        if cx <= event.x <= cx + img_w and cy <= event.y <= cy + img_h:
            self.dragging_split = True
            self.split_position = (event.x - cx) / img_w
            self.split_position = max(0.05, min(0.95, self.split_position))
            self.trigger_preview()

    def on_canvas_drag(self, event):
        if self.dragging_split and self.preview_image is not None:
            cw = self.preview_canvas.winfo_width()
            img_w = self.preview_image.size[0]
            cx = (cw - img_w) // 2
            self.split_position = (event.x - cx) / img_w
            self.split_position = max(0.05, min(0.95, self.split_position))
            self.trigger_preview()

    def on_canvas_release(self, event):
        self.dragging_split = False

    # ─── APERÇU TEMPS RÉEL ───
    def trigger_preview(self):
        # L'aperçu nécessite une image, mais on ne bloque pas l'export
        if self.source_image is None:
            self._draw_hald_preview()  # Mettre à jour quand même l'aperçu du Hald-CLUT
            return
        self.pending_preview = True
        if self.preview_thread is None or not self.preview_thread.is_alive():
            self.preview_thread = threading.Thread(target=self._preview_worker, daemon=True)
            self.preview_thread.start()

    def _preview_worker(self):
        while self.pending_preview:
            self.pending_preview = False
            time.sleep(0.06)
            if self.pending_preview:
                continue
            try:
                self._update_preview()
            except Exception as e:
                print(f"Erreur aperçu : {e}")

    def _update_preview(self):
        if self.preview_image is None:
            return
        settings = self.get_settings_dict()
        arr = np.array(self.preview_image).astype(np.float32) / 255.0
        processed = ImageEngine.apply_all(arr, settings)
        processed_uint8 = (np.clip(processed, 0, 1) * 255).astype(np.uint8)
        result_img = Image.fromarray(processed_uint8)

        cw = self.preview_canvas.winfo_width()
        ch = self.preview_canvas.winfo_height()
        img_w, img_h = self.preview_image.size
        cx = (cw - img_w) // 2
        cy = (ch - img_h) // 2

        if self.before_after or self.dragging_split:
            # Séparateur déplaçable (Fonctionnalité 2)
            split_x = int(img_w * self.split_position)
            split = Image.new("RGB", (img_w, img_h))
            split.paste(self.preview_image.crop((0, 0, split_x, img_h)), (0, 0))
            split.paste(result_img.crop((split_x, 0, img_w, img_h)), (split_x, 0))
            draw = ImageDraw.Draw(split)
            draw.line([(split_x, 0), (split_x, img_h)], fill="yellow", width=2)
            # Triangle indicateur
            draw.polygon([(split_x-6, img_h//2-8), (split_x+6, img_h//2), (split_x-6, img_h//2+8)], fill="yellow")
            result_img = split

        self.preview_tk = ImageTk.PhotoImage(result_img)
        self.preview_canvas.delete("all")
        self.preview_canvas.create_image(cx, cy, image=self.preview_tk, anchor=tk.NW)

        if self.before_after or self.dragging_split:
            # Légendes
            self.preview_canvas.create_text(cx + 10, cy + 10, text="ORIGINAL", fill="white", font=("Segoe UI", 10, "bold"), anchor=tk.NW)
            self.preview_canvas.create_text(cx + img_w - 10, cy + 10, text="LUT", fill="yellow", font=("Segoe UI", 10, "bold"), anchor=tk.NE)

        self._draw_hald_preview()

    def _draw_hald_preview(self):
        settings = self.get_settings_dict()
        level = 8
        side = level ** 3
        cube = level ** 2
        indices = np.arange(side * side)
        r = (indices % cube).astype(np.float32) / (cube - 1)
        g = ((indices // cube) % cube).astype(np.float32) / (cube - 1)
        b = (indices // (cube * cube)).astype(np.float32) / (cube - 1)
        mini_identity = np.stack([r, g, b], axis=-1)
        mini_processed = ImageEngine.apply_all(mini_identity, settings)
        mini_uint8 = (np.clip(mini_processed, 0, 1) * 255).astype(np.uint8).reshape(side, side, 3)
        mini_img = Image.fromarray(mini_uint8)
        mini_img = mini_img.resize((256, 256), Image.NEAREST)
        self.hald_preview_tk = ImageTk.PhotoImage(mini_img)
        self.hald_canvas.delete("all")
        cx = self.hald_canvas.winfo_width() // 2
        cy = self.hald_canvas.winfo_height() // 2
        self.hald_canvas.create_image(cx, cy, image=self.hald_preview_tk, anchor=tk.CENTER)

    def toggle_before_after(self):
        self.before_after = not self.before_after
        if not self.before_after:
            self.split_position = 0.5
        self.trigger_preview()

    # ─── EXPORT HALD-CLUT ───
    def export_hald(self):
        default_name = "mon_lut_hald12.png"
        if self.settings["monochrome"].get():
            default_name = "mon_lut_hald12_nb.png"
        path = filedialog.asksaveasfilename(
            title="Exporter le Hald-CLUT",
            defaultextension=".png",
            filetypes=[("PNG Hald-CLUT", "*.png")],
            initialfile=default_name
        )
        if not path:
            return
        self._do_export(path, "png")

    # ─── EXPORT MULTI-FORMAT (Fonctionnalité 4) ───
    def export_multi_format(self):
        base = filedialog.asksaveasfilename(
            title="Exporter en multi-format (base du nom)",
            defaultextension=".png",
            filetypes=[("PNG Hald-CLUT", "*.png")],
            initialfile="mon_lut"
        )
        if not base:
            return

        base_path = os.path.splitext(base)[0]
        self.status_label.config(text="⏳ Export multi-format...")
        self.progress.pack(fill=tk.X, padx=10, pady=5)
        self.progress["value"] = 10
        self.root.update_idletasks()

        def worker():
            try:
                settings = self.get_settings_dict()
                hald_array = self.hald_gen.generate_processed(settings)
                grayscale = self.settings["monochrome"].get()
                name = os.path.basename(base_path)

                # 1. PNG Hald-CLUT
                self.root.after(0, lambda: self.progress.configure(value=25))
                png_path = base_path + "_hald12.png"
                self.hald_gen.save(hald_array, png_path, grayscale=grayscale)

                # 2. .cube (DaVinci Resolve, Premiere)
                self.root.after(0, lambda: self.progress.configure(value=50))
                cube_path = base_path + ".cube"
                MultiFormatExporter.export_cube(hald_array, cube_path, name=name, grayscale=grayscale)

                # 3. .csp (Photoshop, After Effects)
                self.root.after(0, lambda: self.progress.configure(value=75))
                csp_path = base_path + ".csp"
                MultiFormatExporter.export_csp(hald_array, csp_path, name=name, grayscale=grayscale)

                self.root.after(0, lambda: self._multi_export_done(png_path, cube_path, csp_path))
            except Exception as e:
                self.root.after(0, lambda: self._export_error(e))
        threading.Thread(target=worker, daemon=True).start()

    def _multi_export_done(self, png_path, cube_path, csp_path):
        self.progress["value"] = 100
        self.status_label.config(text="✓ Export multi-format terminé")
        messagebox.showinfo("Export réussi",
            f"3 formats exportés :\n\n"
            f"📷 PNG Hald-CLUT :\n   {png_path}\n\n"
            f"🎬 CUBE (DaVinci/Premiere) :\n   {cube_path}\n\n"
            f"🎨 CSP (Photoshop/AE) :\n   {csp_path}")
        self.progress.pack_forget()
        self.save_auto_settings()

    def _do_export(self, path, fmt):
        self.status_label.config(text="⏳ Génération du Hald-CLUT...")
        self.progress.pack(fill=tk.X, padx=10, pady=5)
        self.progress["value"] = 10
        self.root.update_idletasks()

        def worker():
            try:
                settings = self.get_settings_dict()
                self.root.after(0, lambda: self.progress.configure(value=30))
                hald_array = self.hald_gen.generate_processed(settings)
                self.root.after(0, lambda: self.progress.configure(value=70))
                grayscale = self.settings["monochrome"].get()
                self.hald_gen.save(hald_array, path, grayscale=grayscale)
                self.root.after(0, lambda: self._export_done(path, grayscale))
            except Exception as e:
                self.root.after(0, lambda: self._export_error(e))
        threading.Thread(target=worker, daemon=True).start()

    def _export_done(self, path, grayscale):
        self.progress["value"] = 100
        mode_str = "Grayscale" if grayscale else "RGB"
        self.status_label.config(text=f"✓ Exporté ({mode_str}) : {os.path.basename(path)}")
        messagebox.showinfo("Export réussi",
            f"Hald-CLUT exporté !\n\n"
            f"Fichier : {path}\n"
            f"Mode : {mode_str}\n"
            f"Dimensions : {HALD_SIDE}×{HALD_SIDE} px\n"
            f"Niveau : {HALD_LEVEL}")
        self.progress.pack_forget()
        self.save_auto_settings()

    def _export_error(self, error):
        self.progress.pack_forget()
        self.status_label.config(text="❌ Erreur d'export")
        messagebox.showerror("Erreur", f"Échec de l'export :\n{error}")

    # ─── EXTRACTION DE LOOK (Fonctionnalité 1) ───
    def open_extractor(self):
        win = tk.Toplevel(self.root)
        win.title("🔍 Extraction automatique de look")
        win.geometry("500x400")
        win.transient(self.root)
        # win.grab_set()  # Désactivé : bloque les interactions après fermeture

        ttk.Label(win, text="Sélectionnez une paire d'images :", font=("Segoe UI", 12, "bold")).pack(pady=10)

        color_path_var = tk.StringVar()
        bw_path_var = tk.StringVar()
        name_var = tk.StringVar(value="Look Extrait")

        f1 = ttk.Frame(win)
        f1.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f1, text="Image couleur :").pack(side=tk.LEFT)
        ttk.Entry(f1, textvariable=color_path_var, width=30).pack(side=tk.LEFT, padx=5)
        ttk.Button(f1, text="📂", width=3, command=lambda: color_path_var.set(filedialog.askopenfilename(filetypes=[("Images", "*.jpg *.png *.jpeg")]))).pack(side=tk.LEFT)

        f2 = ttk.Frame(win)
        f2.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f2, text="Image N&B :").pack(side=tk.LEFT)
        ttk.Entry(f2, textvariable=bw_path_var, width=30).pack(side=tk.LEFT, padx=5)
        ttk.Button(f2, text="📂", width=3, command=lambda: bw_path_var.set(filedialog.askopenfilename(filetypes=[("Images", "*.jpg *.png *.jpeg")]))).pack(side=tk.LEFT)

        f3 = ttk.Frame(win)
        f3.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f3, text="Nom du preset :").pack(side=tk.LEFT)
        ttk.Entry(f3, textvariable=name_var, width=30).pack(side=tk.LEFT, padx=5)

        result_text = tk.Text(win, height=10, width=55, state=tk.DISABLED)
        result_text.pack(padx=10, pady=10)

        def do_extract():
            cp = color_path_var.get()
            bp = bw_path_var.get()
            if not cp or not bp:
                messagebox.showwarning("Attention", "Sélectionnez les deux images.")
                return
            try:
                preset = LookExtractor.extract(cp, bp, name_var.get())
                # Appliquer dans le générateur
                settings = preset["settings"]
                for key, val in settings.items():
                    if key in self.settings and hasattr(self.settings[key], "set"):
                        self.settings[key].set(val)
                    elif key in self.settings:
                        self.settings[key] = val

                # Mettre à jour les sliders mono depuis mono_weights
                if "mono_weights" in settings:
                    mw = settings["mono_weights"]
                    self.settings["mono_r"].set(int(mw[0] * 100))
                    self.settings["mono_g"].set(int(mw[1] * 100))
                    self.settings["mono_b"].set(100 - int(mw[0]*100) - int(mw[1]*100))

                self.on_monochrome_toggle()
                self.trigger_preview()
                self.root.lift()  # Remettre la fenêtre principale au premier plan
                self.root.focus_force()  # Forcer le focus

                # Afficher le résumé
                result_text.config(state=tk.NORMAL)
                result_text.delete("1.0", tk.END)
                result_text.insert(tk.END, f"✅ Look extrait : {preset['name']}\n\n")
                result_text.insert(tk.END, f"Mixeur N&B : R={settings['mono_r']}% V={settings['mono_g']}% B={settings['mono_b']}%\n")
                result_text.insert(tk.END, f"Contraste : {settings['contrast']}\n")
                result_text.insert(tk.END, f"Courbe S : {settings['tone_curve']}\n")
                result_text.insert(tk.END, f"Points N/B : {settings['black_point']} / {settings['white_point']}\n")
                result_text.config(state=tk.DISABLED)

                self.extract_status.config(text=f"✓ {preset['name']} chargé", foreground="green")
                self.status_label.config(text=f"Look extrait : {preset['name']}")
            except Exception as e:
                messagebox.showerror("Erreur", f"Extraction échouée :\n{e}")

        btn_frame = ttk.Frame(win)
        btn_frame.pack(pady=10)
        ttk.Button(btn_frame, text="🔍 Extraire et appliquer", command=do_extract).pack(side=tk.LEFT, padx=5)

        def extract_and_export():
            do_extract()
            win.destroy()
            self.root.after(200, self.export_hald)  # Exporter après fermeture

        ttk.Button(btn_frame, text="🔍 Extraire + Exporter LUT", command=extract_and_export).pack(side=tk.LEFT, padx=5)
        ttk.Button(win, text="❌ Fermer", command=win.destroy).pack(pady=5)

    # ─── BATCH PROCESSING (Fonctionnalité 5) ───
    def open_batch(self):
        win = tk.Toplevel(self.root)
        win.title("📁 Batch Processing")
        win.geometry("600x500")
        win.transient(self.root)
        # win.grab_set()  # Désactivé : bloque les interactions après fermeture

        ttk.Label(win, text="Appliquer le LUT actuel sur un dossier entier", font=("Segoe UI", 12, "bold")).pack(pady=10)

        input_var = tk.StringVar()
        output_var = tk.StringVar()
        format_var = tk.StringVar(value="jpg")

        f1 = ttk.Frame(win)
        f1.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f1, text="Dossier source :").pack(side=tk.LEFT)
        ttk.Entry(f1, textvariable=input_var, width=35).pack(side=tk.LEFT, padx=5)
        ttk.Button(f1, text="📂", width=3, command=lambda: input_var.set(filedialog.askdirectory())).pack(side=tk.LEFT)

        f2 = ttk.Frame(win)
        f2.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f2, text="Dossier sortie :").pack(side=tk.LEFT)
        ttk.Entry(f2, textvariable=output_var, width=35).pack(side=tk.LEFT, padx=5)
        ttk.Button(f2, text="📂", width=3, command=lambda: output_var.set(filedialog.askdirectory())).pack(side=tk.LEFT)

        f3 = ttk.Frame(win)
        f3.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(f3, text="Format :").pack(side=tk.LEFT)
        ttk.Combobox(f3, textvariable=format_var, values=["jpg", "png", "tiff"], width=10, state="readonly").pack(side=tk.LEFT, padx=5)

        progress_var = tk.DoubleVar(value=0)
        progress = ttk.Progressbar(win, variable=progress_var, maximum=100, length=500)
        progress.pack(padx=10, pady=10)

        status_label = ttk.Label(win, text="Prêt", anchor=tk.W)
        status_label.pack(fill=tk.X, padx=10)

        log_text = tk.Text(win, height=10, width=70, state=tk.DISABLED)
        log_text.pack(padx=10, pady=5)

        def do_batch():
            src = input_var.get()
            dst = output_var.get()
            if not src or not dst:
                messagebox.showwarning("Attention", "Sélectionnez les deux dossiers.")
                return
            os.makedirs(dst, exist_ok=True)

            # Générer le LUT actuel
            settings = self.get_settings_dict()
            hald_array = self.hald_gen.generate_processed(settings)
            grayscale = self.settings["monochrome"].get()

            if grayscale:
                lut_data = hald_array[..., 0].astype(np.float32) / 255.0
                lut_data = np.stack([lut_data, lut_data, lut_data], axis=-1)
            else:
                lut_data = hald_array.astype(np.float32) / 255.0

            # Extensions supportées
            exts = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
            files = [f for f in os.listdir(src) if f.lower().endswith(exts)]

            if not files:
                messagebox.showwarning("Attention", "Aucune image trouvée dans le dossier source.")
                return

            def worker():
                total = len(files)
                for i, fname in enumerate(files):
                    try:
                        in_path = os.path.join(src, fname)
                        out_name = os.path.splitext(fname)[0] + "_LUT." + format_var.get()
                        out_path = os.path.join(dst, out_name)

                        img = Image.open(in_path).convert("RGB")
                        img_arr = np.array(img).astype(np.float32) / 255.0

                        r_idx = np.clip((img_arr[..., 0] * (HALD_CUBE_SIZE - 1)).astype(np.int32), 0, HALD_CUBE_SIZE - 1)
                        g_idx = np.clip((img_arr[..., 1] * (HALD_CUBE_SIZE - 1)).astype(np.int32), 0, HALD_CUBE_SIZE - 1)
                        b_idx = np.clip((img_arr[..., 2] * (HALD_CUBE_SIZE - 1)).astype(np.int32), 0, HALD_CUBE_SIZE - 1)

                        hald_index = r_idx + g_idx * HALD_CUBE_SIZE + b_idx * HALD_CUBE_SIZE * HALD_CUBE_SIZE
                        hald_x = hald_index % HALD_SIDE
                        hald_y = hald_index // HALD_SIDE

                        result = lut_data[hald_y, hald_x]
                        result = (np.clip(result, 0, 1) * 255).astype(np.uint8)
                        out_img = Image.fromarray(result)

                        if format_var.get() == "jpg":
                            out_img.save(out_path, quality=95)
                        elif format_var.get() == "png":
                            out_img.save(out_path, optimize=True)
                        else:
                            out_img.save(out_path)

                        pct = int((i + 1) / total * 100)
                        win.after(0, lambda p=pct, f=fname: update_progress(p, f))
                    except Exception as e:
                        win.after(0, lambda f=fname, err=str(e): log_error(f, err))

                win.after(0, lambda: finish_batch())

            def update_progress(pct, fname):
                progress_var.set(pct)
                status_label.config(text=f"Traitement... {pct}% ({fname})")

            def log_error(fname, err):
                log_text.config(state=tk.NORMAL)
                log_text.insert(tk.END, f"❌ {fname} : {err}\n")
                log_text.config(state=tk.DISABLED)

            def finish_batch():
                progress_var.set(100)
                status_label.config(text=f"✅ Terminé ! {total} images traitées.")
                messagebox.showinfo("Batch terminé", f"{total} images traitées et sauvegardées dans :\n{dst}")

            threading.Thread(target=worker, daemon=True).start()

        ttk.Button(win, text="▶ Lancer le batch", command=do_batch).pack(pady=10)
        ttk.Button(win, text="❌ Fermer", command=win.destroy).pack(pady=5)

    # ─── SYNCHRONISATION (Fonctionnalité 6) ───
    def load_sync_path(self):
        if os.path.exists(SYNC_MARKER_FILE):
            try:
                with open(SYNC_MARKER_FILE, "r") as f:
                    self.sync_path = f.read().strip()
            except:
                self.sync_path = None

    def configure_sync(self):
        path = filedialog.askdirectory(title="Sélectionnez le dossier luts/ de votre Studio")
        if path:
            self.sync_path = path
            with open(SYNC_MARKER_FILE, "w") as f:
                f.write(path)
            messagebox.showinfo("Synchro configurée", f"Dossier de synchro :\n{path}\n\nLes LUTs exportés seront copiés automatiquement ici.")
            self.status_label.config(text=f"✓ Synchro : {path}")

    def sync_to_studio(self):
        if not self.sync_path or not os.path.isdir(self.sync_path):
            messagebox.showwarning("Synchro non configurée", "Configurez d'abord le dossier de synchro (Outils → Configurer).")
            return
        # Copier les LUTs existants
        lut_dir = os.path.join(os.path.dirname(__file__) if '__file__' in dir() else '.', "luts")
        if not os.path.isdir(lut_dir):
            messagebox.showwarning("Aucun LUT", "Générez d'abord des LUTs.")
            return
        copied = 0
        for f in os.listdir(lut_dir):
            if f.endswith(".png"):
                src = os.path.join(lut_dir, f)
                dst = os.path.join(self.sync_path, f)
                import shutil
                shutil.copy2(src, dst)
                copied += 1
        messagebox.showinfo("Synchro terminée", f"{copied} LUTs copiés vers :\n{self.sync_path}")
        self.status_label.config(text=f"✓ {copied} LUTs synchronisés")

    # ─── GESTION DES PRESETS ───
    def _build_preset_names(self):
        """Reconstruit la liste affichée dans le menu à partir de self.presets_data
        (sans jamais recharger quoi que ce soit depuis le disque)."""
        self.preset_names = ["— Choisir un preset —"]
        if self.presets_data:
            try:
                categories = {}
                for name, data in self.presets_data.items():
                    cat = data.get("category", "Autre")
                    if cat not in categories:
                        categories[cat] = []
                    categories[cat].append(name)
                for cat in sorted(categories.keys()):
                    self.preset_names.append(f"== {cat} ==")
                    for name in sorted(categories[cat]):
                        self.preset_names.append(f"  {name}")
            except Exception as e:
                messagebox.showerror("Erreur presets", f"Impossible de construire la liste des presets :\n{e}")
        try:
            self.preset_combo["values"] = self.preset_names
        except tk.TclError as e:
            messagebox.showerror("Erreur affichage", f"Impossible d'afficher la liste des presets :\n{e}")

    def _load_presets(self):
        self.presets_data = {}
        search_paths = []
        # Priorité 1 : le dernier fichier de presets chargé manuellement (mémorisé
        # entre deux lancements, même s'il est dans un sous-dossier).
        if os.path.exists(LAST_PRESETS_PATH_FILE):
            try:
                with open(LAST_PRESETS_PATH_FILE, "r", encoding="utf-8") as f:
                    last_path = f.read().strip()
                if last_path:
                    search_paths.append(last_path)
            except Exception:
                pass
        # Priorité 2 : le fichier par défaut à côté du programme / dans le dossier courant.
        search_paths += [
            os.path.join(os.path.dirname(__file__) if '__file__' in dir() else '.', "film_presets.json"),
            "film_presets.json",
            os.path.expanduser("~/.hald_clut_presets.json")
        ]
        for path in search_paths:
            if path and os.path.exists(path):
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        self.presets_data = json.load(f)
                    break
                except Exception:
                    continue
        self._build_preset_names()

    def on_preset_selected(self, event=None):
        name = self.preset_var.get().strip()
        if name.startswith("══") or name.startswith("—"):
            return
        name = name.lstrip("  ")
        if name not in self.presets_data:
            return
        settings = self.presets_data[name]["settings"]
        for key, val in settings.items():
            if key in self.settings and hasattr(self.settings[key], "set"):
                self.settings[key].set(val)
            elif key in self.settings:
                self.settings[key] = val
        self.on_monochrome_toggle()
        self.trigger_preview()
        self.status_label.config(text=f"✓ Preset chargé : {name}")

    def load_presets_file(self):
        path = filedialog.askopenfilename(title="Charger un fichier de presets", filetypes=[("JSON Presets", "*.json")])
        if path:
            try:
                with open(path, "r", encoding="utf-8") as f:
                    self.presets_data = json.load(f)
                self._build_preset_names()
                self.preset_combo.set("— Choisir un preset —")
                self.status_label.config(text=f"✓ {len(self.presets_data)} presets chargés")
                # Mémorise ce chemin pour le recharger automatiquement au prochain lancement,
                # même s'il se trouve dans un sous-dossier ou ailleurs sur le disque.
                try:
                    with open(LAST_PRESETS_PATH_FILE, "w", encoding="utf-8") as f:
                        f.write(path)
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("Erreur", f"Impossible de charger :\n{e}")

    # ─── SETTINGS IMPORT/EXPORT ───
    def export_settings(self):
        path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")], initialfile="reglages_lut.json")
        if path:
            with open(path, "w") as f:
                json.dump(self.get_settings_dict(), f, indent=2)
            self.status_label.config(text="Réglages exportés")

    def import_settings(self):
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
        if not path:
            return
        try:
            with open(path, "r") as f:
                data = json.load(f)
            for key, val in data.items():
                if key in self.settings and hasattr(self.settings[key], "set"):
                    self.settings[key].set(val)
                elif key in self.settings:
                    self.settings[key] = val
            self.on_monochrome_toggle()
            self.trigger_preview()
            self.status_label.config(text="Réglages importés")
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible d'importer :\n{e}")

    def save_auto_settings(self):
        try:
            with open(SETTINGS_FILE, "w") as f:
                json.dump(self.get_settings_dict(), f, indent=2)
        except:
            pass

    def load_auto_settings(self):
        if os.path.exists(SETTINGS_FILE):
            try:
                with open(SETTINGS_FILE, "r") as f:
                    data = json.load(f)
                for key, val in data.items():
                    if key in self.settings and hasattr(self.settings[key], "set"):
                        self.settings[key].set(val)
                    elif key in self.settings:
                        self.settings[key] = val
                self.on_monochrome_toggle()
            except:
                pass

    def on_close(self):
        self.save_auto_settings()
        self.root.destroy()


# ═══════════════════════════════════════════════════════════════════════════════
# MODE BATCH (ligne de commande)
# ═══════════════════════════════════════════════════════════════════════════════

def batch_generate(settings_path, output_path):
    with open(settings_path, "r") as f:
        settings = json.load(f)
    print(f"Chargement réglages depuis {settings_path}")
    print(f"Génération Hald-CLUT niveau {HALD_LEVEL} ({HALD_SIDE}×{HALD_SIDE})...")
    hald_gen = HaldClutGenerator()
    hald_array = hald_gen.generate_processed(settings)
    grayscale = settings.get("monochrome", False)
    hald_gen.save(hald_array, output_path, grayscale=grayscale)
    mode = "Grayscale" if grayscale else "RGB"
    print(f"✓ Hald-CLUT exporté : {output_path} ({mode})")


# ═══════════════════════════════════════════════════════════════════════════════
# POINT D'ENTRÉE
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Hald-CLUT Generator PRO v2.0")
    parser.add_argument("--batch", nargs=2, metavar=("settings.json", "output.png"), help="Mode batch")
    args = parser.parse_args()

    if args.batch:
        batch_generate(args.batch[0], args.batch[1])
    else:
        root = tk.Tk()
        style = ttk.Style()
        # "vista" est un thème natif Windows (implémenté en C, pas en scripts Tcl
        # séparés) : il est beaucoup plus fiable une fois compilé avec PyInstaller.
        # "clam" dépend de fichiers .tcl que PyInstaller embarque parfois mal,
        # ce qui peut casser silencieusement des widgets comme les Combobox.
        theme_applied = None
        for preferred_theme in ("vista", "clam", "default"):
            if preferred_theme in style.theme_names():
                try:
                    style.theme_use(preferred_theme)
                    theme_applied = preferred_theme
                    break
                except tk.TclError:
                    continue
        if theme_applied is None:
            print("Attention : aucun thème ttk n'a pu être appliqué, thème système par défaut utilisé.")
        style.configure("TFrame", background="#f5f5f5")
        style.configure("TLabel", background="#f5f5f5", font=("Segoe UI", 10))
        style.configure("TButton", font=("Segoe UI", 10))
        style.configure("TScale", background="#f5f5f5")
        app = App(root)
        root.mainloop()