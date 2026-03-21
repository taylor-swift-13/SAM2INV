#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Render structural diversity results as a PNG table.")
    parser.add_argument("--input", type=Path, required=True, help="Input JSON from evaluate_structural_diversity.py")
    parser.add_argument("--output", type=Path, required=True, help="Output PNG path")
    return parser.parse_args()


def _load_font(size: int) -> ImageFont.ImageFont:
    candidates = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
    ]
    for path in candidates:
        p = Path(path)
        if p.exists():
            return ImageFont.truetype(str(p), size=size)
    return ImageFont.load_default()


def _text_size(draw: ImageDraw.ImageDraw, text: str, font: ImageFont.ImageFont) -> tuple[int, int]:
    bbox = draw.textbbox((0, 0), text, font=font)
    return bbox[2] - bbox[0], bbox[3] - bbox[1]


def main() -> None:
    args = parse_args()
    rows = json.loads(args.input.read_text(encoding="utf-8"))

    headers = [
        "Dataset",
        "Files",
        "Ctrl Unique",
        "Skel Unique",
        "Ctrl Score",
        "Skel Score",
        "Total Score",
    ]
    body = [
        [
            row["name"],
            str(row["files"]),
            str(row["control_unique"]),
            str(row["skeleton_unique"]),
            f'{row["control_score"]:.3f}',
            f'{row["skeleton_score"]:.3f}',
            f'{row["total_score"]:.3f}',
        ]
        for row in rows
    ]

    font = _load_font(22)
    header_font = _load_font(24)
    padding_x = 18
    padding_y = 12
    row_h = 44

    probe = Image.new("RGB", (10, 10), "white")
    draw = ImageDraw.Draw(probe)
    col_widths = []
    for col_idx, header in enumerate(headers):
        width = _text_size(draw, header, header_font)[0]
        for row in body:
            width = max(width, _text_size(draw, row[col_idx], font)[0])
        col_widths.append(width + 2 * padding_x)

    total_w = sum(col_widths) + 2
    total_h = row_h * (len(body) + 1) + 2
    img = Image.new("RGB", (total_w, total_h), "white")
    draw = ImageDraw.Draw(img)

    colors = {
        "border": "#94a3b8",
        "header": "#dbeafe",
        "odd": "#f8fafc",
        "even": "#eef2ff",
        "text": "#0f172a",
    }

    y = 1
    x = 1
    for col_idx, header in enumerate(headers):
        w = col_widths[col_idx]
        draw.rectangle([x, y, x + w, y + row_h], fill=colors["header"], outline=colors["border"], width=1)
        tw, th = _text_size(draw, header, header_font)
        draw.text((x + (w - tw) / 2, y + (row_h - th) / 2 - 2), header, font=header_font, fill=colors["text"])
        x += w

    for row_idx, row in enumerate(body, start=1):
        y = 1 + row_idx * row_h
        x = 1
        fill = colors["odd"] if row_idx % 2 == 1 else colors["even"]
        for col_idx, cell in enumerate(row):
            w = col_widths[col_idx]
            draw.rectangle([x, y, x + w, y + row_h], fill=fill, outline=colors["border"], width=1)
            tw, th = _text_size(draw, cell, font)
            draw.text((x + (w - tw) / 2, y + (row_h - th) / 2 - 1), cell, font=font, fill=colors["text"])
            x += w

    args.output.parent.mkdir(parents=True, exist_ok=True)
    img.save(args.output)


if __name__ == "__main__":
    main()
