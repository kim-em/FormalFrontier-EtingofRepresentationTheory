#!/usr/bin/env python3
"""Verify that concatenating all blob files in book order reproduces
the complete transcribed text from pages/*.md."""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGES_DIR = REPO_ROOT / "pages"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
BLOBS_DIR = REPO_ROOT / "blobs"
MAPPING_PATH = REPO_ROOT / "pdf" / "pages" / "mapping.json"

EXCLUDED_FILES = {"CONVENTIONS.md"}


def get_page_order():
    with open(MAPPING_PATH) as f:
        data = json.load(f)
    pairs = sorted(data["mapping"].items(), key=lambda p: int(p[0]))
    return [logical for _, logical in pairs]


def main():
    # Build expected text: concatenation of all pages in order
    page_order = get_page_order()
    page_files = {p.stem for p in PAGES_DIR.glob("*.md") if p.name not in EXCLUDED_FILES}

    expected_parts = []
    for page in page_order:
        if page not in page_files:
            continue
        p = PAGES_DIR / f"{page}.md"
        expected_parts.append(p.read_text())

    expected = "".join(expected_parts)

    # Build actual text: concatenation of all blobs in items.json order
    with open(ITEMS_PATH) as f:
        items = json.load(f)

    actual_parts = []
    for item in items:
        blob_path = BLOBS_DIR / f"{item['id']}.md"
        if not blob_path.exists():
            print(f"ERROR: missing blob file: {blob_path}", file=sys.stderr)
            return 1
        actual_parts.append(blob_path.read_text())

    actual = "".join(actual_parts)

    if expected == actual:
        print(f"VERIFICATION PASSED: blob concatenation matches page text")
        print(f"  {len(items)} blobs, {len(expected)} characters total")
        return 0
    else:
        # Find first difference
        for i, (e, a) in enumerate(zip(expected, actual)):
            if e != a:
                ctx_start = max(0, i - 40)
                print(f"MISMATCH at character {i}:", file=sys.stderr)
                print(f"  Expected: {repr(expected[ctx_start:i+40])}", file=sys.stderr)
                print(f"  Actual:   {repr(actual[ctx_start:i+40])}", file=sys.stderr)
                break
        else:
            shorter = "expected" if len(expected) < len(actual) else "actual"
            print(f"MISMATCH: {shorter} is shorter ({len(expected)} vs {len(actual)} chars)", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
