#!/usr/bin/env python3
"""Stage 1.6: Extract per-blob markdown files from page-level transcriptions.

For each item in progress/items.json, extract the corresponding lines from
pages/*.md and write to blobs/<id>.md.
"""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGES_DIR = REPO_ROOT / "pages"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
BLOBS_DIR = REPO_ROOT / "blobs"
MAPPING_PATH = REPO_ROOT / "pdf" / "pages" / "mapping.json"


def get_page_order():
    """Return ordered list of logical page names matching the book's order."""
    with open(MAPPING_PATH) as f:
        data = json.load(f)
    pairs = sorted(data["mapping"].items(), key=lambda p: int(p[0]))
    return [logical for _, logical in pairs]


def read_page_lines(page_name):
    """Return list of lines (with newlines) for a page file."""
    p = PAGES_DIR / f"{page_name}.md"
    if not p.exists():
        return []
    with open(p) as f:
        return f.readlines()


def extract_blob(item, page_order):
    """Extract the text for one item from the page files."""
    sp = item["start_page"]
    ep = item["end_page"]
    sl = item["start_line"]
    el = item["end_line"]

    si = page_order.index(sp)
    ei = page_order.index(ep)

    lines = []
    for pi in range(si, ei + 1):
        page = page_order[pi]
        page_lines = read_page_lines(page)
        lc = len(page_lines)

        if pi == si and pi == ei:
            lo, hi = sl, el
        elif pi == si:
            lo, hi = sl, lc
        elif pi == ei:
            lo, hi = 1, el
        else:
            lo, hi = 1, lc

        # Clamp to valid range
        lo = max(1, lo)
        hi = min(lc, hi) if lc > 0 else 0

        for line_num in range(lo, hi + 1):
            lines.append(page_lines[line_num - 1])

    return "".join(lines)


def main():
    with open(ITEMS_PATH) as f:
        items = json.load(f)

    page_order = get_page_order()

    # Clean output directory
    BLOBS_DIR.mkdir(exist_ok=True)

    count = 0
    empty = 0
    for item in items:
        item_id = item["id"]
        blob_text = extract_blob(item, page_order)

        # Write blob file
        blob_path = BLOBS_DIR / f"{item_id}.md"
        blob_path.parent.mkdir(parents=True, exist_ok=True)
        with open(blob_path, "w") as f:
            f.write(blob_text)

        count += 1
        if not blob_text.strip():
            empty += 1

    print(f"Extracted {count} blobs to {BLOBS_DIR}/")
    if empty:
        print(f"  ({empty} empty blobs — blank pages)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
