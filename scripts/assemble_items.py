#!/usr/bin/env python3
"""Merge per-chapter structure files into progress/items.json.

Reads structure/*.json in book order (Frontmatter, Chapter1-9, Backmatter)
and concatenates their arrays into a single items.json.
"""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
STRUCTURE_DIR = REPO_ROOT / "structure"
OUTPUT_PATH = REPO_ROOT / "progress" / "items.json"

# Book order: Frontmatter, then Chapters 1-9, then Backmatter
CHAPTER_ORDER = [
    "Frontmatter",
    "Chapter1",
    "Chapter2",
    "Chapter3",
    "Chapter4",
    "Chapter5",
    "Chapter6",
    "Chapter7",
    "Chapter8",
    "Chapter9",
    "Backmatter",
]


def main():
    all_items = []
    seen_ids = set()

    for chapter in CHAPTER_ORDER:
        path = STRUCTURE_DIR / f"{chapter}.json"
        if not path.exists():
            print(f"ERROR: missing structure file: {path}", file=sys.stderr)
            return 1

        with open(path) as f:
            items = json.load(f)

        if not isinstance(items, list):
            print(f"ERROR: {path} root is not an array", file=sys.stderr)
            return 1

        for item in items:
            item_id = item.get("id", "<unknown>")
            if item_id in seen_ids:
                print(f"ERROR: duplicate id '{item_id}' in {chapter}", file=sys.stderr)
                return 1
            seen_ids.add(item_id)

        all_items.extend(items)
        print(f"  {chapter}: {len(items)} items")

    # Write output
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, "w") as f:
        json.dump(all_items, f, indent=2)
        f.write("\n")

    print(f"\nAssembled {len(all_items)} items into {OUTPUT_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
