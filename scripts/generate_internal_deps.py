#!/usr/bin/env python3
"""Generate conservative internal dependencies (Stage 2.1).

Each item depends on all items that precede it in book order.
The book (Etingof's Introduction to Representation Theory) does not
contain explicit chapter-independence declarations, so no trimming
is applied to the conservative baseline.
"""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
DEPS_PATH = REPO_ROOT / "dependencies" / "internal.json"


def main():
    items = json.load(open(ITEMS_PATH))
    item_ids = [item["id"] for item in items if isinstance(item, dict) and "id" in item]

    deps = {}
    for idx, item_id in enumerate(item_ids):
        deps[item_id] = item_ids[:idx]

    DEPS_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(DEPS_PATH, "w") as f:
        json.dump(deps, f, indent=2)
        f.write("\n")

    total_edges = sum(len(v) for v in deps.values())
    print(f"Generated {len(deps)} entries with {total_edges} dependency edges")
    print(f"Written to {DEPS_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
