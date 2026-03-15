#!/usr/bin/env python3
"""Validate items.json for Stage 1.5 contiguity: every line of every page
belongs to exactly one blob, with no gaps and no overlaps."""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGES_DIR = REPO_ROOT / "pages"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
SCHEMA_PATH = Path(__file__).resolve().parent / "items_schema.json"

VALID_TYPES = {
    "theorem", "lemma", "proposition", "corollary",
    "definition", "example", "exercise", "remark",
    "discussion", "introduction", "preface", "notation",
    "bibliography", "index",
}

# Files in pages/ that are not actual page content
EXCLUDED_FILES = {"CONVENTIONS.md"}


def get_page_order():
    """Return ordered list of logical page names matching the book's order."""
    mapping_path = REPO_ROOT / "pdf" / "pages" / "mapping.json"
    if mapping_path.exists():
        with open(mapping_path) as f:
            data = json.load(f)
        # mapping is raw_page -> logical_page; sort by raw page number
        pairs = sorted(data["mapping"].items(), key=lambda p: int(p[0]))
        return [logical for _, logical in pairs]

    # Fallback: frontmatter first, then numbered pages
    pages = []
    for p in sorted(PAGES_DIR.glob("frontmatter-*.md"),
                     key=lambda x: int(x.stem.split("-")[1])):
        pages.append(p.stem)
    for p in sorted(PAGES_DIR.glob("[0-9]*.md"),
                     key=lambda x: int(x.stem)):
        pages.append(p.stem)
    for p in sorted(PAGES_DIR.glob("backmatter-*.md"),
                     key=lambda x: int(x.stem.split("-")[1])):
        pages.append(p.stem)
    return pages


def get_page_files():
    """Return set of page names that have .md files (excluding non-page files)."""
    return {
        p.stem for p in PAGES_DIR.glob("*.md")
        if p.name not in EXCLUDED_FILES
    }


def load_items(path):
    with open(path) as f:
        return json.load(f)


def page_line_count(page_name):
    """Return the number of lines in a page's markdown file."""
    p = PAGES_DIR / f"{page_name}.md"
    if not p.exists():
        return None
    return sum(1 for _ in open(p))


def expand_item_lines(item, page_order):
    """Expand an item into a set of (page, line) tuples it covers.

    Returns (set_of_tuples, list_of_errors).
    """
    errors = []
    covered = set()

    start_page = item["start_page"]
    end_page = item["end_page"]
    start_line = item["start_line"]
    end_line = item["end_line"]

    if start_page not in page_order_set:
        errors.append(f"  start_page '{start_page}' not in page order")
        return covered, errors
    if end_page not in page_order_set:
        errors.append(f"  end_page '{end_page}' not in page order")
        return covered, errors

    si = page_order.index(start_page)
    ei = page_order.index(end_page)

    if si > ei:
        errors.append(f"  start_page '{start_page}' comes after end_page '{end_page}'")
        return covered, errors

    for pi in range(si, ei + 1):
        page = page_order[pi]
        lc = page_line_count(page)
        if lc is None:
            errors.append(f"  page file pages/{page}.md does not exist")
            continue

        if pi == si and pi == ei:
            # Same page
            lo, hi = start_line, end_line
        elif pi == si:
            lo, hi = start_line, lc
        elif pi == ei:
            lo, hi = 1, end_line
        else:
            lo, hi = 1, lc

        if lo < 1:
            errors.append(f"  line {lo} < 1 on page {page}")
            lo = 1
        if lc is not None and hi > lc:
            errors.append(f"  end_line {hi} exceeds line count {lc} on page {page}")
            hi = lc
        if lo > hi:
            errors.append(f"  start_line {lo} > end_line {hi} on page {page}")
            continue

        for line in range(lo, hi + 1):
            covered.add((page, line))

    return covered, errors


def validate(items_path):
    errors = []
    warnings = []

    # --- Load items ---
    try:
        items = load_items(items_path)
    except json.JSONDecodeError as e:
        print(f"FATAL: items.json is not valid JSON: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print(f"FATAL: {items_path} not found", file=sys.stderr)
        return 1

    if not isinstance(items, list):
        print("FATAL: items.json root must be an array", file=sys.stderr)
        return 1

    print(f"Loaded {len(items)} items from {items_path}")

    page_order = get_page_order()
    global page_order_set
    page_order_set = set(page_order)
    page_files = get_page_files()

    # --- Schema-level checks per item ---
    required_fields = {"id", "type", "title", "start_page", "end_page", "start_line", "end_line"}
    seen_ids = set()

    for i, item in enumerate(items):
        prefix = f"Item [{i}]"
        if not isinstance(item, dict):
            errors.append(f"{prefix}: not an object")
            continue

        item_id = item.get("id", f"<index {i}>")
        prefix = f"Item '{item_id}'"

        # Required fields
        missing = required_fields - set(item.keys())
        if missing:
            errors.append(f"{prefix}: missing fields: {missing}")
            continue

        # Extra fields
        extra = set(item.keys()) - required_fields
        if extra:
            warnings.append(f"{prefix}: unexpected fields: {extra}")

        # Duplicate IDs
        if item_id in seen_ids:
            errors.append(f"{prefix}: duplicate id")
        seen_ids.add(item_id)

        # Type enum
        if item["type"] not in VALID_TYPES:
            errors.append(f"{prefix}: invalid type '{item['type']}'")

        # Line number types
        if not isinstance(item["start_line"], int):
            errors.append(f"{prefix}: start_line must be integer, got {type(item['start_line']).__name__}")
        if not isinstance(item["end_line"], int):
            errors.append(f"{prefix}: end_line must be integer, got {type(item['end_line']).__name__}")

    # --- Contiguity check ---
    # Build complete coverage map: (page, line) -> item_id
    coverage = {}
    for item in items:
        if not isinstance(item, dict) or "id" not in item:
            continue
        item_id = item["id"]
        covered, item_errors = expand_item_lines(item, page_order)
        for e in item_errors:
            errors.append(f"Item '{item_id}': {e}")
        for pl in covered:
            if pl in coverage:
                errors.append(
                    f"Overlap: page {pl[0]} line {pl[1]} claimed by "
                    f"both '{coverage[pl]}' and '{item_id}'"
                )
            else:
                coverage[pl] = item_id

    # --- Gap check: every line of every page file must be covered ---
    pages_referenced = {item.get("start_page") for item in items if isinstance(item, dict)}
    pages_referenced |= {item.get("end_page") for item in items if isinstance(item, dict)}
    pages_referenced.discard(None)

    uncovered_pages = page_files - pages_referenced
    if uncovered_pages:
        # Sort for readable output
        sorted_uncovered = sorted(uncovered_pages, key=lambda p: (
            0 if p.startswith("frontmatter") else (2 if p.startswith("backmatter") else 1),
            int(p.split("-")[-1]) if "-" in p else int(p) if p.isdigit() else 0
        ))
        errors.append(
            f"Pages with no blob coverage ({len(uncovered_pages)}): "
            + ", ".join(sorted_uncovered)
        )

    gap_count = 0
    for page in page_order:
        if page not in page_files:
            continue  # Page file doesn't exist yet (still being transcribed)
        lc = page_line_count(page)
        if lc is None or lc == 0:
            continue  # Empty page (blank pages are OK)
        for line in range(1, lc + 1):
            if (page, line) not in coverage:
                gap_count += 1
                if gap_count <= 20:
                    errors.append(f"Gap: page {page} line {line} not covered by any blob")
    if gap_count > 20:
        errors.append(f"  ... and {gap_count - 20} more uncovered lines")

    # --- Report ---
    if warnings:
        print(f"\nWarnings ({len(warnings)}):")
        for w in warnings:
            print(f"  WARNING: {w}")

    if errors:
        print(f"\nErrors ({len(errors)}):", file=sys.stderr)
        for e in errors:
            print(f"  ERROR: {e}", file=sys.stderr)
        print(f"\nVALIDATION FAILED: {len(errors)} error(s)", file=sys.stderr)
        return 1

    total_lines = sum(
        page_line_count(p) or 0
        for p in page_order if p in page_files
    )
    print(f"\nCoverage: {len(coverage)}/{total_lines} lines across {len(page_files)} pages")
    print(f"Items: {len(items)} blobs, {len(seen_ids)} unique IDs")
    print("VALIDATION PASSED")
    return 0


if __name__ == "__main__":
    items_path = Path(sys.argv[1]) if len(sys.argv) > 1 else ITEMS_PATH
    sys.exit(validate(items_path))
