#!/usr/bin/env python3
"""Validate dependencies/external.json against items.json for Stage 2.2.

Checks:
- Valid JSON structure (array of external dependency objects)
- Schema compliance (required fields, valid categories)
- All item IDs in 'items' arrays exist in items.json
- No duplicate descriptions
- Summary statistics: count by category, items with most external dependencies
"""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
EXTERNAL_PATH = REPO_ROOT / "dependencies" / "external.json"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"

VALID_CATEGORIES = {"undergraduate_prerequisite", "external_result", "folklore"}


def load_json(path):
    with open(path) as f:
        return json.load(f)


def validate(external_path, items_path):
    errors = []
    warnings = []

    # --- Load items.json ---
    try:
        items = load_json(items_path)
    except json.JSONDecodeError as e:
        print(f"FATAL: items.json is not valid JSON: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print(f"FATAL: {items_path} not found", file=sys.stderr)
        return 1

    if not isinstance(items, list):
        print("FATAL: items.json root must be an array", file=sys.stderr)
        return 1

    item_ids = {item["id"] for item in items if isinstance(item, dict) and "id" in item}
    print(f"Loaded {len(item_ids)} items from {items_path}")

    # --- Load external.json ---
    try:
        externals = load_json(external_path)
    except json.JSONDecodeError as e:
        print(f"FATAL: external.json is not valid JSON: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print(f"FATAL: {external_path} not found", file=sys.stderr)
        return 1

    if not isinstance(externals, list):
        print("FATAL: external.json root must be an array", file=sys.stderr)
        return 1

    print(f"Loaded {len(externals)} external dependencies from {external_path}")

    # --- Validate each entry ---
    seen_descriptions = {}
    category_counts = {c: 0 for c in VALID_CATEGORIES}
    item_dep_counts = {}  # item_id -> number of external deps referencing it

    for i, entry in enumerate(externals):
        prefix = f"Entry [{i}]"

        if not isinstance(entry, dict):
            errors.append(f"{prefix}: not an object")
            continue

        # Required fields
        for field in ("description", "category", "items"):
            if field not in entry:
                errors.append(f"{prefix}: missing required field '{field}'")

        if "description" not in entry or "category" not in entry:
            continue

        desc = entry["description"]
        prefix = f"Entry '{desc[:60]}'"

        # Description must be a non-empty string
        if not isinstance(desc, str) or len(desc) == 0:
            errors.append(f"Entry [{i}]: description must be a non-empty string")
            continue

        # Duplicate description check
        if desc in seen_descriptions:
            errors.append(
                f"{prefix}: duplicate description (first seen at index {seen_descriptions[desc]})"
            )
        seen_descriptions[desc] = i

        # Category validation
        cat = entry["category"]
        if not isinstance(cat, str):
            errors.append(f"{prefix}: category must be a string")
        elif cat not in VALID_CATEGORIES:
            errors.append(
                f"{prefix}: invalid category '{cat}' "
                f"(must be one of: {', '.join(sorted(VALID_CATEGORIES))})"
            )
        else:
            category_counts[cat] += 1

        # Items array validation
        if "items" not in entry:
            continue
        entry_items = entry["items"]
        if not isinstance(entry_items, list):
            errors.append(f"{prefix}: 'items' must be an array")
            continue

        if len(entry_items) == 0:
            errors.append(f"{prefix}: 'items' array must not be empty")

        seen_item_ids = set()
        for item_id in entry_items:
            if not isinstance(item_id, str):
                errors.append(f"{prefix}: item ID must be a string, got {type(item_id).__name__}")
                continue
            if item_id not in item_ids:
                errors.append(f"{prefix}: item ID '{item_id}' not found in items.json")
            if item_id in seen_item_ids:
                warnings.append(f"{prefix}: duplicate item ID '{item_id}'")
            seen_item_ids.add(item_id)
            item_dep_counts[item_id] = item_dep_counts.get(item_id, 0) + 1

        # Extra fields check
        allowed = {"description", "category", "items", "source"}
        extra = set(entry.keys()) - allowed
        if extra:
            warnings.append(f"{prefix}: unexpected fields: {extra}")

        # Source field validation (optional)
        if "source" in entry:
            if not isinstance(entry["source"], str):
                errors.append(f"{prefix}: 'source' must be a string")

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

    # --- Summary statistics ---
    print(f"\nExternal dependencies: {len(externals)}")
    print("By category:")
    for cat in sorted(VALID_CATEGORIES):
        print(f"  {cat}: {category_counts[cat]}")

    if item_dep_counts:
        top_items = sorted(item_dep_counts.items(), key=lambda x: -x[1])[:10]
        print(f"\nItems with most external dependencies (top {min(10, len(top_items))}):")
        for item_id, count in top_items:
            print(f"  {item_id}: {count}")

    unique_items_referenced = len(item_dep_counts)
    print(f"\nUnique items referencing external deps: {unique_items_referenced}/{len(item_ids)}")
    print("VALIDATION PASSED")
    return 0


if __name__ == "__main__":
    external_path = Path(sys.argv[1]) if len(sys.argv) > 1 else EXTERNAL_PATH
    items_path = Path(sys.argv[2]) if len(sys.argv) > 2 else ITEMS_PATH
    sys.exit(validate(external_path, items_path))
