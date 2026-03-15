#!/usr/bin/env python3
"""Validate dependencies/internal.json against items.json for Stage 2.1.

Checks:
- Valid JSON structure (object mapping item IDs to arrays of item IDs)
- All source item IDs exist in items.json
- All dependency target IDs exist in items.json
- No self-dependencies
- No forward dependencies (item depending on a later item) unless flagged
- Conservative default applied (each item depends on all preceding items)
"""

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEPS_PATH = REPO_ROOT / "dependencies" / "internal.json"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"


def load_json(path):
    with open(path) as f:
        return json.load(f)


def build_item_order(items):
    """Return a list of item IDs in book order (same order as items.json array)."""
    return [item["id"] for item in items if isinstance(item, dict) and "id" in item]


def validate(deps_path, items_path):
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

    item_order = build_item_order(items)
    item_set = set(item_order)
    item_index = {item_id: idx for idx, item_id in enumerate(item_order)}

    print(f"Loaded {len(item_order)} items from {items_path}")

    # --- Load dependencies ---
    try:
        deps = load_json(deps_path)
    except json.JSONDecodeError as e:
        print(f"FATAL: internal.json is not valid JSON: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print(f"FATAL: {deps_path} not found", file=sys.stderr)
        return 1

    if not isinstance(deps, dict):
        print("FATAL: internal.json root must be an object", file=sys.stderr)
        return 1

    print(f"Loaded {len(deps)} dependency entries from {deps_path}")

    # --- Validate each entry ---
    for source_id, dep_list in deps.items():
        prefix = f"Item '{source_id}'"

        # Source must exist in items.json
        if source_id not in item_set:
            errors.append(f"{prefix}: source ID not found in items.json")
            continue

        # Dependencies must be an array
        if not isinstance(dep_list, list):
            errors.append(f"{prefix}: dependencies must be an array, got {type(dep_list).__name__}")
            continue

        seen_deps = set()
        for dep_id in dep_list:
            if not isinstance(dep_id, str):
                errors.append(f"{prefix}: dependency must be a string, got {type(dep_id).__name__}")
                continue

            # Target must exist in items.json
            if dep_id not in item_set:
                errors.append(f"{prefix}: dependency target '{dep_id}' not found in items.json")
                continue

            # No self-dependencies
            if dep_id == source_id:
                errors.append(f"{prefix}: self-dependency")
                continue

            # No duplicate dependencies
            if dep_id in seen_deps:
                warnings.append(f"{prefix}: duplicate dependency on '{dep_id}'")
            seen_deps.add(dep_id)

            # No forward dependencies
            if item_index[dep_id] > item_index[source_id]:
                errors.append(
                    f"{prefix}: forward dependency on '{dep_id}' "
                    f"(index {item_index[dep_id]} > {item_index[source_id]})"
                )

    # --- Coverage check: every item in items.json should have an entry ---
    missing_entries = item_set - set(deps.keys())
    # The first item has no dependencies, so an empty array is expected but entry should exist
    if missing_entries:
        sorted_missing = sorted(missing_entries, key=lambda x: item_index.get(x, 0))
        if len(sorted_missing) <= 10:
            for m in sorted_missing:
                warnings.append(f"Item '{m}' has no entry in internal.json")
        else:
            warnings.append(
                f"{len(sorted_missing)} items have no entry in internal.json "
                f"(first 5: {', '.join(sorted_missing[:5])})"
            )

    # --- Conservative default check ---
    # Each item should depend on all items before it (conservative assumption).
    # Missing dependencies from the conservative set are warnings, not errors,
    # since the issue says overrides should be intentional.
    override_count = 0
    for idx, item_id in enumerate(item_order):
        if item_id not in deps:
            continue
        dep_set = set(deps[item_id])
        preceding = set(item_order[:idx])
        missing_from_conservative = preceding - dep_set
        if missing_from_conservative:
            override_count += len(missing_from_conservative)

    if override_count > 0:
        warnings.append(
            f"Conservative default: {override_count} dependencies removed from "
            f"the 'everything before me' default across all items "
            f"(this is expected if dependencies have been intentionally trimmed)"
        )

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

    total_deps = sum(len(v) for v in deps.values() if isinstance(v, list))
    print(f"\nDependency entries: {len(deps)}")
    print(f"Total dependency edges: {total_deps}")
    print(f"Items in items.json: {len(item_order)}")
    print("VALIDATION PASSED")
    return 0


if __name__ == "__main__":
    deps_path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEPS_PATH
    items_path = Path(sys.argv[2]) if len(sys.argv) > 2 else ITEMS_PATH
    sys.exit(validate(deps_path, items_path))
