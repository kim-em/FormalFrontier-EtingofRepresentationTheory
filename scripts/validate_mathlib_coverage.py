#!/usr/bin/env python3
"""Validate mathlib-coverage-external.json against dependencies/external.json.

Checks:
  - Every external dependency has a corresponding coverage entry
  - Match quality is a valid enum value (exact, partial, missing)
  - Mathlib names are non-empty strings (when not missing)
  - Required fields present in each entry

Prints summary statistics and exits non-zero on validation failure.
"""

import json
import sys
from pathlib import Path


VALID_MATCH_QUALITIES = {"exact", "partial", "missing"}
REQUIRED_FIELDS = {"description", "category", "mathlib_names", "match_quality", "notes"}


def load_json(path: Path) -> list:
    with open(path) as f:
        return json.load(f)


def validate():
    repo_root = Path(__file__).resolve().parent.parent
    external_path = repo_root / "dependencies" / "external.json"
    coverage_path = repo_root / "research" / "mathlib-coverage-external.json"

    if not external_path.exists():
        print(f"ERROR: {external_path} not found")
        return False
    if not coverage_path.exists():
        print(f"ERROR: {coverage_path} not found")
        return False

    external = load_json(external_path)
    coverage = load_json(coverage_path)

    errors = []
    warnings = []

    # Build lookup by description
    coverage_by_desc = {}
    for i, entry in enumerate(coverage):
        # Check required fields
        missing_fields = REQUIRED_FIELDS - set(entry.keys())
        if missing_fields:
            errors.append(f"Coverage entry {i}: missing fields {missing_fields}")
            continue

        desc = entry["description"]
        if desc in coverage_by_desc:
            errors.append(f"Duplicate coverage entry for: {desc}")
        coverage_by_desc[desc] = entry

        # Validate match_quality
        mq = entry["match_quality"]
        if mq not in VALID_MATCH_QUALITIES:
            errors.append(f"Entry '{desc}': invalid match_quality '{mq}' "
                          f"(must be one of {VALID_MATCH_QUALITIES})")

        # Validate mathlib_names
        names = entry["mathlib_names"]
        if not isinstance(names, list):
            errors.append(f"Entry '{desc}': mathlib_names must be a list")
        elif mq != "missing":
            if len(names) == 0:
                warnings.append(f"Entry '{desc}': match_quality is '{mq}' but "
                                f"mathlib_names is empty")
            for name in names:
                if not isinstance(name, str) or len(name.strip()) == 0:
                    errors.append(f"Entry '{desc}': mathlib_names contains "
                                  f"empty or non-string value: {name!r}")

        # Validate notes
        if not isinstance(entry["notes"], str) or len(entry["notes"].strip()) == 0:
            warnings.append(f"Entry '{desc}': notes is empty")

    # Check completeness: every external dep must have a coverage entry
    for ext_dep in external:
        ext_desc = ext_dep["description"]
        if ext_desc not in coverage_by_desc:
            errors.append(f"Missing coverage for external dep: {ext_desc}")

    # Summary statistics
    exact_count = sum(1 for e in coverage if e.get("match_quality") == "exact")
    partial_count = sum(1 for e in coverage if e.get("match_quality") == "partial")
    missing_count = sum(1 for e in coverage if e.get("match_quality") == "missing")
    total = len(coverage)

    print(f"=== Mathlib Coverage Validation ===")
    print(f"External dependencies: {len(external)}")
    print(f"Coverage entries:      {total}")
    print()
    print(f"  exact:   {exact_count:3d} ({100*exact_count/total:.0f}%)")
    print(f"  partial: {partial_count:3d} ({100*partial_count/total:.0f}%)")
    print(f"  missing: {missing_count:3d} ({100*missing_count/total:.0f}%)")
    print()

    if warnings:
        print(f"Warnings ({len(warnings)}):")
        for w in warnings:
            print(f"  WARN: {w}")
        print()

    if errors:
        print(f"Errors ({len(errors)}):")
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        print("VALIDATION FAILED")
        return False

    print("VALIDATION PASSED")
    return True


if __name__ == "__main__":
    success = validate()
    sys.exit(0 if success else 1)
