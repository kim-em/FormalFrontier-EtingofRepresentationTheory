#!/usr/bin/env python3
"""Generate .refs.md companion files for each blob item.

Reads research data from Phase 2 and produces blobs/<ItemID>.refs.md files
that formalization agents can consult when working on each item.

Usage:
    python3 scripts/generate_refs.py              # generate files
    python3 scripts/generate_refs.py --dry-run     # print what would be generated
"""

import argparse
import json
import os
import sys
from pathlib import Path


def load_json(path: str):
    with open(path) as f:
        return json.load(f)


def build_item_index(items: list[dict]) -> dict[str, dict]:
    """Map item ID to item metadata."""
    return {item["id"]: item for item in items}


def build_definition_coverage(defs_data: dict) -> dict[str, dict]:
    """Map item ID to Mathlib coverage info for definitions."""
    result = {}
    for entry in defs_data.get("definitions", []):
        item_id = entry.get("id")
        if item_id:
            result[item_id] = entry
    return result


def build_external_dep_map(ext_deps: list[dict]) -> dict[str, list[dict]]:
    """Map item ID to list of external dependencies it relies on."""
    result: dict[str, list[dict]] = {}
    for dep in ext_deps:
        for item_id in dep.get("items", []):
            if item_id not in result:
                result[item_id] = []
            result[item_id].append({
                "description": dep.get("description", ""),
                "category": dep.get("category", ""),
            })
    return result


def build_ext_coverage_map(ext_coverage: list[dict]) -> dict[str, dict]:
    """Map external dep description to its Mathlib coverage."""
    return {entry["description"]: entry for entry in ext_coverage}


def build_definition_gap_map(ext_sources: dict) -> dict[str, dict]:
    """Map item ID to external sources for definition gaps."""
    result = {}
    for entry in ext_sources.get("definition_gaps", []):
        item_id = entry.get("id")
        if item_id:
            result[item_id] = entry
    return result


def build_ext_dep_gap_map(ext_sources: dict) -> list[dict]:
    """Return list of external dep gap entries for prefix matching."""
    return ext_sources.get("external_dependency_gaps", [])


def find_ext_dep_gap(desc: str, ext_dep_gaps: list[dict]) -> dict | None:
    """Find matching gap entry using prefix matching.

    external-sources.json may use abbreviated descriptions (e.g. "Ext functors")
    while external.json uses expanded ones (e.g. "Ext functors: definition as...").
    Match if either is a prefix of the other.
    """
    for gap in ext_dep_gaps:
        gap_desc = gap.get("description", "")
        if desc == gap_desc or desc.startswith(gap_desc) or gap_desc.startswith(desc):
            return gap
    return None


def generate_refs_content(
    item_id: str,
    item: dict,
    def_coverage: dict[str, dict],
    ext_dep_map: dict[str, list[dict]],
    ext_coverage_map: dict[str, dict],
    def_gap_map: dict[str, dict],
    ext_dep_gaps: list[dict],
) -> str | None:
    """Generate .refs.md content for one item. Returns None if no references."""
    sections = []

    # 1. Mathlib coverage for definitions
    if item_id in def_coverage:
        cov = def_coverage[item_id]
        quality = cov.get("match_quality", "unknown")
        decls = cov.get("mathlib_declarations", [])
        notes = cov.get("notes", "")

        lines = [f"## Mathlib Coverage ({quality})"]
        if decls:
            lines.append("")
            for d in decls:
                lines.append(f"- `{d}`")
        if notes:
            lines.append("")
            lines.append(notes)
        sections.append("\n".join(lines))

    # 2. External sources for definition gaps
    if item_id in def_gap_map:
        gap = def_gap_map[item_id]
        sources = gap.get("sources", [])
        if sources:
            lines = ["## External Sources (definition gap)"]
            lines.append("")
            for src in sources:
                src_type = src.get("source_type", "unknown")
                ref = src.get("reference", "")
                relevance = src.get("relevance", "")
                lines.append(f"- **[{src_type}]** {ref}")
                if relevance:
                    lines.append(f"  {relevance}")
            sections.append("\n".join(lines))

    # 3. External dependencies this item relies on
    if item_id in ext_dep_map:
        deps = ext_dep_map[item_id]
        lines = ["## External Dependencies"]
        lines.append("")
        for dep in deps:
            desc = dep["description"]
            cat = dep["category"]
            lines.append(f"- **{desc}** ({cat})")

            # Add Mathlib names if available
            if desc in ext_coverage_map:
                cov = ext_coverage_map[desc]
                quality = cov.get("match_quality", "unknown")
                mathlib_names = cov.get("mathlib_names", [])
                if mathlib_names:
                    names_str = ", ".join(f"`{n}`" for n in mathlib_names)
                    lines.append(f"  Mathlib ({quality}): {names_str}")
                cov_notes = cov.get("notes", "")
                if cov_notes:
                    lines.append(f"  {cov_notes}")

            # Add external sources for gaps
            gap = find_ext_dep_gap(desc, ext_dep_gaps)
            if gap:
                gap_sources = gap.get("sources", [])
                for src in gap_sources:
                    src_type = src.get("source_type", "unknown")
                    ref = src.get("reference", "")
                    lines.append(f"  External source [{src_type}]: {ref}")

        sections.append("\n".join(lines))

    if not sections:
        return None

    header = f"# References: {item.get('title', item_id)}\n"
    return header + "\n" + "\n\n".join(sections) + "\n"


def blob_path(item_id: str) -> Path:
    """Convert item ID like 'Chapter2/Definition2.2.1' to blob path."""
    return Path("blobs") / (item_id + ".md")


def refs_path(item_id: str) -> Path:
    """Convert item ID to .refs.md path."""
    return Path("blobs") / (item_id + ".refs.md")


def main():
    parser = argparse.ArgumentParser(description="Generate .refs.md files")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print what would be generated without writing files")
    args = parser.parse_args()

    # Load all data
    items = load_json("progress/items.json")
    defs_data = load_json("research/mathlib-coverage-definitions.json")
    ext_coverage = load_json("research/mathlib-coverage-external.json")
    ext_sources = load_json("research/external-sources.json")
    ext_deps = load_json("dependencies/external.json")

    # Build lookup structures
    item_index = build_item_index(items)
    def_coverage = build_definition_coverage(defs_data)
    ext_dep_map = build_external_dep_map(ext_deps)
    ext_coverage_map = build_ext_coverage_map(ext_coverage)
    def_gap_map = build_definition_gap_map(ext_sources)
    ext_dep_gaps = build_ext_dep_gap_map(ext_sources)

    generated = 0
    skipped = 0
    errors = []

    for item in items:
        item_id = item["id"]

        # Verify blob exists
        bp = blob_path(item_id)
        if not bp.exists():
            errors.append(f"Blob not found: {bp}")
            continue

        content = generate_refs_content(
            item_id, item,
            def_coverage, ext_dep_map, ext_coverage_map,
            def_gap_map, ext_dep_gaps,
        )

        if content is None:
            skipped += 1
            continue

        rp = refs_path(item_id)
        if args.dry_run:
            print(f"Would write: {rp} ({len(content)} bytes)")
        else:
            rp.parent.mkdir(parents=True, exist_ok=True)
            rp.write_text(content)

        generated += 1

    print(f"\nSummary: {generated} refs files generated, {skipped} items with no references")
    if errors:
        print(f"Errors ({len(errors)}):")
        for e in errors:
            print(f"  {e}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
