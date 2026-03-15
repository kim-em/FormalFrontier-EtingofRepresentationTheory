#!/usr/bin/env python3
"""Extract chapter and section boundaries from transcribed page files.

Scans pages/*.md for chapter and section headings, producing a structured
chapter_map.json. Re-runnable as new pages are transcribed.
"""

import json
import os
import re
import sys
from pathlib import Path


def parse_page_id(filename: str) -> str:
    """Return the page identifier (e.g. '4', 'frontmatter-3')."""
    return filename.removesuffix(".md")


def page_sort_key(page_id: str):
    """Sort key: frontmatter pages first (by number), then numeric pages."""
    if page_id.startswith("frontmatter-"):
        return (0, int(page_id.split("-")[1]))
    try:
        return (1, int(page_id))
    except ValueError:
        return (2, 0)


def find_headings(pages_dir: Path):
    """Scan all page files for chapter (#) and section (##) headings."""
    headings = []  # (page_id, line_num, level, text)

    for f in sorted(pages_dir.glob("*.md")):
        if f.name == "CONVENTIONS.md":
            continue
        page_id = parse_page_id(f.name)
        for i, line in enumerate(f.read_text().splitlines(), start=1):
            m = re.match(r"^(#{1,2})\s+(.+)$", line)
            if m:
                level = len(m.group(1))
                text = m.group(2).strip()
                headings.append((page_id, i, level, text))

    return headings


# Chapter heading patterns from the book:
#   "Chapter N: Title", "Chapter N. Title", "Chapter N" (no title on same line)
# Also standalone titles that serve as chapter subtitles (e.g. "# General results...")
CHAPTER_RE = re.compile(
    r"^Chapter\s+(\d+)(?:\s*[:.]\s*(.+))?$"
)

# Section heading patterns: "N.M. Title" or "N. Title" (for chapter-level ## repeats)
SECTION_RE = re.compile(
    r"^(\d+)\.(\d+)\.\s+(.+)$"
)


def build_chapter_map(pages_dir: Path):
    """Build the chapter map structure from page headings."""
    headings = find_headings(pages_dir)

    # Identify all page files present
    all_pages = sorted(
        [parse_page_id(f.name) for f in pages_dir.glob("*.md") if f.name != "CONVENTIONS.md"],
        key=page_sort_key,
    )

    frontmatter_pages = [p for p in all_pages if p.startswith("frontmatter-")]
    content_pages = [p for p in all_pages if not p.startswith("frontmatter-")]

    # Expected content pages (1-227)
    expected_pages = set(str(i) for i in range(1, 228))
    missing_pages = sorted(expected_pages - set(content_pages), key=lambda x: int(x))

    # Build chapters from headings
    chapters = []
    current_chapter = None

    # Known chapter info from TOC (frontmatter) for titles not on the Chapter line
    chapter_titles = {
        1: "Introduction",
        2: "Basic notions of representation theory",
        3: "General results of representation theory",
        4: "Representations of finite groups: Basic results",
        5: "Representations of finite groups: Further results",
        6: "Quiver representations",
        7: "Introduction to categories",
        8: "Homological algebra",
        9: "Structure of finite dimensional algebras",
    }

    # Known chapter start pages from TOC
    chapter_start_pages = {
        1: "1", 2: "5", 3: "43", 4: "61", 5: "93",
        6: "149", 7: "181", 8: "205", 9: "213",
    }

    # Known end pages (page before next chapter starts, or last content page)
    chapter_end_pages = {
        1: "4", 2: "42", 3: "60", 4: "92", 5: "148",
        6: "180", 7: "204", 8: "212", 9: "220",
    }

    # Backmatter starts at page 221
    backmatter_entries = []

    # Sections known from the table of contents (for pages not yet transcribed)
    toc_sections = {
        (5, 11): ("Examples", "112"),
        (5, 12): ("Representations of $S_n$", "112"),
        (5, 13): ("Proof of the classification theorem for representations of $S_n$", "114"),
        (5, 14): ("Induced representations for $S_n$", "116"),
        (5, 15): ("The Frobenius character formula", "118"),
        (5, 16): ("Problems", "120"),
    }

    # Collect sections from headings
    chapter_sections = {i: [] for i in range(1, 10)}

    for page_id, line_num, level, text in headings:
        if page_id.startswith("frontmatter"):
            continue

        # Check for section headings (## N.M. Title)
        if level == 2:
            sm = SECTION_RE.match(text)
            if sm:
                chap_num = int(sm.group(1))
                sec_num = int(sm.group(2))
                sec_title = sm.group(3)
                sec_id = f"{chap_num}.{sec_num}"
                if chap_num in chapter_sections:
                    # Avoid duplicates (sections can repeat across page boundaries)
                    existing_ids = [s["id"] for s in chapter_sections[chap_num]]
                    if sec_id not in existing_ids:
                        chapter_sections[chap_num].append({
                            "id": sec_id,
                            "title": sec_title,
                            "start_page": page_id,
                        })

    # Fill in sections from TOC for missing pages
    for (chap_num, sec_num), (title, start_page) in toc_sections.items():
        sec_id = f"{chap_num}.{sec_num}"
        if chap_num in chapter_sections:
            existing_ids = [s["id"] for s in chapter_sections[chap_num]]
            if sec_id not in existing_ids:
                chapter_sections[chap_num].append({
                    "id": sec_id,
                    "title": title,
                    "start_page": start_page,
                    "source": "toc",
                })

    # Build chapter entries
    for chap_num in range(1, 10):
        chap = {
            "id": f"Chapter{chap_num}",
            "number": chap_num,
            "title": chapter_titles[chap_num],
            "start_page": chapter_start_pages[chap_num],
            "end_page": chapter_end_pages[chap_num],
            "sections": sorted(
                chapter_sections[chap_num],
                key=lambda s: [int(x) for x in s["id"].split(".")],
            ),
        }

        # Note missing pages within this chapter's range
        start = int(chap["start_page"])
        end = int(chap["end_page"])
        chap_missing = [p for p in missing_pages if start <= int(p) <= end]
        if chap_missing:
            chap["missing_pages"] = chap_missing

        chapters.append(chap)

    # Backmatter
    backmatter_headings = []
    for page_id, line_num, level, text in headings:
        if page_id.startswith("frontmatter"):
            continue
        try:
            pnum = int(page_id)
        except ValueError:
            continue
        if pnum >= 221 and level == 1:
            backmatter_headings.append({
                "title": text,
                "start_page": page_id,
            })

    result = {
        "book": "Introduction to Representation Theory",
        "authors": ["Pavel Etingof", "Oleg Golberg", "Sebastian Hensel",
                     "Tiankai Liu", "Alex Schwendner", "Dmitry Vaintrob",
                     "Elena Yudovina"],
        "total_content_pages": 227,
        "frontmatter": {
            "start_page": "frontmatter-1",
            "end_page": "frontmatter-8",
            "page_count": len(frontmatter_pages),
        },
        "chapters": chapters,
        "backmatter": {
            "start_page": "221",
            "end_page": "227",
            "entries": backmatter_headings,
        },
        "missing_pages": missing_pages,
        "transcribed_count": len(all_pages),
        "transcribed_percentage": round(len(all_pages) / (227 + 8) * 100, 1),
    }

    return result


def main():
    # Determine pages directory
    script_dir = Path(__file__).resolve().parent
    repo_dir = script_dir.parent
    pages_dir = repo_dir / "pages"

    if not pages_dir.is_dir():
        print(f"Error: pages directory not found at {pages_dir}", file=sys.stderr)
        sys.exit(1)

    chapter_map = build_chapter_map(pages_dir)

    output_path = pages_dir / "chapter_map.json"
    with open(output_path, "w") as f:
        json.dump(chapter_map, f, indent=2)
        f.write("\n")

    print(f"Wrote {output_path}")
    print(f"Found {len(chapter_map['chapters'])} chapters")
    total_sections = sum(len(c["sections"]) for c in chapter_map["chapters"])
    print(f"Found {total_sections} sections")
    if chapter_map["missing_pages"]:
        print(f"Missing pages: {', '.join(chapter_map['missing_pages'])}")
    print(f"Transcribed: {chapter_map['transcribed_count']}/{227 + 8} "
          f"({chapter_map['transcribed_percentage']}%)")


if __name__ == "__main__":
    main()
