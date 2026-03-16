#!/usr/bin/env python3
"""Generate leanblueprint LaTeX content from items.json and dependency data.

Reads progress/items.json, dependencies/internal.json, and dependencies/external.json,
then generates blueprint/src/content.tex with all chapter content inline.

Each item becomes a leanblueprint environment with \\label and \\uses annotations.
"""

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
INTERNAL_DEPS_PATH = REPO_ROOT / "dependencies" / "internal.json"
EXTERNAL_DEPS_PATH = REPO_ROOT / "dependencies" / "external.json"
BLOBS_DIR = REPO_ROOT / "blobs"
CONTENT_TEX = REPO_ROOT / "blueprint" / "src" / "content.tex"

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

# Map item types to leanblueprint LaTeX environments.
# Types without a dedicated theorem-like environment use 'remark'.
TYPE_TO_ENV = {
    "theorem": "theorem",
    "proposition": "proposition",
    "lemma": "lemma",
    "corollary": "corollary",
    "definition": "definition",
    "example": "example",
    "remark": "remark",
    # Non-theorem types all map to remark
    "discussion": "remark",
    "introduction": "remark",
    "notation": "remark",
    "preface": "remark",
    "exercise": "remark",
    "bibliography": "remark",
}

# Chapter display names
CHAPTER_TITLES = {
    "Frontmatter": "Front Matter",
    "Chapter1": "Introduction",
    "Chapter2": "Basic Notions of Representation Theory",
    "Chapter3": "General Results of Representation Theory",
    "Chapter4": "Representations of Finite Groups: Basic Results",
    "Chapter5": "Representations of Finite Groups: Further Results",
    "Chapter6": "Quiver Representations",
    "Chapter7": "Introduction to Categories",
    "Chapter8": "Homological Algebra",
    "Chapter9": "Structure of Finite Dimensional Algebras",
    "Backmatter": "Back Matter",
}


def sanitize_label(item_id: str) -> str:
    """Convert item ID like 'Chapter2/Theorem2.1.1' to a valid LaTeX label.

    Labels use colons as separators: 'Chapter2:Theorem2.1.1'
    """
    return item_id.replace("/", ":")


def markdown_to_latex(text: str) -> str:
    """Convert markdown blob text to LaTeX.

    Blobs are markdown with embedded LaTeX math ($...$, $$...$$).
    We convert markdown formatting to LaTeX equivalents while preserving math.
    """
    # First, protect math blocks by replacing them with placeholders
    math_blocks = []

    def save_math(m):
        idx = len(math_blocks)
        math_blocks.append(m.group(0))
        return f"\x00MATH{idx}\x00"

    # Save display math first ($$...$$), then inline math ($...$)
    text = re.sub(r'\$\$.*?\$\$', save_math, text, flags=re.DOTALL)
    text = re.sub(r'\$[^\$]+?\$', save_math, text)

    # Now convert markdown to LaTeX in the non-math parts

    # Markdown headers → LaTeX section commands (unnumbered)
    # Must come BEFORE escaping # so headers are recognized
    text = re.sub(r'^####\s+(.+)$', r'\\paragraph*{\1}', text, flags=re.MULTILINE)
    text = re.sub(r'^###\s+(.+)$', r'\\subsubsection*{\1}', text, flags=re.MULTILINE)
    text = re.sub(r'^##\s+(.+)$', r'\\subsection*{\1}', text, flags=re.MULTILINE)
    text = re.sub(r'^#\s+(.+)$', r'\\section*{\1}', text, flags=re.MULTILINE)

    # Escape special LaTeX chars in text (not in math)
    text = text.replace('&', '\\&')
    text = text.replace('%', '\\%')
    # Only escape # that aren't part of \section etc. already
    text = re.sub(r'(?<!\\)#', r'\\#', text)

    # Markdown bold **text** → \textbf{text}
    text = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', text)

    # Markdown italic *text* → \textit{text}  (but not inside \textbf)
    text = re.sub(r'\*(.+?)\*', r'\\textit{\1}', text)

    # Markdown lists: lines starting with - or * (not math)
    # Convert blocks of list items to itemize environments
    def convert_lists(text):
        lines = text.split('\n')
        result = []
        in_list = False
        for line in lines:
            stripped = line.strip()
            is_item = bool(re.match(r'^[-*]\s+', stripped))
            if is_item and not in_list:
                result.append('\\begin{itemize}')
                in_list = True
            elif not is_item and in_list and stripped:
                result.append('\\end{itemize}')
                in_list = False
            elif not is_item and in_list and not stripped:
                # Blank line in list — keep going
                pass

            if is_item:
                item_text = re.sub(r'^[-*]\s+', '', stripped)
                result.append(f'\\item {item_text}')
            else:
                result.append(line)

        if in_list:
            result.append('\\end{itemize}')
        return '\n'.join(result)

    text = convert_lists(text)

    # Markdown footnotes [^N] → \footnote{...} — just strip the markers
    text = re.sub(r'\[\^[^\]]+\]', '', text)

    # Markdown links [text](url) → \href{url}{text}
    text = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', r'\\href{\2}{\1}', text)

    # Restore math blocks
    for idx, block in enumerate(math_blocks):
        text = text.replace(f"\x00MATH{idx}\x00", block)

    return text


def blob_to_latex_body(item_id: str) -> str:
    """Read the blob file for an item and convert to LaTeX body text."""
    chapter, name = item_id.split("/", 1)
    blob_path = BLOBS_DIR / chapter / f"{name}.md"

    if not blob_path.exists():
        return f"% Blob not found: {item_id}"

    text = blob_path.read_text(encoding="utf-8").strip()
    if not text:
        return "% Empty blob"

    # Strip the leading theorem/definition header line if present
    # e.g., "**Theorem 2.1.1.** *statement...*"
    # becomes just "*statement...*"
    text = re.sub(r'^\*\*(Theorem|Proposition|Lemma|Corollary|Definition|Example|Remark|Exercise|Problem)\s+[\d.]+\.?\*\*\s*', '', text)

    return markdown_to_latex(text)


def generate_chapter_tex(
    chapter: str,
    items: list[dict],
    internal_deps: dict,
) -> str:
    """Generate LaTeX content for one chapter."""
    lines = []
    title = CHAPTER_TITLES.get(chapter, chapter)
    lines.append(f"\\chapter{{{title}}}")
    lines.append("")

    for item in items:
        item_id = item["id"]
        item_type = item["type"]
        item_title = item["title"]
        env = TYPE_TO_ENV.get(item_type, "remark")
        label = sanitize_label(item_id)

        # Get internal dependencies for this item
        deps = internal_deps.get(item_id, [])
        dep_labels = [sanitize_label(d) for d in deps]

        # Build the environment
        lines.append(f"\\begin{{{env}}}[{item_title}]")
        lines.append(f"\\label{{{label}}}")
        if dep_labels:
            lines.append(f"\\uses{{{', '.join(dep_labels)}}}")

        # Add blob content as body
        body = blob_to_latex_body(item_id)
        lines.append(body)
        lines.append(f"\\end{{{env}}}")
        lines.append("")

    return "\n".join(lines)


def generate_content_tex(
    chapters_with_items: list[str],
    chapter_items: dict[str, list[dict]],
    internal_deps: dict,
) -> str:
    """Generate content.tex with all chapter content inline.

    plasTeX has difficulty with \\input of subdirectory files,
    so we put everything directly in content.tex.
    """
    lines = [
        "% Auto-generated by scripts/generate_blueprint.py",
        "% Do not edit manually.",
        "",
    ]
    for chapter in chapters_with_items:
        tex = generate_chapter_tex(chapter, chapter_items[chapter], internal_deps)
        lines.append(tex)
    lines.append("")
    return "\n".join(lines)


def main():
    # Load data
    with open(ITEMS_PATH) as f:
        items = json.load(f)
    with open(INTERNAL_DEPS_PATH) as f:
        internal_deps = json.load(f)
    with open(EXTERNAL_DEPS_PATH) as f:
        external_deps = json.load(f)

    print(f"Loaded {len(items)} items, {len(internal_deps)} internal dep entries, "
          f"{len(external_deps)} external dep entries")

    # Group items by chapter
    chapter_items: dict[str, list[dict]] = {ch: [] for ch in CHAPTER_ORDER}
    for item in items:
        chapter = item["id"].split("/")[0]
        if chapter in chapter_items:
            chapter_items[chapter].append(item)
        else:
            print(f"Warning: unknown chapter '{chapter}' for item {item['id']}")
            chapter_items.setdefault(chapter, []).append(item)

    # Determine which chapters have items
    chapters_with_items = []
    for chapter in CHAPTER_ORDER:
        chapter_list = chapter_items[chapter]
        if not chapter_list:
            print(f"Skipping empty chapter: {chapter}")
            continue
        chapters_with_items.append(chapter)
        print(f"  {chapter}: {len(chapter_list)} items")

    # Generate content.tex with all content inline
    content = generate_content_tex(chapters_with_items, chapter_items, internal_deps)
    CONTENT_TEX.write_text(content, encoding="utf-8")
    print(f"\nUpdated {CONTENT_TEX}")
    print(f"Generated {len(chapters_with_items)} chapters with {len(items)} total items")


if __name__ == "__main__":
    main()
