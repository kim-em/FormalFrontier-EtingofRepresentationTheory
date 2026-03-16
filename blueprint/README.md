# Blueprint

This directory contains the [leanblueprint](https://github.com/PatrickMassot/leanblueprint) sources for tracking the formalization of *Introduction to Representation Theory* by Etingof et al.

## Setup

Install leanblueprint and its dependencies:

```bash
pip install leanblueprint
```

Note: `pygraphviz` requires graphviz system headers. On macOS:

```bash
brew install graphviz
pip install pygraphviz
pip install leanblueprint
```

## Building the web version

From the `lean/` directory:

```bash
cd blueprint && mkdir -p web && cd src && plastex -c plastex.cfg web.tex
```

Or if leanblueprint CLI works with your project layout:

```bash
leanblueprint web
```

The output will be in `blueprint/web/`.

## Directory structure

- `src/` — LaTeX source files
  - `content.tex` — Main blueprint content (theorems, definitions, dependency annotations)
  - `web.tex` — Entry point for the web version
  - `print.tex` — Entry point for the PDF version
  - `macros/` — Shared and version-specific LaTeX macros
  - `plastex.cfg` — plasTeX configuration
- `web/` — Generated HTML output (not committed)
- `print/` — Generated PDF output (not committed)
