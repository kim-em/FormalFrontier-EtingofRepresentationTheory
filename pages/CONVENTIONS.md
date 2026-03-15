# Transcription Conventions

Book: *Introduction to Representation Theory* by Pavel Etingof et al.

## Page Naming

Each transcription file is named by its **logical (printed) page number**, matching the files in `pdf/pages/`. For example, `pages/31.md` corresponds to `pdf/pages/31.pdf`. Frontmatter pages use the pattern `frontmatter-N.md`.

Blank pages in the PDF get an empty `.md` file (e.g., page 42 is blank).

## Inline Math

Use `$...$` for inline math. Examples:
- `$V \otimes W$`
- `$\mathfrak{sl}(2)$`
- `$\chi_V(g) = 0$`

## Display Math

Use `$$...$$` on separate lines for display math:

```
$$
(v_1 + v_2) \otimes w - v_1 \otimes w - v_2 \otimes w,
$$
```

Multiple consecutive display equations each get their own `$$...$$` block. Do not use `\begin{align}` or other LaTeX environments.

## Section Headers

Use `##` (h2) for section and subsection headings, preserving the book's numbering:

```
## 2.11. Tensor products
## 3.8. The Krull-Schmidt theorem
## 5. Representations of finite groups: Further results
```

## Theorem Environments

Use bold for the label and number, followed by the statement in italics (for theorems, lemmas, propositions, corollaries). Definitions use bold for the label and the defined term.

**Theorems, Lemmas, Propositions, Corollaries:**
```
**Theorem 5.4.3** (Burnside). *Any group $G$ of order $p^a q^b$...*
**Lemma 3.1.6.** *There exists a subset $J \subseteq I$...*
**Corollary 3.5.5.** *$\sum_i (\dim V_i)^2 \leq \dim A$...*
```

**Definitions:**
```
**Definition 2.11.1.** The **tensor product** $V \otimes W$...
```

**Exercises and Problems:**
```
**Exercise 2.11.2.** Show that $V \otimes W$...
**Problem 2.16.1.** Let $\mathfrak{g}$ be...
```

**Remarks and Examples:**
```
**Remark 2.9.3.** Ado's theorem says...
**Example 3.3.1.** ...
```

## Proofs

Start with `**Proof.**` and end with `$\square$`:

```
**Proof.** Let $V$ be an irreducible representation... $\square$
```

## Citations

Use bold for reference numbers: `[**47**, p. 310]`, `[**11**, pp. 88-89]`.

## Tables

Use standard markdown tables with `|` delimiters and `---` separators. Math is allowed in cells:

```
| $S_4$ | Id | (12) | (12)(34) | (123) | (1234) |
|---|---|---|---|---|---|
| $\mathbb{C}_+$ | 1 | 1 | 1 | 1 | 1 |
```

## Matrices

Use LaTeX matrix environments inside display math:

```
$$e = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$$
```

## Historical/Narrative Text

Historical interludes and narrative passages are transcribed as plain paragraphs with no special markup beyond inline math and citations.

## Page Continuity

Pages typically begin mid-sentence or mid-paragraph, continuing from the previous page. Do not add artificial breaks or headers at page boundaries — just continue the text naturally.
