# Provenance and version policy

First edition assembled **20 October 2026** by OpenAI Codex, at the repository owner's request, from the preceding research on the dissertation question. The owner requested a complete paper, a repository-contained entry and supplemental proved consequences. The arguments and prose were produced by AI systems under that direction; the owner is not assigned mathematical authorship by this record.

The main paper is a fresh, full exposition of the effective selection and arithmetic reflection reduction. The supplement expands related consequences with explicit assumptions and proofs. All local definitions and proof dependencies needed to read the entry are included. There are no dependencies on private working notes or on directories outside this repository.

The source location, quantifier order, canonical semantics and published arithmetic theorem were checked against the primary passages listed in [SOURCE-CHECKS.md](SOURCE-CHECKS.md). Codex also checked the dependency chain in [PROOF-GUIDE.md](PROOF-GUIDE.md). These checks are not independent mathematical review, and no independent human review is recorded. The separate repository Lean proofs of Questions 3-1-1 through 3-1-3 do not formalize this result. Novelty and priority have not been established.

The arithmetic non-descent theorem is Pakhomov–Walsh's. Alexander supplies the source question and the canonical modal framework; the paper credits Carlson's preceding work. Standard arithmetic inputs are distinguished from the local reduction. Source papers are linked rather than redistributed. The initial assembly did not submit the work or contact the source authors. The owner subsequently authorized publication of this entry to this GitHub repository; its review status is unchanged.

## One canonical text per paper

- `successor-knowers-3-2-1.md` is the canonical main paper.
- `supplemental/additional-results.md` is the canonical supplemental paper.
- The TeX and PDF files are generated from those sources by `build_pdf.py`.
- `pdf-build-report.json` records hashes and document checks.

The exposition uses an introductory dependency narrative, a concrete example before the general selection algorithm, definitions near their use, point-of-use source credit and explicit proof endings. These choices respond to the earlier dissertation-paper rewrite review. No mathematical-expression preservation claim is made relative to previous research sketches. Future substantive changes should update this record and the proof guide, then rebuild both formats from the canonical sources.

## 21 October 2026: Computer Modern typesetting

At the owner's request, the main paper and supplement now use Computer Modern
instead of the original DejaVu font selection. The canonical Markdown sources
are byte-for-byte unchanged, and the generated TeX from `\begin{document}`
onward is identical to the previous edition. The changed font metrics produce
12 main-paper pages and 5 supplemental pages. Both PDFs retain every proof
ending; the build report records embedded fonts and document diagnostics.
