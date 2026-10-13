# Archived 3 October 2026 proof paper

> **Archived 13 October 2026.** This is the earlier 20-page paper. Read the
> [current revised proof](../../README.md) for the 8 October finite-guard revision.
> The manuscript, PDF and build records are preserved unchanged.

> **Placement, 3 October 2026.** This paper was moved here from the owner's working directory.
> The manuscript (`paper.tex`, `paper.pdf`) is unchanged; only relative paths in this README,
> `PROVENANCE.md` and `source-map.json` were updated for the new location.
> Links that begin with `../../../../` (the hand notes, audits, dissertation text, style source and
> historical Lean metadata) point into that local working tree. They are not part of this
> repository and will not resolve on GitHub.

> **13 October 2026:** this folder retains the earlier 3 October paper. The
> [revised finite-guard proof PDF](../../REVISED-3-1-3-PROOF.pdf),
> [current Lean project](../../../alexander-dissertation-lean/README.md) and
> [detailed comparison](../../../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
> are now included in this repository.

Read **[paper.pdf](paper.pdf)**. The editable, canonical manuscript is
[paper.tex](paper.tex).

This is a standalone 20-page presentation of the complete proposed affirmative
hand proof for Alexander's Question 3-1-3, for every recursively enumerable
well-founded hierarchy and unrestricted modal formulas. Questions 3-1-1 and
3-1-2 follow as corollaries. The paper includes the fixed common theory,
recorded auxiliary syntax, the complete generator rules, finite-support
collapse, fixed-label transport, fully sound reconstruction, core and
whole-ideal genericity, actual-family soundness, known schemas, the original
language reduct, and the uniform typed ordinal extraction from Wilken.

The layout and explanatory approach follow
[the biological-unavoidability submission paper](../../../../biological-unavoidability-submission/paper.tex):
11-point Latin Modern, one-inch margins, spaced paragraphs, a theorem near the
beginning, displayed constructions, and prose explanations followed by proofs.
The manuscript is newly written here; it does not use this repository's
`preamble.tex` or its document template.

## Proof and verification status

The source hand proof and its recorded modal and ordinal checks are complete
at the **proposed hand-proof** level. The paper incorporates the final typed
ordinal-closure verification, rather than leaving the ordinal package as an
additional hypothesis. No external peer review or literature priority is claimed.

The [current Lean formalization](../../../alexander-dissertation-lean/README.md) has
unconditional proofs of the three independent comparator targets. It follows
the revised finite-guard construction with a Carlson ordinal package; the
[comparison](../../../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
records its scope and differences from the prose. This earlier paper's
[source map](source-map.json) retains its original draft correspondence as a
historical snapshot and adds links to the current embedded formalization.

## Files and reproduction

- `paper.tex`, `paper.pdf`: canonical source and compiled manuscript.
- [PROVENANCE.md](PROVENANCE.md): mathematical sources, style source and contribution scope.
- [source-map.json](source-map.json): manuscript claims and sections mapped to
  the original hand notes, primary sources and separate formalization metadata.
- [build_documents.py](build_documents.py): reproducible document build using
  cached Tectonic resources by default.
- `paper.log`, `build-output.txt`, [build-report.json](build-report.json):
  final build diagnostics, PDF/source hashes and cross-reference checks.

From this directory, with Tectonic and Poppler's `pdfinfo`, `pdftotext` and
`pdffonts` installed:

```sh
python3 build_documents.py
```

Use `--allow-downloads` only if Tectonic resources are missing and downloads
are wanted. The recorded build used only cached resources. Standard XeLaTeX
or PDFLaTeX can also compile `paper.tex` with its listed packages; those engines
were not separately tested here.

The final build resolved every reference and citation, had no overfull boxes
or missing glyphs, and embedded all PDF fonts. Representative rendered pages
(opening, theory construction, generator table and conclusion) were visually
inspected. These are document checks, not a new mathematical audit or Lean
certification. One minor underfull paragraph in the bibliography is reported
in the build metadata.
