# Full 3-1-3 — explanatory proof paper

> **Placement, 3 October 2026.** This paper was moved here from the owner's working directory.
> The manuscript (`paper.tex`, `paper.pdf`) is unchanged; only relative paths in this README,
> `PROVENANCE.md` and `source-map.json` were updated for the new location.
> Links that begin with `../../` (the hand notes, audits, dissertation text, style source and
> Lean package) point into that local working tree. They are not part of this
> repository and will not resolve on GitHub.

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
[the biological-unavoidability submission paper](../../biological-unavoidability-submission/paper.tex):
11-point Latin Modern, one-inch margins, spaced paragraphs, a theorem near the
beginning, displayed constructions, and prose explanations followed by proofs.
The manuscript is newly written here; it does not use this repository's
`preamble.tex` or its document template.

## Proof and verification status

The source hand proof and its recorded modal and ordinal checks are complete
at the **proposed hand-proof** level. The paper incorporates the final typed
ordinal-closure verification, rather than leaving the ordinal package as an
additional hypothesis. No external peer review or literature priority is claimed.

The separate [Lean formalization](../../alexander-thesis-3-1-3-lean/README.md)
remains incomplete and uncompiled. This paper does not create a Lean completion
claim or change the status of that task. Its comparator challenge and
`formalization.yaml` remain in the Lean package. The links in
[source-map.json](source-map.json) indicate corresponding subjects and draft
targets, not completed formal proofs of the paper's lemmas.

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
