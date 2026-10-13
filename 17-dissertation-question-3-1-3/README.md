# Dissertation Question 3-1-3 — revised proof

Read the **[31-page revised proof PDF](REVISED-3-1-3-PROOF.pdf)**:
*An affirmative 3-1-3 proof using finite guards*, dated 8 October 2026.
The [Markdown manuscript](REVISED-3-1-3-PROOF.md) is the supplied revised paper,
preserved without editing. This is the current paper for note 17.

The [Lean project](../alexander-dissertation-lean/README.md) includes the completed
unconditional 3-1-1, 3-1-2 and 3-1-3 comparator proofs and the additional paper
conclusions. [Public CI passed](https://github.com/avg-netizen/alexander-open-problems-results/actions/runs/38453360717)
compilation and all 107 axiom reports. The
[paper-to-Lean comparison](../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
records the precise correspondence, construction differences and remaining
scope qualifications; the Lean proof uses the completed Carlson ordinal package.

## Earlier paper

The 3 October 2026 paper is retained in
[archive/2026-10-03/](archive/2026-10-03/README.md), with its
[20-page PDF](archive/2026-10-03/paper.pdf), LaTeX manuscript, source map,
provenance and build records. Its manuscript and PDF are unchanged. The archive's
proof-status statements describe that earlier snapshot.

## Files and reproduction

- [REVISED-3-1-3-PROOF.md](REVISED-3-1-3-PROOF.md): current manuscript.
- [REVISED-3-1-3-PROOF.pdf](REVISED-3-1-3-PROOF.pdf): 31-page typeset version with 66 section bookmarks.
- [REVISED-3-1-3-PROOF.tex](REVISED-3-1-3-PROOF.tex): generated LaTeX.
- [build_pdf.py](build_pdf.py), [pdf-format.lua](pdf-format.lua) and
  [pdf-header.tex](pdf-header.tex): reproducible typesetting files.
- [pdf-build-report.json](pdf-build-report.json): recorded PDF checks and hashes.
- [PROVENANCE.md](PROVENANCE.md) and [source-map.json](source-map.json): source identity and placement records.

From this directory, with Pandoc, Tectonic and Poppler installed:

```sh
python3 build_pdf.py
```

The default uses cached TeX resources; `--allow-downloads` permits missing
resources to be downloaded. All seven manuscript and typesetting files were
copied byte for byte from the
[paper bundle inside the Lean project](../alexander-dissertation-lean/paper/README.md).
That copy remains alongside the proofs so the imported project is self-contained.
No independent human mathematical review has been recorded.
