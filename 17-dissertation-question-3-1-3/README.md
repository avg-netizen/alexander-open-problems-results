# Dissertation Question 3-1-3 — revised proof

Read the **[33-page standalone proof PDF](REVISED-3-1-3-PROOF.pdf)**:
*Knowing machines with mutual truthfulness and mechanicalness*, dated
13 October 2026. The [Markdown manuscript](REVISED-3-1-3-PROOF.md) introduces
the problem, background assumptions, notation and proof method before the
formal construction. Its abstract states the result and method independently
of the earlier papers.

The [Lean project](../alexander-dissertation-lean/README.md) includes the completed
unconditional 3-1-1, 3-1-2 and 3-1-3 comparator proofs and the additional paper
conclusions. [Public CI passed](https://github.com/avg-netizen/alexander-open-problems-results/actions/runs/38453360717)
compilation and all 107 axiom reports. The
[paper-to-Lean comparison](../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
records the precise correspondence, construction differences and remaining
scope qualifications; the Lean proof uses the completed Carlson ordinal package.
That audit concerns the archived 8 October parent. This editorial edition
preserves its main theorem, all 18 numbered lemma statements, all 104 displayed
formulas and the main proof's mathematical expressions. The
[editorial review record](standalone-editorial-review.json) binds those checks
to the exact current manuscript and PDF build.

## Earlier editions and construction history

The supplied [8 October finite-guard edition](archive/2026-10-08/README.md)
is archived with its original 31-page PDF, manuscript and typesetting bundle.
The [construction comparison](CONSTRUCTION-COMPARISON.md) preserves its
discussion of the earlier approach and the formalization handoff. That history
is separate from the current proof's exposition.

The 3 October 2026 paper is retained in
[archive/2026-10-03/](archive/2026-10-03/README.md), with its
[20-page PDF](archive/2026-10-03/paper.pdf), LaTeX manuscript, source map,
provenance and build records. Its manuscript and PDF are unchanged. The archive's
proof-status statements describe that earlier snapshot.

## Files and reproduction

- [REVISED-3-1-3-PROOF.md](REVISED-3-1-3-PROOF.md): current manuscript.
- [REVISED-3-1-3-PROOF.pdf](REVISED-3-1-3-PROOF.pdf): 33-page typeset version with 68 section bookmarks.
- [REVISED-3-1-3-PROOF.tex](REVISED-3-1-3-PROOF.tex): generated LaTeX.
- [build_pdf.py](build_pdf.py), [pdf-format.lua](pdf-format.lua) and
  [pdf-header.tex](pdf-header.tex): reproducible typesetting files.
- [pdf-build-report.json](pdf-build-report.json): recorded PDF checks and hashes.
- [PROVENANCE.md](PROVENANCE.md) and [source-map.json](source-map.json): source identity and placement records.
- [standalone-editorial-review.json](standalone-editorial-review.json): mathematical-expression preservation and document checks.

From this directory, with Pandoc, Tectonic and Poppler installed:

```sh
python3 build_pdf.py
```

The default uses cached TeX resources; `--allow-downloads` permits missing
resources to be downloaded. The original 8 October
[paper bundle inside the Lean project](../alexander-dissertation-lean/paper/README.md)
remains unchanged, alongside the proofs and their hash-bound comparison.
No independent human mathematical review has been recorded.
