# Revised paper and formalization comparison

[REVISED-3-1-3-PROOF.md](REVISED-3-1-3-PROOF.md) is the supplied revised paper,
*An affirmative 3-1-3 proof using finite guards*, dated 8 October 2026.
It was copied without alteration from the vault's
`projects/inverse/samuel-allen-alexander/review-finite-guards-2026-10-09/REVISED-3-1-3-PROOF.md`.
That file agrees byte for byte with the archived 9 October upload.

The [31-page PDF](REVISED-3-1-3-PROOF.pdf) typesets that same text, with
mathematical notation and section bookmarks. The [generated LaTeX](REVISED-3-1-3-PROOF.tex)
and [build record](pdf-build-report.json) accompany it. Rebuild with
`python3 paper/build_pdf.py` from the repository root (Pandoc and Tectonic required).
The default uses cached TeX resources; `--allow-downloads` permits missing resources
to be downloaded. The build record reports no missing symbols, unresolved
references or overflowing text.

SHA-256: `bc012600043e35b9a415311614b31fbc9e2b61847af044fe1a3452f0a185c16a`.
The file has 1,270 lines and 93,123 UTF-8 bytes. This is the finite-guard
revision, distinct from the earlier 3 October TeX paper in the results repo.

[The detailed comparison](LEAN-COMPARISON-2026-10-13.md) records the exact
coverage and the differences. The checked main result uses the constructed
Carlson covering package. Identification with the paper's pure elementary
ordinal structure is outside that result's scope. The new
[`CompileRevisedPaper.lean`](../CompileRevisedPaper.lean) also checks the stronger
parameter and transitive-inheritance conclusions for the same witness.
