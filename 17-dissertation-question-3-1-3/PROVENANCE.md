# Standalone proof provenance and editorial scope

The current manuscript is *Knowing machines with mutual truthfulness and
mechanicalness*, dated 13 October 2026. It is a standalone exposition of
the finite-guard construction. Its parent is *An affirmative 3-1-3 proof using
finite guards*, dated 8 October 2026, retained in the
[embedded Lean project's paper bundle](../alexander-dissertation-lean/paper/README.md),
imported from standalone commit `b06b50a9bdc61f6c620985bf322ad5edbd2e98d0`.
The import record identifies the original repository and every copied file.

On 13 October 2026, at the owner's request, OpenAI Codex placed the revised
parent paper directly in note 17 and archived the earlier paper under
[archive/2026-10-03/](archive/2026-10-03/README.md). At that placement, the revision's Markdown,
PDF, generated LaTeX, build record and three typesetting files are byte-identical
to the embedded bundle. The old LaTeX manuscript, PDF and build records are
also unchanged; only relative references in the archive's documentation and
source map were adjusted for their new location.

The parent manuscript SHA-256 is
`bc012600043e35b9a415311614b31fbc9e2b61847af044fe1a3452f0a185c16a`.
The parent PDF SHA-256 is
`3cf586d0dfe1ae36d41dc3e77a9f1d91ac8e38ba01a7ad6237057c22cd3efabf`.
The parent manuscript and all seven paper/build files are preserved without
editing in [archive/2026-10-08/](archive/2026-10-08/README.md).
[source-map.json](source-map.json) records the current artifact paths and hashes.

## Standalone editorial revision, 13 October 2026

After the owner clarified that the paper should assume no familiarity with
the earlier proof, Codex read the full manuscript and rewrote its exposition.
The edition adds a result/problem/method abstract, a contextual introduction,
an explicit description of self-doubting Epistemic Arithmetic, and explanations
of the auxiliary theory, stage roles, reconstruction and the two inductions.
The background axiom descriptions were checked against the archived dissertation
text, Definitions 1.2.9, 1.2.15, 1.2.17 and 1.2.19.

The auxiliary-strength consequences are now stated with their own definitions.
The historical comparison and handoff/module correspondence are retained in
[CONSTRUCTION-COMPARISON.md](CONSTRUCTION-COMPARISON.md). All mathematical
content needed by the main proof remains in the paper. The main theorem and
all 18 numbered lemma statements are byte-identical; all 104 displayed formulas
are unchanged; all 888 mathematical expressions in Sections 1–17 remain in
their original order. No mathematical hypothesis or Lean source was changed.

The rebuilt PDF has 33 pages and 68 section bookmarks. All 998 mathematical
expressions match the generated LaTeX up to writer indentation. Fonts are
embedded; no missing symbols, unresolved references or overflowing text were
reported; the opening two pages were visually inspected. The
[editorial review record](standalone-editorial-review.json) records this scope.

The
[comparison](../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
states the formal result's scope against the archived parent. The
[public CI result](https://github.com/avg-netizen/alexander-open-problems-results/actions/runs/38453360717)
checks the completed proof closure and paper extensions, with all 107 axiom
reports passing. The earlier source notes and historical verification record
remain described in the [archived provenance](archive/2026-10-03/PROVENANCE.md).
No independent human mathematical review has been recorded, and nothing has
been sent to the source authors.
