# An explicit ill-founded hierarchy of self-referential theories

An explanatory paper giving a specified recursive order and effective
construction of a true uniformly r.e. hierarchy satisfying Alexander's
*Self-referential theories*, Theorem 79(1).

- [Read the paper](ill-founded-hierarchy.pdf).
- [Canonical LaTeX source](ill-founded-hierarchy.tex).
- [Build and document checks](pdf-build-report.json).

Every member expresses particular codes of everyone and the truthfulness of
all its subordinates. The order is ill-founded but has no descending path
computable from arithmetic truth. An unsound fixed-point family would let
that oracle enumerate unsound members and follow a forbidden path.

The paper states the result first, develops the effective construction and
its proofs, gives worked examples of the finite tree tests, then explains the
relation to successor chains and paper 07's introspection bundle. It contains
all local arguments and uses only published logical inputs and identified
companion papers in this repository. No wider working directory is needed.

This is a hand proof without independent mathematical review, formal
verification or an established priority claim. The full universal-background
statement of Theorem 79(1) is retained; the different stratified construction
in part (2) is outside the result. A complete executable modal consequence
enumerator is not supplied.

Rebuild from this directory with:

```sh
python3 build.py
```

The build uses Tectonic's existing cache, stays offline, and selects Computer
Modern text and mathematics. Poppler's `pdfinfo`, `pdffonts` and `pdftotext`
check the resulting document. The report records source/PDF hashes, fonts,
page count, visible proof endings and any layout diagnostics.

The shorter [construction note](../18-dissertation-problem-3-2-1/supplemental/explicit-ill-founded-witness.md)
is retained with the 3.2.1 supplements. The full paper stands on its own.
