# Archived 8 October 2026 finite-guard paper

This is the supplied 8 October edition of
*An affirmative 3-1-3 proof using finite guards*. Its manuscript,
[31-page PDF](REVISED-3-1-3-PROOF.pdf), generated LaTeX, build record and
typesetting files are preserved byte for byte.

The [current standalone paper](../../README.md) expands the reader's introduction,
defines the background assumptions, and presents the construction without
requiring the earlier proof or the formalization handoff. The
[historical comparison note](../../CONSTRUCTION-COMPARISON.md) retains this
edition's construction comparison and source correspondence.

The archived manuscript SHA-256 is
`bc012600043e35b9a415311614b31fbc9e2b61847af044fe1a3452f0a185c16a`.
The archived PDF SHA-256 is
`3cf586d0dfe1ae36d41dc3e77a9f1d91ac8e38ba01a7ad6237057c22cd3efabf`.
These are also the paper hashes in the original imported Lean project and
the 13 October paper-to-Lean audit.

To reproduce this archived edition from this directory:

```sh
python3 build_pdf.py
```

Its original Lua filter and title metadata remain intact. Rebuilding needs
Pandoc, Tectonic and Poppler; cached TeX resources are used by default.
