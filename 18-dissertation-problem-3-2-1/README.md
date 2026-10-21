# Dissertation Open Problem 3.2.1: successor chains without ordinals

**Result:** a negative answer in Alexander's recursively named language and standard canonical semantics. Full particular-code knowledge allows a reduction to the published Pakhomov–Walsh arithmetic non-descent theorem. No ordinal predicate is assumed.

The question was posed in Samuel Allen Alexander's 2013 Ohio State dissertation, *The Theory of Several Knowing Machines*, **§3.2, Open Problem 3.2.1, printed p. 89** (PDF page 99). The preceding Theorem 3.1.6 includes an ordinal hypothesis; the question asks whether it can be removed. See the [OhioLINK record](https://rave.ohiolink.edu/etdc/view?acc_num=osu1366362999).

## Read the entry

- [Full paper, 13-page PDF](successor-knowers-3-2-1.pdf), with definitions, all local proofs, arithmetic presentation conventions and bibliography.
- [Canonical Markdown manuscript](successor-knowers-3-2-1.md) and [generated LaTeX](successor-knowers-3-2-1.tex).
- [Supplemental results](supplemental/README.md): uniform enumeration of later consequence sets; no computable infinite endorsement path or finite cycle; an explicit separating arithmetic sentence; and an obstruction to true \(\Sigma_3\)-guarded codes under a specified inclusion of consequences.
- [Proof guide and assumption checks](PROOF-GUIDE.md).
- [Published-source locations](SOURCE-CHECKS.md) and [provenance](PROVENANCE.md).

The paper is the proof, rather than an abbreviated account of an argument stored elsewhere. Every local dependency is included here. Standard published inputs are stated and cited at their point of use; their source papers are linked rather than redistributed. No wider working directory is needed to read, build or assess this entry.

## Scope and review status

The result uses the particular-code condition printed in Definition 3.1.5: for each unary modal formula, an actual numeral index is endorsed by the predecessor. The argument does not establish the same conclusion for an arithmetic-only code schema, a schema of fixed finite modal depth, or a merely known existential code assertion.

These are hand proofs, assembled and checked by Codex. No independent human review, formal verification or established novelty is asserted. The Lean developments elsewhere in this repository concern Questions 3-1-1 through 3-1-3 and provide no certificate for this entry. The arithmetic non-descent theorem is credited to Pakhomov and Walsh; the question and modal framework to Alexander, with Carlson's earlier framework credited separately.

## Rebuild

From this directory:

```sh
python3 build_pdf.py
```

This builds both papers from their Markdown sources using Pandoc, Tectonic, the DejaVu fonts and the installed TeX cache. It needs Python 3 and Poppler's `pdfinfo` and `pdftotext`. Add `--allow-downloads` only if TeX resources are missing and downloads are wanted. The default build is offline. Generated TeX and PDFs are retained; [pdf-build-report.json](pdf-build-report.json) records source/output hashes, tool versions, page counts and diagnostics.

Edit the Markdown sources, then rebuild. Do not edit the generated LaTeX or PDF separately. This first edition is a fresh expansion of the argument, dated 20 October 2026; it does not claim text or formula preservation from an earlier sketch. The dependency guide and visible proof endings address the exposition issues encountered in the repository's earlier dissertation paper.
