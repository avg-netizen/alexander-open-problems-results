# Additional proved consequences

Read [the 6-page supplemental PDF](additional-results.pdf), its [canonical Markdown](additional-results.md), or the [generated LaTeX](additional-results.tex).

| Result | Content | Main input |
|---|---|---|
| S1 | A single root enumeration uniformly enumerates every later full consequence set. Arithmetic induction and known truthfulness of successors are unnecessary for this conclusion. | Main paper, Lemma 2 |
| S2–S3 | No computable infinite endorsement path, hence no finite cycle, under the arithmetic hypotheses. This does not assert well-foundedness. | Main reduction and Pakhomov–Walsh |
| S4 | An endorsed edge supplies a specific \(\Pi_3\) theorem of the predecessor that is not a theorem of the successor. | Arithmetic column conversion and second incompleteness |
| S5–S6 | A true \(\Sigma_3\) condition cannot support a conditional successor code when the predecessor's designated \(\Pi_3\) consequences are included in the successor's. | Finite-extension argument and column conversion |

All statements have proofs, with exact assumptions. References to the [main paper](../successor-knowers-3-2-1.md) resolve within this repository. These consequences are worth retaining separately, but no independent novelty or formal-verification claim is attached to them.

Run `python3 build_pdf.py` from the parent directory to rebuild both papers.
