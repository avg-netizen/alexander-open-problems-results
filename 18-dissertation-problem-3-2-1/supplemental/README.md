# Additional proved consequences

Read [the 5-page supplemental PDF](additional-results.pdf), its [canonical Markdown](additional-results.md), or the [generated LaTeX](additional-results.tex).

**Separate new note, 27 October 2026:**
[An explicit ill-founded witnessing hierarchy](explicit-ill-founded-witness.md)
specifies a recursive order and effective fixed-point construction satisfying
Alexander's Theorem 79(1). An oracle for arithmetic truth could enumerate any
unsound indices and descend through them; an explicit diagonal tree prevents
such a path. The proof does not depend on the negative 3.2.1 result, and paper
07's generic introspection bundle can optionally be added. This is a local
hand proof without independent review or a novelty determination, and is not
included in the existing supplemental PDF.
The expanded [13-page explanatory paper](../../19-explicit-ill-founded-hierarchy/ill-founded-hierarchy.pdf)
has its own [source and build record](../../19-explicit-ill-founded-hierarchy/README.md)
in entry 19 and contains the entire argument.

| Result | Content | Main input |
|---|---|---|
| S1 | A single root enumeration uniformly enumerates every later full consequence set. Arithmetic induction and known truthfulness of successors are unnecessary for this conclusion. | Main paper, Lemma 2 |
| S2–S3 | No computable infinite endorsement path, hence no finite cycle, under the arithmetic hypotheses. This does not assert well-foundedness. | Main reduction and Pakhomov–Walsh |
| S4 | An endorsed edge supplies a specific \(\Pi_3\) theorem of the predecessor that is not a theorem of the successor. | Arithmetic column conversion and second incompleteness |
| S5–S6 | A true \(\Sigma_3\) condition cannot support a conditional successor code when the predecessor's designated \(\Pi_3\) consequences are included in the successor's. | Finite-extension argument and column conversion |

All statements have proofs, with exact assumptions. References to the [main paper](../successor-knowers-3-2-1.md) resolve within this repository. These consequences are worth retaining separately, but no independent novelty or formal-verification claim is attached to them.

Run `python3 build_pdf.py` from the parent directory to rebuild both papers.
