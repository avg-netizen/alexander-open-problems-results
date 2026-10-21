# Proof dependencies and assumption checks

This guide accompanies the [paper](successor-knowers-3-2-1.md). It is navigation and a record of checks, not a substitute for its proofs.

## Main dependency chain

1. **Source interpretation, Sections 1–2.** Definition 3.1.5 supplies an actual standard numeral whose code assertion is a predecessor consequence. The canonical clause identifies the successor's answers with its consequences. Truthfulness in the common standard structure supplies external soundness.
2. **Lemma 2.** A simultaneous induction over every unary modal formula propagates selected codes from the root. Both external correctness and predecessor endorsement are retained. No unprovided enumeration of a later theory is used.
3. **Lemma 3.** A fixed partial truth predicate and normalized weak base have the uniform truth properties needed for the arithmetic conversion. The induction used here is a PA induction on a fixed satisfaction formula with syntax parameters.
4. **Lemma 4.** Truth of one enumerated \(\Pi_3\) column implies reflection for that column over the normalized \(\mathsf I\Sigma_1\) base. Logical cut elimination and bounded-level satisfaction justify the uniform claim. This is not a claim that PA proves its own reflection.
5. **Lemma 5.** The resulting arithmetic theory has exactly the original machine's designated \(\Pi_3\) consequences. The equality is external, not assumed as an internal theorem.
6. **Lemma 6.** Compiled wrapper programs give a uniform presentation without an internal totality proof. Each fixed actual terminating computation supplies base-verified witness and proof translations.
7. **Theorem 1, Section 7.** The predecessor proves successor reflection. Its designated normalization becomes an actual axiom of the predecessor's arithmetic column theory. Thus the reflection is proved in the arithmetic sequence to which non-descent applies.
8. **Appendix A and Theorem 7.** Fixed definitional translations reconcile the source's exponentiation language, partial truth predicates and proof conventions. The resulting uniformly enumerable sound reflection sequence contradicts Pakhomov–Walsh, Theorem 3.4.
9. **Corollary 8.** The source question satisfies the hypotheses just checked, including full unary code knowledge and the required truthfulness instance.

## Checks against common scope errors

| Possible gap | Where it is addressed |
|---|---|
| Confusing a particular endorsed numeral with a known existential assertion | Section 2.2 |
| Assuming the family is uniformly enumerable at the outset | Lemma 2 and wrapper construction |
| Recovering correct indices but losing their endorsements | Both conclusions of Lemma 2 |
| Assuming arithmetic proves totality of the selection procedure | Sections 3 and 5; pointwise Lemma 6 |
| Exchanging extensionally equal proof predicates without a proof translation | Lemma 6 and Appendix A |
| Proving reflection only in a modal theory, not its arithmetic projection | The actual-axiom step (30) in Section 7 |
| Using all modal code instances while claiming bounded modal depth suffices | Section 8.1 states the actual unbounded recursive family |
| Turning a noncomputable path into an effectively named chain | Section 8.2 and supplement S2–S3 |
| Treating an earlier source theorem as a new local result | Theorem 7 and the point-of-use source credits |
| Implying that the separate 3-1-x Lean project certifies this argument | Section 8.3 and entry README |

## Supplemental dependency chain

S1 uses Lemma 2 with a dummy-variable formula to enumerate sentence consequences. S2 adapts the effective syntax construction along a total computable path, using the full main reduction; S3 repeats a finite cycle periodically. S4 uses Lemmas 4–5 and second incompleteness. S5 supplies an explicit finite-extension incompleteness argument. S6 transfers a normalized guarded reflection sentence through the stated inclusion of \(\Pi_3\) consequences, then applies S5.

The counterexample \(\sigma=R_V\) in the supplement explains why the arithmetic guard bound cannot simply be extended to arbitrary true \(\Pi_3\) conditions. It is not a modal-model construction.

## Check status

The source passages listed in [SOURCE-CHECKS.md](SOURCE-CHECKS.md) were read against the hypotheses used. The local argument was expanded and checked for the dependencies above by the assembling Codex agent. This is not an independent review. The typesetting report checks document generation and proof-ending counts; it does not certify the mathematical argument. No formal proof or priority search is included in this entry.
