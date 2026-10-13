# Recursive endpoints and total derivation verifiers

`PrimitiveCertificateAlgebra` gives primitive-recursive operations for all five
rule clauses and both chain constructors. Its summaries contain the complete
original source and target encodings and the original Boolean check. The
reflection constructors retain their target tables even when a side condition
is false. A chain join compares whole pattern codes, including off-carrier tables.

`PrimitiveRecursiveChecks` folds this algebra over the original normalized mutual
certificate grammar. Its all-input equations identify the result with the original
derived decoder mapped to the actual endpoints and check. Decoding failure gives
`none`; successfully decoded but invalid certificates retain their endpoints and
have a false check. `PrimitiveGenerationChecks` proves the corresponding result
for the original generation record, including source-carrier containment.

Both algorithms are primitive recursive uniformly in the label bound and raw
certificate code. At each fixed bound, the original typed endpoint and check
functions are also primitive recursive with unchanged certificate encodings.

`PrimitiveDerivationRecognition` discharges the finite-checker premises of the
existing rational reduction. The original rational rule, chain, and generation
checkers are primitive recursive and have actual total `Nat.Partrec.Code` machines
on every raw certificate input. Existential acceptance by these same machines
characterizes the original three semantic generating relations. This certifies
verification and positive recognition; it gives no bound for searching for a
derivation that might not exist.

`CompileCarlsonDerivationChecks` checks independent statements using the original
derived decoders, actual source/target/check functions, and original rational
checkers. It audits every public theorem of the six new modules (93 reports).
Kernel controls cover malformed children, the empty finite bound, false reflection
conditions with retained endpoints, restriction without a new point, valid minimal
identity lifting, a lifting with a false recursive child, an off-carrier join
mismatch, nested chains and generation, and source-carrier failure. The actual
rational machines inherit accepted and rejected raw-code controls, including
unused duplicate labels and the zero grid. Their proofs avoid evaluating the
large numeral denoted by a nested derived encoding.

The focused GitHub workflow compiles the proof modules, controls, and both new
gates before merge; each gate is checked by the existing axiom whitelist.

Fair-stage history recursion and translation into the project's `Program`
language still remain. [Least-copy completeness and finite amalgamation existence](CARLSON-LEAST-COPIES-2026-10-12.md)
advance comparison across finite seeds. The [October 13 continuation](CARLSON-POINTED-COMPARISON-2026-10-13.md)
proves compatible amalgamation uniqueness, rational existence, semantic pointed
comparison, and the full pure rational generation characterization.
Effective pointed comparison and enumeration of the whole core and
its three actual relation-recognizing Programs remain necessary for unconditional
3-1-3. A total certificate verifier does not supply those constructions.
