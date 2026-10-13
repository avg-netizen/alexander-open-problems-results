# Original recursive certificate codecs

`PrimitiveRecursiveCertificates` instantiates the certified S-expression fold
for the original mutual `RuleCertificate n` and `ChainCertificate n` encodings.
The label bound and raw natural code are both inputs. The interpretation
retains atom fields, rule results, chain results and proper-list spines
separately. Every constructor checks its tag, exact field count and field
kind. Recursive fields are trees; scalar fields are atoms containing the
original scalar codes.

Scalar normalization uses the existing original pattern, finite-label,
finite-carrier and total-map codecs. Both reflection levels retain their
original derived encodings. The interpreter retains complete pattern tables,
including off-carrier entries. Accepted noncanonical carrier encodings are
normalized with the original finite-set encoder; malformed components are
rejected.

The exact raw-output equations are `normalizeRule_eq` and
`normalizeChain_eq`: their results are precisely the existing decoder's result
mapped through its existing encoder. These equations hold on every raw natural
input, with no canonical-code or certificate-validity assumption. The
primitive coding instances reuse the original encoders and decoders. Uniform
primitive-recursion proofs supply actual total `Nat.Partrec.Code` machines
which return the original encoded `Option` decode result at every label bound.

The mutual deriving handler's auxiliary names carry hygiene scopes. The proof
opens the uniquely identified imported constants by their names with those
scopes erased. This introduces aliases only. Exact decoder compatibility and
all seven constructor encoding equations are proved from those imported
constants and their equation theorems, then checked by Lean's kernel.
The component encodings and certificate declarations are unchanged.

`PrimitiveGenerationCodec` supplies the same exact raw-output equation,
unchanged primitive coding instance and uniform total decoding machine for
`GenerationCertificate n`. Its outer tag-zero record stores two scalar atoms,
containing the chain code and target pattern code, and requires the exact zero
terminator. The chain is encoded as an atom here because the generation record
is outside the mutual rule/chain declaration. Its component normalization uses
the certified original chain and pattern decoders.

The focused gate checks conclusions stated with the original derived
instances, audits every public theorem and coding instance, and checks
malformed recursive children, mismatched rule/chain kinds, finite-bound
failure after a valid nested child, the empty label bound, a false reflection
side condition, and an off-carrier join mismatch. Generation controls reject
an undecodable scalar chain and an unwrapped chain tree, and accept a nested
chain in the original record encoding. No semantic validity follows merely
from successful decoding. The gate audits 62 reports using only `propext`,
`Classical.choice` and `Quot.sound`.

## Remaining dependencies

The recursive source/target computations, Boolean derivation checks and
unconditional rational checker machines are now proved in
[the recursive verifier continuation](CARLSON-DERIVATION-CHECKS-2026-10-12.md).
Fair-stage history recursion and translation into the project's `Program`
language remain.

[Least-copy completeness and finite amalgamation existence](CARLSON-LEAST-COPIES-2026-10-12.md)
now prove Theorem 14.10 in the pure case, agreement along valid rules, and an actual
finite ordinal amalgamation of any finite family of rational patterns.
Amalgamation uniqueness and effective pointed comparison remain. They are needed
for an effective enumeration of the whole classical core and its three
relation-recognizing Programs. `OrdinalPackage.ofCarlsonCore` still requires that
effective presentation and those recognizers. Unconditional 3-1-3 and 3-1-2
remain unconstructed.
