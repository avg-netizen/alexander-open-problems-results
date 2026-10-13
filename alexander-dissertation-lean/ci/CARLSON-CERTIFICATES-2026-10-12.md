# Reflection targets and recursive certificate groundwork

This records the reflection-constructor milestone. The subsequent original
recursive certificate codecs and current computational frontier are described
in [the recursive codec note](CARLSON-RECURSIVE-CODECS-2026-10-12.md).

`PrimitiveReflectionConstructors` certifies the actual downward and upward
targets at every finite label bound. The algorithms decode the original
pattern, anchor, carrier and total-map fields, construct both complete Boolean
tables, and return the original encoded target. Compatibility holds on every
raw natural input, including noncanonical accepted carrier codes and malformed
fields. It requires no patternhood or reflection-hypothesis assumption.

The downward construction retains the old-old clause, the copied-low clause
using the executable back map, and the additional first-relation bridge only
at the second reflection level. The upward construction retains its different
first- and second-relation cross clauses. Both construct every ambient table
entry, including off-carrier entries. Neither constructor replaces validity
checking: an input with valid field decodes but failed reflection hypotheses
still has a target.

`constructDownward_primrec`, `constructUpward_primrec` and their program
theorems supply uniform primitive-recursive algorithms and actual total
`Nat.Partrec.Code` machines. The latter's successful result encodes an
`Option Nat`; malformed fields return `none`. These are mathlib machines,
with translation into the project's `Program` language still required.

`PrimitiveSExpression` handles the recursive tree format used by the pinned
derived encoders. An atom has code `pair 0 n`; a cons has code
`pair (headCode + 1) tailCode`. Both child codes are strictly smaller than a
cons code. The history recursion computes each child from previous results,
and `fold_primrec` proves primitive recursiveness uniformly in a coded
parameter, provided the atom and cons interpretation operations are themselves
primitive recursive. The module also checks structural compatibility with the
pinned deriving handler's private tree. Existing certificate codecs are
unchanged.

`CompileCarlsonReflectionConstructors.lean` checks the original-code output
statements and audits all 43 new public theorems. Kernel regressions distinguish
the second-level downward bridge, the two upward cross clauses, and off-carrier
tables; accept an unsorted carrier; reject duplicate carriers, malformed
patterns, out-of-range anchors and malformed total maps; cover the empty label
bound; and check nested tree recursion and an actual machine result. The
focused GitHub workflow compiles these proofs and controls and runs the
existing logical-axiom whitelist before merge.

## Remaining route to an effective ordinal package

The recursive finite checker still needs a lossless interpretation algebra for
the original mutual rule/chain trees, with exact raw decoding, source and
target computation, and every rule check. The generic fold proves the recursion
mechanism; it does not instantiate that algebra. Generation certificates also
need their original record wrapper. The reflection target constructors remove
one previously missing part of the endpoint algebra.

After finite checking, the existing rational-checker reduction can be applied.
The fair-stage scheduler, target selection and certified liftings must then be
combined with finite-history recursion, and their machines represented in the
project's `Program` language.

The classical core and its finite tallness are proved separately in
[the core development](CARLSON-CORE-2026-10-12.md). A computed fair sequence from
one finite seed presents that seed's initial segment. Equality of its bound
with the common `coreBound` has not been proved. An effective presentation of
the whole core needs cross-seed pointed-pattern comparisons or an effective
cofinal amalgamating construction, followed by a unique-representative
enumeration and actual order/first/second relation Programs. A classical
bijection with natural numbers does not supply those recognizers.

Unconditional 3-1-3 and 3-1-2 remain unconstructed until those computational
inputs instantiate `OrdinalPackage.ofCarlsonCore`.
