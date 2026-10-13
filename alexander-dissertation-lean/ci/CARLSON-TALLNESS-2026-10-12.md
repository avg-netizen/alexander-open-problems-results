# Unconditional pure Carlson coveredness and tallness

The new modules prove classical existence of arbitrarily long finite strict
chains for the actual recursively defined `Carlson.R2`, and that every finite
pure Carlson pattern is covered. The proof uses `ω₁` and countable closure,
not an ordinal package, coveredness, tallness, a supplied realization, or a
set-theoretic reflection principle.

Source correspondence: Carlson, *Patterns of Resemblance of Order 2*,
Definitions 5.2–5.4 and Lemma 15.11. The covering relation is forward on both
relations, and the pure-language base is the finite linear order. This is an
alternative proof of the pure case of Lemma 15.11. It does not identify these
relations with Wilken's elementarity relations.

## The proof

For each countable cutoff `ξ`, a finite witness request records a size, optional
fixed anchors at most `ξ`, three finite relation tables (strict order, `R1`,
`R2`), and unary `R1` links to `ω₁`. An unanchored position must lie above `ξ`.
There are countably many such requests: the anchor interval is countable,
the domain of each table is finite, and finite truth tables have finitely
many values, classically. For each request realized below `ω₁`, choose one
realization and bound its finitely many points. Their countable supremum is
`witnessBound ξ < ω₁`.

A second countable family records a finite anchor set and arbitrary finite
relation tables for Carlson's cofinal-copy clause. For every family that is
not cofinal below `ω₁`, choose a cutoff above which no copy occurs. The
supremum of these cutoffs is `obstructionBound ξ < ω₁`.

`closureStep ξ` bounds the successor of `ξ` and both bounds at every cutoff
at most `ξ`. Countable regularity keeps this step below `ω₁`. Iterating it
through the natural numbers above any given `γ < ω₁` and taking the supremum
produces `γ < a < ω₁` closed under both bounds. Such an `a` is a
`ReflectionPoint`.

Finite type reflection fixes the requested anchors, carries both actual
relations and strict order forward, keeps moved points above the cutoff,
and preserves the unary ambient links. Taking the cutoff above every point
of a finite set already below `a` proves **`R1 a ω₁` first**. Consequently,
when `a ≤ b` are reflection points, `R1 y b` implies `R1 y ω₁` by
transitivity. The preserved unary flag gives `R1 (f y) ω₁`; connectedness
then gives `R1 (f y) a`. This is precisely the linked-copy clause of `R2`.

Closure under obstruction cutoffs proves that a copy family cofinal below
`a` is cofinal below `ω₁`. Finite witness reflection at `b` pulls its copies
above any prescribed cutoff below `b`. These prove Carlson's second
cofinal clause and hence **`R2 a b`** for any ordered reflection points.

Repeatedly choosing a larger reflection point gives a strictly increasing
sequence with every forward `R2` link. A finite pattern maps its increasing
carrier enumeration into a finite part of this sequence. Its first and
second edges respect the linear order, so both carry forward (`R2 ⊆ R1`).
This is a covering, including for an empty pattern.

## Public results and remaining integration

- `exists_reflectionPoint_above`: reflection points exist above every
  countable ordinal.
- `ReflectionPoint.first`, `ReflectionPoint.second`: the actual ordinal
  relations hold at the constructed points.
- `reflectionSequence_strictMono`, `reflectionSequence_second`: an
  infinite increasing sequence of pairwise forward `R2` links below `ω₁`.
- `exists_finite_second_chain`, `exists_ordinal_guard`: strict finite chains
  of any length, in the exact list shape needed by ordinal guards.
- `exists_covering_below_omega_one`, `every_pattern_covered`: every pure
  pattern is covered by countable ordinals.

These remove the global mathematical coveredness and finite-chain
assumptions. A computable presentation of one initial segment containing
guards of every finite rank, represented by all natural-number labels and
the project's actual `Program` language, still needs construction. The
realization of one arbitrary finite seed is not asserted to contain guards
of all ranks.

## Validation

`CompileCarlsonTallness.lean` checks independently stated closure, second
relation, finite-chain, and coveredness propositions and prints the axioms
of every new theorem. `TallnessExamples` covers complete finite chains,
zero-length chains and zero-rank guards, and proves that a reversed first
edge in a two-point linear order cannot be covered.

The separate GitHub workflow is `compile-carlson-tallness.yml`. It builds
the complete import closure of the proofs, builds the controls, runs the
gate, and applies the existing axiom whitelist. Merge requires a successful
GitHub run; local checks alone do not meet that condition.
