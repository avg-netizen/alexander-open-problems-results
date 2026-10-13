# The common classical core and its finite guards

This continues the [unconditional coveredness proof](CARLSON-TALLNESS-2026-10-12.md).
The existing conditional fair/minimal realization theorems now apply to every
pure rational pattern. The new development constructs one common countable
initial segment containing finite guards of every rank, identifies it with
the union of finite isominimal ordinal substructures, and transports its
tallness into the ordinal-package interface.

## Construction and source correspondence

`UnconditionalRealization` discharges the coveredness premise of
`GeneratingSequence.exists_fair_ordinalRealization` and
`GeneratingSequence.exists_minimal_ordinal_copy`. A `PatternRealization`
retains the exact supplied stage-zero structure, its fair sequence, and an
exact ordinal realization. Its label map is pointwise least among all
ordinal coverings of its seed. Comparing these least labels with the
countable covering from the closure construction gives a finite strict
bound below `ω₁`, hence its ordinal limit bound is below `ω₁`.

`CoreSeed` ranges over the encoded `RationalPresentation` records which
are patterns. This index type is countable. `coreBound` is the supremum of
their chosen realization bounds, and countable regularity proves
`coreBound < ω₁`.

Every chosen least seed label lies below `coreBound`. Conversely, a point
below the supremum lies in one seed's ordinal realization, hence in one
finite stage of its union. Encode that stage as a rational presentation.
Its chosen least seed labels equal the original stage labels by mutual
pointwise minimality. Thus `CorePoint a ↔ a < coreBound`.

`CoreIsominimal` matches the original core definition from Carlson's
introduction and the initial-segment part of Theorem 14.14. A realized stage
is isominimal by the existing Lemma 14.9 theorem. Conversely, rational
relabeling of an arbitrary finite ordinal set supplies a least exact copy
pointwise below its original labels. If the original induced structure is
isominimal, the two carriers coincide. Hence

```lean
(∃ U : Finset Ordinal.{0}, a ∈ U ∧ IsominimalOrdinalSet U) ↔ a < coreBound
```

Both actual ordinal relations remain inside this core: a point below the
supremum lies below a seed-realization bound, and no `R1` or `R2` edge can
leave that realized segment. The least-cutpoint characterization
`coreBound ≤₁ ∞` from the rest of Theorem 14.14 is not asserted here.

`CoreTallness` realizes each finite rational complete-chain pattern in its
least exact ordinal copy inside the core. This gives the exact finite guard
list shape at every rank, with every point below `coreBound`. It also proves
that the core carrier is countable and infinite, so a classical bijection
with all natural numbers exists.

`OrdinalPresentation.tall_of_core` transports these guards through any
initial-segment presentation whose bound equals `coreBound`.
`OrdinalPackage.ofCarlsonCore` uses that theorem to assemble the package
without a tallness parameter. Its remaining inputs are the presentation,
three actual `Program` records, and proofs that their domains recognize
order and both transported relations. A classical natural-number bijection
does not supply these computational obligations.

## Validation

`CompileCarlsonCore.lean` checks independently stated core membership,
countable bound, finite guard, transported tallness and bijection results,
then audits all new theorem axioms. `CoreExamples` checks the empty-seed
bound, excludes the core's own boundary from membership, excludes relation
edges from internal points to that boundary, and specializes least-copy
existence to a nontrivial two-point chain.

The separate `compile-carlson-core.yml` workflow builds the proof modules,
controls and gate and applies the existing axiom whitelist. A successful
GitHub run is required before merging this continuation.
