import Alexander313.Carlson.ComputableArithmeticLifting
import Alexander313.Carlson.ComputablePatternCandidate
import Alexander313.Carlson.PatternLiftingConstruction
import Alexander313.Carlson.PatternLiftingNormalization
import Alexander313.Carlson.FiniteRelabeling
import Alexander313.Carlson.GeneratingRules

/-!
# Executable continuous minimal liftings on rational presentations

The constructor returns a finite target presentation and a total rational
map. It computes placements, source-image tables, least upper anchors, and
the two finite candidate relations. Its data do not depend on proofs of the
input hypotheses. Those hypotheses certify that its result is a continuous
minimal pattern lifting in the original, unnormalized sense.

The correctness argument identifies the computed tables with Carlson's
common-carrier candidate. Arithmetic uniqueness compares the computed map
with every competing lifting map on the same target carrier, so minimality
is proved directly without choosing a smaller pattern or enumerating all
possible relation tables.

This is a Lean-executable constructor. No representation in the project's
`Program` language, effective fair sequence, or ordinal package is asserted.
-/

namespace Alexander313.Carlson.Finite.RationalPresentation

/-- The total map computed by the bounded rational lifting construction.
Its behavior outside the source carrier is immaterial to correctness. -/
def liftMap (P Pplus Q : RationalPresentation) (h : ℚ → ℚ) : ℚ → ℚ :=
  ArithmeticLifting.computableMap P.U Pplus.U Q.U h

/-- The finite target of the rational lifting construction. -/
def liftTarget (P Pplus Q : RationalPresentation) (h : ℚ → ℚ) :
    RationalPresentation :=
  liftingCandidate (P.U.image h) (Pplus.map (liftMap P Pplus Q h)) Q
    (ArithmeticLifting.computableTarget P.U Pplus.U Q.U h)

/-- Compute both the target presentation and the lifting map from finite
endpoint data and the supplied base map. -/
def lift (P Pplus Q : RationalPresentation) (h : ℚ → ℚ) :
    RationalPresentation × (ℚ → ℚ) :=
  (liftTarget P Pplus Q h, liftMap P Pplus Q h)

@[simp] theorem liftTarget_U (P Pplus Q : RationalPresentation) (h : ℚ → ℚ) :
    (liftTarget P Pplus Q h).U = Q.U ∪ Pplus.U.image (liftMap P Pplus Q h) := rfl

/-- The computed target and map satisfy the original lifting definition,
its universal minimality condition, and continuity over the old target. -/
theorem lift_spec {P Pplus Q : RationalPresentation} {h : ℚ → ℚ}
    (hS : Pplus.toStr.IsPattern) (hQ : Q.toStr.IsPattern)
    (hC : Str.Continuous P.toStr Pplus.toStr)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h) :
    PatternLifting P.toStr Pplus.toStr Q.toStr (lift P Pplus Q h).1.toStr
      h (lift P Pplus Q h).2 ∧
    PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr
      (lift P Pplus Q h).1.toStr h ∧
    Str.Continuous Q.toStr (lift P Pplus Q h).1.toStr := by
  classical
  let f := liftMap P Pplus Q h
  let U := ArithmeticLifting.computableTarget P.U Pplus.U Q.U h
  let S := Pplus.map f
  let R := liftTarget P Pplus Q h
  have hmem : ∀ x ∈ P.U, h x ∈ Q.U := by
    intro x hx
    exact hE.2.1.1 (hE.1.mem hx)
  have A : ArithmeticLifting P.U Pplus.U Q.U U h f :=
    ArithmeticLifting.computable_rat hC.1.1 hC.2.1 hE.1.2.1 hmem
  have eplus : Str.IsIso Pplus.toStr S.toStr f := Pplus.map_isIso f A.mono
  let D : PatternLiftingConstruction.Data
      (Q.toStr.restrict (P.U.image h)) S.toStr Q.toStr U :=
    { source_pattern := eplus.isPattern hS
      target_pattern := hQ
      source_cont := hC.of_isIso hE.1 eplus A.agrees
      target_cont := hE.2
      arithmetic := A.normalized }
  have e : Str.IsIso D.candidate R.toStr id := liftingCandidate_iso D
  have hcont : Str.Continuous Q.toStr R.toStr :=
    D.candidate_continuous.of_isIso (Str.IsIso.refl Q.toStr) e (fun _ _ => rfl)
  have L : PatternLifting P.toStr Pplus.toStr Q.toStr R.toStr h f :=
    { source_pattern := hS
      target_pattern := e.isPattern D.candidate_isPattern
      source_sub := hC.1
      target_sub := hcont.1
      arithmetic := A
      relations := by
        intro x hx y hy
        have hs := eplus.2.2 x hx y hy
        have hc := D.candidate_source_sub.2 (f x) (eplus.mem hx) (f y) (eplus.mem hy)
        have he := e.2.2 (f x) (D.source_mem (eplus.mem hx))
          (f y) (D.source_mem (eplus.mem hy))
        exact ⟨hs.1.trans (hc.1.trans he.1), hs.2.trans (hc.2.trans he.2)⟩ }
  have hminimal : PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr R.toStr h := by
    intro T g hTU E
    have hT : T.U = U := hTU
    have Earith : ArithmeticLifting P.U Pplus.U Q.U U h g := by
      simpa only [toStr_U, hT] using E.arithmetic
    have hfg : ∀ x ∈ Pplus.U, f x = g x := fun x hx => A.unique Earith hx
    have hsource : Str.IsSub S.toStr T := by
      refine ⟨?_, ?_⟩
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
        rw [hfg x hx]
        exact E.arithmetic.mem x hx
      · intro u hu v hv
        obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
        obtain ⟨y, hy, rfl⟩ := eplus.preimage hv
        have hs := eplus.2.2 x hx y hy
        have ht := E.relations x hx y hy
        rw [← hfg x hx, ← hfg y hy] at ht
        exact ⟨hs.1.symm.trans ht.1, hs.2.symm.trans ht.2⟩
    have hc := D.candidate_coversInto E.target_pattern hT hsource E.target_sub
    refine ⟨?_, fun _ _ _ _ hxy => hxy, ?_, ?_⟩
    · intro x hx
      exact hTU.symm ▸ hx
    · intro x hx y hy hr
      exact hc.2.2.1 x hx y hy ((e.2.2 x hx y hy).1.mpr hr)
    · intro x hx y hy hr
      exact hc.2.2.2 x hx y hy ((e.2.2 x hx y hy).2.mpr hr)
  exact ⟨L, hminimal, hcont⟩

/-- The constructor fixes every old source point at its supplied base image. -/
theorem lift_agrees {P Pplus Q : RationalPresentation} {h : ℚ → ℚ}
    (hS : Pplus.toStr.IsPattern) (hQ : Q.toStr.IsPattern)
    (hC : Str.Continuous P.toStr Pplus.toStr)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h) {x : ℚ} (hx : x ∈ P.U) :
    (lift P Pplus Q h).2 x = h x :=
  (lift_spec hS hQ hC hE).1.arithmetic.agrees x hx

/-- The target contains exactly one new point for each new source point. -/
theorem lift_card {P Pplus Q : RationalPresentation} {h : ℚ → ℚ}
    (hS : Pplus.toStr.IsPattern) (hQ : Q.toStr.IsPattern)
    (hC : Str.Continuous P.toStr Pplus.toStr)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h) :
    (lift P Pplus Q h).1.U.card = Q.U.card + (Pplus.U \ P.U).card :=
  (lift_spec hS hQ hC hE).1.arithmetic.card_target

/-- A source extension at one old point lifts at its base image. -/
theorem lift_extensionAt {P Pplus Q : RationalPresentation} {h : ℚ → ℚ} {a : ℚ}
    (hS : Pplus.toStr.IsPattern) (hQ : Q.toStr.IsPattern)
    (hC : Str.Continuous P.toStr Pplus.toStr)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h)
    (hAt : Str.ExtensionAt P.toStr Pplus.toStr a) :
    Str.ExtensionAt Q.toStr (lift P Pplus Q h).1.toStr (h a) :=
  (lift_spec hS hQ hC hE).1.extensionAt hAt

/-- Cofinal validity passes to this computed minimal lifting. -/
theorem lift_cofinallyValid {P Pplus Q : RationalPresentation} {h : ℚ → ℚ}
    (hS : Pplus.toStr.IsPattern) (hQ : Q.toStr.IsPattern)
    (hC : Str.Continuous P.toStr Pplus.toStr)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h)
    (hcv : Str.CofinallyValid P.toStr Pplus.toStr) :
    Str.CofinallyValid Q.toStr (lift P Pplus Q h).1.toStr :=
  (lift_spec hS hQ hC hE).1.cofinallyValid (lift_spec hS hQ hC hE).2.1 hcv

/-- The computed lifting realizes clause 5 of Carlson's generating-rule
calculus. Thus a recognized source request has a concrete generated target
along every supplied continuous base embedding into a target pattern. -/
theorem lift_generatingRule {P Pplus Q : RationalPresentation} {h : ℚ → ℚ}
    (d : Str.GeneratingRule P.toStr Pplus.toStr) (hQ : Q.toStr.IsPattern)
    (hE : Str.ContinuousEmbedding P.toStr Q.toStr h) :
    Str.GeneratingRule Q.toStr (lift P Pplus Q h).1.toStr :=
  .lifting d hE (lift_spec d.target_pattern hQ d.continuous hE).1
    (lift_spec d.target_pattern hQ d.continuous hE).2.1

end Alexander313.Carlson.Finite.RationalPresentation
