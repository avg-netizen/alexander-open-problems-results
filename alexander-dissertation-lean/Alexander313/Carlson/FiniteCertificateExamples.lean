import Alexander313.Carlson.FiniteRecognition

/-!
# Kernel-checked finite certificate regressions

These examples exercise all five certificate constructors, a genuine
two-step chain, restriction of that chain, and natural-number recognition.
Every finite calculation is checked by Lean's kernel. The examples contain
both valid inputs and deliberately malformed data; no pattern proof,
ordinal covering, or validity witness is stored in a certificate.

The reflection examples use the old points `1 < 3` in `Fin 4`. Downward
reflection inserts `0`, while upward reflection inserts `2`. Performing
upward reflection followed by a downward step produces a chain with new
points at two different old anchors. Its restriction to the lower copy is
an extension at one anchor, whereas the whole chain endpoint is not.
-/

namespace Alexander313.Carlson.Finite.CertificateExamples

set_option maxRecDepth 8192

/-- Two old points, related at both levels. -/
def base : PatternCode 4 where
  U := {1, 3}
  r₁ x y := decide (x ≤ y)
  r₂ x y := decide (x ≤ y)

/-- The same induced structure, with the irrelevant off-carrier entries erased. -/
def trimmedBase : PatternCode 4 where
  U := base.U
  r₁ x y := decide (x ∈ base.U ∧ y ∈ base.U ∧ x ≤ y)
  r₂ x y := decide (x ∈ base.U ∧ y ∈ base.U ∧ x ≤ y)

def arithmeticRule : RuleCertificate 4 := .arithmetic base trimmedBase

/-- Arithmetic rules can change the full tables outside their common carrier. -/
theorem arithmetic_accepts : arithmeticRule.check = true := by decide

theorem arithmetic_changes_off_carrier : base ≠ trimmedBase := by decide

/-- Removing the required reflexive edges makes even an identity rule invalid. -/
def nonPattern : PatternCode 4 where
  U := base.U
  r₁ _ _ := false
  r₂ _ _ := false

theorem arithmetic_rejects_nonpattern :
    (RuleCertificate.arithmetic nonPattern nonPattern).check = false := by decide

/-- A nonempty lower copy of the old point `1`. -/
def downwardRule : RuleCertificate 4 :=
  .downward base .two 1 3 {1} {0} (fun _ => 1)

theorem downward_accepts : downwardRule.check = true := by decide

theorem downward_adds_point : downwardRule.target.U = {0, 1, 3} := by decide

/-- Both levels of downward reflection have executable accepted certificates. -/
theorem downward_one_accepts :
    (RuleCertificate.downward base .one 1 3 {1} {0} (fun _ => 1)).check = true := by
  decide

/-- An old point cannot be supplied as a fresh lower copy. -/
theorem downward_rejects_old_new_overlap :
    (RuleCertificate.downward base .two 1 3 {1} {1} (fun _ => 1)).check = false := by
  decide

/-- A fresh point in the wrong gap also fails the placement hypotheses. -/
theorem downward_rejects_wrong_gap :
    (RuleCertificate.downward base .two 1 3 {1} {2} (fun _ => 1)).check = false := by
  decide

/-- The declared map must actually identify the copy with the selected old block. -/
theorem downward_rejects_wrong_matching :
    (RuleCertificate.downward base .two 1 3 {1} {0} (fun _ => 3)).check = false := by
  decide

/-- Reflect the earlier lower-copy rule upward, placing its new point at `2`. -/
def upwardRule : RuleCertificate 4 :=
  .upward downwardRule 1 3 {2} (fun _ => 0)

theorem upward_accepts : upwardRule.check = true := by decide

theorem upward_adds_point : upwardRule.target.U = {1, 2, 3} := by decide

theorem upward_rejects_old_new_overlap :
    (RuleCertificate.upward downwardRule 1 3 {1} (fun _ => 0)).check = false := by
  decide

theorem upward_rejects_wrong_matching :
    (RuleCertificate.upward downwardRule 1 3 {2} (fun _ => 1)).check = false := by
  decide

/-- A second genuine step inserts the lower copy into the upward extension. -/
def downwardAfterUpward : RuleCertificate 4 :=
  .downward upwardRule.target .two 1 3 {1} {0} (fun _ => 1)

theorem downward_after_upward_accepts : downwardAfterUpward.check = true := by decide

def joinedChain : ChainCertificate 4 :=
  .tail (.tail (.refl base) upwardRule) downwardAfterUpward

theorem chain_accepts_join : joinedChain.check = true := by decide

theorem chain_has_both_copies : joinedChain.target.U = Finset.univ := by decide

/-- The next rule is valid by itself, but its source is not the chain's endpoint. -/
theorem chain_rejects_wrong_join :
    (ChainCertificate.tail joinedChain arithmeticRule).check = false := by decide

theorem chain_rejects_nonpattern_refl :
    (ChainCertificate.refl nonPattern).check = false := by decide

/-- Discard the upper copy while retaining the lower one and both old points. -/
def restrictionRule : RuleCertificate 4 :=
  .finiteRestriction joinedChain downwardRule.target 1

theorem finite_restriction_accepts : restrictionRule.check = true := by decide

/-- Substructure alone is insufficient: clause four requires some new point. -/
theorem finite_restriction_rejects_identity :
    (RuleCertificate.finiteRestriction joinedChain base 1).check = false := by decide

/-- The new lower point is immediately below `1`, not immediately below `3`. -/
theorem finite_restriction_rejects_wrong_anchor :
    (RuleCertificate.finiteRestriction joinedChain downwardRule.target 3).check = false := by
  decide

/-- A chain can add points at two anchors, but clause four still requires one anchor. -/
theorem finite_restriction_rejects_two_anchors :
    (RuleCertificate.finiteRestriction joinedChain joinedChain.target 1).check = false := by
  decide

/-- Generation permits a final restriction that keeps the source and a new point. -/
def generation : GenerationCertificate 4 where
  chain := joinedChain
  target := downwardRule.target

theorem generation_accepts_restriction : generation.check = true := by decide

theorem generation_restriction_is_proper : generation.target.U ≠ joinedChain.target.U := by
  decide

def losesOldPoint : PatternCode 4 where
  U := {1}
  r₁ := base.r₁
  r₂ := base.r₂

/-- This is a substructure of the chain endpoint, but it omits the source point `3`. -/
theorem generation_rejects_missing_source :
    (GenerationCertificate.mk joinedChain losesOldPoint).check = false := by decide

/-- The final restriction must also preserve the endpoint's induced relations. -/
theorem generation_rejects_wrong_relations :
    (GenerationCertificate.mk joinedChain nonPattern).check = false := by decide

/-! A one-point ambient order keeps the exhaustive minimality search small:
there are exactly eight carrier-and-table codes and a single total map. -/

def singleton : PatternCode 1 where
  U := Finset.univ
  r₁ _ _ := true
  r₂ _ _ := true

def singletonNoEdges : PatternCode 1 where
  U := Finset.univ
  r₁ _ _ := false
  r₂ _ _ := false

def singletonArithmetic : RuleCertificate 1 := .arithmetic singleton singleton

def liftingRule : RuleCertificate 1 :=
  .lifting singletonArithmetic singleton singleton id id

/-- Acceptance includes exhaustive comparison with every fixed-carrier competitor. -/
theorem lifting_accepts : liftingRule.check = true := by decide

theorem lifting_rejects_invalid_embedding :
    (RuleCertificate.lifting singletonArithmetic singletonNoEdges singletonNoEdges id id).check =
      false := by
  decide

/-- Even with a valid base embedding, the proposed lifted endpoint must be a pattern. -/
theorem lifting_rejects_invalid_endpoint :
    (RuleCertificate.lifting singletonArithmetic singleton singletonNoEdges id id).check = false := by
  decide

/-- A two-point pattern with only reflexive relations. -/
def discretePair : PatternCode 2 where
  U := Finset.univ
  r₁ x y := decide (x = y)
  r₂ x y := decide (x = y)

/-- A candidate with the extra level-one edge `0 → 1`. -/
def orderedPair : PatternCode 2 where
  U := Finset.univ
  r₁ x y := decide (x ≤ y)
  r₂ x y := decide (x = y)

/-- The discrete pattern is a valid competitor on the candidate's carrier. -/
theorem minimality_competitor_is_lifting :
    PatternCode.checkLifting discretePair discretePair discretePair discretePair id id = true := by
  decide

/-- The extra candidate edge cannot be carried into that competitor by the identity. -/
theorem minimality_competitor_obstructs_covering :
    orderedPair.checkCoversInto discretePair id = false := by decide

/-- The exhaustive minimality predicate rejects this candidate. This check is
independent of whether the candidate itself satisfies the lifting predicate. -/
theorem minimality_rejects_extra_edge_candidate :
    PatternCode.checkMinimal discretePair discretePair discretePair orderedPair id = false := by
  decide

/-! Natural-number inputs are decoded before checking. Encode/decode identities
are rewritten first, avoiding reduction of enormous concrete numerals. -/

theorem pattern_nat_roundtrip :
    Encodable.decode (α := PatternCode 4) (Encodable.encode base) = some base :=
  Encodable.encodek base

theorem rule_nat_roundtrip :
    Encodable.decode (α := RuleCertificate 4) (Encodable.encode upwardRule) = some upwardRule :=
  Encodable.encodek upwardRule

theorem chain_nat_roundtrip :
    Encodable.decode (α := ChainCertificate 4) (Encodable.encode joinedChain) = some joinedChain :=
  Encodable.encodek joinedChain

theorem generation_nat_roundtrip :
    Encodable.decode (α := GenerationCertificate 4) (Encodable.encode generation) =
      some generation :=
  Encodable.encodek generation

theorem rule_nat_accepts :
    checkRule downwardRule.source downwardRule.target (Encodable.encode downwardRule) = true := by
  simp [checkRule, Encodable.encodek, downward_accepts]

theorem chain_nat_accepts :
    checkChain joinedChain.source joinedChain.target (Encodable.encode joinedChain) = true := by
  simp [checkChain, Encodable.encodek, chain_accepts_join]

theorem generation_nat_accepts :
    checkGeneration generation.source generation.target (Encodable.encode generation) = true := by
  simp [checkGeneration, Encodable.encodek, generation_accepts_restriction]

theorem rule_nat_rejects_wrong_source :
    checkRule trimmedBase downwardRule.target (Encodable.encode downwardRule) = false := by
  rw [checkRule, Encodable.encodek]
  decide

theorem rule_nat_rejects_wrong_target :
    checkRule base base (Encodable.encode downwardRule) = false := by
  rw [checkRule, Encodable.encodek]
  decide

theorem chain_nat_rejects_wrong_target :
    checkChain base base (Encodable.encode joinedChain) = false := by
  rw [checkChain, Encodable.encodek]
  decide

theorem generation_nat_rejects_wrong_target :
    checkGeneration base base (Encodable.encode generation) = false := by
  rw [checkGeneration, Encodable.encodek]
  decide

/-- Zero is genuinely malformed, independently of the claimed endpoints.
Kernel reduction also unfolds the derived decoder's auxiliary definitions. -/
theorem rule_decode_zero : Encodable.decode (α := RuleCertificate 4) 0 = none := by
  decide +kernel

theorem chain_decode_zero : Encodable.decode (α := ChainCertificate 4) 0 = none := by
  decide +kernel

theorem generation_decode_zero : Encodable.decode (α := GenerationCertificate 4) 0 = none := by
  decide +kernel

theorem rule_nat_rejects_zero : checkRule base base 0 = false := by
  rw [checkRule, rule_decode_zero]

theorem chain_nat_rejects_zero : checkChain base base 0 = false := by
  rw [checkChain, chain_decode_zero]

theorem generation_nat_rejects_zero : checkGeneration base base 0 = false := by
  rw [checkGeneration, generation_decode_zero]

/-- One audit entry point for the main successful and unsuccessful executions. -/
theorem regression_suite :
    arithmeticRule.check = true ∧
    (RuleCertificate.arithmetic nonPattern nonPattern).check = false ∧
    downwardRule.check = true ∧
    (RuleCertificate.downward base .one 1 3 {1} {0} (fun _ => 1)).check = true ∧
    (RuleCertificate.downward base .two 1 3 {1} {1} (fun _ => 1)).check = false ∧
    upwardRule.check = true ∧
    (RuleCertificate.upward downwardRule 1 3 {1} (fun _ => 0)).check = false ∧
    joinedChain.check = true ∧
    (ChainCertificate.tail joinedChain arithmeticRule).check = false ∧
    restrictionRule.check = true ∧
    (RuleCertificate.finiteRestriction joinedChain base 1).check = false ∧
    (RuleCertificate.finiteRestriction joinedChain joinedChain.target 1).check = false ∧
    generation.check = true ∧
    (GenerationCertificate.mk joinedChain losesOldPoint).check = false ∧
    liftingRule.check = true ∧
    (RuleCertificate.lifting singletonArithmetic singleton singletonNoEdges id id).check = false ∧
    PatternCode.checkMinimal discretePair discretePair discretePair orderedPair id = false ∧
    Encodable.decode (α := PatternCode 4) (Encodable.encode base) = some base ∧
    Encodable.decode (α := RuleCertificate 4) (Encodable.encode upwardRule) = some upwardRule ∧
    Encodable.decode (α := ChainCertificate 4) (Encodable.encode joinedChain) = some joinedChain ∧
    Encodable.decode (α := GenerationCertificate 4) (Encodable.encode generation) =
      some generation ∧
    checkRule downwardRule.source downwardRule.target (Encodable.encode downwardRule) = true ∧
    checkChain joinedChain.source joinedChain.target (Encodable.encode joinedChain) = true ∧
    checkGeneration generation.source generation.target (Encodable.encode generation) = true ∧
    checkRule trimmedBase downwardRule.target (Encodable.encode downwardRule) = false ∧
    checkRule base base (Encodable.encode downwardRule) = false ∧
    checkChain base base (Encodable.encode joinedChain) = false ∧
    checkGeneration base base (Encodable.encode generation) = false ∧
    Encodable.decode (α := RuleCertificate 4) 0 = none ∧
    Encodable.decode (α := ChainCertificate 4) 0 = none ∧
    Encodable.decode (α := GenerationCertificate 4) 0 = none ∧
    checkRule base base 0 = false ∧
    checkChain base base 0 = false ∧
    checkGeneration base base 0 = false :=
  ⟨arithmetic_accepts, arithmetic_rejects_nonpattern,
    downward_accepts, downward_one_accepts, downward_rejects_old_new_overlap,
    upward_accepts, upward_rejects_old_new_overlap,
    chain_accepts_join, chain_rejects_wrong_join,
    finite_restriction_accepts, finite_restriction_rejects_identity,
    finite_restriction_rejects_two_anchors,
    generation_accepts_restriction, generation_rejects_missing_source,
    lifting_accepts, lifting_rejects_invalid_endpoint,
    minimality_rejects_extra_edge_candidate,
    pattern_nat_roundtrip, rule_nat_roundtrip, chain_nat_roundtrip, generation_nat_roundtrip,
    rule_nat_accepts, chain_nat_accepts, generation_nat_accepts,
    rule_nat_rejects_wrong_source, rule_nat_rejects_wrong_target,
    chain_nat_rejects_wrong_target, generation_nat_rejects_wrong_target,
    rule_decode_zero, chain_decode_zero, generation_decode_zero,
    rule_nat_rejects_zero, chain_nat_rejects_zero, generation_nat_rejects_zero⟩

/-! The accepted examples reach the existing semantic calculus through the
proved soundness results, without adding any semantic premise to their data. -/

theorem checked_downward_is_generating_rule :
    Str.GeneratingRule downwardRule.source.toStr downwardRule.target.toStr :=
  downwardRule.sound downward_accepts

theorem checked_chain_exactly_generates :
    Str.ExactlyGenerates joinedChain.source.toStr joinedChain.target.toStr :=
  checkChain_sound chain_nat_accepts

theorem checked_restriction_generates :
    Str.Generates generation.source.toStr generation.target.toStr :=
  checkGeneration_sound generation_nat_accepts

end Alexander313.Carlson.Finite.CertificateExamples
