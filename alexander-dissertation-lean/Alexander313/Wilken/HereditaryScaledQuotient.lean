import Alexander313.Wilken.HereditaryExactDivision

/-!
# Executing the scaled exact quotient in relative tracking

The arithmetic preparation in note 27 section 7 is b*((1/a)*z).
This file executes the genuine positive-left exact quotient and then the
actual ordinal multiplier. Its exact domain retains all three original
inputs, positive a, and literal quotient existence. The latter is derived
as the halting domain of the existing certificate search, not a decision
oracle. A real multiplicative-principal cap bounds the scaled result when
the stated real caller inequalities hold. Actual tracking reach bounds and
temporary-base conversion are still separate unfinished constructions.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.ScaledQuotient

def SourceDomain (a b z : Nat) : Prop :=
  unionCheck b = true ∧ ExactDivision.SourceDomain a z

/-- Input encodes ((a,b),z); the quotient code is an actual returned result. -/
def evaluation (input : Nat) : Part Nat :=
  cond (unionCheck input.unpair.1.unpair.2)
    ((ExactDivision.divide input.unpair.1.unpair.1 input.unpair.2).bind
      (Multiplication.multiply input.unpair.1.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have hi := Primrec.unpair
  have hab := Primrec.unpair.comp (Primrec.fst.comp hi)
  have ha := Primrec.fst.comp hab
  have hb := Primrec.snd.comp hab
  have hz := Primrec.snd.comp hi
  have hdiv := ExactDivision.divide_partrec.comp ha.to_comp hz.to_comp
  have hmul : Partrec₂ (fun (input : Nat) (d : Nat) =>
      Multiplication.multiply input.unpair.1.unpair.2 d) :=
    (Multiplication.multiply_partrec.comp (hb.comp Primrec.fst).to_comp Computable.snd).to₂
  exact Partrec.cond (Uniform.unionCheck_primrec.comp hb).to_comp
    (hdiv.bind hmul) Partrec.none

def scale (a b z : Nat) : Part Nat := evaluation (Nat.pair (Nat.pair a b) z)

theorem scale_partrec : Partrec (fun p : (Nat × Nat) × Nat => scale p.1.1 p.1.2 p.2) :=
  evaluation_partrec.comp
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp

theorem scale_eq (a b z : Nat) : scale a b z =
    cond (unionCheck b) ((ExactDivision.divide a z).bind (Multiplication.multiply b)) Part.none := by
  simp only [scale, evaluation, Nat.unpair_pair]

def OutputSpec (a b z c : Nat) : Prop :=
  SourceDomain a b z ∧ Canonical.check c = true ∧
    ∃ δ : Ordinal.{0}, unionInterpretation a * δ = unionInterpretation z ∧
      unionInterpretation c = unionInterpretation b * δ

theorem scale_value (a b z c : Nat) (hc : c ∈ scale a b z) : OutputSpec a b z c := by
  rw [scale_eq] at hc
  cases hb : unionCheck b with
  | false =>
    have hf : False := by simpa only [hb, Bool.cond_false, Part.notMem_none] using hc
    exact hf.elim
  | true =>
    simp only [hb, Bool.cond_true] at hc
    obtain ⟨d, hd, hm⟩ := Part.mem_bind_iff.mp hc
    have hs := ExactDivision.divide_value a z d hd
    have ht := Multiplication.multiply_value b d c hm
    refine ⟨⟨hb, hs.1, hs.2.1, hs.2.2.1, unionInterpretation d, hs.2.2.2.2⟩,
      ht.2.2.1, unionInterpretation d, hs.2.2.2.2, ht.2.2.2⟩

theorem scale_returns (a b z : Nat) (h : SourceDomain a b z) :
    ∃ c, c ∈ scale a b z ∧ OutputSpec a b z c := by
  obtain ⟨d, hd, hdc, _⟩ := ExactDivision.divide_returns a z h.2
  obtain ⟨c, hc, _, _⟩ := Multiplication.multiply_returns b d h.1 (Canonical.check_original hdc)
  have hm : c ∈ scale a b z := by
    rw [scale_eq, h.1]
    exact Part.mem_bind hd hc
  exact ⟨c, hm, scale_value a b z c hm⟩

theorem scale_domain (a b z : Nat) : (scale a b z).Dom ↔ SourceDomain a b z := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp hd
    exact (scale_value a b z c hc).1
  · intro h
    obtain ⟨c, hc, _⟩ := scale_returns a b z h
    exact Part.dom_iff_mem.mpr ⟨c, hc⟩

theorem spec_unique (a b z c d : Nat) (hc : OutputSpec a b z c) (hd : OutputSpec a b z d) : c = d := by
  obtain ⟨δ, hδ, hcv⟩ := hc.2.2
  obtain ⟨ε, hε, hdv⟩ := hd.2.2
  have he : δ = ε := MultiplicativePrincipalArithmetic.positive_mul_injective
    hc.1.2.2.2.1 (hδ.trans hε.symm)
  apply Canonical.check_value_injective c d hc.2.1 hd.2.1
  rw [hcv, hdv, he]

theorem scale_graph_iff (a b z c : Nat) : c ∈ scale a b z ↔ OutputSpec a b z c := by
  constructor
  · exact scale_value a b z c
  · intro hs
    obtain ⟨d, hd, hds⟩ := scale_returns a b z hs.1
    rw [spec_unique a b z c d hs hds]
    exact hd

theorem scale_unique (a b z : Nat) (h : SourceDomain a b z) : ∃! c, c ∈ scale a b z := by
  obtain ⟨c, hc, hs⟩ := scale_returns a b z h
  exact ⟨c, hc, fun d hd => spec_unique a b z d c (scale_value a b z d hd) hs⟩

theorem scale_original (a b z c : Nat) (hc : c ∈ scale a b z) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := (scale_value a b z c hc).2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem scale_every_solution (a b z c : Nat) (hc : c ∈ scale a b z)
    (δ : Ordinal.{0}) (he : unionInterpretation a * δ = unionInterpretation z) :
    unionInterpretation c = unionInterpretation b * δ := by
  have hs := scale_value a b z c hc
  obtain ⟨ε, hε, hv⟩ := hs.2.2
  have hδ : ε = δ := MultiplicativePrincipalArithmetic.positive_mul_injective
    hs.1.2.2.2.1 (hε.trans he.symm)
  rw [hv, hδ]

theorem scale_invariant (a b z a' b' z' c d : Nat)
    (hc : c ∈ scale a b z) (hd : d ∈ scale a' b' z')
    (ha : unionInterpretation a = unionInterpretation a')
    (hb : unionInterpretation b = unionInterpretation b')
    (hz : unionInterpretation z = unionInterpretation z') : c = d := by
  have hs := scale_value a b z c hc
  have ht := scale_value a' b' z' d hd
  obtain ⟨δ, hδ, hcv⟩ := hs.2.2
  obtain ⟨ε, hε, hdv⟩ := ht.2.2
  have he : δ = ε := MultiplicativePrincipalArithmetic.positive_mul_injective hs.1.2.2.2.1
    (hδ.trans (hz.trans (by rw [ha]; exact hε.symm)))
  apply Canonical.check_value_injective c d hs.2.1 ht.2.1
  rw [hcv, hdv, hb, he]

/-- Real positive multiplication reflects the caller's strict reach bound. -/
theorem quotient_lt_cap {a z δ cap : Ordinal.{0}} (ha : 0 < a)
    (he : a * δ = z) (hz : z < a * cap) : δ < cap := by
  apply lt_of_not_ge
  intro hge
  have hm := (MultiplicativePrincipalArithmetic.positive_mul_strictMono ha).monotone hge
  rw [he] at hm
  exact (not_le_of_gt hz) hm

/-- This proves the actual scaled return bound from a genuine multiplicative
cap; it does not construct the source tracking reach inequalities. -/
theorem scale_below_cap (a b z c : Nat) (hc : c ∈ scale a b z)
    (cap : Ordinal.{0}) (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal cap)
    (hb : unionInterpretation b < cap)
    (hz : unionInterpretation z < unionInterpretation a * cap) : unionInterpretation c < cap := by
  have hs := scale_value a b z c hc
  obtain ⟨δ, hδ, hcv⟩ := hs.2.2
  rw [hcv]
  exact hm.2.2 hb (quotient_lt_cap hs.1.2.2.2.1 hδ hz)

theorem scale_below_conversion_bound (a b z c : Nat) (hc : c ∈ scale a b z)
    (cap bound : Ordinal.{0}) (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal cap)
    (hb : unionInterpretation b < cap) (hz : unionInterpretation z < unionInterpretation a * cap)
    (hbound : cap ≤ bound) : unionInterpretation c < bound :=
  (scale_below_cap a b z c hc cap hm hb hz).trans_le hbound

end Alexander313.Wilken.RelativeTerm.Hereditary.ScaledQuotient
