import Alexander313.Carlson.RationalAmalgamation
import Alexander313.Carlson.CoreTallness
import Alexander313.Carlson.ExactnessExamples

/-!
# A finite presented amalgamation of unequal least input images

The singleton input and the strict two-point R2 input both use rational
label 0. Their least ordinal copies assign different labels to that point.
The constructed rational amalgamation must separate the two images and
retain the strict R2 edge, including its false reverse.
-/

noncomputable section

namespace Alexander313.Carlson

private def singletonChainFamily (i : Fin 2) : Str ℚ :=
  Fin.cases (rationalFullChain 1) (fun _ => rationalFullChain 2) i

/-- A real finite-edge witness, with an additional point before the strict
R2 pair, exercises generation transport beyond identity endpoint maps. -/
theorem singleton_chain_presented_amalgamation :
    ∃ (Q : Finite.RationalPresentation) (f : Fin 2 → ℚ → ℚ),
      Str.Amalgamation singletonChainFamily Q.toStr f ∧
      f 0 0 < f 1 0 ∧ f 1 0 < f 1 1 ∧
      Q.toStr.r₂ (f 1 0) (f 1 1) ∧ ¬Q.toStr.r₂ (f 1 1) (f 1 0) := by
  have hP : ∀ i, (singletonChainFamily i).IsPattern :=
    Fin.cases (rationalFullChain_isPattern 1) (fun _ => rationalFullChain_isPattern 2)
  obtain ⟨Q, f, d⟩ := exists_presented_amalgamation singletonChainFamily hP
  let A := PatternRealization.ofPattern (rationalFullChain 1) (rationalFullChain_isPattern 1)
  let C := PatternRealization.ofPattern (rationalFullChain 2) (rationalFullChain_isPattern 2)
  let B := PatternRealization.ofPattern Q.toStr d.pattern
  have hA0 : A.label 0 = 0 := by
    apply (singleton_isominimal_iff_zero _).mp
    simpa only [rationalFullChain, Finset.range_one, Finset.image_singleton,
      Nat.cast_zero] using A.image_isominimal
  have hz : (0 : ℚ) ∈ (rationalFullChain 2).U := rationalFullChain_mem (by decide : 0 < 2)
  have ho : (1 : ℚ) ∈ (rationalFullChain 2).U := rationalFullChain_mem (by decide : 1 < 2)
  have hz' : (0 : ℚ) ∈ (rationalFullChain 1).U := rationalFullChain_mem (by decide : 0 < 1)
  have hc01 : C.label 0 < C.label 1 := C.seed_isIso.2.1 0 hz 1 ho (by norm_num)
  have hcR : R1 (C.label 0) (C.label 1) :=
    C.seed_covering.2.1 0 hz 1 ho (by change (0 : ℚ) ≤ 1; norm_num)
  have hcpos : 0 < C.label 0 := positive_of_strict_first hcR hc01
  have h0 : B.label (f 0 0) = A.label 0 :=
    (d.embeddings 0).exact_least_copy_agrees (hxExact := d.exact 0) (A := A) (B := B) 0 hz'
  have h10 : B.label (f 1 0) = C.label 0 :=
    (d.embeddings 1).exact_least_copy_agrees (hxExact := d.exact 1) (A := C) (B := B) 0 hz
  have h11 : B.label (f 1 1) = C.label 1 :=
    (d.embeddings 1).exact_least_copy_agrees (hxExact := d.exact 1) (A := C) (B := B) 1 ho
  have hbefore : f 0 0 < f 1 0 :=
    (B.seed_isIso.lt_iff (d.mem 0 hz') (d.mem 1 hz)).mp (by rw [h0, h10, hA0]; exact hcpos)
  have hstrict : f 1 0 < f 1 1 :=
    (B.seed_isIso.lt_iff (d.mem 1 hz) (d.mem 1 ho)).mp (by rw [h10, h11]; exact hc01)
  refine ⟨Q, f, d, hbefore, hstrict, ?_, ?_⟩
  · exact ((d.embeddings 1).2.2 0 hz 1 ho).2.mp (by change (0 : ℚ) ≤ 1; norm_num)
  · intro hreverse
    have hle := d.pattern.le₁ _ (d.mem 1 ho) _ (d.mem 1 hz)
      (d.pattern.sub₂ _ (d.mem 1 ho) _ (d.mem 1 hz) hreverse)
    exact (not_le_of_gt hstrict) hle

end Alexander313.Carlson
