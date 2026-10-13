import Alexander313.Wilken.HereditaryNativeArithmetic
import Alexander313.Wilken.OrdinalRightSubtraction

/-!
# Genuine source dotted right subtraction on original native full sorts

Both ORIGINAL input codes are checked in the actual coded epsilon context.
The real native normalizer/ANF extractor supplies finite principal words.
Their suffix is matched by genuine equality of atom VALUES, using the actual
native comparator. If a<=b the result is admitted zero. Otherwise a complete
right suffix gives its left prefix; a failed match returns the normalized a.

Actual ANF normalization proves existence, leastness over EVERY ordinal g,
and no-solution necessity. Nothing is supplied as a suffix, minimality or
arithmetic oracle. The genuine prefix reconstruction is originally admitted,
weak normal and has literal height <=the original left input height, hence
stays in its original finite fragment. Uniform finite kernels and numerical
graphs are PR. This is the source dotted operation, distinct from existing
left removal (Mathlib d-c). Native spelling uniqueness is not asserted.
All proof terms are uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RightSubtraction

open ThetaCourse
open OrdinalRightSubtraction (suffixMatch)
open scoped Classical

def inputCheck (q c d : Nat) : Bool := Arithmetic.inputCheck q c d

theorem inputCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) := Arithmetic.inputCheck_primrec

theorem inputCheck_exact (q c d : Nat) : inputCheck q c d = true ↔
    checkCode q c = true ∧ checkCode q d = true := Arithmetic.inputCheck_exact q c d

def rightMatch (q c d : Nat) : List (RelativeTerm Nat) × Bool := suffixMatch (Comparison.equal q)
  (Arithmetic.normalizedWord q c) (Arithmetic.normalizedWord q d)

theorem rightMatch_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => rightMatch p.1 p.2.1 p.2.2) :=
  (OrdinalRightSubtraction.suffixMatch_primrec Normalization.zeroTree Comparison.equal
    Comparison.Effective.equal_primrec).comp (Primrec.fst.pair
      ((Arithmetic.normalizedWord_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        (Arithmetic.normalizedWord_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))

theorem rightMatch_values (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    ((rightMatch q c d).1.map (denote q), (rightMatch q c d).2) =
      suffixMatch (fun a b : Ordinal.{0} => decide (a = b))
        (canonicalANF (interpretation q c)) (canonicalANF (interpretation q d)) := by
  classical
  have hs := Arithmetic.normalizedWord_spec q c hc
  have ht := Arithmetic.normalizedWord_spec q d hd
  have he := OrdinalRightSubtraction.suffixMatch_map (Comparison.equal q) (denote q)
    (Arithmetic.normalizedWord q c) (Arithmetic.normalizedWord q d) (by
      intro a ha b hb
      have haa := hs.1 a ha
      have hbb := ht.1 b hb
      exact Comparison.equal_correct q a b haa.1 hbb.1 haa.2.1 hbb.2.1)
  simpa only [rightMatch, hs.2, ht.2] using he

theorem rightMatch_prefix (q c d : Nat) :
    ∃ after, Arithmetic.normalizedWord q c = (rightMatch q c d).1 ++ after :=
  OrdinalRightSubtraction.suffixMatch_prefix _ _ _

theorem rightMatch_mem (q c d : Nat) (a : RelativeTerm Nat)
    (ha : a ∈ (rightMatch q c d).1) : a ∈ Arithmetic.normalizedWord q c :=
  OrdinalRightSubtraction.suffixMatch_mem _ _ _ _ ha

theorem rightMatch_normal (q c d : Nat) (hc : checkCode q c = true) :
    IsAdditiveNormalForm ((rightMatch q c d).1.map (denote q)) := by
  obtain ⟨after, he⟩ := rightMatch_prefix q c d
  have hn := Arithmetic.normalizedWord_normal q c hc
  rw [he, List.map_append] at hn
  exact OrdinalRightSubtraction.anf_prefix hn

def word (q c d : Nat) : List (RelativeTerm Nat) := cond (Arithmetic.leCode q c d) []
  (cond (rightMatch q c d).2 (rightMatch q c d).1 (Arithmetic.normalizedWord q c))

theorem word_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => word p.1 p.2.1 p.2.2) :=
  Arithmetic.leCode_primrec.cond (Primrec.const [])
    ((Primrec.snd.comp rightMatch_primrec).cond (Primrec.fst.comp rightMatch_primrec)
      (Arithmetic.normalizedWord_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))

theorem word_mem (q c d : Nat) (a : RelativeTerm Nat) (ha : a ∈ word q c d) :
    a ∈ Arithmetic.normalizedWord q c := by
  cases hl : Arithmetic.leCode q c d with
  | true => simp only [word, hl, Bool.cond_true, List.not_mem_nil] at ha
  | false =>
    cases hm : (rightMatch q c d).2 with
    | true => exact rightMatch_mem q c d a (by simpa only [word, hl, hm, Bool.cond_false, Bool.cond_true] using ha)
    | false => simpa only [word, hl, hm, Bool.cond_false] using ha

theorem word_normal (q c d : Nat) (hc : checkCode q c = true) :
    IsAdditiveNormalForm ((word q c d).map (denote q)) := by
  cases hl : Arithmetic.leCode q c d with
  | true => simpa only [word, hl, Bool.cond_true, List.map_nil] using
      (additiveNormalForm_nil : IsAdditiveNormalForm ([] : List Ordinal.{0}))
  | false =>
    cases hm : (rightMatch q c d).2 with
    | true => simpa only [word, hl, hm, Bool.cond_false, Bool.cond_true] using rightMatch_normal q c d hc
    | false => simpa only [word, hl, hm, Bool.cond_false] using Arithmetic.normalizedWord_normal q c hc

theorem word_good (q n c d : Nat) (hc : checkCode q c = true) (hh : heightCode c ≤ n) :
    Normalization.GoodAtoms q n (word q c d) :=
  fun a ha => Arithmetic.normalizedWord_good q n c hc hh a (word_mem q c d a ha)

theorem word_value (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    principalSum ((word q c d).map (denote q)) =
      OrdinalRightSubtraction.rightSubtract (interpretation q c) (interpretation q d) := by
  classical
  cases hl : Arithmetic.leCode q c d with
  | true =>
    have hle := (Arithmetic.leCode_exact q c d hc hd).mp hl
    simp only [word, hl, Bool.cond_true, List.map_nil, principalSum,
      OrdinalRightSubtraction.rightSubtract_of_le _ _ hle]
  | false =>
    have hn : ¬ interpretation q c ≤ interpretation q d := by
      intro hle
      have ht := (Arithmetic.leCode_exact q c d hc hd).mpr hle
      simp only [hl, Bool.false_eq_true] at ht
    have hp := rightMatch_values q c d hc hd
    have hf := congrArg Prod.fst hp
    have hs := congrArg Prod.snd hp
    simp only [word, hl, Bool.cond_false, OrdinalRightSubtraction.rightSubtract, if_neg hn]
    rw [← hf, ← hs]
    cases hm : (rightMatch q c d).2 with
    | true => simp only [hm, Bool.cond_true]
    | false =>
      simp only [hm, Bool.cond_false]
      rw [(Arithmetic.normalizedWord_spec q c hc).2, principalSum_canonicalANF]

def rightTerm (q c d : Nat) : RelativeTerm Nat := Normalization.buildAtoms (word q c d)

theorem rightTerm_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => rightTerm p.1 p.2.1 p.2.2) :=
  Normalization.Effective.buildAtoms_primrec.comp word_primrec

theorem rightTerm_height (q c d : Nat) (hc : checkCode q c = true) :
    (rightTerm q c d).height ≤ heightCode c :=
  Height.buildAtoms_height_le _ _ (fun a ha => Arithmetic.normalizedWord_height q c hc a (word_mem q c d a ha))

theorem rightTerm_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    admissible q (heightCode c) (rightTerm q c d) ∧ Comparison.Normal q (rightTerm q c d) ∧
      denote q (rightTerm q c d) = OrdinalRightSubtraction.rightSubtract (interpretation q c) (interpretation q d) := by
  have hq := (Bool.and_eq_true.mp (Arithmetic.raw_checked q c hc)).1
  have hg := word_good q (heightCode c) c d hc le_rfl
  exact ⟨Normalization.buildAtoms_admissible q _ hq _ hg,
    Normalization.buildAtoms_normal q _ _ hg (word_normal q c d hc),
    (Normalization.buildAtoms_denote q _).trans (word_value q c d hc hd)⟩

def rightCode (q c d : Nat) : Nat := cond (inputCheck q c d) (rightTerm q c d).code 0

theorem rightCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => rightCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (code_primrec.comp rightTerm_primrec) (Primrec.const 0)

theorem rightCode_rejected (q c d : Nat) (h : inputCheck q c d = false) : rightCode q c d = 0 := by
  simp only [rightCode, h, Bool.cond_false]

theorem rightCode_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    Comparison.acceptedCode q (rightCode q c d) = true ∧
      interpretation q (rightCode q c d) = OrdinalRightSubtraction.rightSubtract (interpretation q c) (interpretation q d) ∧
      heightCode (rightCode q c d) ≤ heightCode c := by
  have hs := rightTerm_spec q c d hc hd
  have hq := (Bool.and_eq_true.mp (Arithmetic.raw_checked q c hc)).1
  have hi := (inputCheck_exact q c d).mpr ⟨hc, hd⟩
  simp only [rightCode, hi, Bool.cond_true, interpretation_code, heightCode_code]
  refine ⟨(Comparison.acceptedCode_exact q _).mpr ⟨?_, ?_⟩, hs.2.2, rightTerm_height q c d hc⟩
  · rw [checkCode_code]
    exact Comparison.admitted_checked q _ hq _ hs.1
  · simpa only [rawTree_code] using hs.2.1

/-- Literal source minimality quantifies over every ordinal solution, not
only admitted codes or the particular source grammar. -/
theorem rightCode_source (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    OrdinalRightSubtraction.SourceSpec (interpretation q c) (interpretation q d) (interpretation q (rightCode q c d)) := by
  rw [(rightCode_spec q c d hc hd).2.1]
  exact OrdinalRightSubtraction.rightSubtract_spec _ _

theorem rightCode_zero_of_le (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (h : interpretation q c ≤ interpretation q d) : interpretation q (rightCode q c d) = 0 := by
  rw [(rightCode_spec q c d hc hd).2.1, OrdinalRightSubtraction.rightSubtract_of_le _ _ h]

theorem rightCode_zero_right (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (h : interpretation q d = 0) : interpretation q (rightCode q c d) = interpretation q c := by
  rw [(rightCode_spec q c d hc hd).2.1, h, OrdinalRightSubtraction.rightSubtract_zero_right]

theorem rightCode_minimum (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hab : interpretation q d < interpretation q c)
    (hex : ∃ g : Ordinal.{0}, interpretation q c = g + interpretation q d) :
    interpretation q c = interpretation q (rightCode q c d) + interpretation q d ∧
      ∀ g : Ordinal.{0}, interpretation q c = g + interpretation q d → interpretation q (rightCode q c d) ≤ g := by
  rw [(rightCode_spec q c d hc hd).2.1]
  exact OrdinalRightSubtraction.rightSubtract_minimum _ _ hab hex

theorem rightCode_no_solution (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hab : interpretation q d < interpretation q c)
    (hn : ∀ g : Ordinal.{0}, interpretation q c ≠ g + interpretation q d) :
    interpretation q (rightCode q c d) = interpretation q c := by
  rw [(rightCode_spec q c d hc hd).2.1]
  exact OrdinalRightSubtraction.rightSubtract_no_solution _ _ hab hn

theorem rightCode_le (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    interpretation q (rightCode q c d) ≤ interpretation q c := by
  rw [(rightCode_spec q c d hc hd).2.1]
  exact OrdinalRightSubtraction.rightSubtract_le _ _

theorem rightCode_value_invariant (q c d c' d' : Nat)
    (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hc' : checkCode q c' = true) (hd' : checkCode q d' = true)
    (hec : interpretation q c = interpretation q c') (hed : interpretation q d = interpretation q d') :
    interpretation q (rightCode q c d) = interpretation q (rightCode q c' d') := by
  rw [(rightCode_spec q c d hc hd).2.1, (rightCode_spec q c' d' hc' hd').2.1, hec, hed]

theorem rightCode_fragment (q n c d : Nat) (hc : Height.fragmentCheck q n c = true) (hd : checkCode q d = true) :
    Height.fragmentCheck q n (rightCode q c d) = true := by
  have hi := (Height.fragmentCheck_exact q n c).mp hc
  have hs := rightCode_spec q c d hi.1 hd
  exact (Height.fragmentCheck_exact q n _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp hs.1).1, hs.2.2.trans hi.2⟩

/-- Every real source finite fragment retains admission and the same actual
dotted subtraction, not just a global value equation. -/
theorem rightCode_finite (q n : Nat) (hq : baseCheck q = true) (a b : RelativeTerm Nat)
    (ha : admissible q n a) (hb : admissible q n b) :
    admissible q n (rawTree (rightCode q a.code b.code)) ∧
      Comparison.Normal q (rawTree (rightCode q a.code b.code)) ∧
      finiteDenote q n (rawTree (rightCode q a.code b.code)) =
        OrdinalRightSubtraction.rightSubtract (finiteDenote q n a) (finiteDenote q n b) := by
  have hc : checkCode q a.code = true := by
    simpa only [checkCode_code] using Comparison.admitted_checked q n hq a ha
  have hd : checkCode q b.code = true := by
    simpa only [checkCode_code] using Comparison.admitted_checked q n hq b hb
  have hs := rightCode_spec q a.code b.code hc hd
  have ht := (Comparison.acceptedCode_exact q _).mp hs.1
  have hheight : heightCode (rightCode q a.code b.code) ≤ n := hs.2.2.trans
    (by simpa only [heightCode_code] using Height.admissible_height_le q n a ha)
  have hn := Comparison.checked_admissible q n (rawTree (rightCode q a.code b.code))
    (Arithmetic.raw_checked q _ ht.1) ((Height.input_heightCode q _ ht.1).le.trans hheight)
  refine ⟨hn, ht.2, ?_⟩
  have hv := (denote_eq_finite q n hq _ hn.2).symm.trans (Arithmetic.raw_value q _ ht.1)
  rw [hv, hs.2.1, interpretation_code, interpretation_code,
    denote_eq_finite q n hq a ha.2, denote_eq_finite q n hq b hb.2]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RightSubtraction
