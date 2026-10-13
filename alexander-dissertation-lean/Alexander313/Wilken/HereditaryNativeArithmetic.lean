import Alexander313.Wilken.HereditaryNativeHeight
import Alexander313.Wilken.HereditaryDifference

/-!
# Actual addition and left removal in native epsilon contexts

Addition normalizes the real written source sum. Left removal opens each
genuinely normalized principal word and removes equal initial VALUES using
the real native comparator. At a strict mismatch, actual principal closure
absorbs the remaining left word; the retained right suffix reconstructs the
unique result of c + result = d. This is the source notation -c+d from w2.txt,
lines 453-454, and Mathlib's d-c. The total checked-pair version returns admitted
zero on reversed pairs. The separately guarded ordered version retains the
source partial domain. It is not the source's distinct right subtraction c-d.

Every result retains original native admission, weak normality and actual
finite/global values. Addition has height at most the maximum input height;
left removal has height at most the right input height. The actual finite
parser therefore admits the constructed results in the original input
fragment. All kernels are uniform primitive recursive finite operations.
No native-public recoding, arithmetic or comparison oracle, unique spelling,
canonical ordinal-height law, multiplication or logarithm producer is used.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Arithmetic

open ThetaCourse

def inputCheck (q c d : Nat) : Bool := checkCode q c && checkCode q d

theorem inputCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (checkCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem inputCheck_exact (q c d : Nat) : inputCheck q c d = true ↔
    checkCode q c = true ∧ checkCode q d = true := Bool.and_eq_true

theorem raw_checked (q c : Nat) (hc : checkCode q c = true) : check q (rawTree c) = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  simpa only [rawTree_code] using ht

theorem raw_value (q c : Nat) (hc : checkCode q c = true) :
    denote q (rawTree c) = interpretation q c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  simp only [rawTree_code, interpretation_code]

def addTerm (q c d : Nat) : RelativeTerm Nat :=
  Normalization.normalize q (.sum (rawTree c) (rawTree d))

theorem addTerm_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => addTerm p.1 p.2.1 p.2.2) :=
  Normalization.Effective.normalize_primrec.comp Primrec.fst
    (sum_primrec.comp (rawTree_primrec.comp (Primrec.fst.comp Primrec.snd))
      (rawTree_primrec.comp (Primrec.snd.comp Primrec.snd)))

theorem addTerm_height (q c d : Nat) :
    (addTerm q c d).height ≤ max (rawTree c).height (rawTree d).height :=
  Height.normalize_height q (.sum (rawTree c) (rawTree d))

theorem addTerm_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    admissible q (max (heightCode c) (heightCode d)) (addTerm q c d) ∧
      Comparison.Normal q (addTerm q c d) ∧
      denote q (addTerm q c d) = interpretation q c + interpretation q d := by
  have hct := raw_checked q c hc
  have hdt := raw_checked q d hd
  have hq := (Bool.and_eq_true.mp hct).1
  let n := max (heightCode c) (heightCode d)
  have ha := Comparison.checked_admissible q n (rawTree c) hct
    ((Height.input_heightCode q c hc).le.trans (le_max_left _ _))
  have hb := Comparison.checked_admissible q n (rawTree d) hdt
    ((Height.input_heightCode q d hd).le.trans (le_max_right _ _))
  have hs : admissible q n (.sum (rawTree c) (rawTree d)) :=
    ⟨⟨ha.1, hb.1⟩, .sum ha.2 hb.2⟩
  have hn := Normalization.normalize_spec q n hq _ hs
  refine ⟨hn.1, hn.2.1, ?_⟩
  change denote q (Normalization.normalize q (.sum (rawTree c) (rawTree d))) = _
  rw [hn.2.2]
  change denote q (rawTree c) + denote q (rawTree d) = _
  rw [raw_value q c hc, raw_value q d hd]

def addCode (q c d : Nat) : Nat := cond (inputCheck q c d) (addTerm q c d).code 0

theorem addCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => addCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (code_primrec.comp addTerm_primrec) (Primrec.const 0)

theorem addCode_rejected (q c d : Nat) (h : inputCheck q c d = false) : addCode q c d = 0 := by
  simp only [addCode, h, Bool.cond_false]

theorem addCode_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    Comparison.acceptedCode q (addCode q c d) = true ∧
      interpretation q (addCode q c d) = interpretation q c + interpretation q d ∧
      heightCode (addCode q c d) ≤ max (heightCode c) (heightCode d) := by
  have hs := addTerm_spec q c d hc hd
  have hq := (Bool.and_eq_true.mp (raw_checked q c hc)).1
  have hi := (inputCheck_exact q c d).mpr ⟨hc, hd⟩
  simp only [addCode, hi, Bool.cond_true, interpretation_code, heightCode_code]
  refine ⟨(Comparison.acceptedCode_exact q _).mpr ⟨?_, ?_⟩, hs.2.2, ?_⟩
  · rw [checkCode_code]
    exact Comparison.admitted_checked q _ hq _ hs.1
  · simpa only [rawTree_code] using hs.2.1
  · simpa only [Height.input_heightCode q c hc, Height.input_heightCode q d hd] using
      addTerm_height q c d

def normalizedWord (q c : Nat) : List (RelativeTerm Nat) :=
  Decomposition.word (Normalization.normalizeCode q c)

theorem normalizedWord_primrec : Primrec₂ normalizedWord :=
  (Decomposition.word_primrec.comp Normalization.Effective.normalizeCode_primrec).to₂

theorem normalizedWord_spec (q c : Nat) (hc : checkCode q c = true) :
    (∀ a ∈ normalizedWord q c, check q a = true ∧ Comparison.Normal q a ∧
      0 < denote q a ∧ Ordinal.IsPrincipal (· + ·) (denote q a)) ∧
      (normalizedWord q c).map (denote q) = canonicalANF (interpretation q c) := by
  have hs := Normalization.normalizeCode_accepted q c hc
  have hw := Decomposition.word_spec q _ hs.1
  exact ⟨hw.1, hw.2.trans (congrArg canonicalANF hs.2)⟩

theorem normalizedWord_normal (q c : Nat) (hc : checkCode q c = true) :
    IsAdditiveNormalForm ((normalizedWord q c).map (denote q)) := by
  rw [(normalizedWord_spec q c hc).2]
  exact canonicalANF_normal _

theorem normalizedWord_height (q c : Nat) (hc : checkCode q c = true)
    (a : RelativeTerm Nat) (ha : a ∈ normalizedWord q c) : a.height ≤ heightCode c := by
  have hn := Normalization.normalizeCode_checked q c hc
  exact (Height.word_height _ a ha).trans
    ((Height.input_heightCode q _ hn.1).le.trans (Height.normalizeCode_height q c hc))

theorem normalizedWord_good (q n c : Nat) (hc : checkCode q c = true) (hh : heightCode c ≤ n) :
    Normalization.GoodAtoms q n (normalizedWord q c) := by
  intro a ha
  have hs := (normalizedWord_spec q c hc).1 a ha
  exact ⟨Comparison.checked_admissible q n a hs.1 ((normalizedWord_height q c hc a ha).trans hh),
    hs.2.1, hs.2.2⟩

def differenceWord (q c d : Nat) : List (RelativeTerm Nat) :=
  Difference.removeCommon (Comparison.equal q) (normalizedWord q c) (normalizedWord q d)

theorem differenceWord_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => differenceWord p.1 p.2.1 p.2.2) :=
  (Difference.removeCommon_primrec Normalization.zeroTree Comparison.equal
    Comparison.Effective.equal_primrec).comp (Primrec.fst.pair
      ((normalizedWord_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        (normalizedWord_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))

theorem differenceWord_mem (q c d : Nat) (a : RelativeTerm Nat)
    (ha : a ∈ differenceWord q c d) : a ∈ normalizedWord q d :=
  Difference.removeCommon_mem _ _ _ _ ha

theorem differenceWord_normal (q c d : Nat) (hd : checkCode q d = true) :
    IsAdditiveNormalForm ((differenceWord q c d).map (denote q)) :=
  Difference.removeCommon_normal _ _ _ _ (normalizedWord_normal q d hd)

theorem differenceWord_add (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hle : interpretation q c ≤ interpretation q d) :
    interpretation q c + principalSum ((differenceWord q c d).map (denote q)) = interpretation q d := by
  have hs := normalizedWord_spec q c hc
  have ht := normalizedWord_spec q d hd
  have h := Difference.removeCommon_add (Comparison.equal q) (denote q)
    (normalizedWord q c) (normalizedWord q d) (normalizedWord_normal q c hc)
    (normalizedWord_normal q d hd) (by
      intro a ha b hb
      have haa := hs.1 a ha
      have hbb := ht.1 b hb
      exact Comparison.equal_correct q a b haa.1 hbb.1 haa.2.1 hbb.2.1)
    (by simpa only [hs.2, ht.2, principalSum_canonicalANF] using hle)
  simpa only [hs.2, ht.2, principalSum_canonicalANF, differenceWord] using h

def leCode (q c d : Nat) : Bool := !Normalization.lessRawCode q d c

theorem leCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => leCode p.1 p.2.1 p.2.2) :=
  Primrec.not.comp (Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd))))

theorem leCode_exact (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    leCode q c d = true ↔ interpretation q c ≤ interpretation q d := by
  have he := Normalization.lessRawCode_exact q d c
  cases h : Normalization.lessRawCode q d c with
  | false =>
    have hle : interpretation q c ≤ interpretation q d := le_of_not_gt (by
      intro hdc
      have htrue := he.mpr ⟨hd, hc, hdc⟩
      simp only [h, Bool.false_eq_true] at htrue)
    simp only [leCode, h, Bool.not_false, Bool.true_eq_true, true_iff]
    exact hle
  | true =>
    have hdc := (he.mp h).2.2
    simp only [leCode, h, Bool.not_true, Bool.false_eq_true, false_iff]
    exact not_le_of_gt hdc

def orderedCheck (q c d : Nat) : Bool := inputCheck q c d && leCode q c d

theorem orderedCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => orderedCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp inputCheck_primrec leCode_primrec

theorem orderedCheck_exact (q c d : Nat) : orderedCheck q c d = true ↔
    checkCode q c = true ∧ checkCode q d = true ∧ interpretation q c ≤ interpretation q d := by
  constructor
  · intro h
    obtain ⟨hi, hl⟩ := Bool.and_eq_true.mp h
    obtain ⟨hc, hd⟩ := (inputCheck_exact q c d).mp hi
    exact ⟨hc, hd, (leCode_exact q c d hc hd).mp hl⟩
  · rintro ⟨hc, hd, hl⟩
    exact Bool.and_eq_true.mpr ⟨(inputCheck_exact q c d).mpr ⟨hc, hd⟩,
      (leCode_exact q c d hc hd).mpr hl⟩

def subtractTerm (q c d : Nat) : RelativeTerm Nat :=
  cond (leCode q c d) (Normalization.buildAtoms (differenceWord q c d)) Normalization.zeroTree

theorem subtractTerm_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => subtractTerm p.1 p.2.1 p.2.2) :=
  leCode_primrec.cond (Normalization.Effective.buildAtoms_primrec.comp differenceWord_primrec)
    (Primrec.const Normalization.zeroTree)

theorem subtractTerm_height (q c d : Nat) (hd : checkCode q d = true) :
    (subtractTerm q c d).height ≤ heightCode d := by
  cases hl : leCode q c d with
  | false =>
    simp only [subtractTerm, hl, Bool.cond_false]
    exact Nat.zero_le _
  | true =>
    simp only [subtractTerm, hl, Bool.cond_true]
    exact Height.buildAtoms_height_le _ _ (fun a ha =>
      normalizedWord_height q d hd a (differenceWord_mem q c d a ha))

theorem subtractTerm_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    admissible q (heightCode d) (subtractTerm q c d) ∧ Comparison.Normal q (subtractTerm q c d) ∧
      denote q (subtractTerm q c d) = interpretation q d - interpretation q c := by
  have hq := (Bool.and_eq_true.mp (raw_checked q d hd)).1
  cases hl : leCode q c d with
  | false =>
    have hnot : ¬ interpretation q c ≤ interpretation q d := by
      intro h
      have hb := (leCode_exact q c d hc hd).mpr h
      simp only [hl, Bool.false_eq_true] at hb
    have hv : interpretation q d - interpretation q c = 0 :=
      Ordinal.sub_eq_zero_iff_le.mpr (lt_of_not_ge hnot).le
    simpa only [subtractTerm, hl, Bool.cond_false, Normalization.zeroTree_denote, hv] using
      (show admissible q (heightCode d) Normalization.zeroTree ∧
        Comparison.Normal q Normalization.zeroTree ∧ (0 : Ordinal.{0}) = 0 from
        ⟨Normalization.zeroTree_admissible q _ hq, Normalization.zeroTree_normal q, rfl⟩)
  | true =>
    have hle := (leCode_exact q c d hc hd).mp hl
    have hg : Normalization.GoodAtoms q (heightCode d) (differenceWord q c d) :=
      fun a ha => normalizedWord_good q _ d hd le_rfl a (differenceWord_mem q c d a ha)
    have ha := Normalization.buildAtoms_admissible q (heightCode d) hq _ hg
    have hn := Normalization.buildAtoms_normal q (heightCode d) _ hg (differenceWord_normal q c d hd)
    have hs : interpretation q c + denote q (Normalization.buildAtoms (differenceWord q c d)) =
        interpretation q d := by
      rw [Normalization.buildAtoms_denote]
      exact differenceWord_add q c d hc hd hle
    have hv := (Ordinal.sub_eq_of_add_eq hs).symm
    simpa only [subtractTerm, hl, Bool.cond_true] using ⟨ha, hn, hv⟩

def subtractCode (q c d : Nat) : Nat := cond (inputCheck q c d) (subtractTerm q c d).code 0

theorem subtractCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => subtractCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (code_primrec.comp subtractTerm_primrec) (Primrec.const 0)

theorem subtractCode_rejected (q c d : Nat) (h : inputCheck q c d = false) : subtractCode q c d = 0 := by
  simp only [subtractCode, h, Bool.cond_false]

theorem subtractCode_spec (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true) :
    Comparison.acceptedCode q (subtractCode q c d) = true ∧
      interpretation q (subtractCode q c d) = interpretation q d - interpretation q c ∧
      heightCode (subtractCode q c d) ≤ heightCode d := by
  have hs := subtractTerm_spec q c d hc hd
  have hq := (Bool.and_eq_true.mp (raw_checked q d hd)).1
  have hi := (inputCheck_exact q c d).mpr ⟨hc, hd⟩
  simp only [subtractCode, hi, Bool.cond_true, interpretation_code, heightCode_code]
  refine ⟨(Comparison.acceptedCode_exact q _).mpr ⟨?_, ?_⟩, hs.2.2, subtractTerm_height q c d hd⟩
  · rw [checkCode_code]
    exact Comparison.admitted_checked q _ hq _ hs.1
  · simpa only [rawTree_code] using hs.2.1

theorem subtractCode_add (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hle : interpretation q c ≤ interpretation q d) :
    interpretation q c + interpretation q (subtractCode q c d) = interpretation q d := by
  rw [(subtractCode_spec q c d hc hd).2.1]
  exact Ordinal.add_sub_cancel_of_le hle

theorem subtractCode_add_unique (q c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hle : interpretation q c ≤ interpretation q d) (xi : Ordinal.{0})
    (hxi : interpretation q c + xi = interpretation q d) :
    xi = interpretation q (subtractCode q c d) :=
  add_left_cancel (hxi.trans (subtractCode_add q c d hc hd hle).symm)

theorem addCode_fragment (q n c d : Nat) (hc : Height.fragmentCheck q n c = true)
    (hd : Height.fragmentCheck q n d = true) : Height.fragmentCheck q n (addCode q c d) = true := by
  have ha := (Height.fragmentCheck_exact q n c).mp hc
  have hb := (Height.fragmentCheck_exact q n d).mp hd
  have hs := addCode_spec q c d ha.1 hb.1
  exact (Height.fragmentCheck_exact q n _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp hs.1).1, hs.2.2.trans (max_le ha.2 hb.2)⟩

theorem subtractCode_fragment (q n c d : Nat) (hc : checkCode q c = true)
    (hd : Height.fragmentCheck q n d = true) : Height.fragmentCheck q n (subtractCode q c d) = true := by
  have hb := (Height.fragmentCheck_exact q n d).mp hd
  have hs := subtractCode_spec q c d hc hb.1
  exact (Height.fragmentCheck_exact q n _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp hs.1).1, hs.2.2.trans hb.2⟩

theorem arithmetic_finite_values (q n c d : Nat) (hc : Height.fragmentCheck q n c = true)
    (hd : Height.fragmentCheck q n d = true) :
    finiteDenote q n (rawTree (addCode q c d)) = finiteDenote q n (rawTree c) + finiteDenote q n (rawTree d) ∧
      finiteDenote q n (rawTree (subtractCode q c d)) = finiteDenote q n (rawTree d) - finiteDenote q n (rawTree c) := by
  have ha := (Height.fragmentCheck_exact q n c).mp hc
  have hb := (Height.fragmentCheck_exact q n d).mp hd
  have hs := addCode_spec q c d ha.1 hb.1
  have ht := subtractCode_spec q c d ha.1 hb.1
  have ho := (Height.fragmentCheck_exact q n _).mp (addCode_fragment q n c d hc hd)
  have hp := (Height.fragmentCheck_exact q n _).mp (subtractCode_fragment q n c d ha.1 hd)
  have hq := (Bool.and_eq_true.mp (raw_checked q c ha.1)).1
  have agree : ∀ e, checkCode q e = true → heightCode e ≤ n →
      finiteDenote q n (rawTree e) = interpretation q e := by
    intro e he hh
    have adm := Comparison.checked_admissible q n (rawTree e) (raw_checked q e he)
      ((Height.input_heightCode q e he).le.trans hh)
    exact (denote_eq_finite q n hq _ adm.2).symm.trans (raw_value q e he)
  rw [agree _ ho.1 ho.2, agree _ hp.1 hp.2, agree c ha.1 ha.2, agree d hb.1 hb.2]
  exact ⟨hs.2.1, ht.2.1⟩

theorem arithmetic_values_invariant (q c d c' d' : Nat)
    (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hc' : checkCode q c' = true) (hd' : checkCode q d' = true)
    (hec : interpretation q c = interpretation q c') (hed : interpretation q d = interpretation q d') :
    interpretation q (addCode q c d) = interpretation q (addCode q c' d') ∧
      interpretation q (subtractCode q c d) = interpretation q (subtractCode q c' d') := by
  rw [(addCode_spec q c d hc hd).2.1, (addCode_spec q c' d' hc' hd').2.1,
    (subtractCode_spec q c d hc hd).2.1, (subtractCode_spec q c' d' hc' hd').2.1, hec, hed]
  exact ⟨rfl, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Arithmetic
