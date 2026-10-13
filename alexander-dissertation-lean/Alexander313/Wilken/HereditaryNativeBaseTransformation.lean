import Alexander313.Wilken.HereditaryNativeBaseTransformationSupport
import Alexander313.Wilken.HereditaryNativeArithmetic

/-!
# Executing change to a smaller coded epsilon base

The context is external to a native word, so pi keeps its literal parameters
and theta indices. Its denotation changes from the real collapse at q to the
real collapse at v. The exact guard is original admission at q, an originally
coded epsilon v below q, and the atomic-stop bound on the chosen presentation.
Target admission is proved from that bound; it is not an extra caller oracle.

The actual comparator gives order and equality preservation at the two bases.
Raw terms are handled by the constructed common normalizer, and genuine native
addition has the same literal normalized output at both bases. Every target
admitted word has an original source preimage. These are the epsilon-target
part of the finite native pi construction. The target 1, unique printed Par
sets across alternate spellings, localization/zeta/chi commutation, iota and
mu are not claimed. All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseTransformation

open ThetaCourse

def inputCheck (q v c : Nat) : Bool := (checkCode q c && checkCode v c) && parameterCheck q v

theorem inputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.and.comp (checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (checkCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
      (parameterCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))

theorem inputCheck_checks (q v c : Nat) (h : inputCheck q v c = true) :
    checkCode q c = true ∧ checkCode v c = true ∧ base v < base q := by
  have hs := Bool.and_eq_true.mp h
  have hc := Bool.and_eq_true.mp hs.1
  exact ⟨hc.1, hc.2, ((parameterCheck_exact q v).mp hs.2).2.2⟩

theorem inputCheck_exact (q v c : Nat) : inputCheck q v c = true ↔
    checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
      ParBounded q v (rawTree c) := by
  constructor
  · intro h
    obtain ⟨hc, hd, hl⟩ := inputCheck_checks q v c h
    have ht := Arithmetic.raw_checked v c hd
    have hv := (Bool.and_eq_true.mp ht).1
    exact ⟨hc, hv, hl, (parBounded_iff_payloads q v _ (Arithmetic.raw_checked q c hc) hv).mpr
      (checked_admissible v _ ht).1⟩
  · rintro ⟨hc, hv, hl, hp⟩
    obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
    have hpt : Payloads v t := (parBounded_iff_payloads q v t ht hv).mp
      (by simpa only [rawTree_code] using hp)
    have hvcheck : checkCode v t.code = true := by
      simpa only [checkCode_code] using check_change q v t ht hv hpt
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hc, hvcheck⟩,
      (parameterCheck_exact q v).mpr ⟨((baseCheck_exact v).mp hv).1,
        ((baseCheck_exact q).mp (Bool.and_eq_true.mp ht).1).1, hl⟩⟩

theorem payloads_larger (q v : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (hv : baseCheck v = true) (hl : base q ≤ base v) : Payloads v t := by
  apply (payloads_iff_parameters v t).mpr
  intro p hp
  have hs := checked_parameters q t ht p hp
  exact (parameterCheck_exact v p).mpr
    ⟨hs.1, ((baseCheck_exact v).mp hv).1, hs.2.trans_le hl⟩

theorem target_preimage (q v c : Nat) (hq : baseCheck q = true)
    (hl : base v < base q) (hc : checkCode v c = true) : inputCheck q v c = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact v c).mp hc
  have hqt := check_change v q t ht hq (payloads_larger v q t ht hq hl.le)
  exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr
    ⟨by simpa only [checkCode_code] using hqt, hc⟩,
      (parameterCheck_exact q v).mpr ⟨((baseCheck_exact v).mp (Bool.and_eq_true.mp ht).1).1,
        ((baseCheck_exact q).mp hq).1, hl⟩⟩

def normalInputCheck (q v c : Nat) : Bool := inputCheck q v c && Comparison.acceptedCode q c

theorem normalInputCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => normalInputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp inputCheck_primrec
    (Comparison.acceptedCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem normalInputCheck_exact (q v c : Nat) : normalInputCheck q v c = true ↔
    inputCheck q v c = true ∧ Comparison.Normal q (rawTree c) := by
  simp only [normalInputCheck, Bool.and_eq_true, Comparison.acceptedCode_exact]
  constructor
  · rintro ⟨hi, hc, hn⟩; exact ⟨hi, hn⟩
  · rintro ⟨hi, hn⟩; exact ⟨hi, (inputCheck_checks q v c hi).1, hn⟩

/-- The actual pi syntax map retains the finite word and changes its context. -/
def piCode (q v c : Nat) : Nat := cond (inputCheck q v c) c 0

theorem piCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => piCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.const 0)

theorem piCode_eq (q v c : Nat) (hi : inputCheck q v c = true) : piCode q v c = c := by
  simp only [piCode, hi, Bool.cond_true]

theorem piCode_rejected (q v c : Nat) (hi : inputCheck q v c = false) : piCode q v c = 0 := by
  simp only [piCode, hi, Bool.cond_false]

theorem piCode_checked (q v c : Nat) (hi : inputCheck q v c = true) :
    checkCode v (piCode q v c) = true := by
  rw [piCode_eq q v c hi]; exact (inputCheck_checks q v c hi).2.1

theorem piCode_height (q v c : Nat) (hi : inputCheck q v c = true) :
    heightCode (piCode q v c) = heightCode c := by rw [piCode_eq q v c hi]

theorem piCode_fragment (q v n c : Nat) (hi : inputCheck q v c = true)
    (hn : finiteCheckCode q n c = true) : finiteCheckCode v n (piCode q v c) = true := by
  have hs := inputCheck_checks q v c hi
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hs.1
  rw [piCode_eq q v t.code hi, finiteCheckCode_code]
  apply finiteCheck_change q v n t (by simpa only [finiteCheckCode_code] using hn)
  exact (checked_admissible v t (by simpa only [checkCode_code] using hs.2.1)).1

theorem inputCheck_compose (q v w c : Nat) (hqv : inputCheck q v c = true)
    (hvw : inputCheck v w c = true) : inputCheck q w c = true := by
  have hs := inputCheck_checks q v c hqv
  have ht := inputCheck_checks v w c hvw
  exact target_preimage q w c (Bool.and_eq_true.mp hs.1).1 (ht.2.2.trans hs.2.2) ht.2.1

theorem piCode_compose (q v w c : Nat) (hqv : inputCheck q v c = true)
    (hvw : inputCheck v w c = true) :
    piCode v w (piCode q v c) = piCode q w c := by
  rw [piCode_eq q v c hqv, piCode_eq v w c hvw,
    piCode_eq q w c (inputCheck_compose q v w c hqv hvw)]

theorem piCode_normal (q v c : Nat) (hi : normalInputCheck q v c = true) :
    Comparison.acceptedCode v (piCode q v c) = true := by
  obtain ⟨h, hn⟩ := (normalInputCheck_exact q v c).mp hi
  obtain ⟨hc, hd, hl⟩ := inputCheck_checks q v c h
  rw [piCode_eq q v c h]
  exact (Comparison.acceptedCode_exact v c).mpr ⟨hd,
    (normal_context q v _ (Arithmetic.raw_checked q c hc) (Arithmetic.raw_checked v c hd)).mp hn⟩

theorem piCode_support (q v c : Nat) (hi : inputCheck q v c = true) :
    parameterSupport v (rawTree (piCode q v c)) = parameterSupport q (rawTree c) := by
  obtain ⟨hc, hd, hl⟩ := inputCheck_checks q v c hi
  rw [piCode_eq q v c hi]
  exact (parameterSupport_context q v _ (Arithmetic.raw_checked q c hc)
    (Arithmetic.raw_checked v c hd)).symm

theorem normal_less_iff (q v : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (htv : check v t = true) (huv : check v u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u) :
    denote q t < denote q u ↔ denote v t < denote v u := by
  rw [← Comparison.less_correct q t u ht hu hnt hnu, less_context q v,
    Comparison.less_correct v t u htv huv ((normal_context q v t ht htv).mp hnt)
      ((normal_context q v u hu huv).mp hnu)]

theorem raw_less_iff (q v : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (htv : check v t = true) (huv : check v u = true) :
    denote q t < denote q u ↔ denote v t < denote v u := by
  have hqt := Normalization.normalize_checked q t ht
  have hqu := Normalization.normalize_checked q u hu
  have hvt := Normalization.normalize_checked v t htv
  have hvu := Normalization.normalize_checked v u huv
  have htvc : check v (Normalization.normalize q t) = true := by rw [normalize_context q v]; exact hvt.1
  have huvc : check v (Normalization.normalize q u) = true := by rw [normalize_context q v]; exact hvu.1
  have htval : denote v (Normalization.normalize q t) = denote v t := by rw [normalize_context q v]; exact hvt.2.2
  have huval : denote v (Normalization.normalize q u) = denote v u := by rw [normalize_context q v]; exact hvu.2.2
  simpa only [hqt.2.2, hqu.2.2, htval, huval] using
    normal_less_iff q v _ _ hqt.1 hqu.1 htvc huvc hqt.2.1 hqu.2.1

theorem raw_equal_iff (q v : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (htv : check v t = true) (huv : check v u = true) :
    denote q t = denote q u ↔ denote v t = denote v u := by
  have hlt := raw_less_iff q v t u ht hu htv huv
  have hgt := raw_less_iff q v u t hu ht huv htv
  constructor
  · intro he
    apply le_antisymm
    · exact le_of_not_gt (fun h => (ne_of_lt (hgt.mpr h)) he.symm)
    · exact le_of_not_gt (fun h => (ne_of_lt (hlt.mpr h)) he)
  · intro he
    apply le_antisymm
    · exact le_of_not_gt (fun h => (ne_of_lt (hgt.mp h)) he.symm)
    · exact le_of_not_gt (fun h => (ne_of_lt (hlt.mp h)) he)

theorem piCode_less_iff (q v c d : Nat) (hc : inputCheck q v c = true) (hd : inputCheck q v d = true) :
    interpretation q c < interpretation q d ↔
      interpretation v (piCode q v c) < interpretation v (piCode q v d) := by
  obtain ⟨hqc, hvc, hcl⟩ := inputCheck_checks q v c hc
  obtain ⟨hqd, hvd, hdl⟩ := inputCheck_checks q v d hd
  rw [piCode_eq q v c hc, piCode_eq q v d hd]
  simpa only [Arithmetic.raw_value q c hqc, Arithmetic.raw_value q d hqd,
    Arithmetic.raw_value v c hvc, Arithmetic.raw_value v d hvd] using
      raw_less_iff q v _ _ (Arithmetic.raw_checked q c hqc) (Arithmetic.raw_checked q d hqd)
        (Arithmetic.raw_checked v c hvc) (Arithmetic.raw_checked v d hvd)

theorem piCode_equal_iff (q v c d : Nat) (hc : inputCheck q v c = true) (hd : inputCheck q v d = true) :
    interpretation q c = interpretation q d ↔
      interpretation v (piCode q v c) = interpretation v (piCode q v d) := by
  obtain ⟨hqc, hvc, hcl⟩ := inputCheck_checks q v c hc
  obtain ⟨hqd, hvd, hdl⟩ := inputCheck_checks q v d hd
  rw [piCode_eq q v c hc, piCode_eq q v d hd]
  simpa only [Arithmetic.raw_value q c hqc, Arithmetic.raw_value q d hqd,
    Arithmetic.raw_value v c hvc, Arithmetic.raw_value v d hvd] using
      raw_equal_iff q v _ _ (Arithmetic.raw_checked q c hqc) (Arithmetic.raw_checked q d hqd)
        (Arithmetic.raw_checked v c hvc) (Arithmetic.raw_checked v d hvd)

theorem addition_context (q v c d : Nat) (hc : inputCheck q v c = true) (hd : inputCheck q v d = true) :
    Arithmetic.addCode q c d = Arithmetic.addCode v c d := by
  have hs := inputCheck_checks q v c hc
  have ht := inputCheck_checks q v d hd
  have hq := (Arithmetic.inputCheck_exact q c d).mpr ⟨hs.1, ht.1⟩
  have hv := (Arithmetic.inputCheck_exact v c d).mpr ⟨hs.2.1, ht.2.1⟩
  simp only [Arithmetic.addCode, hq, hv, Bool.cond_true, Arithmetic.addTerm, normalize_context q v]

theorem addition_input (q v c d : Nat) (hc : inputCheck q v c = true) (hd : inputCheck q v d = true) :
    inputCheck q v (Arithmetic.addCode q c d) = true := by
  have hs := inputCheck_checks q v c hc
  have ht := inputCheck_checks q v d hd
  have ha := (Comparison.acceptedCode_exact q _).mp (Arithmetic.addCode_spec q c d hs.1 ht.1).1
  have hb := (Comparison.acceptedCode_exact v _).mp (Arithmetic.addCode_spec v c d hs.2.1 ht.2.1).1
  rw [← addition_context q v c d hc hd] at hb
  exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha.1, hb.1⟩, (Bool.and_eq_true.mp hc).2⟩

theorem piCode_addition (q v c d : Nat) (hc : inputCheck q v c = true) (hd : inputCheck q v d = true) :
    piCode q v (Arithmetic.addCode q c d) = Arithmetic.addCode v (piCode q v c) (piCode q v d) := by
  rw [piCode_eq q v _ (addition_input q v c d hc hd), piCode_eq q v c hc, piCode_eq q v d hd,
    addition_context q v c d hc hd]

theorem piCode_addition_value (q v c d : Nat) (hc : inputCheck q v c = true)
    (hd : inputCheck q v d = true) :
    interpretation v (piCode q v (Arithmetic.addCode q c d)) =
      interpretation v (piCode q v c) + interpretation v (piCode q v d) := by
  rw [piCode_addition q v c d hc hd]
  exact (Arithmetic.addCode_spec v _ _ (piCode_checked q v c hc) (piCode_checked q v d hd)).2.1

/-- Normalize first so a discarded raw summand is not an artificial Par restriction. -/
def rawInputCheck (q v c : Nat) : Bool := checkCode q c && inputCheck q v (Normalization.normalizeCode q c)

theorem rawInputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawInputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (inputCheck_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))

theorem rawInputCheck_exact (q v c : Nat) : rawInputCheck q v c = true ↔
    checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
      ParBounded q v (rawTree (Normalization.normalizeCode q c)) := by
  rw [rawInputCheck, Bool.and_eq_true, inputCheck_exact]
  constructor
  · rintro ⟨hc, hn, hv, hl, hp⟩; exact ⟨hc, hv, hl, hp⟩
  · rintro ⟨hc, hv, hl, hp⟩; exact ⟨hc, (Normalization.normalizeCode_checked q c hc).1, hv, hl, hp⟩

def rawPiCode (q v c : Nat) : Nat := cond (rawInputCheck q v c) (Normalization.normalizeCode q c) 0

theorem rawPiCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawPiCode p.1 p.2.1 p.2.2) :=
  rawInputCheck_primrec.cond
    (Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)

theorem rawPiCode_eq (q v c : Nat) (hc : rawInputCheck q v c = true) :
    rawPiCode q v c = Normalization.normalizeCode q c := by simp only [rawPiCode, hc, Bool.cond_true]

theorem rawPiCode_spec (q v c : Nat) (hc : rawInputCheck q v c = true) :
    Comparison.acceptedCode q (rawPiCode q v c) = true ∧
      Comparison.acceptedCode v (rawPiCode q v c) = true ∧
      interpretation q (rawPiCode q v c) = interpretation q c := by
  obtain ⟨hcheck, hi⟩ := Bool.and_eq_true.mp hc
  have hn := Normalization.normalizeCode_checked q c hcheck
  have ht := inputCheck_checks q v _ hi
  rw [rawPiCode_eq q v c hc]
  exact ⟨(Comparison.acceptedCode_exact q _).mpr ⟨hn.1, hn.2.1⟩,
    (Comparison.acceptedCode_exact v _).mpr ⟨ht.2.1,
      (normal_context q v _ (Arithmetic.raw_checked q _ ht.1)
        (Arithmetic.raw_checked v _ ht.2.1)).mp hn.2.1⟩, hn.2.2⟩

theorem rawPiCode_less_iff (q v c d : Nat) (hc : rawInputCheck q v c = true)
    (hd : rawInputCheck q v d = true) : interpretation q c < interpretation q d ↔
      interpretation v (rawPiCode q v c) < interpretation v (rawPiCode q v d) := by
  have hs := Bool.and_eq_true.mp hc
  have ht := Bool.and_eq_true.mp hd
  have hl := piCode_less_iff q v _ _ hs.2 ht.2
  rw [piCode_eq q v _ hs.2, piCode_eq q v _ ht.2,
    (Normalization.normalizeCode_checked q c hs.1).2.2,
    (Normalization.normalizeCode_checked q d ht.1).2.2] at hl
  simpa only [rawPiCode_eq q v c hc, rawPiCode_eq q v d hd] using hl

theorem rawPiCode_equal_iff (q v c d : Nat) (hc : rawInputCheck q v c = true)
    (hd : rawInputCheck q v d = true) : interpretation q c = interpretation q d ↔
      interpretation v (rawPiCode q v c) = interpretation v (rawPiCode q v d) := by
  have hs := Bool.and_eq_true.mp hc
  have ht := Bool.and_eq_true.mp hd
  have hl := piCode_equal_iff q v _ _ hs.2 ht.2
  rw [piCode_eq q v _ hs.2, piCode_eq q v _ ht.2,
    (Normalization.normalizeCode_checked q c hs.1).2.2,
    (Normalization.normalizeCode_checked q d ht.1).2.2] at hl
  simpa only [rawPiCode_eq q v c hc, rawPiCode_eq q v d hd] using hl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseTransformation
