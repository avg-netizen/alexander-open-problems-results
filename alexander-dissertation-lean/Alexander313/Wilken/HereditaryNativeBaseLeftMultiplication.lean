import Alexander313.Wilken.PublicEpsilonNativeLogEndBaseChange
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange

/-!
# Genuine multiplication by the actual native epsilon base

A normalized principal atom has an actual last-log output. Native addition
of the actual base to that logarithm, followed by the genuine omega-power
producer, constructs its left product by the base. A finite partial-recursive
walk adds those real products in the original principal-word order. All local
LOW and normal callers follow from the original RAW LOW input. Admission at
a second base gives literal partial-output agreement; its real checker will
supply full syntactic payload cutoffs. No multiplication or recoder oracle.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseLeftMultiplication

open ThetaCourse

theorem baseCode_low (q : Nat) (hq : baseCheck q = true) :
    lowCheckCode q OmegaPowers.Offsets.baseCode = true := by
  have hs := OmegaPowers.Offsets.baseCode_spec q hq
  apply OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp hs.1).1
  rw [hs.2]
  simpa only [omegaSequence_zero] using
    (omegaSequence_strictMono (base q)) (show 0 < 1 by omega)

def principal (q c : Nat) : Part Nat := (LogEnd.execute q c).map fun ell =>
  OmegaPowers.powerCode q (Arithmetic.addCode q OmegaPowers.Offsets.baseCode ell)

theorem principal_partrec : Partrec₂ principal := by
  have ha : Primrec (fun p : (Nat × Nat) × Nat =>
      Arithmetic.addCode p.1.1 OmegaPowers.Offsets.baseCode p.2) :=
    Arithmetic.addCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.const OmegaPowers.Offsets.baseCode).pair Primrec.snd))
  have hp : Primrec (fun p : (Nat × Nat) × Nat =>
      OmegaPowers.powerCode p.1.1 (Arithmetic.addCode p.1.1 OmegaPowers.Offsets.baseCode p.2)) :=
    OmegaPowers.powerCode_primrec.comp (Primrec.fst.comp Primrec.fst) ha
  exact (LogEnd.execute_partrec.map hp.to_comp.to₂).to₂

theorem principal_domain (q c : Nat) : (principal q c).Dom ↔ lowCheckCode q c = true := by
  change (LogEnd.execute q c).Dom ↔ lowCheckCode q c = true
  exact LogEnd.execute_domain q c

/-- Genuine principal multiplication derives every logarithm, addition
and omega-power caller from original admission, positivity and principality. -/
theorem principal_spec (q c out : Nat) (hc : lowCheckCode q c = true)
    (hpos : 0 < interpretation q c)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation q c))
    (ho : out ∈ principal q c) :
    lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      interpretation q out = base q * interpretation q c := by
  obtain ⟨ell, hl, he⟩ := (Part.mem_map_iff _).mp ho
  subst out
  have hs := LogEnd.execute_spec q c ell hl
  have hi := HeightBoundary.input_spec q c hc
  have hb := OmegaPowers.Offsets.baseCode_spec q hi.2.1
  have ha := Arithmetic.addCode_spec q OmegaPowers.Offsets.baseCode ell
    ((Comparison.acceptedCode_exact q _).mp hb.1).1
    ((Comparison.acceptedCode_exact q _).mp hs.2.2.1).1
  have hal := (OmegaPowerHeight.addCode_low_height q _ ell
    (baseCode_low q hi.2.1) hs.2.1).1
  have hp := OmegaPowers.powerCode_spec q _ hal
  refine ⟨hp.1, hp.2.1, ?_⟩
  have hlog : Ordinal.omega0 ^ interpretation q ell = interpretation q c := by
    have he := hs.2.2.2
    simp only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hpos)] at he
    exact he.trans (SourceChi.Powers.endValue_principal _ hpos hprincipal)
  rw [hp.2.2, ha.2.1, hb.2, Ordinal.opow_add,
    SourceChi.epsilon_base q hi.2.1, hlog]

abbrev State := List (RelativeTerm Nat) × Nat

def step (q : Nat) (state : State) : Part State := match state.1 with
  | [] => Part.some state
  | t :: ts => (principal q t.code).map fun p => (ts, Arithmetic.addCode q state.2 p)

theorem step_partrec : Partrec₂ step := by
  have ho : Primrec (fun p : Nat × State => p.2.1.head?) :=
    Primrec.list_head?.comp (Primrec.fst.comp Primrec.snd)
  have hp : Partrec (fun p : (Nat × State) × RelativeTerm Nat => principal p.1.1 p.2.code) :=
    principal_partrec.comp (Computable.fst.comp Computable.fst)
    (code_primrec.comp Primrec.snd).to_comp
  have hm : Partrec₂ (fun p : Nat × State => fun t : RelativeTerm Nat =>
      (principal p.1 t.code).map fun v =>
        ((p.2.1).tail, Arithmetic.addCode p.1 p.2.2 v)) := by
    have ha : Primrec (fun p : ((Nat × State) × RelativeTerm Nat) × Nat =>
        Arithmetic.addCode p.1.1.1 p.1.1.2.2 p.2) :=
      Arithmetic.addCode_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd))
    have ht : Primrec (fun p : ((Nat × State) × RelativeTerm Nat) × Nat => p.1.1.2.1.tail) :=
      Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    exact (hp.map (ht.pair ha).to_comp.to₂).to₂
  have h := Partrec.optionCasesOn_right ho.to_comp Computable.snd hm
  exact h.to₂.of_eq fun p => by
    rcases p with ⟨q, as, acc⟩
    cases as <;> rfl

/-- The finite loop executes one genuine step per original atom. -/
def walk (q : Nat) (n : Nat) (state : State) : Part State :=
  n.rec (Part.some state) fun _ previous => previous.bind (step q)

theorem walk_partrec : Partrec
    (fun p : (Nat × State) × Nat => walk p.1.1 p.2 p.1.2) := by
  have hs : Partrec₂ (fun p : (Nat × State) × Nat => fun v : Nat × State => step p.1.1 v.2) :=
    (step_partrec.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.snd)).to₂
  exact Partrec.nat_rec Computable.snd (Computable.snd.comp Computable.fst) hs

private theorem walk_front (q n : Nat) (state : State) :
    walk q (n + 1) state = (step q state).bind (walk q n) := by
  induction n generalizing state with
  | zero => simp only [walk, Part.bind_some, Part.bind_some_right]
  | succ n ih =>
    change (walk q (n + 1) state).bind (step q) =
      (step q state).bind (fun s => (walk q n s).bind (step q))
    rw [ih, Part.bind_assoc]

private def WordLow (q : Nat) (as : List (RelativeTerm Nat)) : Prop :=
  ∀ t ∈ as, lowCheckCode q t.code = true ∧ 0 < denote q t ∧
    Ordinal.IsPrincipal (· + ·) (denote q t)

private theorem walk_returns (q : Nat) (as : List (RelativeTerm Nat)) (acc : Nat)
    (hs : WordLow q as) (ha : lowCheckCode q acc = true) :
    ∃ out, out ∈ walk q as.length (as, acc) := by
  revert hs ha
  induction as generalizing acc with
  | nil =>
    intro hs ha
    exact ⟨([], acc), by simp only [walk, List.length_nil, Part.mem_some_iff]⟩
  | cons t ts ih =>
    intro hs ha
    have ht := hs t List.mem_cons_self
    obtain ⟨p, hp⟩ := Part.dom_iff_mem.mp ((principal_domain q t.code).mpr ht.1)
    have hv := principal_spec q t.code p ht.1
      (by simpa only [interpretation_code] using ht.2.1)
      (by simpa only [interpretation_code] using ht.2.2) hp
    have han := (OmegaPowerHeight.addCode_low_height q acc p ha hv.1).1
    obtain ⟨out, ho⟩ := ih (acc := Arithmetic.addCode q acc p)
      (fun u hu => hs u (List.mem_cons_of_mem _ hu)) han
    refine ⟨out, ?_⟩
    rw [List.length_cons, walk_front]
    apply Part.mem_bind_iff.mpr
    exact ⟨(ts, Arithmetic.addCode q acc p),
      by simp only [step]; exact (Part.mem_map_iff _).mpr ⟨p, hp, rfl⟩, ho⟩

private theorem walk_spec (q : Nat) (as : List (RelativeTerm Nat)) (acc : Nat)
    (hs : WordLow q as) (ha : lowCheckCode q acc = true)
    (hn : Comparison.acceptedCode q acc = true) (out : State)
    (ho : out ∈ walk q as.length (as, acc)) :
    out.1 = [] ∧ lowCheckCode q out.2 = true ∧ Comparison.acceptedCode q out.2 = true ∧
      interpretation q out.2 = interpretation q acc + base q * principalSum (as.map (denote q)) := by
  revert hs ha hn ho
  induction as generalizing acc out with
  | nil =>
    intro hs ha hn ho
    have he : out = ([], acc) := by
      simpa only [walk, List.length_nil, Part.mem_some_iff] using ho
    subst out
    exact ⟨rfl, ha, hn, by simp only [List.map_nil, principalSum, mul_zero, add_zero]⟩
  | cons t ts ih =>
    intro hs ha hn ho
    rw [List.length_cons, walk_front] at ho
    obtain ⟨state, hh, hm⟩ := Part.mem_bind_iff.mp ho
    obtain ⟨p, hp, he⟩ := (Part.mem_map_iff _).mp
      (show state ∈ (principal q t.code).map
        (fun p => (ts, Arithmetic.addCode q acc p)) by simpa only [step] using hh)
    subst state
    have ht := hs t List.mem_cons_self
    have hv := principal_spec q t.code p ht.1
      (by simpa only [interpretation_code] using ht.2.1)
      (by simpa only [interpretation_code] using ht.2.2) hp
    have han := (OmegaPowerHeight.addCode_low_height q acc p ha hv.1).1
    have hsum := Arithmetic.addCode_spec q acc p (Bool.and_eq_true.mp ha).1
      ((Comparison.acceptedCode_exact q _).mp hv.2.1).1
    have hrest := ih (acc := Arithmetic.addCode q acc p) (out := out)
      (fun u hu => hs u (List.mem_cons_of_mem _ hu)) han hsum.1 hm
    refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, ?_⟩
    rw [hrest.2.2.2, hsum.2.1, hv.2.2]
    simp only [List.map_cons, principalSum, interpretation_code, mul_add, add_assoc]

def wordProduct (q : Nat) (as : List (RelativeTerm Nat)) : Part Nat :=
  (walk q as.length (as, OmegaPowerHeight.numeralCode 0)).map Prod.snd

theorem wordProduct_partrec : Partrec₂ wordProduct := by
  have hi : Primrec (fun p : Nat × List (RelativeTerm Nat) =>
      ((p.1, (p.2, OmegaPowerHeight.numeralCode 0)), p.2.length)) :=
    (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (OmegaPowerHeight.numeralCode 0)))).pair
      (Primrec.list_length.comp Primrec.snd)
  exact ((walk_partrec.comp hi.to_comp).map (Computable.snd.comp Computable.snd).to₂).to₂

private theorem normalizedWord_low (q c : Nat) (hc : lowCheckCode q c = true) :
    WordLow q (Arithmetic.normalizedWord q c) := by
  have hi := HeightBoundary.input_spec q c hc
  have hs := Arithmetic.normalizedWord_spec q c hi.1
  intro t ht
  have h := hs.1 t ht
  have hv : denote q t ≤ interpretation q c := by
    apply canonicalANF_mem_le
    rw [← hs.2]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  refine ⟨OmegaPowers.low_of_bound q t.code (by simpa only [checkCode_code] using h.1)
    (by simpa only [interpretation_code] using hv.trans_lt hi.2.2), h.2.2.1, h.2.2.2⟩

def execute (q c : Nat) : Part Nat := cond (lowCheckCode q c)
  (wordProduct q (Arithmetic.normalizedWord q c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond lowCheckCode_primrec.to_comp
    (wordProduct_partrec.comp Computable.fst Arithmetic.normalizedWord_primrec.to_comp)
    Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ lowCheckCode q c = true := by
  cases hc : lowCheckCode q c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hq := (HeightBoundary.input_spec q c hc).2.1
    obtain ⟨out, ho⟩ := walk_returns q (Arithmetic.normalizedWord q c)
      (OmegaPowerHeight.numeralCode 0) (normalizedWord_low q c hc)
      (OmegaPowerHeight.numeralCode_spec q 0 hq).1
    have hr : out.2 ∈ execute q c := by
      simp only [execute, hc, Bool.cond_true, wordProduct]
      exact (Part.mem_map_iff _).mpr ⟨out, ho, rfl⟩
    constructor
    · intro _; rfl
    · intro _; exact Part.dom_iff_mem.mpr ⟨out.2, hr⟩

/-- Multiplication by the actual coded epsilon executes on EVERY
original RAW LOW input and constructs a genuine LOW Normal output. -/
theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    lowCheckCode q c = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧
      interpretation q out = base q * interpretation q c := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hi := HeightBoundary.input_spec q c hc
  have hn := OmegaPowerHeight.numeralCode_spec q 0 hi.2.1
  obtain ⟨state, hm, he⟩ := (Part.mem_map_iff Prod.snd).mp
    (show out ∈ (walk q (Arithmetic.normalizedWord q c).length
      (Arithmetic.normalizedWord q c, OmegaPowerHeight.numeralCode 0)).map Prod.snd by
      simpa only [execute, hc, Bool.cond_true, wordProduct] using ho)
  have hs := walk_spec q _ _ (normalizedWord_low q c hc) hn.1 hn.2.1 state hm
  refine ⟨hc, by simpa only [he] using hs.2.1,
    by simpa only [he] using hs.2.2.1, ?_⟩
  rw [← he, hs.2.2.2, hn.2.2.1, Nat.cast_zero, zero_add,
    (Arithmetic.normalizedWord_spec q c hi.1).2, principalSum_canonicalANF]

/-- The actual principal product codes agree whenever the same original
LOW word is genuinely admitted at both coded epsilon contexts. -/
theorem principal_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : principal q c = principal v c := by
  have he := LogEnd.BaseChange.execute_context q v c hcq hcv
  obtain ⟨ell, hlq⟩ := Part.dom_iff_mem.mp ((LogEnd.execute_domain q c).mpr hcq)
  have hlv : ell ∈ LogEnd.execute v c := by rw [← he]; exact hlq
  have hsq := LogEnd.execute_spec q c ell hlq
  have hsv := LogEnd.execute_spec v c ell hlv
  have hiq := HeightBoundary.input_spec q c hcq
  have hiv := HeightBoundary.input_spec v c hcv
  have hbq := OmegaPowers.Offsets.baseCode_spec q hiq.2.1
  have hbv := OmegaPowers.Offsets.baseCode_spec v hiv.2.1
  have hadd := OmegaPowers.BaseChange.addCode_context q v OmegaPowers.Offsets.baseCode ell
    ((Comparison.acceptedCode_exact q _).mp hbq.1).1 (Bool.and_eq_true.mp hsq.2.1).1
    ((Comparison.acceptedCode_exact v _).mp hbv.1).1 (Bool.and_eq_true.mp hsv.2.1).1
  have halq := (OmegaPowerHeight.addCode_low_height q _ ell (baseCode_low q hiq.2.1) hsq.2.1).1
  have halv : lowCheckCode v (Arithmetic.addCode q OmegaPowers.Offsets.baseCode ell) = true := by
    rw [hadd]
    exact (OmegaPowerHeight.addCode_low_height v _ ell (baseCode_low v hiv.2.1) hsv.2.1).1
  have hpower := OmegaPowers.BaseChange.powerCode_context q v _ halq halv
  simp only [principal, Part.eq_some_iff.mpr hlq, Part.eq_some_iff.mpr hlv, Part.map_some]
  rw [hpower, hadd]

private theorem walk_context (q v : Nat) (as : List (RelativeTerm Nat)) (acc : Nat)
    (hsq : WordLow q as) (hsv : WordLow v as)
    (haq : lowCheckCode q acc = true) (hav : lowCheckCode v acc = true) :
    walk q as.length (as, acc) = walk v as.length (as, acc) := by
  revert hsq hsv haq hav
  induction as generalizing acc with
  | nil => intro hsq hsv haq hav; rfl
  | cons t ts ih =>
    intro hsq hsv haq hav
    have htq := hsq t List.mem_cons_self
    have htv := hsv t List.mem_cons_self
    have he := principal_context q v t.code htq.1 htv.1
    obtain ⟨p, hpq⟩ := Part.dom_iff_mem.mp ((principal_domain q t.code).mpr htq.1)
    have hpv : p ∈ principal v t.code := by rw [← he]; exact hpq
    have hvq := principal_spec q t.code p htq.1
      (by simpa only [interpretation_code] using htq.2.1)
      (by simpa only [interpretation_code] using htq.2.2) hpq
    have hvv := principal_spec v t.code p htv.1
      (by simpa only [interpretation_code] using htv.2.1)
      (by simpa only [interpretation_code] using htv.2.2) hpv
    have hadd := OmegaPowers.BaseChange.addCode_context q v acc p
      (Bool.and_eq_true.mp haq).1 (Bool.and_eq_true.mp hvq.1).1
      (Bool.and_eq_true.mp hav).1 (Bool.and_eq_true.mp hvv.1).1
    have hanq := (OmegaPowerHeight.addCode_low_height q acc p haq hvq.1).1
    have hanv : lowCheckCode v (Arithmetic.addCode q acc p) = true := by
      rw [hadd]
      exact (OmegaPowerHeight.addCode_low_height v acc p hav hvv.1).1
    rw [List.length_cons, walk_front, walk_front]
    simp only [step, Part.eq_some_iff.mpr hpq, Part.eq_some_iff.mpr hpv,
      Part.map_some, Part.bind_some]
    rw [← hadd]
    exact ih (acc := Arithmetic.addCode q acc p) (fun u hu => hsq u (List.mem_cons_of_mem _ hu))
      (fun u hu => hsv u (List.mem_cons_of_mem _ hu)) hanq hanv

theorem execute_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : execute q c = execute v c := by
  have hword := OmegaPowers.BaseChange.normalizedWord_context q v c
    (Bool.and_eq_true.mp hcq).1 (Bool.and_eq_true.mp hcv).1
  have hsq := normalizedWord_low q c hcq
  have hsv : WordLow v (Arithmetic.normalizedWord q c) := by
    rw [hword]
    exact normalizedWord_low v c hcv
  have hzq := (OmegaPowerHeight.numeralCode_spec q 0 (HeightBoundary.input_spec q c hcq).2.1).1
  have hzv := (OmegaPowerHeight.numeralCode_spec v 0 (HeightBoundary.input_spec v c hcv).2.1).1
  have he := walk_context q v _ _ hsq hsv hzq hzv
  simp only [execute, hcq, hcv, Bool.cond_true, wordProduct]
  rw [← hword, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseLeftMultiplication
