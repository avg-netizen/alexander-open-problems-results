import Alexander313.Wilken.HereditaryNativeComparison
import Alexander313.Effective.HereditaryOrdinalLabels

/-!
# Actual normalization in native coded epsilon contexts

Original public parameter leaves remain unchanged and atomic. At written sums,
their genuine public principal words supply atoms; the real native comparator
executes suffix absorption. Reconstruction starts from an admitted original
public zero code, not the rejected raw payload zero. Theta bodies normalize
recursively, retaining their actual source argument bounds by value fidelity.
Every originally admitted native term receives an admitted weak-normal term
with the same real denotation. Strong source normality, syntactic uniqueness,
literal parameter/support invariance, public return recoding and temporary-base
translation are not asserted. Written sums may replace a public payload by
its actual principal heads.
All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Normalization

open Comparison (Normal atoms)

def prependAtom (q : Nat) (a : RelativeTerm Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => [a]
  | b :: bs => cond (Comparison.less q a b) (b :: bs) (a :: b :: bs)

def normalizeAtoms (q : Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | a :: as => prependAtom q a (normalizeAtoms q as)

theorem prependAtom_mem (q : Nat) (a p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ prependAtom q a as) : p = a ∨ p ∈ as := by
  cases as with
  | nil => simpa [prependAtom] using hp
  | cons b bs =>
    cases hc : Comparison.less q a b with
    | false => simpa [prependAtom, hc] using hp
    | true => exact Or.inr (by simpa [prependAtom, hc] using hp)

theorem normalizeAtoms_mem (q : Nat) (p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ normalizeAtoms q as) : p ∈ as := by
  revert hp
  induction as with
  | nil => intro hp; simp [normalizeAtoms] at hp
  | cons a as ih =>
    intro hp
    rcases prependAtom_mem q a p _ hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

def GoodAtoms (q n : Nat) (as : List (RelativeTerm Nat)) : Prop :=
  ∀ a ∈ as, admissible q n a ∧ Normal q a ∧
    0 < denote q a ∧ Ordinal.IsPrincipal (· + ·) (denote q a)

theorem GoodAtoms.atoms (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hn : Normal q t) : GoodAtoms q n (atoms t) := by
  intro a ha
  have hs := (Comparison.atoms_spec q n hq t ht hn).1 a ha
  have hp := (Comparison.atoms_normal q n hq t ht hn).1 _
    (List.mem_map.mpr ⟨a, ha, rfl⟩)
  exact ⟨hs.1, hs.2, hp.1, hp.2⟩

theorem GoodAtoms.append {q n : Nat} {as bs : List (RelativeTerm Nat)}
    (ha : GoodAtoms q n as) (hb : GoodAtoms q n bs) : GoodAtoms q n (as ++ bs) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ha p hp
  · exact hb p hp

theorem GoodAtoms.reverse {q n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms q n as) : GoodAtoms q n as.reverse :=
  fun p hp => ha p (List.mem_reverse.mp hp)

theorem GoodAtoms.normalizeAtoms {q n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms q n as) : GoodAtoms q n (normalizeAtoms q as) :=
  fun p hp => ha p (normalizeAtoms_mem q p as hp)

private theorem prependAtom_map (q n : Nat) (hq : baseCheck q = true)
    (a : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (ha : admissible q n a) (hna : Normal q a)
    (has : ∀ b ∈ as, admissible q n b ∧ Normal q b) :
    (prependAtom q a as).map (denote q) = prependPrincipal (denote q a) (as.map (denote q)) := by
  classical
  cases as with
  | nil => rfl
  | cons b bs =>
    have hb := has b List.mem_cons_self
    have hc := Comparison.less_correct q a b (Comparison.admitted_checked q n hq a ha)
      (Comparison.admitted_checked q n hq b hb.1) hna hb.2
    cases hcmp : Comparison.less q a b with
    | false =>
      have hnlt : ¬ denote q a < denote q b := by
        intro h
        have he := hc.mpr h
        simp only [hcmp, Bool.false_eq_true] at he
      simp [prependAtom, prependPrincipal, hcmp, hnlt]
    | true => simp [prependAtom, prependPrincipal, hcmp, hc.mp hcmp]

theorem normalizeAtoms_map (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as) :
    (normalizeAtoms q as).map (denote q) = normalizePrincipal (as.map (denote q)) := by
  revert ha
  induction as with
  | nil => intro _; rfl
  | cons a as ih =>
    intro ha
    have hh := ha a List.mem_cons_self
    have ht : GoodAtoms q n as := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    rw [normalizeAtoms, prependAtom_map q n hq a _ hh.1 hh.2.1
      (fun b hb => ⟨(ht.normalizeAtoms b hb).1, (ht.normalizeAtoms b hb).2.1⟩), ih ht]
    rfl

theorem normalizeAtoms_normal (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as) :
    IsAdditiveNormalForm ((normalizeAtoms q as).map (denote q)) := by
  rw [normalizeAtoms_map q n hq as ha]
  apply normalizePrincipal_normal
  intro p hp
  obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hp
  exact (ha a hm).2.2

theorem normalizeAtoms_denote (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as) :
    principalSum ((normalizeAtoms q as).map (denote q)) = principalSum (as.map (denote q)) := by
  rw [normalizeAtoms_map q n hq as ha]
  apply principalSum_normalizePrincipal
  intro p hp
  obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hp
  exact (ha a hm).2.2

def zeroTree : RelativeTerm Nat := .parameter (Nat.pair 0 (.parameter 0 : RelativeTerm Nat).code)

theorem zeroTree_denote (q : Nat) : denote q zeroTree = 0 :=
  Alexander313.HereditaryOrdinalLabels.zeroCode_value

theorem zeroTree_normal (q : Nat) : Normal q zeroTree := trivial

theorem zeroTree_admissible (q n : Nat) (hq : baseCheck q = true) : admissible q n zeroTree := by
  have hp : parameterCheck q Alexander313.HereditaryOrdinalLabels.zeroCode = true :=
    (parameterCheck_exact q _).mpr ⟨Alexander313.HereditaryOrdinalLabels.zeroCode_checked,
      ((baseCheck_exact q).mp hq).1, by
        rw [parameters, Alexander313.HereditaryOrdinalLabels.zeroCode_value]
        exact base_pos q hq⟩
  exact ⟨hp, .parameter (by
    simpa only [omegaSequence_zero, Alexander313.HereditaryOrdinalLabels.zeroCode, Hereditary.zeroTree] using parameter_sound q _ hp)⟩

theorem zeroTree_checked (q : Nat) (hq : baseCheck q = true) : check q zeroTree = true :=
  Comparison.admitted_checked q 0 hq zeroTree (zeroTree_admissible q 0 hq)

def buildRev : List (RelativeTerm Nat) → RelativeTerm Nat
  | [] => zeroTree
  | a :: as => .sum (buildRev as) a

def buildAtoms (as : List (RelativeTerm Nat)) : RelativeTerm Nat := buildRev as.reverse

theorem buildRev_denote (q : Nat) (as : List (RelativeTerm Nat)) :
    denote q (buildRev as) = principalSum (as.reverse.map (denote q)) := by
  induction as with
  | nil => simp only [buildRev, zeroTree_denote, List.reverse_nil, List.map_nil, principalSum]
  | cons a as ih =>
    change denote q (buildRev as) + denote q a = _
    rw [ih, List.reverse_cons, List.map_append, principalSum_append]
    simp [principalSum]

theorem buildRev_admissible (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as) : admissible q n (buildRev as) := by
  revert ha
  induction as with
  | nil => intro _; exact zeroTree_admissible q n hq
  | cons a as ih =>
    intro ha
    have hp := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hh := (ha a List.mem_cons_self).1
    exact ⟨⟨hp.1, hh.1⟩, .sum hp.2 hh.2⟩

theorem buildRev_normal (q n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as)
    (hn : IsAdditiveNormalForm (as.reverse.map (denote q))) : Normal q (buildRev as) := by
  revert ha hn
  induction as with
  | nil => intro _ _; exact zeroTree_normal q
  | cons a as ih =>
    intro ha hn
    have hfull : IsAdditiveNormalForm ((as.reverse.map (denote q)) ++ [denote q a]) := by
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil] using hn
    have hprefix : IsAdditiveNormalForm (as.reverse.map (denote q)) :=
      ⟨fun p hp => hfull.1 p (List.mem_append_left _ hp), (List.pairwise_append.mp hfull.2).1⟩
    refine ⟨ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hprefix,
      (ha a List.mem_cons_self).2.1, Or.inr ⟨as.reverse.map (denote q), hfull, ?_, ?_⟩⟩
    · exact (buildRev_denote q as).symm
    · rw [principalSum_append]
      simp only [principalSum, add_zero]
      rw [← buildRev_denote q as]
      rfl

theorem buildAtoms_denote (q : Nat) (as : List (RelativeTerm Nat)) :
    denote q (buildAtoms as) = principalSum (as.map (denote q)) := by
  simpa only [buildAtoms, List.reverse_reverse] using buildRev_denote q as.reverse

theorem buildAtoms_admissible (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as) : admissible q n (buildAtoms as) :=
  buildRev_admissible q n hq as.reverse ha.reverse

theorem buildAtoms_normal (q n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms q n as)
    (hn : IsAdditiveNormalForm (as.map (denote q))) : Normal q (buildAtoms as) := by
  apply buildRev_normal q n as.reverse ha.reverse
  simpa only [List.reverse_reverse] using hn

def normalize (q : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter p
  | .theta k a => .theta k (normalize q a)
  | .sum a b => buildAtoms (normalizeAtoms q (atoms (normalize q a) ++ atoms (normalize q b)))

/-- Original admission alone supplies the output admission, weak normality
and actual finite/global value preservation. No input normality is assumed. -/
theorem normalize_spec (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) : admissible q n (normalize q t) ∧ Normal q (normalize q t) ∧
      denote q (normalize q t) = denote q t := by
  revert ht
  induction t with
  | parameter p => intro ht; exact ⟨ht, trivial, rfl⟩
  | theta k a ih =>
    intro ht
    cases ht.2 with
    | theta h0k hkn hsort ha =>
      have hp := ih ⟨ht.1, ha⟩
      have hv : finiteDenote q n (normalize q a) = finiteDenote q n a := by
        rw [← denote_eq_finite q n hq (normalize q a) hp.1.2,
          ← denote_eq_finite q n hq a ha]
        exact hp.2.2
      have hout : admissible q n (.theta k (normalize q a)) :=
        ⟨hp.1.1, .theta h0k hkn (by
          change finiteDenote q n (normalize q a) < omegaSequence (base q) (k + 2)
          rw [hv]
          exact hsort) hp.1.2⟩
      refine ⟨hout, hp.2.1, ?_⟩
      change globalCollapse (base q) k (denote q (normalize q a)) = globalCollapse (base q) k (denote q a)
      rw [hp.2.2]
  | sum a b iha ihb =>
    intro ht
    cases ht.2 with
    | sum ha hb =>
      have hpa := iha ⟨ht.1.1, ha⟩
      have hpb := ihb ⟨ht.1.2, hb⟩
      let word := atoms (normalize q a) ++ atoms (normalize q b)
      have hg : GoodAtoms q n word := (GoodAtoms.atoms q n hq _ hpa.1 hpa.2.1).append
        (GoodAtoms.atoms q n hq _ hpb.1 hpb.2.1)
      have hn := normalizeAtoms_normal q n hq word hg
      have hr := hg.normalizeAtoms
      refine ⟨buildAtoms_admissible q n hq _ hr, buildAtoms_normal q n _ hr hn, ?_⟩
      calc
        denote q (buildAtoms (normalizeAtoms q word)) = principalSum ((normalizeAtoms q word).map (denote q)) :=
          buildAtoms_denote q _
        _ = principalSum (word.map (denote q)) := normalizeAtoms_denote q n hq word hg
        _ = denote q (normalize q a) + denote q (normalize q b) := by
          rw [List.map_append, principalSum_append,
            Comparison.atoms_value q n hq _ hpa.1 hpa.2.1,
            Comparison.atoms_value q n hq _ hpb.1 hpb.2.1]
        _ = denote q (.sum a b) := by rw [hpa.2.2, hpb.2.2]; rfl

theorem normalize_finiteDenote (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) : finiteDenote q n (normalize q t) = finiteDenote q n t := by
  have hs := normalize_spec q n hq t ht
  rw [← denote_eq_finite q n hq (normalize q t) hs.1.2, ← denote_eq_finite q n hq t ht.2]
  exact hs.2.2

theorem normalize_checked (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    check q (normalize q t) = true ∧ Normal q (normalize q t) ∧ denote q (normalize q t) = denote q t := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have hs := normalize_spec q _ hq t (NativeContext.checked_admissible q t ht)
  exact ⟨Comparison.admitted_checked q _ hq _ hs.1, hs.2.1, hs.2.2⟩

/-- Invalid whole codes and invalid epsilon contexts retain raw output zero. -/
def normalizeCode (q c : Nat) : Nat := cond (checkCode q c) (normalize q (ThetaCourse.rawTree c)).code 0

theorem normalizeCode_rejected (q c : Nat) (hc : checkCode q c = false) : normalizeCode q c = 0 := by
  simp only [normalizeCode, hc, Bool.cond_false]

theorem normalizeCode_checked (q c : Nat) (hc : checkCode q c = true) :
    checkCode q (normalizeCode q c) = true ∧ Normal q (ThetaCourse.rawTree (normalizeCode q c)) ∧
      interpretation q (normalizeCode q c) = interpretation q c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  have hs := normalize_checked q t ht
  simpa only [normalizeCode, checkCode_code, ht, Bool.cond_true, ThetaCourse.rawTree_code,
    interpretation_code] using hs

theorem normalizeCode_accepted (q c : Nat) (hc : checkCode q c = true) :
    Comparison.acceptedCode q (normalizeCode q c) = true ∧ interpretation q (normalizeCode q c) = interpretation q c := by
  have hs := normalizeCode_checked q c hc
  exact ⟨(Comparison.acceptedCode_exact q _).mpr ⟨hs.1, hs.2.1⟩, hs.2.2⟩

theorem normalizeCode_value_invariant (q c d : Nat) (hc : checkCode q c = true)
    (hd : checkCode q d = true) (hv : interpretation q c = interpretation q d) :
    interpretation q (normalizeCode q c) = interpretation q (normalizeCode q d) :=
  (normalizeCode_checked q c hc).2.2.trans (hv.trans (normalizeCode_checked q d hd).2.2.symm)

def graph (q c output : Nat) : Bool := checkCode q c && (output == normalizeCode q c)

theorem graph_exact (q c output : Nat) : graph q c output = true ↔
    checkCode q c = true ∧ output = normalizeCode q c := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

theorem graph_spec (q c output : Nat) (h : graph q c output = true) :
    checkCode q c = true ∧ Comparison.acceptedCode q output = true ∧ interpretation q output = interpretation q c := by
  obtain ⟨hc, rfl⟩ := (graph_exact q c output).mp h
  exact ⟨hc, (normalizeCode_accepted q c hc).1, (normalizeCode_accepted q c hc).2⟩

theorem graph_unique (q c : Nat) (hc : checkCode q c = true) : ∃! output, graph q c output = true := by
  refine ⟨normalizeCode q c, (graph_exact q c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graph_exact q c output).mp ho).2

def lessRawCode (q c d : Nat) : Bool := (checkCode q c && checkCode q d) &&
  Comparison.lessCode q (normalizeCode q c) (normalizeCode q d)

def equalRawCode (q c d : Nat) : Bool := (checkCode q c && checkCode q d) &&
  Comparison.equalCode q (normalizeCode q c) (normalizeCode q d)

theorem lessRawCode_exact (q c d : Nat) : lessRawCode q c d = true ↔
    checkCode q c = true ∧ checkCode q d = true ∧ interpretation q c < interpretation q d := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp hs.1
    have hv := ((Comparison.lessCode_exact q _ _).mp hs.2).2.2.2.2
    rw [(normalizeCode_checked q c hc).2.2, (normalizeCode_checked q d hd).2.2] at hv
    exact ⟨hc, hd, hv⟩
  · rintro ⟨hc, hd, hv⟩
    have hsc := normalizeCode_checked q c hc
    have hsd := normalizeCode_checked q d hd
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hc, hd⟩,
      (Comparison.lessCode_exact q _ _).mpr ⟨hsc.1, hsc.2.1, hsd.1, hsd.2.1, by
        rw [hsc.2.2, hsd.2.2]; exact hv⟩⟩

theorem equalRawCode_exact (q c d : Nat) : equalRawCode q c d = true ↔
    checkCode q c = true ∧ checkCode q d = true ∧ interpretation q c = interpretation q d := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp hs.1
    have hv := ((Comparison.equalCode_exact q _ _).mp hs.2).2.2.2.2
    rw [(normalizeCode_checked q c hc).2.2, (normalizeCode_checked q d hd).2.2] at hv
    exact ⟨hc, hd, hv⟩
  · rintro ⟨hc, hd, hv⟩
    have hsc := normalizeCode_checked q c hc
    have hsd := normalizeCode_checked q d hd
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hc, hd⟩,
      (Comparison.equalCode_exact q _ _).mpr ⟨hsc.1, hsc.2.1, hsd.1, hsd.2.1, by
        rw [hsc.2.2, hsd.2.2]; exact hv⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Normalization
