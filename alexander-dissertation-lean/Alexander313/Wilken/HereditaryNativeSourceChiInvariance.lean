import Alexander313.Wilken.HereditaryNativeSourceChiArithmetic
import Alexander313.Wilken.HereditaryNativePublicChiBridge
import Alexander313.Wilken.HereditaryNativePublicReturn

/-!
# Genuine same-context value invariance of the native source indicator

Actual canonical ANF VALUE words align the principal representatives of
two originally admitted weak-normal terms. Representatives inside a sum
have strictly smaller genuine syntax size. Equal theta values have the
same index by real cardinal ranges, and their original sorted arguments
are equal by actual collapse injection. A joint finite-size induction
therefore compares chi and all high Boolean streams without a spelling,
support, value-invariance or reconstructed-code descent assumption.

Original raw terms are genuinely normalized before applying the result.
The same-positive-public return consequence compares two real admitted
normal native values, then invokes the established forward public bridge;
independent normalizer spellings are never identified. Different epsilon
bases and the cross-base source Lemma 3.4 are not asserted.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Invariance

open Comparison (Normal atoms)
open SourceChi.Arithmetic (highBits)

private theorem lastIndicator_bits (es : List Entry) :
    lastIndicator es = (es.map Prod.snd).reverse.head?.getD false := by
  unfold lastIndicator
  rw [← List.map_reverse]
  cases es.reverse <;> rfl

private theorem indicator_atomBits (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    indicator q t = ((atoms t).map (indicator q)).reverse.head?.getD false := by
  rw [SourceChi.Arithmetic.indicator_atoms q t ht hn, lastIndicator_bits, List.map_map]
  rfl

private theorem theta_indicator_bits (q m : Nat) (a : RelativeTerm Nat) :
    indicator q (.theta m a) = cond (baseCase q m a.code) true
      (cond (chooseHigh q m a.code) ((highBits q m a).reverse.head?.getD false)
        (indicator q a)) := by
  change cond (baseCase q m (state q a).1.code) true
    (cond (chooseHigh q m (state q a).1.code)
      (lastIndicator (highLabels m (state q a).2.2)) (indicator q a)) = _
  rw [state_tree, lastIndicator_bits]
  rfl

/-- Both level and genuine original sorted argument are forced by the real
ordinal value of a checked theta node. -/
theorem theta_value_injective (q k l : Nat) (a b : RelativeTerm Nat)
    (ha : check q (.theta k a) = true) (hb : check q (.theta l b) = true)
    (hv : denote q (.theta k a) = denote q (.theta l b)) :
    k = l ∧ denote q a = denote q b := by
  have hq := (Bool.and_eq_true.mp ha).1
  have hra := FixedPoint.checked_theta_range q k a ha
  have hrb := FixedPoint.checked_theta_range q l b hb
  have hk : k = l := by
    rcases lt_trichotomy k l with hkl | he | hlk
    · have ho := hra.2.trans_le (((omegaSequence_strictMono (base q)).monotone
        (Nat.succ_le_of_lt hkl)).trans hrb.1)
      exact False.elim ((ne_of_lt ho) hv)
    · exact he
    · have ho := hrb.2.trans_le (((omegaSequence_strictMono (base q)).monotone
        (Nat.succ_le_of_lt hlk)).trans hra.1)
      exact False.elim ((ne_of_lt ho) hv.symm)
  subst l
  have hac := FixedPoint.checked_theta_argument q k a ha
  have hbc := FixedPoint.checked_theta_argument q k b hb
  let alpha := FixedPoint.sourceOrdinal q k a hac
  let beta := FixedPoint.sourceOrdinal q k b hbc
  have he : globalCollapse (base q) k alpha.val = globalCollapse (base q) k beta.val := hv
  exact ⟨rfl, (globalCollapse_eq_iff (base q) (base_pos q hq) k alpha beta
    (FixedPoint.checked_theta_sort q k a ha) (FixedPoint.checked_theta_sort q k b hb)).mp he⟩

private theorem atom_original (q : Nat) (t a : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) (ha : a ∈ atoms t) :
    check q a = true ∧ Normal q a := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hs := (Comparison.atoms_spec q _ hq t
    (NativeContext.checked_admissible q t ht) hn).1 a ha
  exact ⟨Comparison.admitted_checked q _ hq a hs.1, hs.2⟩

private theorem atoms_sum_size_lt (a b x : RelativeTerm Nat) (hx : x ∈ atoms (.sum a b)) :
    x.size < (.sum a b : RelativeTerm Nat).size := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (Comparison.atoms_size_le a x hx).trans_lt (RelativeTerm.sum_left_size_lt a b)
  · exact (Comparison.atoms_size_le b x hx).trans_lt (RelativeTerm.sum_right_size_lt a b)

private theorem aligned_words (q : Nat) (as bs : List (RelativeTerm Nat))
    (hv : as.map (denote q) = bs.map (denote q))
    (hr : ∀ a ∈ as, ∀ b ∈ bs, denote q a = denote q b →
      indicator q a = indicator q b ∧ ∀ m, highBits q m a = highBits q m b) :
    as.map (indicator q) = bs.map (indicator q) ∧
      ∀ m, as.flatMap (highBits q m) = bs.flatMap (highBits q m) := by
  revert bs hv hr
  induction as with
  | nil =>
    intro bs hv _
    have hb : bs = [] := List.map_eq_nil_iff.mp hv.symm
    subst bs
    exact ⟨rfl, fun _ => rfl⟩
  | cons a as ih =>
    intro bs hv hr
    cases bs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b bs =>
      have he := List.cons.inj hv
      have hh := hr a List.mem_cons_self b List.mem_cons_self he.1
      have ht := ih bs he.2 (fun x hx y hy =>
        hr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      refine ⟨by rw [List.map_cons, List.map_cons, hh.1, ht.1], ?_⟩
      intro m
      rw [List.flatMap_cons, List.flatMap_cons, hh.2 m, ht.2 m]

private theorem via_atoms (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (hnt : Normal q t) (hnu : Normal q u)
    (hv : denote q t = denote q u)
    (hr : ∀ x ∈ atoms t, ∀ y ∈ atoms u, denote q x = denote q y →
      indicator q x = indicator q y ∧ ∀ m, highBits q m x = highBits q m y) :
    indicator q t = indicator q u ∧ ∀ m, highBits q m t = highBits q m u := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hw : (atoms t).map (denote q) = (atoms u).map (denote q) := by
    rw [Comparison.atoms_anf q _ hq t (NativeContext.checked_admissible q t ht) hnt,
      Comparison.atoms_anf q _ hq u (NativeContext.checked_admissible q u hu) hnu, hv]
  have he := aligned_words q (atoms t) (atoms u) hw hr
  constructor
  · rw [indicator_atomBits q t ht hnt, indicator_atomBits q u hu hnu, he.1]
  · intro m
    rw [← SourceChi.Arithmetic.highBits_atoms, ← SourceChi.Arithmetic.highBits_atoms]
    exact he.2 m

/-- Actual same-q value invariance on BOTH original admitted weak-normal
full-sort inputs, including zero-prefix and atomic parameter spellings. -/
theorem indicator_highBits_invariant (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) (hv : denote q t = denote q u) :
    indicator q t = indicator q u ∧ ∀ m, highBits q m t = highBits q m u := by
  have H : ∀ n : Nat, ∀ t u : RelativeTerm Nat, t.size + u.size = n →
      check q t = true → check q u = true → Normal q t → Normal q u → denote q t = denote q u →
      indicator q t = indicator q u ∧ ∀ m, highBits q m t = highBits q m u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t u hs ht hu hnt hnu hv
      have recur (x y : RelativeTerm Nat) (hsize : x.size + y.size < n)
          (hx : check q x = true) (hy : check q y = true) (hnx : Normal q x) (hny : Normal q y)
          (he : denote q x = denote q y) :
          indicator q x = indicator q y ∧ ∀ m, highBits q m x = highBits q m y :=
        ih (x.size + y.size) hsize x y rfl hx hy hnx hny he
      have atoms_recur (hsize : ∀ x ∈ atoms t, ∀ y ∈ atoms u, x.size + y.size < n) :
          indicator q t = indicator q u ∧ ∀ m, highBits q m t = highBits q m u := by
        apply via_atoms q t u ht hu hnt hnu hv
        intro x hx y hy he
        have hcx := atom_original q t x ht hnt hx
        have hcy := atom_original q u y hu hnu hy
        exact recur x y (hsize x hx y hy) hcx.1 hcy.1 hcx.2 hcy.2 he
      cases t with
      | sum a b =>
        apply atoms_recur
        intro x hx y hy
        have hxs := atoms_sum_size_lt a b x hx
        have hys := Comparison.atoms_size_le u y hy
        omega
      | parameter p =>
        cases u with
        | sum a b =>
          apply atoms_recur
          intro x hx y hy
          have hxs := Comparison.atoms_size_le (.parameter p) x hx
          have hys := atoms_sum_size_lt a b y hy
          omega
        | parameter v =>
          exact ⟨rfl, fun m => by rw [SourceChi.Arithmetic.highBits_parameter,
            SourceChi.Arithmetic.highBits_parameter]⟩
        | theta k a =>
          have hp := FixedPoint.checked_parameter_lt_base q p ht
          have hb : base q ≤ denote q (.theta k a) :=
            ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)).trans
              (FixedPoint.checked_theta_range q k a hu).1
          rw [← hv] at hb
          exact False.elim (hp.not_ge hb)
      | theta k a =>
        cases u with
        | sum b c =>
          apply atoms_recur
          intro x hx y hy
          have hxs := Comparison.atoms_size_le (.theta k a) x hx
          have hys := atoms_sum_size_lt b c y hy
          omega
        | parameter p =>
          have hp := FixedPoint.checked_parameter_lt_base q p hu
          have hb : base q ≤ denote q (.theta k a) :=
            ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)).trans
              (FixedPoint.checked_theta_range q k a ht).1
          rw [hv] at hb
          exact False.elim (hp.not_ge hb)
        | theta l b =>
          obtain ⟨hkl, he⟩ := theta_value_injective q k l a b ht hu hv
          subst l
          have hsize : a.size + b.size < n := by
            have ha := RelativeTerm.theta_arg_size_lt k a
            have hb := RelativeTerm.theta_arg_size_lt k b
            omega
          have hh := recur a b hsize (FixedPoint.checked_theta_argument q k a ht)
            (FixedPoint.checked_theta_argument q k b hu) hnt hnu he
          have hc := SourceChi.Arithmetic.theta_branch_agreement q k a b ht hu hnt hnu he
          have hchi : indicator q (.theta k a) = indicator q (.theta k b) := by
            rw [theta_indicator_bits, theta_indicator_bits, hc.1, hc.2, hh.1, hh.2 k]
          refine ⟨hchi, ?_⟩
          intro m
          rw [SourceChi.Arithmetic.highBits_theta, SourceChi.Arithmetic.highBits_theta]
          change cond (decide (m + 1 < k + 1)) [indicator q (.theta k a)] [] =
            cond (decide (m + 1 < k + 1)) [indicator q (.theta k b)] []
          rw [hchi]
  exact H (t.size + u.size) t u rfl ht hu hnt hnu hv

theorem indicator_invariant (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) (hv : denote q t = denote q u) :
    indicator q t = indicator q u := (indicator_highBits_invariant q t u ht hu hnt hnu hv).1

theorem highBits_invariant (q m : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) (hv : denote q t = denote q u) :
    highBits q m t = highBits q m u := (indicator_highBits_invariant q t u ht hu hnt hnu hv).2 m

theorem chiCode_invariant (q c d : Nat) (hc : SourceChi.inputCheck q c = true)
    (hd : SourceChi.inputCheck q d = true) (hv : interpretation q c = interpretation q d) :
    chiCode q c = chiCode q d := by
  have hs := (SourceChi.inputCheck_exact q c).mp hc
  have ht := (SourceChi.inputCheck_exact q d).mp hd
  obtain ⟨t, rfl, hct⟩ := (checkCode_exact q c).mp hs.1
  obtain ⟨u, rfl, hdu⟩ := (checkCode_exact q d).mp ht.1
  have hn : Normal q t := by simpa only [ThetaCourse.rawTree_code] using hs.2
  have hm : Normal q u := by simpa only [ThetaCourse.rawTree_code] using ht.2
  rw [chiCode_correct q t hct hn, chiCode_correct q u hdu hm]
  exact indicator_invariant q t u hct hdu hn hm (by simpa only [interpretation_code] using hv)

/-- Every originally admitted raw spelling is genuinely normalized; the
normal invariance theorem is then applicable to both constructed outputs. -/
theorem rawChiCode_invariant (q c d : Nat) (hc : checkCode q c = true)
    (hd : checkCode q d = true) (hv : interpretation q c = interpretation q d) :
    rawChiCode q c = rawChiCode q d := by
  have hs := Normalization.normalizeCode_accepted q c hc
  have ht := Normalization.normalizeCode_accepted q d hd
  have he := chiCode_invariant q _ _ hs.1 ht.1 (hs.2.trans (hv.trans ht.2.symm))
  simp only [rawChiCode, rawInputCheck, hc, hd, Bool.true_and, he]

private theorem dual_not_chi (q c : Nat) (hc : SourceChi.inputCheck q c = true) :
    dualCode q c = !(chiCode q c) := by
  simp only [dualCode, chiCode, hc, Bool.true_and]

theorem dualCode_invariant (q c d : Nat) (hc : SourceChi.inputCheck q c = true)
    (hd : SourceChi.inputCheck q d = true) (hv : interpretation q c = interpretation q d) :
    dualCode q c = dualCode q d := by
  rw [dual_not_chi q c hc, dual_not_chi q d hd, chiCode_invariant q c d hc hd hv]

theorem rawDualCode_invariant (q c d : Nat) (hc : checkCode q c = true)
    (hd : checkCode q d = true) (hv : interpretation q c = interpretation q d) :
    rawDualCode q c = rawDualCode q d := by
  have hs := Normalization.normalizeCode_accepted q c hc
  have ht := Normalization.normalizeCode_accepted q d hd
  have he := dualCode_invariant q _ _ hs.1 ht.1 (hs.2.trans (hv.trans ht.2.symm))
  simp only [rawDualCode, rawInputCheck, hc, hd, Bool.true_and, he]

/-- Reverse same-positive-public-epsilon return agreement follows from
real normal native values and the actual forward parameter bridge. -/
theorem returnedCode_chi (s c : Nat)
    (hc : SourceChi.inputCheck (NativePublicBridge.contextCode s) c = true) :
    chiCode (NativePublicBridge.contextCode s) c =
      Hereditary.SourceChi.chiCode (s + 1) (NativePublicReturn.returnedCode s c) := by
  have hr := NativePublicReturn.returnedCode_normal_spec s c hc
  have ht := NativePublicBridge.translateCode_accepted s _ hr.1
  have hv := (NativePublicBridge.translateCode_value s (NativePublicReturn.returnedCode s c)).trans hr.2
  exact (chiCode_invariant _ _ c ht hc hv).symm.trans
    (NativePublicBridge.chiCode_agreement s _ hr.1)

theorem returnedCode_dual (s c : Nat)
    (hc : SourceChi.inputCheck (NativePublicBridge.contextCode s) c = true) :
    dualCode (NativePublicBridge.contextCode s) c =
      Hereditary.SourceChi.dualCode (s + 1) (NativePublicReturn.returnedCode s c) := by
  have hr := NativePublicReturn.returnedCode_normal_spec s c hc
  have ht := NativePublicBridge.translateCode_accepted s _ hr.1
  have hv := (NativePublicBridge.translateCode_value s (NativePublicReturn.returnedCode s c)).trans hr.2
  exact (dualCode_invariant _ _ c ht hc hv).symm.trans
    (NativePublicBridge.dualCode_agreement s _ hr.1)

/-- Full original raw admission: normalize natively on one side and
publicly AFTER the actual return on the other. Equality is only derived
for their real normal values, never asserted for their literal spellings. -/
theorem rawReturnCode_chi (s c : Nat)
    (hc : checkCode (NativePublicBridge.contextCode s) c = true) :
    rawChiCode (NativePublicBridge.contextCode s) c =
      Hereditary.SourceChi.chiCode (s + 1) (NativePublicReturn.rawReturnCode s c) := by
  have hn := Normalization.normalizeCode_accepted (NativePublicBridge.contextCode s) c hc
  have hr := NativePublicReturn.rawReturnCode_spec s c hc
  have ht := NativePublicBridge.translateCode_accepted s _ hr.1
  have hv := (NativePublicBridge.translateCode_value s (NativePublicReturn.rawReturnCode s c)).trans hr.2
  have he := chiCode_invariant _ _ _ hn.1 ht (hn.2.trans hv.symm)
  calc
    rawChiCode (NativePublicBridge.contextCode s) c =
        chiCode (NativePublicBridge.contextCode s) (Normalization.normalizeCode (NativePublicBridge.contextCode s) c) := by
      simp only [rawChiCode, rawInputCheck, hc, Bool.true_and]
    _ = chiCode (NativePublicBridge.contextCode s)
        (NativePublicBridge.translateCode s (NativePublicReturn.rawReturnCode s c)) := he
    _ = Hereditary.SourceChi.chiCode (s + 1) (NativePublicReturn.rawReturnCode s c) :=
      NativePublicBridge.chiCode_agreement s _ hr.1

theorem rawReturnCode_dual (s c : Nat)
    (hc : checkCode (NativePublicBridge.contextCode s) c = true) :
    rawDualCode (NativePublicBridge.contextCode s) c =
      Hereditary.SourceChi.dualCode (s + 1) (NativePublicReturn.rawReturnCode s c) := by
  have hn := Normalization.normalizeCode_accepted (NativePublicBridge.contextCode s) c hc
  have hr := NativePublicReturn.rawReturnCode_spec s c hc
  have ht := NativePublicBridge.translateCode_accepted s _ hr.1
  have hv := (NativePublicBridge.translateCode_value s (NativePublicReturn.rawReturnCode s c)).trans hr.2
  have he := dualCode_invariant _ _ _ hn.1 ht (hn.2.trans hv.symm)
  calc
    rawDualCode (NativePublicBridge.contextCode s) c =
        dualCode (NativePublicBridge.contextCode s) (Normalization.normalizeCode (NativePublicBridge.contextCode s) c) := by
      simp only [rawDualCode, rawInputCheck, hc, Bool.true_and]
    _ = dualCode (NativePublicBridge.contextCode s)
        (NativePublicBridge.translateCode s (NativePublicReturn.rawReturnCode s c)) := he
    _ = Hereditary.SourceChi.dualCode (s + 1) (NativePublicReturn.rawReturnCode s c) :=
      NativePublicBridge.dualCode_agreement s _ hr.1

/-- The adapter executes genuine public normalization AFTER actual return. -/
def returnChi (s c : Nat) : Bool := checkCode (NativePublicBridge.contextCode s) c &&
  Hereditary.SourceChi.chiCode (s + 1) (NativePublicReturn.rawReturnCode s c)

theorem returnChi_primrec : Primrec₂ returnChi := by
  have hg := checkCode_primrec.comp (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd
  have hv := Hereditary.SourceChi.chiCode_primrec.comp (Primrec.succ.comp Primrec.fst)
    NativePublicReturn.rawReturnCode_primrec
  exact (Primrec.and.comp hg hv).to₂

/-- Exact on every natural query, including malformed/rejected inputs. -/
theorem returnChi_agreement (s c : Nat) :
    returnChi s c = rawChiCode (NativePublicBridge.contextCode s) c := by
  cases hc : checkCode (NativePublicBridge.contextCode s) c with
  | false => simp only [returnChi, rawChiCode, rawInputCheck, hc, Bool.false_and]
  | true => simp only [returnChi, hc, Bool.true_and, rawReturnCode_chi s c hc]

theorem returnChi_invariant (s c d : Nat)
    (hc : checkCode (NativePublicBridge.contextCode s) c = true)
    (hd : checkCode (NativePublicBridge.contextCode s) d = true)
    (hv : interpretation (NativePublicBridge.contextCode s) c =
      interpretation (NativePublicBridge.contextCode s) d) : returnChi s c = returnChi s d := by
  rw [returnChi_agreement, returnChi_agreement]
  exact rawChiCode_invariant _ c d hc hd hv

/-- Original positive public levels inherit SAME-base normal chi invariance
through the real parameter bridge. This is not a different-base translation. -/
theorem publicChiCode_invariant (s c d : Nat)
    (hc : Hereditary.SourceDecomposition.inputCheck (s + 1) c = true)
    (hd : Hereditary.SourceDecomposition.inputCheck (s + 1) d = true)
    (hv : Hereditary.interpretation (s + 1) c = Hereditary.interpretation (s + 1) d) :
    Hereditary.SourceChi.chiCode (s + 1) c = Hereditary.SourceChi.chiCode (s + 1) d := by
  have ht := NativePublicBridge.translateCode_accepted s c hc
  have hu := NativePublicBridge.translateCode_accepted s d hd
  have he := chiCode_invariant _ _ _ ht hu
    ((NativePublicBridge.translateCode_value s c).trans
      (hv.trans (NativePublicBridge.translateCode_value s d).symm))
  simpa only [NativePublicBridge.chiCode_agreement s c hc,
    NativePublicBridge.chiCode_agreement s d hd] using he

theorem publicDualCode_invariant (s c d : Nat)
    (hc : Hereditary.SourceDecomposition.inputCheck (s + 1) c = true)
    (hd : Hereditary.SourceDecomposition.inputCheck (s + 1) d = true)
    (hv : Hereditary.interpretation (s + 1) c = Hereditary.interpretation (s + 1) d) :
    Hereditary.SourceChi.dualCode (s + 1) c = Hereditary.SourceChi.dualCode (s + 1) d := by
  have ht := NativePublicBridge.translateCode_accepted s c hc
  have hu := NativePublicBridge.translateCode_accepted s d hd
  have he := dualCode_invariant _ _ _ ht hu
    ((NativePublicBridge.translateCode_value s c).trans
      (hv.trans (NativePublicBridge.translateCode_value s d).symm))
  simpa only [NativePublicBridge.dualCode_agreement s c hc,
    NativePublicBridge.dualCode_agreement s d hd] using he

/-- Public raw spelling invariance uses BOTH actually constructed public
normal forms and retains every original public admission guard. -/
theorem publicRawChiCode_invariant (s c d : Nat)
    (hc : Hereditary.checkCode (s + 1) c = true)
    (hd : Hereditary.checkCode (s + 1) d = true)
    (hv : Hereditary.interpretation (s + 1) c = Hereditary.interpretation (s + 1) d) :
    Hereditary.SourceChi.rawChiCode (s + 1) c = Hereditary.SourceChi.rawChiCode (s + 1) d := by
  have hn := Theta.Normalization.normalizeCode_accepted (s + 1) c hc
  have hm := Theta.Normalization.normalizeCode_accepted (s + 1) d hd
  have he := publicChiCode_invariant s _ _ hn.1 hm.1 (hn.2.trans (hv.trans hm.2.symm))
  have hrc := (Hereditary.SourceChi.rawInputCheck_exact (s + 1) c).mpr ⟨Nat.succ_pos s, hc⟩
  have hrd := (Hereditary.SourceChi.rawInputCheck_exact (s + 1) d).mpr ⟨Nat.succ_pos s, hd⟩
  simp only [Hereditary.SourceChi.rawChiCode, hrc, hrd, Bool.true_and, he]

theorem publicRawDualCode_invariant (s c d : Nat)
    (hc : Hereditary.checkCode (s + 1) c = true)
    (hd : Hereditary.checkCode (s + 1) d = true)
    (hv : Hereditary.interpretation (s + 1) c = Hereditary.interpretation (s + 1) d) :
    Hereditary.SourceChi.rawDualCode (s + 1) c = Hereditary.SourceChi.rawDualCode (s + 1) d := by
  have hn := Theta.Normalization.normalizeCode_accepted (s + 1) c hc
  have hm := Theta.Normalization.normalizeCode_accepted (s + 1) d hd
  have he := publicDualCode_invariant s _ _ hn.1 hm.1 (hn.2.trans (hv.trans hm.2.symm))
  have hrc := (Hereditary.SourceChi.rawInputCheck_exact (s + 1) c).mpr ⟨Nat.succ_pos s, hc⟩
  have hrd := (Hereditary.SourceChi.rawInputCheck_exact (s + 1) d).mpr ⟨Nat.succ_pos s, hd⟩
  simp only [Hereditary.SourceChi.rawDualCode, hrc, hrd, Bool.true_and, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Invariance
