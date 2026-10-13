import Alexander313.Wilken.HereditaryNativeHeight
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.HereditaryNativeBaseTransformationSupport

/-!
# Value-invariant native height and the actual least finite fragment

The height of two original weak-normal native terms of equal value is equal.
The proof aligns their genuine canonical ANF value words. Sum representatives
are strictly smaller in syntax size; theta cardinal ranges and real collapse
injection force equal indices and equal argument values. Parameters remain
atomic, with height zero, even when their public payloads have internal trees.

Actual native normalization therefore computes a height independent of the
original raw spelling. It is the least finite-fragment index among ALL original
admitted native representations of that value. The algorithm and its fragment
predicate are genuinely PR and retain the original coded-epsilon checks.

This establishes a canonical value-height on the original native domain,
including the exact zero-height boundary below the base. Base substitution
with the chosen-presentation atomic-stop Par bound preserves this height by
context-independent normalization.
The higher printed endpoints in Lemma 2.22, cross-base iota bounds 2.46,
lambda/mu descent 3.7 and rho's height estimate remain separate. No ordinal
height, representation, minimality or effectiveness oracle is assumed.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.CanonicalHeight

open ThetaCourse
open Comparison (Normal atoms)

/-- Principal extraction records every native theta contributing to height;
public parameter heads remain native height-zero leaves. -/
theorem height_le_iff_atoms (t : RelativeTerm Nat) (n : Nat) :
    t.height ≤ n ↔ ∀ a ∈ atoms t, a.height ≤ n := by
  constructor
  · intro ht a ha
    exact (Height.atoms_height t a ha).trans ht
  · intro ha
    revert ha
    induction t with
    | parameter p => intro _; exact Nat.zero_le n
    | sum a b iha ihb =>
      intro ha
      exact max_le
        (iha (fun x hx => ha x (List.mem_append.mpr (Or.inl hx))))
        (ihb (fun x hx => ha x (List.mem_append.mpr (Or.inr hx))))
    | theta k a => intro ha; exact ha (.theta k a) List.mem_cons_self

theorem height_eq_zero_of_atoms_nil (t : RelativeTerm Nat) (ht : atoms t = []) :
    t.height = 0 := by
  apply Nat.le_zero.mp
  apply (height_le_iff_atoms t 0).mpr
  intro a ha
  rw [ht] at ha
  exact False.elim (List.not_mem_nil ha)

private theorem atom_original (q : Nat) (t a : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) (ha : a ∈ atoms t) :
    check q a = true ∧ Normal q a := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hs := (Comparison.atoms_spec q _ hq t
    (NativeContext.checked_admissible q t ht) hn).1 a ha
  exact ⟨Comparison.admitted_checked q _ hq a hs.1, hs.2⟩

private theorem atoms_sum_size_lt (a b x : RelativeTerm Nat)
    (hx : x ∈ atoms (.sum a b)) : x.size < (.sum a b : RelativeTerm Nat).size := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (Comparison.atoms_size_le a x hx).trans_lt (RelativeTerm.sum_left_size_lt a b)
  · exact (Comparison.atoms_size_le b x hx).trans_lt (RelativeTerm.sum_right_size_lt a b)

private theorem aligned_heights (q : Nat) (as bs : List (RelativeTerm Nat))
    (hv : as.map (denote q) = bs.map (denote q))
    (hr : ∀ a ∈ as, ∀ b ∈ bs, denote q a = denote q b → a.height = b.height) :
    as.map RelativeTerm.height = bs.map RelativeTerm.height := by
  revert bs hv hr
  induction as with
  | nil =>
    intro bs hv _
    have hb : bs = [] := List.map_eq_nil_iff.mp hv.symm
    subst bs
    rfl
  | cons a as ih =>
    intro bs hv hr
    cases bs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b bs =>
      have he := List.cons.inj hv
      have hh := hr a List.mem_cons_self b List.mem_cons_self he.1
      have ht := ih bs he.2 (fun x hx y hy =>
        hr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      rw [List.map_cons, List.map_cons, hh, ht]

private theorem via_atoms (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (hnt : Normal q t) (hnu : Normal q u)
    (hv : denote q t = denote q u)
    (hr : ∀ x ∈ atoms t, ∀ y ∈ atoms u, denote q x = denote q y → x.height = y.height) :
    t.height = u.height := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hw : (atoms t).map (denote q) = (atoms u).map (denote q) := by
    rw [Comparison.atoms_anf q _ hq t (NativeContext.checked_admissible q t ht) hnt,
      Comparison.atoms_anf q _ hq u (NativeContext.checked_admissible q u hu) hnu, hv]
  have hh := aligned_heights q (atoms t) (atoms u) hw hr
  apply Nat.le_antisymm
  · apply (height_le_iff_atoms t u.height).mpr
    intro a ha
    have hmem : a.height ∈ (atoms u).map RelativeTerm.height := by
      rw [← hh]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
    exact he ▸ Height.atoms_height u b hb
  · apply (height_le_iff_atoms u t.height).mpr
    intro b hb
    have hmem : b.height ∈ (atoms t).map RelativeTerm.height := by
      rw [hh]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    exact he ▸ Height.atoms_height t a ha

/-- Genuine SAME-q value-height invariance on both original admitted
weak-normal inputs. Equal raw spellings are not an assumption. -/
theorem height_invariant (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) (hv : denote q t = denote q u) :
    t.height = u.height := by
  have H : ∀ n : Nat, ∀ t u : RelativeTerm Nat, t.size + u.size = n →
      check q t = true → check q u = true → Normal q t → Normal q u →
      denote q t = denote q u → t.height = u.height := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t u hs ht hu hnt hnu hv
      have recur (x y : RelativeTerm Nat) (hsize : x.size + y.size < n)
          (hx : check q x = true) (hy : check q y = true)
          (hnx : Normal q x) (hny : Normal q y) (he : denote q x = denote q y) :
          x.height = y.height := ih (x.size + y.size) hsize x y rfl hx hy hnx hny he
      have atoms_recur (hsize : ∀ x ∈ atoms t, ∀ y ∈ atoms u, x.size + y.size < n) :
          t.height = u.height := by
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
        | parameter v => rfl
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
          obtain ⟨hkl, he⟩ := SourceChi.Invariance.theta_value_injective q k l a b ht hu hv
          subst l
          have hsize : a.size + b.size < n := by
            have ha := RelativeTerm.theta_arg_size_lt k a
            have hb := RelativeTerm.theta_arg_size_lt k b
            omega
          have hh := recur a b hsize (FixedPoint.checked_theta_argument q k a ht)
            (FixedPoint.checked_theta_argument q k b hu) hnt hnu he
          exact congrArg (max (k + 1)) hh
  exact H (t.size + u.size) t u rfl ht hu hnt hnu hv

/-- Empty canonical ANF is handled without a missing principal witness. -/
theorem normal_zero_height (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) (hv : denote q t = 0) : t.height = 0 := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := Comparison.atoms_anf q _ hq t (NativeContext.checked_admissible q t ht) hn
  rw [hv, canonicalANF_zero] at ha
  exact height_eq_zero_of_atoms_nil t (List.map_eq_nil_iff.mp ha)

theorem normalized_height_invariant (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (hv : denote q t = denote q u) :
    (Normalization.normalize q t).height = (Normalization.normalize q u).height := by
  have hs := Normalization.normalize_checked q t ht
  have hr := Normalization.normalize_checked q u hu
  exact height_invariant q _ _ hs.1 hr.1 hs.2.1 hr.2.1
    (hs.2.2.trans (hv.trans hr.2.2.symm))

/-- Actual normalization attains no larger height than ANY original
admitted representation of its value, whether that representation is normal. -/
theorem normalized_height_minimal (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (hv : denote q t = denote q u) :
    (Normalization.normalize q t).height ≤ u.height := by
  rw [normalized_height_invariant q t u ht hu hv]
  exact Height.normalize_height q u

theorem normalCode_height_invariant (q c d : Nat)
    (hc : Comparison.acceptedCode q c = true) (hd : Comparison.acceptedCode q d = true)
    (hv : interpretation q c = interpretation q d) : heightCode c = heightCode d := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  have hr := (Comparison.acceptedCode_exact q d).mp hd
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hs.1
  obtain ⟨u, rfl, hu⟩ := (checkCode_exact q d).mp hr.1
  have hn : Normal q t := by simpa only [rawTree_code] using hs.2
  have hm : Normal q u := by simpa only [rawTree_code] using hr.2
  simpa only [heightCode_code] using height_invariant q t u ht hu hn hm
    (by simpa only [interpretation_code] using hv)

/-- The finite algorithm defining ordinal value-height on original codes. -/
def canonicalHeightCode (q c : Nat) : Nat := heightCode (Normalization.normalizeCode q c)

theorem canonicalHeightCode_primrec : Primrec₂ canonicalHeightCode :=
  (heightCode_primrec.comp
    (Normalization.Effective.normalizeCode_primrec.comp Primrec.fst Primrec.snd)).to₂

theorem canonicalHeightCode_invariant (q c d : Nat)
    (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hv : interpretation q c = interpretation q d) : canonicalHeightCode q c = canonicalHeightCode q d := by
  have hs := Normalization.normalizeCode_accepted q c hc
  have hr := Normalization.normalizeCode_accepted q d hd
  exact normalCode_height_invariant q _ _ hs.1 hr.1 (hs.2.trans (hv.trans hr.2.symm))

theorem canonicalHeightCode_normal (q c : Nat) (hc : Comparison.acceptedCode q c = true) :
    canonicalHeightCode q c = heightCode c := by
  have hi := ((Comparison.acceptedCode_exact q c).mp hc).1
  have hs := Normalization.normalizeCode_accepted q c hi
  exact normalCode_height_invariant q _ c hs.1 hc hs.2

theorem canonicalHeightCode_le_raw (q c : Nat) (hc : checkCode q c = true) :
    canonicalHeightCode q c ≤ heightCode c := Height.normalizeCode_height q c hc

theorem canonicalHeightCode_zero (q c : Nat) (hc : checkCode q c = true)
    (hv : interpretation q c = 0) : canonicalHeightCode q c = 0 := by
  have hs := Normalization.normalizeCode_checked q c hc
  obtain ⟨t, he, ht⟩ := (checkCode_exact q (Normalization.normalizeCode q c)).mp hs.1
  have hn : Normal q t := by simpa only [← he, rawTree_code] using hs.2.1
  have hz : denote q t = 0 := by simpa only [← he, interpretation_code] using hs.2.2.trans hv
  simpa only [canonicalHeightCode, ← he, heightCode_code] using normal_zero_height q t ht hn hz

theorem canonicalHeightCode_le_representation (q c : Nat) (t : RelativeTerm Nat)
    (hc : checkCode q c = true) (ht : check q t = true)
    (hv : interpretation q c = denote q t) : canonicalHeightCode q c ≤ t.height := by
  have hd : checkCode q t.code = true := by simpa only [checkCode_code] using ht
  rw [canonicalHeightCode_invariant q c t.code hc hd (by simpa only [interpretation_code] using hv)]
  simpa only [heightCode_code] using canonicalHeightCode_le_raw q t.code hd

/-- The minimum quantifies over every originally admitted native term,
not merely the output of our normalizer or normal spellings. -/
theorem canonicalHeightCode_fragment_iff (q n c : Nat) (hc : checkCode q c = true) :
    canonicalHeightCode q c ≤ n ↔
      ∃ t : RelativeTerm Nat, admissible q n t ∧ denote q t = interpretation q c := by
  constructor
  · intro hh
    obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
    have hs := Normalization.normalize_checked q t ht
    have hn : (Normalization.normalize q t).height ≤ n := by
      simpa only [canonicalHeightCode, Normalization.normalizeCode, checkCode_code, ht,
        Bool.cond_true, rawTree_code, heightCode_code] using hh
    exact ⟨Normalization.normalize q t, Comparison.checked_admissible q n _ hs.1 hn,
      by simpa only [interpretation_code] using hs.2.2⟩
  · rintro ⟨t, ht, hv⟩
    have hq := (Bool.and_eq_true.mp hc).1
    exact (canonicalHeightCode_le_representation q c t hc
      (Comparison.admitted_checked q n hq t ht) hv.symm).trans (Height.admissible_height_le q n t ht)

theorem canonicalHeightCode_attained (q c : Nat) (hc : checkCode q c = true) :
    ∃ t : RelativeTerm Nat, admissible q (canonicalHeightCode q c) t ∧
      Normal q t ∧ denote q t = interpretation q c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  have hs := Normalization.normalize_checked q t ht
  have hh : (Normalization.normalize q t).height = canonicalHeightCode q t.code := by
    simp only [canonicalHeightCode, Normalization.normalizeCode, checkCode_code, ht,
      Bool.cond_true, rawTree_code, heightCode_code]
  exact ⟨Normalization.normalize q t, Comparison.checked_admissible q _ _ hs.1 hh.le,
    hs.2.1, by simpa only [interpretation_code] using hs.2.2⟩

/-- Positive finite-fragment recognizer for the VALUE, with original whole
admission checked internally. It performs actual normalization, not search. -/
def canonicalFragmentCheck (q n c : Nat) : Bool := checkCode q c && decide (canonicalHeightCode q c ≤ n)

theorem canonicalFragmentCheck_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => canonicalFragmentCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hn := Primrec.snd.comp Primrec.fst
  have hh := canonicalHeightCode_primrec.comp hq Primrec.snd
  exact Primrec.and.comp (checkCode_primrec.comp hq Primrec.snd) (Primrec.nat_le.comp hh hn).decide

theorem canonicalFragmentCheck_exact (q n c : Nat) : canonicalFragmentCheck q n c = true ↔
    checkCode q c = true ∧
      ∃ t : RelativeTerm Nat, admissible q n t ∧ denote q t = interpretation q c := by
  simp only [canonicalFragmentCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_fragment_iff q n c hc).mp hh⟩
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_fragment_iff q n c hc).mpr hh⟩

theorem canonicalFragmentCheck_invariant (q n c d : Nat)
    (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hv : interpretation q c = interpretation q d) :
    canonicalFragmentCheck q n c = canonicalFragmentCheck q n d := by
  simp only [canonicalFragmentCheck, hc, hd, Bool.true_and, canonicalHeightCode_invariant q c d hc hd hv]

theorem canonicalHeightCode_parts (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    canonicalHeightCode q (Decomposition.highCode m c) ≤ canonicalHeightCode q c ∧
      canonicalHeightCode q (Decomposition.lowCode m c) ≤ canonicalHeightCode q c := by
  have hs := Decomposition.parts_accepted q m c hc
  have hi := ((Decomposition.inputCheck_exact q c).mp hc).1
  have hn : Comparison.acceptedCode q c = true := hc
  rw [canonicalHeightCode_normal q c hn, canonicalHeightCode_normal q _ hs.1,
    canonicalHeightCode_normal q _ hs.2]
  exact Height.parts_code_height q m c hi

/-- The same original tree admitted at two bases has the same canonical
height, even though its two ordinal values need not be equal. This follows
the actual context-independent normalizer, not collapse naturality. -/
theorem canonicalHeightCode_context (q v c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    canonicalHeightCode q c = canonicalHeightCode v c :=
  congrArg heightCode (BaseTransformation.normalizeCode_context q v c hq hv)

theorem height_eq_zero_iff_pure (t : RelativeTerm Nat) :
    t.height = 0 ↔ BaseTransformation.Pure t := by
  induction t with
  | parameter p => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | sum a b iha ihb =>
    constructor
    · intro hh
      exact ⟨iha.mp (Nat.le_zero.mp ((le_max_left _ _).trans hh.le)),
        ihb.mp (Nat.le_zero.mp ((le_max_right _ _).trans hh.le))⟩
    · intro hp
      simp only [RelativeTerm.height, iha.mpr hp.1, ihb.mpr hp.2, max_self]
  | theta k a ih =>
    constructor
    · intro hh
      have hz : k + 1 ≤ 0 := (le_max_left _ _).trans hh.le
      omega
    · intro hp; exact False.elim hp

/-- The zero-fragment boundary is genuinely semantic: precisely the values
below the original epsilon base have canonical native height zero. -/
theorem canonicalHeightCode_zero_iff_below_base (q c : Nat) (hc : checkCode q c = true) :
    canonicalHeightCode q c = 0 ↔ interpretation q c < base q := by
  have hs := Normalization.normalizeCode_checked q c hc
  obtain ⟨t, he, ht⟩ := (checkCode_exact q (Normalization.normalizeCode q c)).mp hs.1
  have hv : denote q t = interpretation q c := by
    simpa only [← he, interpretation_code] using hs.2.2
  change heightCode (Normalization.normalizeCode q c) = 0 ↔ _
  rw [← he, heightCode_code, ← hv]
  exact (height_eq_zero_iff_pure t).trans (BaseTransformation.below_base_iff_pure q t ht).symm

/-- The atomic-stop Par bound on this chosen presentation derives the second
original admission. It is not a claim of unique printed Par across spellings.
The operation keeps all native theta indices and atomic parameter payloads. -/
theorem canonicalHeightCode_change_base (q v : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hv : baseCheck v = true)
    (hp : BaseTransformation.ParBounded q v t) :
    canonicalHeightCode q t.code = canonicalHeightCode v t.code := by
  have hs := BaseTransformation.check_change q v t ht hv
    ((BaseTransformation.parBounded_iff_payloads q v t ht hv).mp hp)
  exact canonicalHeightCode_context q v t.code
    (by simpa only [checkCode_code] using ht) (by simpa only [checkCode_code] using hs)

theorem canonicalFragmentCheck_context (q v n c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    canonicalFragmentCheck q n c = canonicalFragmentCheck v n c := by
  simp only [canonicalFragmentCheck, hq, hv, Bool.true_and, canonicalHeightCode_context q v c hq hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.CanonicalHeight
