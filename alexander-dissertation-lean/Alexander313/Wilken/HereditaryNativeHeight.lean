import Alexander313.Wilken.HereditaryNativeDecomposition

/-!
# Actual native syntax-height and finite-fragment construction bounds

Original public payloads remain atomic native parameters of height zero.
The genuine native principal-word extraction, suffix absorption, zero-prefix
reconstruction, raw normalization and cardinal decomposition do not increase
literal syntax height. Their original source admission and real denotations
are retained, including at the least fragment of the original written term.

The actual finite parser recognizes exactly original native admission plus
the literal height bound. This derives least-fragment admission for a fixed
written term, as motivated by Definition 2.21. It does not identify a unique
ordinal normal-form height, prove the ordinal characterization 2.22, or
construct the translations or lambda/mu bounds of 2.46 and 3.7. All candidates
remain uncompiled. No syntax or ordinal evaluation oracle is supplied.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Height

open ThetaCourse

/-- Public principal heads extracted from an atomic native payload stay
native parameter leaves; their internal public height is not opened. -/
theorem atoms_height (t a : RelativeTerm Nat) (ha : a ∈ Comparison.atoms t) :
    a.height ≤ t.height := by
  revert a ha
  induction t with
  | parameter p =>
    intro a ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact le_rfl
  | sum a b iha ihb =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact (iha s hs).trans (le_max_left _ _)
    · exact (ihb s hs).trans (le_max_right _ _)
  | theta k a ih =>
    intro s hs
    have he : s = .theta k a := List.mem_singleton.mp hs
    subst s
    exact le_rfl

theorem normalizeAtoms_height (q : Nat) (as : List (RelativeTerm Nat)) (a : RelativeTerm Nat)
    (ha : a ∈ Normalization.normalizeAtoms q as) (n : Nat)
    (hn : ∀ b ∈ as, b.height ≤ n) : a.height ≤ n :=
  hn a (Normalization.normalizeAtoms_mem q a as ha)

theorem buildRev_height_le (as : List (RelativeTerm Nat)) (n : Nat)
    (hn : ∀ a ∈ as, a.height ≤ n) : (Normalization.buildRev as).height ≤ n := by
  revert hn
  induction as with
  | nil => intro _; exact Nat.zero_le n
  | cons a as ih =>
    intro hn
    exact max_le (ih (fun b hb => hn b (List.mem_cons_of_mem _ hb))) (hn a List.mem_cons_self)

theorem buildAtoms_height_le (as : List (RelativeTerm Nat)) (n : Nat)
    (hn : ∀ a ∈ as, a.height ≤ n) : (Normalization.buildAtoms as).height ≤ n :=
  buildRev_height_le as.reverse n (fun a ha => hn a (List.mem_reverse.mp ha))

theorem buildRev_member_height (as : List (RelativeTerm Nat)) (a : RelativeTerm Nat)
    (ha : a ∈ as) : a.height ≤ (Normalization.buildRev as).height := by
  revert ha
  induction as with
  | nil => intro ha; simp only [List.not_mem_nil] at ha
  | cons b bs ih =>
    intro ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_right _ _
    · exact (ih ha).trans (le_max_left _ _)

theorem buildAtoms_member_height (as : List (RelativeTerm Nat)) (a : RelativeTerm Nat)
    (ha : a ∈ as) : a.height ≤ (Normalization.buildAtoms as).height :=
  buildRev_member_height as.reverse a (List.mem_reverse.mpr ha)

/-- Zero-prefix reconstruction has exactly the maximum atom height. -/
theorem buildAtoms_height_iff (as : List (RelativeTerm Nat)) (n : Nat) :
    (Normalization.buildAtoms as).height ≤ n ↔ ∀ a ∈ as, a.height ≤ n :=
  ⟨fun h a ha => (buildAtoms_member_height as a ha).trans h, buildAtoms_height_le as n⟩

/-- The actual recursive normalizer never introduces a higher theta index.
This structural bound holds even before admission is checked. -/
theorem normalize_height (q : Nat) (t : RelativeTerm Nat) :
    (Normalization.normalize q t).height ≤ t.height := by
  induction t with
  | parameter p => exact le_rfl
  | theta k a ih => exact max_le_max le_rfl ih
  | sum a b iha ihb =>
    apply buildAtoms_height_le
    intro s hs
    have hmem := Normalization.normalizeAtoms_mem q s _ hs
    rcases List.mem_append.mp hmem with ha | hb
    · exact (atoms_height _ s ha).trans (iha.trans (le_max_left _ _))
    · exact (atoms_height _ s hb).trans (ihb.trans (le_max_right _ _))

theorem word_height (c : Nat) (a : RelativeTerm Nat) (ha : a ∈ Decomposition.word c) :
    a.height ≤ (rawTree c).height := atoms_height (rawTree c) a ha

theorem highWord_height (m c : Nat) (a : RelativeTerm Nat) (ha : a ∈ Decomposition.highWord m c) :
    a.height ≤ (rawTree c).height := word_height c a ((Decomposition.highWord_mem m c a).mp ha).1

theorem lowWord_height (m c : Nat) (a : RelativeTerm Nat) (ha : a ∈ Decomposition.lowWord m c) :
    a.height ≤ (rawTree c).height := word_height c a ((Decomposition.lowWord_mem m c a).mp ha).1

theorem parts_height (m c : Nat) :
    (Decomposition.highPartTerm m c).height ≤ (rawTree c).height ∧
      (Decomposition.lowPartTerm m c).height ≤ (rawTree c).height :=
  ⟨buildAtoms_height_le _ _ (highWord_height m c), buildAtoms_height_le _ _ (lowWord_height m c)⟩

theorem rebuild_height (c : Nat) :
    (Decomposition.rebuildTerm c).height ≤ (rawTree c).height :=
  buildAtoms_height_le _ _ (word_height c)

/-- Every genuine finite source derivation limits all literal theta indices. -/
theorem admissible_height_le (q n : Nat) (t : RelativeTerm Nat) (ht : admissible q n t) :
    t.height ≤ n := by
  revert ht
  induction t with
  | parameter p => intro _; exact Nat.zero_le n
  | sum a b iha ihb =>
    intro ht
    cases ht.2 with
    | sum ha hb => exact max_le (iha ⟨ht.1.1, ha⟩) (ihb ⟨ht.1.2, hb⟩)
  | theta k a ih =>
    intro ht
    cases ht.2 with
    | theta h0k hkn hsort ha =>
      exact max_le (Nat.succ_le_of_lt hkn) (ih ⟨ht.1, ha⟩)

theorem admissible_iff_checked_height (q n : Nat) (hq : baseCheck q = true)
    (t : RelativeTerm Nat) : admissible q n t ↔ check q t = true ∧ t.height ≤ n :=
  ⟨fun ht => ⟨Comparison.admitted_checked q n hq t ht, admissible_height_le q n t ht⟩,
    fun h => Comparison.checked_admissible q n t h.1 h.2⟩

/-- The least fragment for THIS literal originally admitted term. -/
theorem checked_at_height (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    admissible q t.height t := Comparison.checked_admissible q t.height t ht le_rfl

theorem checked_finite_agreement_at_height (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    denote q t = finiteDenote q t.height t :=
  denote_eq_finite q t.height (Bool.and_eq_true.mp ht).1 t (checked_at_height q t ht).2

theorem normalize_at_original_height (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    admissible q t.height (Normalization.normalize q t) ∧
      Comparison.Normal q (Normalization.normalize q t) ∧
      (Normalization.normalize q t).height ≤ t.height ∧
      finiteDenote q t.height (Normalization.normalize q t) = finiteDenote q t.height t := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := checked_at_height q t ht
  have hs := Normalization.normalize_spec q t.height hq t ha
  exact ⟨hs.1, hs.2.1, normalize_height q t,
    Normalization.normalize_finiteDenote q t.height hq t ha⟩

theorem input_heightCode (q c : Nat) (hc : checkCode q c = true) : (rawTree c).height = heightCode c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  simp only [rawTree_code, heightCode_code]

theorem normalizeCode_height (q c : Nat) (hc : checkCode q c = true) :
    heightCode (Normalization.normalizeCode q c) ≤ heightCode c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
  simpa only [Normalization.normalizeCode, checkCode_code, ht, Bool.cond_true,
    rawTree_code, heightCode_code] using normalize_height q t

theorem parts_code_height (q m c : Nat) (hc : checkCode q c = true) :
    heightCode (Decomposition.highCode m c) ≤ heightCode c ∧
      heightCode (Decomposition.lowCode m c) ≤ heightCode c := by
  simpa only [Decomposition.highCode, Decomposition.lowCode, heightCode_code,
    input_heightCode q c hc] using parts_height m c

theorem rebuildCode_height (q c : Nat) (hc : checkCode q c = true) :
    heightCode (Decomposition.rebuildCode c) ≤ heightCode c := by
  simpa only [Decomposition.rebuildCode, heightCode_code, input_heightCode q c hc] using rebuild_height c

/-- Unlike a numerical bound alone, this guard executes the full original
payload, constructor, sort and coded-epsilon checks. -/
def fragmentCheck (q n c : Nat) : Bool := baseCheck q && finiteCheckCode q n c

theorem fragmentCheck_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => fragmentCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (baseCheck_primrec.comp (Primrec.fst.comp Primrec.fst)) finiteCheckCode_primrec

theorem fragmentCheck_exact (q n c : Nat) : fragmentCheck q n c = true ↔
    checkCode q c = true ∧ heightCode c ≤ n := by
  constructor
  · intro hc
    obtain ⟨hq, hf⟩ := Bool.and_eq_true.mp hc
    obtain ⟨t, rfl, ht⟩ := (finiteCheckCode_exact q n c).mp hf
    exact ⟨by simpa only [checkCode_code] using Comparison.admitted_checked q n hq t ht,
      by simpa only [heightCode_code] using admissible_height_le q n t ht⟩
  · rintro ⟨hc, hh⟩
    obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hc
    have ha := Comparison.checked_admissible q n t ht (by simpa only [heightCode_code] using hh)
    exact Bool.and_eq_true.mpr ⟨(Bool.and_eq_true.mp ht).1,
      by simpa only [finiteCheckCode_code] using (finiteCheck_exact q n t).mpr ha⟩

theorem fragmentCheck_at_height (q c : Nat) (hc : checkCode q c = true) :
    fragmentCheck q (heightCode c) c = true := (fragmentCheck_exact q _ c).mpr ⟨hc, le_rfl⟩

theorem fragmentCheck_below_height (q n c : Nat) (hn : n < heightCode c) : fragmentCheck q n c = false := by
  cases h : fragmentCheck q n c with
  | false => rfl
  | true => exact False.elim (hn.not_ge ((fragmentCheck_exact q n c).mp h).2)

theorem normalizeCode_fragment (q n c : Nat) (hc : fragmentCheck q n c = true) :
    fragmentCheck q n (Normalization.normalizeCode q c) = true := by
  have hs := (fragmentCheck_exact q n c).mp hc
  exact (fragmentCheck_exact q n _).mpr
    ⟨(Normalization.normalizeCode_checked q c hs.1).1,
      (normalizeCode_height q c hs.1).trans hs.2⟩

theorem parts_code_fragment (q n m c : Nat) (hc : Decomposition.inputCheck q c = true)
    (hn : heightCode c ≤ n) :
    fragmentCheck q n (Decomposition.highCode m c) = true ∧
      fragmentCheck q n (Decomposition.lowCode m c) = true := by
  have hi := ((Decomposition.inputCheck_exact q c).mp hc).1
  have hs := Decomposition.parts_accepted q m c hc
  have hh := parts_code_height q m c hi
  exact ⟨(fragmentCheck_exact q n _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp hs.1).1, hh.1.trans hn⟩,
    (fragmentCheck_exact q n _).mpr
      ⟨((Comparison.acceptedCode_exact q _).mp hs.2).1, hh.2.trans hn⟩⟩

theorem parts_at_original_height (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    admissible q (heightCode c) (Decomposition.highPartTerm m c) ∧
      admissible q (heightCode c) (Decomposition.lowPartTerm m c) ∧
      Comparison.Normal q (Decomposition.highPartTerm m c) ∧
      Comparison.Normal q (Decomposition.lowPartTerm m c) ∧
      (Decomposition.highPartTerm m c).height ≤ heightCode c ∧
      (Decomposition.lowPartTerm m c).height ≤ heightCode c := by
  have hi := ((Decomposition.inputCheck_exact q c).mp hc).1
  have hh : (rawTree c).height ≤ heightCode c := (input_heightCode q c hi).le
  have ha := Decomposition.parts_admissible q (heightCode c) m c hc hh
  have hn := Decomposition.parts_normal q m c hc
  have hs := parts_height m c
  exact ⟨ha.1, ha.2, hn.1, hn.2, hs.1.trans hh, hs.2.trans hh⟩

theorem parts_finite_agreement_at_original_height (q m c : Nat)
    (hc : Decomposition.inputCheck q c = true) :
    finiteDenote q (heightCode c) (Decomposition.highPartTerm m c) =
      omegaSequence (base q) (m + 1) * (interpretation q c / omegaSequence (base q) (m + 1)) ∧
    finiteDenote q (heightCode c) (Decomposition.lowPartTerm m c) =
      interpretation q c % omegaSequence (base q) (m + 1) := by
  have hq := (Bool.and_eq_true.mp (Decomposition.input_tree q c hc).1).1
  have ha := parts_at_original_height q m c hc
  have hv := Decomposition.parts_value q m c hc
  exact ⟨(denote_eq_finite q _ hq _ ha.1.2).symm.trans hv.1,
    (denote_eq_finite q _ hq _ ha.2.1.2).symm.trans hv.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Height
