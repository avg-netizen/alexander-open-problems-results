import Alexander313.Wilken.HereditaryNativeIotaBaseChangeSupport

/-!
# Original-domain iota/pi commutation (source Lemma 2.47)

The guard tests two original admitted weak-normal high theta0 roots at the
same positive public contextCode s, with source base < gamma < alpha, and
the ORIGINAL input's source-star restriction to gamma. It never tests a
transformed-input admission as an additional hypothesis. The gap theorem
derives equal literal iota words and the true Par caller for pi. The existing
context-independent finite normalizer gives the normalized equation too.
Raw inputs first execute the genuine source normalizer; their restriction is
tested on that output. This proves the commutative equation on this original
native domain; image equality with all T_alpha[gamma], surjectivity/inverse
and the remaining full Lemma 2.46 semantics are separate obligations.
All candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange

open NativePublicBridge (contextCode contextCode_checked)

def rootsCheck (s g a : Nat) : Bool := (rootCheck s g && rootCheck s a) &&
  (parameterCheck (alphaCode s g) (contextCode s) &&
    Normalization.lessRawCode (contextCode s) g a)

theorem rootsCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => rootsCheck p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat × (Nat × Nat) => p.1) := Primrec.fst
  have hg : Primrec (fun p : Nat × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Primrec.and.comp (rootCheck_primrec.comp hs hg)
    (rootCheck_primrec.comp hs ha)) (Primrec.and.comp
      (parameterCheck_primrec.comp (alphaCode_primrec.comp hs hg)
        (NativePublicBridge.contextCode_primrec.comp hs))
      (Normalization.Effective.lessRawCode_primrec.comp
        ((NativePublicBridge.contextCode_primrec.comp hs).pair (hg.pair ha))))

theorem rootsCheck_exact (s g a : Nat) : rootsCheck s g a = true ↔
    rootCheck s g = true ∧ rootCheck s a = true ∧
      base (contextCode s) < interpretation (contextCode s) g ∧
      interpretation (contextCode s) g < interpretation (contextCode s) a := by
  simp only [rootsCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hg, ha⟩, hp, hl⟩
    have hs := (parameterCheck_exact _ _).mp hp
    have hga := (Normalization.lessRawCode_exact _ _ _).mp hl
    exact ⟨hg, ha, by simpa only [parameters, base, (alphaCode_spec s g hg).2] using hs.2.2,
      hga.2.2⟩
  · rintro ⟨hg, ha, hsg, hga⟩
    exact ⟨⟨hg, ha⟩, (parameterCheck_exact _ _).mpr
      ⟨((baseCheck_exact _).mp (contextCode_checked s)).1,
        Canonical.check_original (alphaCode_spec s g hg).1,
        by simpa only [parameters, base, (alphaCode_spec s g hg).2] using hsg⟩,
      (Normalization.lessRawCode_exact _ _ _).mpr
        ⟨root_original s g hg, root_original s a ha, hga⟩⟩

def inputCheck (s g a c : Nat) : Bool := rootsCheck s g a && Iota.inputCheck s g c

theorem inputCheck_primrec : Primrec
    (fun p : (Nat × (Nat × Nat)) × Nat => inputCheck p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (rootsCheck_primrec.comp Primrec.fst)
    (Iota.inputCheck_primrec.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))

theorem inputCheck_exact (s g a c : Nat) : inputCheck s g a c = true ↔
    rootCheck s g = true ∧ rootCheck s a = true ∧
      base (contextCode s) < interpretation (contextCode s) g ∧
      interpretation (contextCode s) g < interpretation (contextCode s) a ∧
      ∃ t : RelativeTerm Nat, c = t.code ∧ check (contextCode s) t = true ∧
        Comparison.Normal (contextCode s) t ∧
        sourceStar (contextCode s) t < interpretation (contextCode s) g := by
  rw [inputCheck, Bool.and_eq_true, rootsCheck_exact, Iota.inputCheck_exact]
  constructor
  · rintro ⟨⟨hg, ha, hsg, hga⟩, hg', ht⟩
    exact ⟨hg, ha, hsg, hga, ht⟩
  · rintro ⟨hg, ha, hsg, hga, ht⟩
    exact ⟨⟨hg, ha, hsg, hga⟩, hg, ht⟩

theorem gamma_input (s g a c : Nat) (hi : inputCheck s g a c = true) :
    Iota.inputCheck s g c = true := (Bool.and_eq_true.mp hi).2

theorem alpha_input (s g a c : Nat) (hi : inputCheck s g a c = true) :
    Iota.inputCheck s a c = true := by
  obtain ⟨hg, ha, hsg, hga, t, he, ht, hn, hr⟩ := (inputCheck_exact s g a c).mp hi
  exact (Iota.inputCheck_exact s a c).mpr ⟨ha, t, he, ht, hn, hr.trans hga⟩

theorem literal_eq (s g a c : Nat) (hi : inputCheck s g a c = true) :
    literalCode s a c = literalCode s g c := by
  obtain ⟨hg, ha, hsg, hga, t, he, ht, hn, hs⟩ := (inputCheck_exact s g a c).mp hi
  have hr := (restricted_iff_sourceStar s g hg t ht hn).mpr hs
  simp only [literalCode, alpha_input s g a c hi, gamma_input s g a c hi,
    Bool.cond_true, he, stateCode_code, transform_eq s g a hg ha hga t ht hr]

/-- The actual alpha-output has Par below gamma, derived from each original
atomized subtree's below-gamma bound. Target admission is a conclusion. -/
theorem literal_parBounded (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g)
      (ThetaCourse.rawTree (literalCode s a c)) := by
  obtain ⟨hg, ha, hsg, hga, t, he, ht, hn, hs⟩ := (inputCheck_exact s g a c).mp hi
  have hr := (restricted_iff_sourceStar s g hg t ht hn).mpr hs
  simpa only [literalCode, alpha_input s g a c hi, Bool.cond_true, he,
    stateCode_code, ThetaCourse.rawTree_code] using
      transform_parBounded s g a hg ha hga t ht hr

theorem literal_pi_caller (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.inputCheck (alphaCode s a) (alphaCode s g) (literalCode s a c) = true := by
  obtain ⟨hg, ha, hsg, hga, ht⟩ := (inputCheck_exact s g a c).mp hi
  obtain ⟨t, he, hl, hc, hh⟩ := literalCode_spec s a c (alpha_input s g a c hi)
  apply (BaseTransformation.inputCheck_exact _ _ _).mpr
  exact ⟨by simpa only [hl, checkCode_code] using hc,
    alphaCode_baseCheck s g hg,
    by simpa only [base, (alphaCode_spec s g hg).2, (alphaCode_spec s a ha).2] using hga,
    literal_parBounded s g a c hi⟩

theorem literal_commutes (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.piCode (alphaCode s a) (alphaCode s g) (literalCode s a c) =
      literalCode s g c := by
  rw [BaseTransformation.piCode_eq _ _ _ (literal_pi_caller s g a c hi)]
  exact literal_eq s g a c hi

theorem normalized_eq (s g a c : Nat) (hi : inputCheck s g a c = true) :
    normalizeCode s a c = normalizeCode s g c := by
  have hc := BaseTransformation.inputCheck_checks _ _ _ (literal_pi_caller s g a c hi)
  simp only [Iota.normalizeCode, alpha_input s g a c hi, gamma_input s g a c hi, Bool.cond_true]
  rw [BaseTransformation.normalizeCode_context _ _ _ hc.1 hc.2.1, literal_eq s g a c hi]

theorem normalized_pi_caller (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.normalInputCheck (alphaCode s a) (alphaCode s g) (normalizeCode s a c) = true := by
  have hc := BaseTransformation.inputCheck_checks _ _ _ (literal_pi_caller s g a c hi)
  have hna := normalizeCode_spec s a c (alpha_input s g a c hi)
  have hng := normalizeCode_spec s g c (gamma_input s g a c hi)
  have hq := ((Comparison.acceptedCode_exact _ _).mp hna.1).1
  have hv : checkCode (alphaCode s g) (normalizeCode s a c) = true := by
    rw [normalized_eq s g a c hi]
    exact ((Comparison.acceptedCode_exact _ _).mp hng.1).1
  have hp := (Bool.and_eq_true.mp (literal_pi_caller s g a c hi)).2
  exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hq, hv⟩, hp⟩, hna.1⟩

theorem normalized_parBounded (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g)
      (ThetaCourse.rawTree (normalizeCode s a c)) :=
  ((BaseTransformation.inputCheck_exact _ _ _).mp
    (Bool.and_eq_true.mp (normalized_pi_caller s g a c hi)).1).2.2.2

theorem normalized_commutes (s g a c : Nat) (hi : inputCheck s g a c = true) :
    BaseTransformation.piCode (alphaCode s a) (alphaCode s g) (normalizeCode s a c) =
      normalizeCode s g c := by
  rw [BaseTransformation.piCode_eq _ _ _ (Bool.and_eq_true.mp (normalized_pi_caller s g a c hi)).1]
  exact normalized_eq s g a c hi

theorem source_commutes (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hsg : base (contextCode s) < interpretation (contextCode s) g)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s g t) :
    BaseTransformation.inputCheck (alphaCode s a) (alphaCode s g) (literalCode s a t.code) = true ∧
      BaseTransformation.piCode (alphaCode s a) (alphaCode s g) (literalCode s a t.code) =
        literalCode s g t.code := by
  have hi := (inputCheck_exact s g a t.code).mpr ⟨hg, ha, hsg, hga, t, rfl, ht, hn,
    (restricted_iff_sourceStar s g hg t ht hn).mp hr⟩
  exact ⟨literal_pi_caller s g a t.code hi, literal_commutes s g a t.code hi⟩

def rawInputCheck (s g a c : Nat) : Bool := checkCode (contextCode s) c &&
  inputCheck s g a (Normalization.normalizeCode (contextCode s) c)

theorem rawInputCheck_primrec : Primrec
    (fun p : (Nat × (Nat × Nat)) × Nat => rawInputCheck p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hq := NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hn := Normalization.Effective.normalizeCode_primrec.comp hq Primrec.snd
  exact Primrec.and.comp (checkCode_primrec.comp hq Primrec.snd)
    (inputCheck_primrec.comp (Primrec.fst.pair hn))

theorem rawInputCheck_exact (s g a c : Nat) : rawInputCheck s g a c = true ↔
    checkCode (contextCode s) c = true ∧ rootCheck s g = true ∧ rootCheck s a = true ∧
      base (contextCode s) < interpretation (contextCode s) g ∧
      interpretation (contextCode s) g < interpretation (contextCode s) a ∧
      sourceStar (contextCode s) (ThetaCourse.rawTree (Normalization.normalizeCode (contextCode s) c)) <
        interpretation (contextCode s) g := by
  rw [rawInputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hi⟩
    obtain ⟨hg, ha, hsg, hga, t, he, ht, hn, hs⟩ := (inputCheck_exact s g a _).mp hi
    exact ⟨hc, hg, ha, hsg, hga, by simpa only [he, ThetaCourse.rawTree_code] using hs⟩
  · rintro ⟨hc, hg, ha, hsg, hga, hs⟩
    have hn := Normalization.normalizeCode_checked (contextCode s) c hc
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ _).mp hn.1
    exact ⟨hc, (inputCheck_exact s g a _).mpr ⟨hg, ha, hsg, hga, t, he.symm, ht,
      by simpa only [← he, ThetaCourse.rawTree_code] using hn.2.1,
      by simpa only [← he, ThetaCourse.rawTree_code] using hs⟩⟩

theorem raw_gamma_input (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    Iota.rawInputCheck s g c = true := by
  have hs := Bool.and_eq_true.mp hi
  exact Bool.and_eq_true.mpr ⟨hs.1, gamma_input s g a _ hs.2⟩

theorem raw_alpha_input (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    Iota.rawInputCheck s a c = true := by
  have hs := Bool.and_eq_true.mp hi
  exact Bool.and_eq_true.mpr ⟨hs.1, alpha_input s g a _ hs.2⟩

theorem raw_literal_pi_caller (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    BaseTransformation.inputCheck (alphaCode s a) (alphaCode s g) (rawLiteralCode s a c) = true := by
  simpa only [rawLiteralCode, raw_alpha_input s g a c hi, Bool.cond_true] using
    literal_pi_caller s g a _ (Bool.and_eq_true.mp hi).2

theorem raw_literal_commutes (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    BaseTransformation.piCode (alphaCode s a) (alphaCode s g) (rawLiteralCode s a c) =
      rawLiteralCode s g c := by
  simpa only [rawLiteralCode, raw_alpha_input s g a c hi, raw_gamma_input s g a c hi,
    Bool.cond_true] using literal_commutes s g a _ (Bool.and_eq_true.mp hi).2

theorem raw_normalized_pi_caller (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    BaseTransformation.normalInputCheck (alphaCode s a) (alphaCode s g) (rawNormalizeCode s a c) = true := by
  simpa only [rawNormalizeCode, raw_alpha_input s g a c hi, Bool.cond_true] using
    normalized_pi_caller s g a _ (Bool.and_eq_true.mp hi).2

theorem raw_normalized_commutes (s g a c : Nat) (hi : rawInputCheck s g a c = true) :
    BaseTransformation.piCode (alphaCode s a) (alphaCode s g) (rawNormalizeCode s a c) =
      rawNormalizeCode s g c := by
  simpa only [rawNormalizeCode, raw_alpha_input s g a c hi, raw_gamma_input s g a c hi,
    Bool.cond_true] using normalized_commutes s g a _ (Bool.and_eq_true.mp hi).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange
