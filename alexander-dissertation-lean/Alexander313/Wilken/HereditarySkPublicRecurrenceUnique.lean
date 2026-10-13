import Alexander313.Wilken.HereditarySkPublicRecurrence

/-!
# Unique actual public sk recurrence and exact executing correspondence

Every public predecessor has its independently executing mu query. Its
actual output and factor truncation determine the next value. Canonical
admission identifies its literal code. The two maximal stopping tests
exclude every alternative branch; finite path induction gives the whole
chronological word. The terminating selected-source producer executes
exactly this genuine recurrence, not an independently assigned word.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence


theorem mu_input_canonical (a : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true) :
    Canonical.check a = true := ((MuPublicDictionary.Support.inputCheck_image a).mp ha).1

theorem mu_input_epsilon (a : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true) :
    Ordinal.omega0 ^ unionInterpretation a = unionInterpretation a :=
  ((MuPublicDictionary.Support.inputCheck_image a).mp ha).2.1

private theorem muValue_equal_value (a b : Nat)
    (ha : MuPublicDictionary.Support.inputCheck a = true)
    (hb : MuPublicDictionary.Support.inputCheck b = true)
    (hv : unionInterpretation a = unionInterpretation b) : muValue a = muValue b :=
  congrArg unionInterpretation (MuPublicDictionary.publicCode_equal_value a b ha hb hv)

/-- Canonical admission is derived from every actual recurrence constructor,
including its terminal non-epsilon next value. -/
theorem Path.canonical {cutoff : Nat} {codes : List Nat} (hp : Path cutoff codes) :
    ∀ c ∈ codes, Canonical.check c = true := by
  induction hp with
  | stop a ha hs =>
    intro c hc
    simpa only [List.mem_singleton.mp hc] using mu_input_canonical a ha
  | nextStop a d ha hd he hv hs =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact mu_input_canonical a ha
    · simpa only [List.mem_singleton.mp hc] using hd
  | nextContinue a b xs ha hb he hv hab ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact mu_input_canonical a ha
    · exact ih c hc

/-- The independently executing public mu and actual maximal branch tests
make the finite recurrence deterministic in values. -/
theorem Path.values_eq {cutoff other a b : Nat} {xs ys : List Nat}
    (hp : Path cutoff (a :: xs)) (ht : Path other (b :: ys))
    (hcut : unionInterpretation cutoff = unionInterpretation other)
    (hab : unionInterpretation a = unionInterpretation b) :
    (a :: xs).map (unionInterpretation) = (b :: ys).map (unionInterpretation) := by
  induction hp generalizing other b ys with
  | stop a ha hstop =>
    cases ht with
    | stop b hb hhalt => simp only [List.map_cons, List.map_nil, hab]
    | nextStop b d hb hl he hv hs =>
      have hmu := muValue_equal_value a b ha hb hab
      have hle : unionInterpretation cutoff ≤ muValue a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
    | nextContinue b d ys hb hd he hv hbd ht =>
      have hmu := muValue_equal_value a b ha hb hab
      have hle : unionInterpretation cutoff ≤ muValue a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
  | nextStop a d ha hl he hv hstop =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := muValue_equal_value a b ha hb hab
      have hlt : muValue a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := muValue_equal_value a b ha hb hab
      have hvalue : unionInterpretation d = unionInterpretation e := by
        calc
          unionInterpretation d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = unionInterpretation e := hevalue.symm
      simp only [List.map_cons, List.map_nil, hab, hvalue]
    | nextContinue b e ys hb heinput het hevalue hbe htail =>
      have hmu := muValue_equal_value a b ha hb hab
      have hvalue : unionInterpretation d = unionInterpretation e := by
        calc
          unionInterpretation d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = unionInterpretation e := hevalue.symm
      apply False.elim
      apply hstop
      rw [hab, hvalue]
      exact ⟨mu_input_epsilon e heinput, hbe⟩
  | nextContinue a d xs ha hd he hv had htail ih =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := muValue_equal_value a b ha hb hab
      have hlt : muValue a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := muValue_equal_value a b ha hb hab
      have hvalue : unionInterpretation d = unionInterpretation e := by
        calc
          unionInterpretation d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = unionInterpretation e := hevalue.symm
      apply False.elim
      apply hestop
      rw [← hab, ← hvalue]
      exact ⟨mu_input_epsilon d hd, had⟩
    | nextContinue b e ys hb heinput het hevalue hbe hother =>
      have hmu := muValue_equal_value a b ha hb hab
      have hvalue : unionInterpretation d = unionInterpretation e := by
        calc
          unionInterpretation d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = unionInterpretation e := hevalue.symm
      have hrec := ih hother hcut hvalue
      simpa only [List.map_cons, hab] using congrArg (List.cons (unionInterpretation a)) hrec

/-- Every actual public recurrence entry is canonical, so whole value
uniqueness gives literal numerical word uniqueness. -/
theorem Path.codes_eq {cutoff other a b : Nat} {xs ys : List Nat}
    (hp : Path cutoff (a :: xs)) (ht : Path other (b :: ys))
    (hcut : unionInterpretation cutoff = unionInterpretation other)
    (hab : unionInterpretation a = unionInterpretation b) : a :: xs = b :: ys :=
  NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
    _ _ hp.canonical ht.canonical (hp.values_eq ht hcut hab)

/-- Equal actual initial and cutoff values give the same complete canonical
public output, without supplied mu or recurrence agreement. -/
theorem execute_codes_eq (gamma other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (ht : otherCodes ∈ SkPublicDictionary.execute (other, otherCutoff))
    (hroot : unionInterpretation gamma = unionInterpretation other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : codes = otherCodes := by
  obtain ⟨xs, he, _⟩ := execute_initial gamma cutoff codes ho
  obtain ⟨ys, hf, _⟩ := execute_initial other otherCutoff otherCodes ht
  have hp := execute_path gamma cutoff codes ho
  have hq := execute_path other otherCutoff otherCodes ht
  rw [he] at hp ⊢
  rw [hf] at hq ⊢
  exact hp.codes_eq hq hcut hroot

/-- The actual partial program executes exactly the genuine public
maximal recurrence with the literal original initial code. -/
theorem execute_iff_path (gamma cutoff : Nat) (codes : List Nat) :
    codes ∈ SkPublicDictionary.execute (gamma, cutoff) ↔
      SkPublicDictionary.Support.inputCheck gamma cutoff = true ∧ Path cutoff codes ∧
        ∃ xs, codes = gamma :: xs := by
  constructor
  · intro ho
    have hs := execute_spec gamma cutoff codes ho
    obtain ⟨xs, he, _⟩ := execute_initial gamma cutoff codes ho
    exact ⟨hs.1, hs.2.1, xs, he⟩
  · rintro ⟨hi, hp, xs, rfl⟩
    obtain ⟨actual, ha⟩ := SkPublicDictionary.execute_returns gamma cutoff hi
    obtain ⟨ys, he, _⟩ := execute_initial gamma cutoff actual ha
    have ht := execute_path gamma cutoff actual ha
    rw [he] at ht
    have hword : gamma :: xs = actual := (hp.codes_eq ht rfl rfl).trans he.symm
    rw [hword]
    exact ha

/-- The complete correspondence retains exactly the genuine semantic
upsilon-image exclusion and original admitted public cutoff domain. -/
theorem execute_iff_path_image (gamma cutoff : Nat) (codes : List Nat) :
    codes ∈ SkPublicDictionary.execute (gamma, cutoff) ↔
      Canonical.check gamma = true ∧
        Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
          ¬ SourceUpsilonImage (unionInterpretation gamma) ∧ unionCheck cutoff = true ∧
            Path cutoff codes ∧ ∃ xs, codes = gamma :: xs := by
  rw [execute_iff_path, SkPublicDictionary.UpsilonDomain.inputCheck_exact]
  constructor
  · rintro ⟨⟨hc, he, hn, hcut⟩, hp, xs, hcodes⟩
    exact ⟨hc, he, hn, hcut, hp, xs, hcodes⟩
  · rintro ⟨hc, he, hn, hcut, hp, xs, hcodes⟩
    exact ⟨⟨hc, he, hn, hcut⟩, hp, xs, hcodes⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence
