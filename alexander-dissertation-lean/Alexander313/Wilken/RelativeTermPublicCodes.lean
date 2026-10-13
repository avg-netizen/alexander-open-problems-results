import Alexander313.Wilken.RelativeTermAdmissibility
import Alexander313.Wilken.DirectLimitNotations

/-!
# Executable codes for the actual base-one global grammar

A written term chooses the finite fragment `height+1`. Literal code recognition
and the source admissibility checker are primitive recursive. Every accepted
tree has the same denotation under the actual finite and global source collapse
families; every element of `GlobalNotation 1 0` has such a tree. Filtering the
outer value sort gives exactly the interval below `globalBoundary 1 0`.

These are noncanonical raw codes for the base-one grammar. Denotation is the
existing noncomputable semantic source function, not an ordinal comparison
algorithm. Hereditary parameters in later bases, normalization, least-code
representatives, ordinal equality/order, tracking and R₁/R₂ remain separate.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.PublicCodes

private theorem base_pos : (0 : Ordinal.{0}) < 1 := by simp

def fragment (t : RelativeTerm Nat) : Nat := t.height + 1

theorem fragment_pos (t : RelativeTerm Nat) : 0 < fragment t := Nat.zero_lt_succ _

theorem height_le_fragment (t : RelativeTerm Nat) : t.height ≤ fragment t := Nat.le_succ _

theorem fragment_primrec : Primrec fragment := Primrec.succ.comp RelativeTerm.height_primrec

/-- Rechecking a tree in any fragment containing all its written indices
    preserves its source admission. The argument-sort tests are unchanged. -/
theorem check_transfer (n : Nat) (t : RelativeTerm Nat) (h : SourceOne.check n t = true)
    (n' : Nat) (hheight : t.height ≤ n') : SourceOne.check n' t = true := by
  have transfer : ∀ (a : RelativeTerm Nat) (p q : Nat),
      SourceOne.check p a = true → a.height ≤ q → SourceOne.check q a = true := by
    intro a
    induction a with
    | parameter p =>
      intro n n' h hheight
      simpa only [SourceOne.check_parameter] using h
    | sum a b iha ihb =>
      intro n n' h hheight
      have hs : SourceOne.check n a = true ∧ SourceOne.check n b = true := by
        simpa only [SourceOne.check_sum, Bool.and_eq_true] using h
      have ha : a.height ≤ n' := (le_max_left _ _).trans hheight
      have hb : b.height ≤ n' := (le_max_right _ _).trans hheight
      simp only [SourceOne.check_sum, iha n n' hs.1 ha, ihb n n' hs.2 hb, Bool.true_and]
    | theta k a ih =>
      intro n n' h hheight
      have hs : SourceOne.check n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
        simpa only [SourceOne.check_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
      have ha : a.height ≤ n' := (le_max_right _ _).trans hheight
      have hk : k < n' := by
        have hk' : k + 1 ≤ n' := (le_max_left _ _).trans hheight
        omega
      simp only [SourceOne.check_theta, ih n n' hs.1 ha, hk, hs.2.2, decide_true, Bool.true_and]
  exact transfer t n n' h hheight

def check (t : RelativeTerm Nat) : Bool := SourceOne.check (fragment t) t

theorem check_primrec : Primrec check :=
  SourceOne.check_primrec.comp fragment_primrec Primrec.id

theorem check_iff_finite_admissible (t : RelativeTerm Nat) :
    check t = true ↔ ∃ n, SourceOne.admissible n t := by
  constructor
  · intro ht
    exact ⟨fragment t, (SourceOne.check_iff (fragment t) t).mp ht⟩
  · rintro ⟨n, ht⟩
    exact check_transfer n t ((SourceOne.check_iff n t).mpr ht)
      (fragment t) (height_le_fragment t)

def checkCode (c : Nat) : Bool := SourceOne.checkCode (RelativeTerm.heightCode c + 1) c

theorem checkCode_primrec : Primrec checkCode :=
  SourceOne.checkCode_primrec.comp (Primrec.succ.comp RelativeTerm.heightCode_primrec) Primrec.id

@[simp] theorem checkCode_code (t : RelativeTerm Nat) : checkCode t.code = check t := by
  simp only [checkCode, RelativeTerm.heightCode_code, SourceOne.checkCode_code, check, fragment]

theorem checkCode_iff (c : Nat) :
    checkCode c = true ↔ ∃ t : RelativeTerm Nat, t.code = c ∧ check t = true := by
  constructor
  · intro hc
    obtain ⟨t, ht, ha⟩ :=
      (SourceOne.checkCode_iff (RelativeTerm.heightCode c + 1) c).mp hc
    have hs := (SourceOne.check_iff (RelativeTerm.heightCode c + 1) t).mpr ha
    refine ⟨t, ht, ?_⟩
    simpa only [← ht, RelativeTerm.heightCode_code, check, fragment] using hs
  · rintro ⟨t, rfl, ht⟩
    rw [checkCode_code]
    exact ht

noncomputable def denote (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval SourceOne.parameters (globalCollapse 1)

/-- Finite source argument coverage licenses every global call. The zero
    extension of `globalCollapse` outside its domain never enters this proof. -/
theorem denote_eq_finite (n : Nat) (t : RelativeTerm Nat) (ht : SourceOne.admissible n t) :
    denote t = SourceOne.denote n t := by
  induction ht with
  | parameter hp => rfl
  | @sum a b ha hb iha ihb =>
    change denote a + denote b = SourceOne.denote n a + SourceOne.denote n b
    rw [iha, ihb]
  | @theta k a h0k hkn hsort ha ih =>
    change globalCollapse 1 k (denote a) = sourceFiniteCollapse 1 n k (SourceOne.denote n a)
    rw [ih]
    have hn : 0 < n := by omega
    have hnotation : sourceNotation 1 n 0 (SourceOne.denote n a) := by
      rw [sourceNotation, if_pos hn]
      exact ha.denote
    have hbound := source_finite_collapse_argument_lt_boundary 1 base_pos n 0 k
      h0k hkn hnotation hsort
    exact globalCollapse_finite_agreement 1 base_pos n k hkn _ hbound

theorem checked_globalNotation (t : RelativeTerm Nat) (ht : check t = true) :
    GlobalNotation 1 0 (denote t) := by
  have ha := (SourceOne.check_iff (fragment t) t).mp ht
  rw [denote_eq_finite (fragment t) t ha]
  exact sourceNotation_to_globalNotation 1 base_pos (fragment t) 0 (fragment_pos t)
    (SourceOne.checked_sourceNotation (fragment t) (fragment_pos t) t ht)

theorem denote_lt_iff_outerSort_le (t : RelativeTerm Nat) (ht : check t = true)
    (q : Nat) (hq : 0 < q) : denote t < omegaSequence 1 q ↔ t.outerSort ≤ q := by
  have ha := (SourceOne.check_iff (fragment t) t).mp ht
  rw [denote_eq_finite (fragment t) t ha]
  exact SourceOne.denote_lt_iff_outerSort_le (fragment t) t ha q hq

/-- The actual finite source grammar has a Nat-coded zero-parameter tree at
    base one. Parameter ordinals below one are reduced to zero, not guessed. -/
theorem sourceNotation_iff_natTerm (n : Nat) (hn : 0 < n) (ξ : Ordinal.{0}) :
    sourceNotation 1 n 0 ξ ↔
      ∃ t : RelativeTerm Nat, SourceOne.admissible n t ∧ SourceOne.denote n t = ξ := by
  rw [sourceNotation, if_pos hn]
  constructor
  · intro hξ
    induction hξ with
    | @parameter ξ hp =>
      have hzero : ξ = 0 := by simpa [omegaSequence_zero] using hp
      refine ⟨.parameter 0, .parameter ((SourceOne.parameter_lt_base_iff 0).mpr rfl), ?_⟩
      simpa only [SourceOne.denote, RelativeTerm.eval, SourceOne.parameters, Nat.cast_zero] using hzero.symm
    | add ha hb iha ihb =>
      obtain ⟨a, ha, hva⟩ := iha
      obtain ⟨b, hb, hvb⟩ := ihb
      refine ⟨.sum a b, .sum ha hb, ?_⟩
      change SourceOne.denote n a + SourceOne.denote n b = _
      rw [hva, hvb]
    | @collapse k ξ h0k hkn hsort hξ ih =>
      obtain ⟨a, ha, hva⟩ := ih
      refine ⟨.theta k a, .theta h0k hkn ?_ ha, ?_⟩
      · change SourceOne.denote n a < omegaSequence 1 (k + 2)
        rw [hva]
        exact hsort
      · change sourceFiniteCollapse 1 n k (SourceOne.denote n a) = _
        rw [hva]
  · rintro ⟨t, ht, rfl⟩
    exact ht.denote

/-- Exact coverage of the existing semantic base-one global grammar. -/
theorem globalNotation_iff_checked (ξ : Ordinal.{0}) :
    GlobalNotation 1 0 ξ ↔ ∃ t : RelativeTerm Nat, check t = true ∧ denote t = ξ := by
  constructor
  · intro hξ
    obtain ⟨n, hn, hfinite⟩ := globalNotation_finite_witness 1 base_pos 0 hξ
    obtain ⟨t, ht, hvalue⟩ := (sourceNotation_iff_natTerm n hn ξ).mp hfinite
    refine ⟨t, (check_iff_finite_admissible t).mpr ⟨n, ht⟩, ?_⟩
    exact (denote_eq_finite n t ht).trans hvalue
  · rintro ⟨t, ht, rfl⟩
    exact checked_globalNotation t ht

/-- A total raw interpretation; rejected inputs have only an auxiliary
    default. Exact coverage statements below always require `checkCode`. -/
noncomputable def interpretation (c : Nat) : Ordinal.{0} :=
  denote ((RelativeTerm.decode c).getD (.parameter 0))

@[simp] theorem interpretation_code (t : RelativeTerm Nat) : interpretation t.code = denote t := by
  simp only [interpretation, RelativeTerm.decode_code, Option.getD_some]

theorem globalNotation_iff_code (ξ : Ordinal.{0}) :
    GlobalNotation 1 0 ξ ↔ ∃ c : Nat, checkCode c = true ∧ interpretation c = ξ := by
  constructor
  · intro hξ
    obtain ⟨t, ht, hvalue⟩ := (globalNotation_iff_checked ξ).mp hξ
    exact ⟨t.code, by simpa only [checkCode_code] using ht,
      by simpa only [interpretation_code] using hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    obtain ⟨t, ht, hcheck⟩ := (checkCode_iff c).mp hc
    apply (globalNotation_iff_checked ξ).mpr
    refine ⟨t, hcheck, ?_⟩
    simpa only [← ht, interpretation_code] using hvalue

def outerSortCode (c : Nat) : Nat := (SourceOne.stateCode 0 c).2

theorem outerSortCode_primrec : Primrec outerSortCode :=
  Primrec.snd.comp (SourceOne.stateCode_primrec.comp (Primrec.const 0) Primrec.id)

@[simp] theorem outerSortCode_code (t : RelativeTerm Nat) : outerSortCode t.code = t.outerSort := by
  simp only [outerSortCode, SourceOne.stateCode_code, SourceOne.state_sort]

def lowCheck (t : RelativeTerm Nat) : Bool := check t && decide (t.outerSort ≤ 1)

theorem lowCheck_primrec : Primrec lowCheck :=
  Primrec.and.comp check_primrec
    (Primrec.nat_le.comp RelativeTerm.outerSort_primrec (Primrec.const 1)).decide

def lowCheckCode (c : Nat) : Bool := checkCode c && decide (outerSortCode c ≤ 1)

theorem lowCheckCode_primrec : Primrec lowCheckCode :=
  Primrec.and.comp checkCode_primrec
    (Primrec.nat_le.comp outerSortCode_primrec (Primrec.const 1)).decide

@[simp] theorem lowCheckCode_code (t : RelativeTerm Nat) : lowCheckCode t.code = lowCheck t := by
  simp only [lowCheckCode, checkCode_code, outerSortCode_code, lowCheck]

theorem lowCheckCode_iff (c : Nat) :
    lowCheckCode c = true ↔ ∃ t : RelativeTerm Nat, t.code = c ∧ lowCheck t = true := by
  constructor
  · intro hc
    have hs : checkCode c = true ∧ outerSortCode c ≤ 1 := by
      simpa only [lowCheckCode, Bool.and_eq_true, decide_eq_true_eq] using hc
    obtain ⟨t, ht, hcheck⟩ := (checkCode_iff c).mp hs.1
    refine ⟨t, ht, ?_⟩
    have hsort : t.outerSort ≤ 1 := by simpa only [← ht, outerSortCode_code] using hs.2
    simp only [lowCheck, hcheck, hsort, decide_true, Bool.true_and]
  · rintro ⟨t, rfl, ht⟩
    rw [lowCheckCode_code]
    exact ht

/-- The countable-sort filter has exactly the actual source low interval. -/
theorem lt_boundary_iff_checked (ξ : Ordinal.{0}) :
    ξ < globalBoundary 1 0 ↔ ∃ t : RelativeTerm Nat, lowCheck t = true ∧ denote t = ξ := by
  rw [← globalNotation_low_iff_lt_boundary 1 base_pos 0 ξ]
  constructor
  · rintro ⟨hξ, hsmall⟩
    obtain ⟨t, ht, hvalue⟩ := (globalNotation_iff_checked ξ).mp hξ
    have hsort : t.outerSort ≤ 1 :=
      (denote_lt_iff_outerSort_le t ht 1 (by omega)).mp (by simpa only [hvalue] using hsmall)
    exact ⟨t, by simp only [lowCheck, ht, hsort, decide_true, Bool.true_and], hvalue⟩
  · rintro ⟨t, ht, rfl⟩
    have hs : check t = true ∧ t.outerSort ≤ 1 := by
      simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using ht
    exact ⟨checked_globalNotation t hs.1,
      (denote_lt_iff_outerSort_le t hs.1 1 (by omega)).mpr hs.2⟩

theorem lt_boundary_iff_code (ξ : Ordinal.{0}) :
    ξ < globalBoundary 1 0 ↔ ∃ c : Nat, lowCheckCode c = true ∧ interpretation c = ξ := by
  constructor
  · intro hξ
    obtain ⟨t, ht, hvalue⟩ := (lt_boundary_iff_checked ξ).mp hξ
    exact ⟨t.code, by simpa only [lowCheckCode_code] using ht,
      by simpa only [interpretation_code] using hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    obtain ⟨t, ht, hcheck⟩ := (lowCheckCode_iff c).mp hc
    apply (lt_boundary_iff_checked ξ).mpr
    refine ⟨t, hcheck, ?_⟩
    simpa only [← ht, interpretation_code] using hvalue

end Alexander313.Wilken.RelativeTerm.SourceOne.PublicCodes
