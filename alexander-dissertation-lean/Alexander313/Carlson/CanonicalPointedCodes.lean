import Alexander313.Carlson.ComputablePointedPresentation

/-!
# Least natural representatives of actual core labels

Normalization searches the total finite-data equality algorithm, never the
ordinal interpretation. Every input is its own termination witness. The
fixed points form a decidable, duplicate-free presentation of exactly the
same common core. Actual machines implement normalization and membership.
-/

namespace Alexander313.Carlson.CanonicalPointedCodes

open ComputablePointedPresentation

/-- Total minimization of a computable Boolean test with a supplied
termination theorem. The theorem is erased; it does not select the output. -/
theorem find_computable (test : ℕ → ℕ → Bool) (htest : Computable₂ test)
    (hex : ∀ n, ∃ k, test n k = true) :
    Computable (fun n => Nat.find (hex n)) := by
  have hsearch : Partrec (fun n => Nat.rfind (fun k => Part.some (test n k))) :=
    Partrec.rfind htest.partrec₂
  apply hsearch.of_eq
  intro n
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  refine ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    exact (Nat.find_spec (hex n)).symm
  · intro k hk
    simp only [Part.mem_some_iff]
    have hn : test n k ≠ true := Nat.find_min (hex n) hk
    cases hb : test n k with
    | false => rfl
    | true => exact (hn hb).elim

theorem exists_same (n : ℕ) : ∃ k, same n k = true := ⟨n, same_self n⟩

/-- The least natural code with the same actual label as the input. -/
def representative (n : ℕ) : ℕ := Nat.find (exists_same n)

theorem representative_same (n : ℕ) : same n (representative n) = true :=
  Nat.find_spec (exists_same n)

theorem representative_label (n : ℕ) : label (representative n) = label n :=
  ((same_eq_true n (representative n)).mp (representative_same n)).symm

theorem representative_le (n : ℕ) : representative n ≤ n :=
  Nat.find_min' (exists_same n) (same_self n)

theorem representative_le_of_label {n k : ℕ} (h : label n = label k) :
    representative n ≤ k := Nat.find_min' (exists_same n) ((same_eq_true n k).mpr h)

theorem representative_computable : Computable representative :=
  find_computable same same_computable exists_same

/-- Normal forms agree exactly when the actual least ordinal labels agree. -/
theorem representative_eq_iff (m n : ℕ) :
    representative m = representative n ↔ label m = label n := by
  constructor
  · intro h
    exact (representative_label m).symm.trans
      ((congrArg label h).trans (representative_label n))
  · intro h
    exact (representative_le_of_label (h.trans (representative_label n).symm)).antisymm
      (representative_le_of_label (h.symm.trans (representative_label m).symm))

def Canonical (n : ℕ) : Prop := representative n = n

instance (n : ℕ) : Decidable (Canonical n) :=
  inferInstanceAs (Decidable (representative n = n))

theorem representative_canonical (n : ℕ) : Canonical (representative n) :=
  (representative_eq_iff (representative n) n).mpr (representative_label n)

theorem canonical_zero : Canonical 0 := Nat.eq_zero_of_le_zero (representative_le 0)

theorem canonical_iff_no_earlier (n : ℕ) :
    Canonical n ↔ ∀ k < n, label k ≠ label n := by
  constructor
  · intro hn k hk heq
    have hle := representative_le_of_label heq.symm
    change representative n = n at hn
    rw [hn] at hle
    exact (Nat.not_le_of_lt hk) hle
  · intro h
    apply Nat.le_antisymm (representative_le n)
    by_contra hn
    exact h (representative n) (Nat.lt_of_not_ge hn) (representative_label n)

theorem canonical_label_injective {m n : ℕ} (hm : Canonical m) (hn : Canonical n)
    (h : label m = label n) : m = n := by
  have he := (representative_eq_iff m n).mpr h
  exact hm.symm.trans (he.trans hn)

def checkCanonical (n : ℕ) : Bool := decide (Canonical n)

theorem checkCanonical_computable : Computable checkCanonical := by
  have he : Computable₂ (fun m n : ℕ => decide (m = n)) := Primrec.eq.decide.to_comp
  exact he.comp representative_computable Computable.id

theorem checkCanonical_eq_true (n : ℕ) : checkCanonical n = true ↔ Canonical n := by
  simp only [checkCanonical, decide_eq_true_eq]

/-- Every core element has exactly one canonical natural representative. -/
theorem exists_unique_canonical (a : Ordinal.{0}) (ha : a < coreBound) :
    ∃! n : ℕ, Canonical n ∧ label n = a := by
  obtain ⟨n, hn⟩ := label_surjective a ha
  refine ⟨representative n, ⟨representative_canonical n, (representative_label n).trans hn⟩, ?_⟩
  rintro k ⟨hk, hka⟩
  exact canonical_label_injective hk (representative_canonical n)
    (hka.trans ((representative_label n).trans hn).symm)

abbrev Code := {n : ℕ // Canonical n}

noncomputable def toCore (c : Code) : Set.Iio coreBound :=
  ⟨label c.val, label_lt_coreBound c.val⟩

theorem toCore_bijective : Function.Bijective toCore := by
  constructor
  · intro a b h
    exact Subtype.ext (canonical_label_injective a.property b.property
      (congrArg Subtype.val h))
  · intro a
    obtain ⟨n, hn, _⟩ := exists_unique_canonical a.val a.property
    exact ⟨⟨n, hn.1⟩, Subtype.ext hn.2⟩

/-- A semantic equivalence whose forward map is the proved actual label map.
The executable algorithms above do not evaluate this equivalence's inverse. -/
noncomputable def coreEquiv : Code ≃ Set.Iio coreBound :=
  Equiv.ofBijective toCore toCore_bijective

theorem representative_program : ∃ machine : Nat.Partrec.Code, ∀ n : ℕ,
    machine.eval n = Part.some (representative n) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp representative_computable
  refine ⟨machine, fun n => ?_⟩
  rw [hm]
  simp

theorem canonical_program : ∃ machine : Nat.Partrec.Code, ∀ n : ℕ,
    machine.eval n = Part.some (Encodable.encode (checkCanonical n)) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp checkCanonical_computable
  refine ⟨machine, fun n => ?_⟩
  rw [hm]
  simp

end Alexander313.Carlson.CanonicalPointedCodes
