import Alexander313.Wilken.HereditaryMuPublicDictionarySupport

/-!
# Executing canonical public mu at its genuine selected source

The actual canonical epsilon dictionary and source grammar proofs derive
every original mu caller. The concrete primitive recursive result is
canonical public syntax for the actual selected original-source mu value.
Its partial guard excludes precisely the genuine ordinal upsilon image.
Original-source fidelity and a public sk recurrence using this independent
executing query are separate genuine kernels. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary

open Support

def publicCode (gamma : Nat) : Nat := cond (inputCheck gamma)
  (cond (PublicEpsilonSourceDictionary.level gamma == 0) (sourceOneCode gamma) (nativeCode gamma)) 0

theorem publicCode_primrec : Primrec publicCode :=
  inputCheck_primrec.cond
    ((Primrec.beq.comp PublicEpsilonSourceDictionary.level_primrec (Primrec.const 0)).cond
      sourceOneCode_primrec nativeCode_primrec) (Primrec.const 0)

theorem publicCode_spec (gamma : Nat) (hi : inputCheck gamma = true) :
    Canonical.check (publicCode gamma) = true ∧
      unionInterpretation (publicCode gamma) = sourceValue gamma := by
  cases hb : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    have hs := sourceOneCode_spec gamma hi (beq_iff_eq.mp hb)
    simpa only [publicCode, sourceValue, hi, hb, Bool.cond_true] using hs
  | false =>
    have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by
      intro he
      have ht : (PublicEpsilonSourceDictionary.level gamma == 0) = true := beq_iff_eq.mpr he
      rw [hb] at ht
      cases ht
    have hs := nativeCode_spec gamma hi hl
    simpa only [publicCode, sourceValue, hi, hb, Bool.cond_true, Bool.cond_false] using hs

theorem publicCode_rejected (gamma : Nat) (hi : inputCheck gamma = false) : publicCode gamma = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

def execute (gamma : Nat) : Part Nat := cond (inputCheck gamma) (Part.some (publicCode gamma)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (gamma : Nat) : (execute gamma).Dom ↔ inputCheck gamma = true := by
  cases hi : inputCheck gamma <;> simp [execute, hi]

theorem execute_domain_image (gamma : Nat) : (execute gamma).Dom ↔
    Canonical.check gamma = true ∧
      Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
        ¬ SourceUpsilonImage (unionInterpretation gamma) :=
  (execute_domain gamma).trans (inputCheck_image gamma)

theorem execute_graph (gamma out : Nat) : out ∈ execute gamma ↔
    inputCheck gamma = true ∧ out = publicCode gamma := by
  cases hi : inputCheck gamma <;> simp [execute, hi]

theorem execute_returns (gamma : Nat) (hi : inputCheck gamma = true) :
    publicCode gamma ∈ execute gamma := (execute_graph gamma _).mpr ⟨hi, rfl⟩

theorem execute_spec (gamma out : Nat) (ho : out ∈ execute gamma) :
    inputCheck gamma = true ∧ Canonical.check out = true ∧ unionInterpretation out = sourceValue gamma := by
  obtain ⟨hi, rfl⟩ := (execute_graph gamma out).mp ho
  exact ⟨hi, publicCode_spec gamma hi⟩

def graphBool (gamma out : Nat) : Bool := inputCheck gamma && (out == publicCode gamma)

theorem graphBool_primrec : Primrec₂ graphBool :=
  (Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (publicCode_primrec.comp Primrec.fst))).to₂

theorem graphBool_exact (gamma out : Nat) : graphBool gamma out = true ↔ out ∈ execute gamma := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

/-- Canonical original initial values identify the actual selected source
before any mu operation, giving literal output equality. -/
theorem publicCode_equal_value (gamma other : Nat)
    (hi : inputCheck gamma = true) (hj : inputCheck other = true)
    (hv : unionInterpretation gamma = unionInterpretation other) : publicCode gamma = publicCode other := by
  have hg := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp ((inputCheck_exact gamma).mp hi).1
  have ho := (PublicEpsilonSourceDictionary.inputCheck_exact other).mp ((inputCheck_exact other).mp hj).1
  exact congrArg publicCode (Canonical.check_value_injective gamma other hg.1 ho.1 hv)

end Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary
