import Alexander313.Arithmetic.SequenceCoding

/-!
# Arithmetic graphs of the actual universal-program constructor codes

The constructor payload uses mathlib's square pairing, and the tags agree
with `Nat.Partrec.Code.encodeCode`. This is part of decoding a future finite
execution trace. The module constructs the formulas and PA numeral-instance
certificates; it does not assume or assert a universal trace-correctness lemma.
-/

namespace Alexander313

theorem truth_arithmetic_renameVariables {Owner : Type} (φ : Formula Owner)
    (hφ : φ.Arithmetic) (f : Nat → Nat) (hf : Function.Injective f)
    (filtered : Bool) (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (φ.renameVariables f) s ↔ truth filtered P φ (s ∘ f) := by
  rw [← generalTruth_arithmeticStandardModel (φ.renameVariables f)
    (φ.arithmetic_renameVariables hφ f) P filtered s]
  rw [Formula.generalTruth_renameVariables _ φ hφ f hf]
  exact generalTruth_arithmeticStandardModel φ hφ P filtered (s ∘ f)

theorem Formula.positiveExistential_renameVariables {Owner : Type}
    (φ : Formula Owner) (hφ : φ.PositiveExistential) (f : Nat → Nat) :
    (φ.renameVariables f).PositiveExistential := by
  induction φ <;> simp_all [Formula.renameVariables, Formula.PositiveExistential]

/-- Ports 0,1 are the two program-code payloads; port 2 is the resulting
    code. The internal pairing output is variable 4, kept distinct from
    the local order witness 3. -/
def binaryProgramGraph (Owner : Type) (tag : Nat) : Formula Owner :=
  .ex 4 (.conj ((pairGraph Owner).renameVariables (Equiv.swap 2 4))
    (.equal (.var 2) (.add (.mul (Term.numeral 4) (.var 4)) (Term.numeral tag))))

theorem binaryProgramGraph_positive (Owner : Type) (tag : Nat) :
    (binaryProgramGraph Owner tag).PositiveExistential := by
  exact ⟨(pairGraph Owner).positiveExistential_renameVariables
    (pairGraph_positive Owner) _, trivial⟩

theorem binaryProgramGraph_truth {Owner : Type} (tag : Nat) (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (binaryProgramGraph Owner tag) s ↔
      s 2 = 4 * Nat.pair (s 0) (s 1) + tag := by
  simp only [binaryProgramGraph, truth]
  have hpair (p : Nat) : truth filtered P
      ((pairGraph Owner).renameVariables (Equiv.swap 2 4)) (Function.update s 4 p) ↔
      p = Nat.pair (s 0) (s 1) := by
    rw [truth_arithmetic_renameVariables _
      (Formula.positiveExistential_arithmetic _ (pairGraph_positive Owner))
      _ (Equiv.swap 2 4).injective, pairGraph_truth]
    simp [Function.comp_def, Equiv.swap_apply_def]
  simp only [hpair, Term.eval, Term.eval_numeral, Function.update_self,
    Function.update_of_ne (by decide : 2 ≠ 4)]
  constructor
  · rintro ⟨p, rfl, hp⟩
    exact hp
  · intro h
    exact ⟨_, rfl, h⟩

/-- The minimization constructor has one directly arithmetic payload. -/
def searchProgramGraph (Owner : Type) : Formula Owner :=
  .equal (.var 1) (.add (.mul (Term.numeral 4) (.var 0)) (Term.numeral 7))

theorem searchProgramGraph_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (searchProgramGraph Owner) s ↔ s 1 = 4 * s 0 + 7 := by
  simp [searchProgramGraph, truth, Term.eval]

theorem program_pair_encoding (c d : Program) :
    Encodable.encode (Nat.Partrec.Code.pair c d) =
      4 * Nat.pair (Encodable.encode c) (Encodable.encode d) + 4 := by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  omega

theorem program_comp_encoding (c d : Program) :
    Encodable.encode (Nat.Partrec.Code.comp c d) =
      4 * Nat.pair (Encodable.encode c) (Encodable.encode d) + 6 := by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  omega

theorem program_prec_encoding (c d : Program) :
    Encodable.encode (Nat.Partrec.Code.prec c d) =
      4 * Nat.pair (Encodable.encode c) (Encodable.encode d) + 5 := by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  omega

theorem program_rfind_encoding (c : Program) :
    Encodable.encode (Nat.Partrec.Code.rfind' c) = 4 * Encodable.encode c + 7 := by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  omega

theorem pa_proves_binary_program_instance (Owner : Type) (tag a b : Nat) :
    Provable (PAInstance Owner) ((binaryProgramGraph Owner tag).close
      (fun v => if v = 0 then a else if v = 1 then b
        else if v = 2 then 4 * Nat.pair a b + tag else 0)) := by
  apply pa_proves_positive_numeral_instance _ (binaryProgramGraph_positive Owner tag)
  apply (binaryProgramGraph_truth tag false (fun _ _ => False) _).mpr
  simp

theorem pa_proves_search_program_instance (Owner : Type) (c : Program) :
    Provable (PAInstance Owner) ((searchProgramGraph Owner).close
      (fun v => if v = 0 then Encodable.encode c
        else if v = 1 then Encodable.encode (Nat.Partrec.Code.rfind' c) else 0)) := by
  apply pa_proves_positive_numeral_instance _ (show
    (searchProgramGraph Owner).PositiveExistential from trivial)
  apply (searchProgramGraph_truth false (fun _ _ => False) _).mpr
  simpa using program_rfind_encoding c

end Alexander313
