import Alexander313.CommonCoreAssembly
import Alexander313.ParameterColumns

/-!
# Actual numerical columns for the core genericity argument

An effective predicate family need not be consequence closed. Its actual joint
recognizer and the existing unary-instance compiler nevertheless enumerate every
numerical parameter column. Full soundness at the queried owner removes the
filtered truth conjunct, so that same column witnesses the literal unrestricted
parameter mechanicalness sentence. No column or mechanicalness oracle is used.
-/

namespace Alexander313

theorem EffectiveFamily.parameter_column_exists (F : EffectiveFamily Nat)
    (owners : ∀ a, F.encodeOwner a = a) (j : Nat) (φ : Formula Nat)
    (x : Nat) (s : Assignment) :
    ∃ c : Nat, ∀ n, W c n ↔ F.proves j (φ.close (Function.update s x n)) := by
  let p := unaryColumnCompiler (((F.recognizes, j),
    (φ.parameterInstance x s).code id), x)
  refine ⟨Encodable.encode p, ?_⟩
  intro n
  have decode : Nat.Partrec.Code.ofNatCode (Encodable.encode p) = p :=
    Denumerable.ofNat_encode p
  rw [W, decode]
  dsimp only [p]
  rw [unaryColumnCompiler_eval, Formula.substCode_code, Formula.parameterInstance_subst]
  have ownerFunction : F.encodeOwner = id := funext owners
  have formulaCode : F.encodeFormula (φ.close (Function.update s x n)) =
      (φ.close (Function.update s x n)).code id := by
    rw [F.formula_coding, ownerFunction]
  simpa only [Program.domain, owners j, formulaCode] using
    F.recognizes_correct j (φ.close (Function.update s x n))

theorem EffectiveFamily.parameter_mechanical_truth (F : EffectiveFamily Nat)
    (owners : ∀ a, F.encodeOwner a = a) (A : ArithmeticCoding Nat)
    (j x e : Nat) (φ : Formula Nat) (fresh : e ∉ φ.freeVars)
    (distinct : e ≠ x) (sound : RawSound F.proves j) (s : Assignment) :
    filteredTruth F.proves (parameterMechanicalSentence A j x e φ) s := by
  apply truth_universalClosure true F.proves _ _ s
  intro t
  obtain ⟨c, column⟩ := F.parameter_column_exists owners j φ x t
  refine ⟨c, ?_⟩
  intro n
  have knowColumn : filteredTruth F.proves (.know j φ)
      (Function.update (Function.update t e c) x n) ↔ W c n := by
    rw [filtered_know_iff F.proves sound,
      Formula.close_update_fresh_before φ x e n c t fresh]
    exact (column n).symm
  have memberColumn : filteredTruth F.proves (A.member (.var e) (.var x))
      (Function.update (Function.update t e c) x n) ↔ W c n := by
    change truth true F.proves (A.member (.var e) (.var x))
      (Function.update (Function.update t e c) x n) ↔ W c n
    rw [A.correct]
    simp only [Term.eval, Function.update_self, Function.update_of_ne distinct]
  exact ⟨fun h => memberColumn.mpr (knowColumn.mp h),
    fun h => knowColumn.mpr (memberColumn.mp h)⟩

end Alexander313
