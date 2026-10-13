import Alexander313.ArithmeticInstances
import Alexander313.SourceColumns
import Alexander313.Thesis311

/-!
# Finite-proof common-core inheritance

A closed core theorem is padded with x = x, compiled into the actual unary
column, and transferred using its finite arithmetic computation certificate,
the admitted particular core code, and core reflection. The proof uses
Assigned Validity for the two modal numeral instances and nothing stronger.

The source family and the universal arithmetic finite-trace certificate are
explicit inputs to this general lemma. The canonical assembly constructs both. This lemma proves the inheritance
step from those inputs; it does not produce the full fixed-point family.
-/

namespace Alexander313

def closedUnaryPadding (σ : Formula Nat) (hσ : σ.Closed) : UnaryFormula Nat where
  input := 0
  body := .conj σ (.equal (.var 0) (.var 0))
  freeVars_exact := by
    have hs : σ.freeVars = ∅ := hσ
    simp [Formula.freeVars, Term.freeVars, hs]

@[simp] theorem closedUnaryPadding_close (σ : Formula Nat) (hσ : σ.Closed)
    (s : Assignment) :
    (closedUnaryPadding σ hσ).body.close s =
      .conj σ (.equal (Term.numeral (s 0)) (Term.numeral (s 0))) := by
  change Formula.conj (σ.close s)
    (.equal (Term.numeral (s 0)) (Term.numeral (s 0))) = _
  rw [Formula.close_eq_self_of_closed σ hσ s]

theorem closedUnaryPadding_member (F : MachineFamily) (core : Nat)
    {σ : Formula Nat} (hp : F.effective.proves core σ) (s : Assignment) :
    F.effective.proves core ((closedUnaryPadding σ (F.sentences core σ hp)).body.close s) := by
  apply (F.theory_closed core _ (Formula.close_closed _ s)).mp
  refine ⟨{ premises := [σ], admitted := ?_, validity := ?_ }⟩
  · intro θ hθ
    simpa only [List.mem_singleton.mp hθ] using hp
  · intro D hD M t
    rw [closedUnaryPadding_close]
    exact fun h => ⟨h, rfl⟩

theorem ArithmeticCoding.member_numerals_closed {Owner : Type}
    (A : ArithmeticCoding Owner) (e n : Nat) :
    (A.member (Term.numeral e) (Term.numeral n)).Closed := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := A.variables (Term.numeral e) (Term.numeral n) hv
  have hempty : v ∈ (∅ : Finset Nat) := by
    simpa only [Term.freeVars_numeral, Finset.empty_union] using h
  exact Finset.notMem_empty v hempty

/-- This is a consequence theorem with literal schema premises, rather than
    an inheritance property assumed of the desired family. -/
theorem common_core_inheritance (A : ArithmeticCoding Nat)
    (coherent : CoherentArithmeticCoding A) (F : MachineFamily) (core i : Nat)
    (assigned : ∀ θ t, Valid θ → F.effective.proves i (θ.close t))
    (arithmetic : ∀ θ, PAInstance Nat θ → F.effective.proves i θ)
    (codes : ∀ φ : UnaryFormula Nat, F.effective.proves i
      (codeSentence A core φ (F.unaryColumnIndex core φ)))
    (reflects : ∀ φ, F.effective.proves i (reflection core φ))
    (trace : ∀ e n, W e n → Provable (PAInstance Nat)
      (A.member (Term.numeral e) (Term.numeral n))) :
    ∀ σ, F.effective.proves core σ → F.effective.proves i σ := by
  intro σ hp
  have hσ := F.sentences core σ hp
  let φ := closedUnaryPadding σ hσ
  let s : Assignment := fun _ => 0
  let u := Function.update s φ.input 0
  let e := F.unaryColumnIndex core φ
  have hcore : F.effective.proves core (φ.body.close u) :=
    closedUnaryPadding_member F core hp u
  have he : W e 0 := by
    have hW := (F.unaryColumn_equation core φ u).mpr hcore
    simpa only [u, Function.update_self] using hW
  have hquery : F.effective.proves i (A.member (Term.numeral e) (Term.numeral 0)) :=
    (F.theory_closed i _ (A.member_numerals_closed e 0)).mp
      ((trace e 0 he).mono arithmetic)
  have hcode : F.effective.proves i
      ((Formula.iff (.know core φ.body) (A.member (Term.numeral e) (.var φ.input))).close u) := by
    apply F.all_numerical_instance i φ.input
      (.iff (.know core φ.body) (A.member (Term.numeral e) (.var φ.input))) s 0 assigned
    change F.effective.proves i ((codeSentence A core φ e).close s)
    rw [Formula.close_eq_self_of_closed _ (codeSentence_closed A core φ e)]
    exact codes φ
  have hknown : F.effective.proves i (.know core (φ.body.close u)) := by
    have hc : (Formula.know core (φ.body.close u)).Closed := φ.body.close_closed u
    apply (F.theory_closed i _ hc).mp
    refine ⟨{ premises := [
      (Formula.iff (.know core φ.body) (A.member (Term.numeral e) (.var φ.input))).close u,
      A.member (Term.numeral e) (Term.numeral 0)], admitted := ?_, validity := ?_ }⟩
    · intro θ hθ
      rcases List.mem_cons.mp hθ with rfl | hθ
      · exact hcode
      · simpa only [List.mem_singleton.mp hθ] using hquery
    · intro D hD M t
      apply chain_intro
      intro hΓ
      have hc := hΓ _ List.mem_cons_self
      have hq := hΓ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      have hequiv := arithmetic_member_close_valid A coherent e φ.input 0 u
        (Function.update_self _ _ _) D hD M t
      exact hc.2 (hequiv.2 hq)
  have hr : F.effective.proves i
      ((Formula.imp (.know core φ.body) φ.body).close u) := by
    apply F.all_numerical_instance i φ.input (.imp (.know core φ.body) φ.body)
      s 0 assigned
    have hreflection : reflection core φ.body =
        .all φ.input (.imp (.know core φ.body) φ.body) := by
      simp [reflection, Formula.universalClosure, Formula.freeVars, φ.freeVars_exact]
    have hc : (Formula.all φ.input (.imp (.know core φ.body) φ.body)).Closed := by
      rw [← hreflection]
      exact Formula.universalClosure_closed _
    rw [Formula.close_eq_self_of_closed _ hc, ← hreflection]
    exact reflects φ.body
  have hbody : F.effective.proves i (φ.body.close u) :=
    F.modus_ponens i hr hknown
  apply (F.theory_closed i σ hσ).mp
  refine ⟨{ premises := [φ.body.close u], admitted := ?_, validity := ?_ }⟩
  · intro θ hθ
    simpa only [List.mem_singleton.mp hθ] using hbody
  · intro D hD M t h
    change generalTruth M ((closedUnaryPadding σ hσ).body.close u) t at h
    rw [closedUnaryPadding_close] at h
    exact h.1

end Alexander313
