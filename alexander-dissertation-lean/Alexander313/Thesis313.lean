import Alexander313.Thesis311
import Alexander313.Thesis312
import Alexander313.WholeIdeal

/-!
# The final schema assembly and logical reductions

`assemble313` is explicitly conditional. Constructing its family,
soundness proof and schema memberships from an arbitrary r.e. well-founded
R is the unfinished task. It is not named `thesis313` and cannot be
mistaken for the unconditional comparator target.
-/

namespace Alexander313

structure SchemaMembership313 (R : Nat → Nat → Prop)
    (A : ArithmeticCoding Nat) (F : MachineFamily) : Prop where
  ea : ∀ i φ, EAInstance i φ → ∀ s, F.effective.proves i (φ.close s)
  truth : ∀ i j φ s, F.effective.proves i ((reflection j φ).close s)
  codes : ∀ i j, R j i → ∀ φ : UnaryFormula Nat,
    ∃ e, ∀ s, F.effective.proves i ((codeSentence A j φ e).close s)
  mechanical : ∀ i j (φ : UnaryFormula Nat) s,
    F.effective.proves i ((mechanicalSentence A j φ).close s)

theorem assemble313 (R : Nat → Nat → Prop) (A : ArithmeticCoding Nat)
    (F : MachineFamily) (sound : ∀ i, RawSound F.effective.proves i)
    (membership : SchemaMembership313 R A F) : Nonempty (Solution313 R) := by
  have hea : satisfiesEA F := by
    intro i φ hφ s
    exact (filtered_eq_actual F.effective.proves sound φ s).mp
      (sound i φ s (membership.ea i φ hφ s))
  have htruth : knowsTruth F := by
    intro i j φ s
    exact ⟨membership.truth i j φ s, trivial⟩
  have hcodes : knowsParticularCodes A F R := by
    intro i j hji φ
    obtain ⟨e, he⟩ := membership.codes i j hji φ
    exact ⟨e, fun s => ⟨he s, trivial⟩⟩
  have hall : knowsAllMechanicalness A F := by
    intro i j φ s
    exact ⟨membership.mechanical i j φ s, trivial⟩
  exact ⟨{
    toSolution312 := {
      toSolution311 := {
        arithmetic := A
        family := F
        realization := F.actualRealization
        epistemic_arithmetic := hea
        mutual_truth := htruth
        particular_codes := hcodes
        subordinate_mechanicalness := fun i j _ φ s => hall i j φ s }
      own_mechanicalness := fun i φ s => hall i i φ s }
    all_mechanicalness := hall }⟩

theorem statement313_implies312 (h : Statement313) : Statement312 := by
  intro R hre hwf
  obtain ⟨S⟩ := h R hre hwf
  exact ⟨S.toSolution312⟩

theorem statement313_implies311 (h : Statement313) : Statement311 :=
  statement312_implies311 (statement313_implies312 h)

end Alexander313
