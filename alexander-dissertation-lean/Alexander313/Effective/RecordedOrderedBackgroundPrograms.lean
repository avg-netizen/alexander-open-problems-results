import Alexander313.Effective.RecordedOrderedFormation
import Alexander313.Effective.RecordedPositiveImages

/-!
# The actual seven recorded background rows with a supplied order Program

Formula formation, assignments, contexts, reflection and all seven row tags
are the existing literal construction. The whole output nesting check and
the introspection edge use positive computations of the supplied order
Program. Validity remains the original executing validity Program, interpreted
through the proved injective recorded-owner encoding, without source erasure.
-/

noncomputable section

namespace Alexander313.OrderedRecordedBackgroundProgram

open RecordedFormula
open RecordedBackgroundProgram (positive positive_primrec positive_iff)

abbrev Parameters := Program × RecordedBackgroundProgram.Parameters
abbrev Witness := RecordedBackgroundProgram.Witness
abbrev Cutoffs := Nat × Nat

def formula (a : Nat) (w : Witness) : Syntax := RecordedBackgroundProgram.formula a w

theorem formula_primrec : Primrec₂ formula := RecordedBackgroundProgram.formula_primrec

theorem formula_closed (a : Nat) (w : Witness) : (formula a w).Closed :=
  RecordedBackgroundProgram.formula_closed a w

def branch (p : Parameters) (w : Witness) : Prop :=
  if w.1.1 = 0 then w.2.2.2.2.1.1 ≤ 6 else
  if w.1.1 = 1 ∨ w.1.1 = 2 then p.2.2.domain (w.2.1.2.1.code RecordedHead.code) else
  if w.1.1 = 3 then True else
  if w.1.1 = 4 then p.1.domain (Nat.pair w.1.2.1 w.1.2.2) else
  if w.1.1 = 5 then True else p.2.1.2.domain (Nat.pair w.1.2.1 w.1.2.2)

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  (letI : LT Nat := Program.orderLT p.1
   (formula a w).RecordedAdmissible p.2.1.1.1.toFinset p.2.1.1.2.toFinset) ∧ branch p w

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w : Witness, side p a w ∧ σ = formula a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, _, rfl⟩ := h
  exact formula_closed a w

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) :
    letI : LT Nat := Program.orderLT p.1
    σ.RecordedAdmissible p.2.1.1.1.toFinset p.2.1.1.2.toFinset := by
  obtain ⟨w, hs, rfl⟩ := h
  exact hs.1

theorem background_exact (p : Parameters) (R : Nat → Nat → Prop)
    (hedge : ∀ μ ν, p.2.1.2.domain (Nat.pair μ ν) ↔ R μ ν)
    (hvalid : ∀ φ : Formula Nat, p.2.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    admits p a σ ↔
      letI : LT Nat := Program.orderLT p.1
      RecordedBackground p.2.1.1.1.toFinset p.2.1.1.2.toFinset a R σ := by
  letI : LT Nat := Program.orderLT p.1
  have hv (φ : Syntax) : p.2.2.domain (φ.code RecordedHead.code) ↔ Valid φ := by
    rw [← encode_code, hvalid, valid_encode]
  constructor
  · rintro ⟨w, ⟨ha, hb⟩, rfl⟩
    by_cases h0 : w.1.1 = 0
    · simp only [formula, RecordedBackgroundProgram.formula, if_pos h0] at ha ⊢
      exact .arithmetic (paFormula_pa _ (by simpa [branch, h0] using hb)) ha
    by_cases h1 : w.1.1 = 1
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_pos h1, close] at ha ⊢
      exact .assigned _ _ ((hv _).mp (by simpa [branch, h0, h1] using hb))
        ((Formula.recordedAdmissible_close _ _ _ _).mp ha)
    by_cases h2 : w.1.1 = 2
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_neg h1,
        if_pos h2] at ha ⊢
      exact .own_validity _ _ ((hv _).mp (by simpa [branch, h0, h1, h2] using hb)) ha
    by_cases h3 : w.1.1 = 3
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_neg h1,
        if_neg h2, if_pos h3] at ha ⊢
      exact .deduction _ _ _ ha
    by_cases h4 : w.1.1 = 4
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_neg h1,
        if_neg h2, if_neg h3, if_pos h4] at ha ⊢
      exact .introspection _ _ _ (by simpa [branch, h0, h1, h2, h3, h4] using hb) ha
    by_cases h5 : w.1.1 = 5
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_neg h1,
        if_neg h2, if_neg h3, if_neg h4, if_pos h5] at ha ⊢
      exact .reflection _ _ ha
    · simp only [formula, RecordedBackgroundProgram.formula, if_neg h0, if_neg h1,
        if_neg h2, if_neg h3, if_neg h4, if_neg h5, collapse] at ha ⊢
      exact .contextual _ _ _ _ _
        ((hedge _ _).mp (by simpa [branch, h0, h1, h2, h3, h4, h5] using hb)) ha
  · intro h
    cases h with
    | arithmetic hp ha =>
      obtain ⟨v, ht, hσ⟩ := pa_represents σ hp
      let w : Witness := ((0, (0, 0)), ((.live 0, (.falsum, .falsum)), ([], ([], v))))
      exact ⟨w, by simpa [side, formula, RecordedBackgroundProgram.formula, branch, w, ← hσ]
        using And.intro ha ht, by simpa [formula, RecordedBackgroundProgram.formula, w] using hσ⟩
    | assigned φ s hvφ ha =>
      obtain ⟨L, hL⟩ := close_represents φ s
      let w : Witness := ((1, (0, 0)), ((.live 0, (φ, .falsum)),
        (L, ([], ((0, 0), (.falsum, .falsum))))))
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · simpa [formula, RecordedBackgroundProgram.formula, w, close] using
          (Formula.recordedAdmissible_close _ _ φ (FiniteAssignment.assignment L)).mpr ha
      · simpa [branch, w] using (hv φ).mpr hvφ
      · simpa [formula, RecordedBackgroundProgram.formula, w] using hL
    | own_validity ν φ hvφ ha =>
      let w : Witness := ((2, (0, ν)), ((.live 0, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, ⟨by simpa [formula, RecordedBackgroundProgram.formula, w] using ha,
        by simpa [branch, w] using (hv φ).mpr hvφ⟩, rfl⟩
    | deduction ν φ ψ ha =>
      let w : Witness := ((3, (0, ν)), ((.live 0, (φ, ψ)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, RecordedBackgroundProgram.formula, branch, w] using ha, rfl⟩
    | introspection μ ν φ hμν ha =>
      let w : Witness := ((4, (μ, ν)), ((.live 0, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, RecordedBackgroundProgram.formula, branch, w]
        using And.intro ha hμν, rfl⟩
    | reflection b φ ha =>
      let w : Witness := ((5, (0, 0)), ((b, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, RecordedBackgroundProgram.formula, branch, w] using ha, rfl⟩
    | contextual c b μ ν φ hr ha =>
      obtain ⟨L, hL⟩ := context_represents c
      let w : Witness := ((6, (μ, ν)), ((.live b, (φ, .falsum)),
        ([], (L, ((0, 0), (.falsum, .falsum))))))
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · simpa [formula, RecordedBackgroundProgram.formula, w, collapse, RecordedHead.erase, hL] using ha
      · simpa [branch, w] using (hedge μ ν).mpr hr
      · simp [formula, RecordedBackgroundProgram.formula, w, collapse, RecordedHead.erase, hL]

def branchCheck (p : Parameters) (w : Witness) (cutoff : Nat) : Bool :=
  if w.1.1 = 0 then decide (w.2.2.2.2.1.1 ≤ 6) else
  if w.1.1 = 1 ∨ w.1.1 = 2 then positive cutoff p.2.2 (w.2.1.2.1.code RecordedHead.code) else
  if w.1.1 = 3 then true else
  if w.1.1 = 4 then positive cutoff p.1 (Nat.pair w.1.2.1 w.1.2.2) else
  if w.1.1 = 5 then true else positive cutoff p.2.1.2 (Nat.pair w.1.2.1 w.1.2.2)

theorem branchCheck_primrec : Primrec (fun p : (Parameters × Witness) × Nat =>
    branchCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × Witness) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Witness) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht := Primrec.fst.comp (Primrec.fst.comp hw)
  have hμ := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hν := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hφ := code_primrec.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hw))))
  have hpa := Primrec.fst.comp (Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hw)))))
  have hdata := Primrec.snd.comp hp
  have hedge := Primrec.snd.comp (Primrec.fst.comp hdata)
  have hvalid := Primrec.snd.comp hdata
  have horder := Primrec.fst.comp hp
  have hinput := Primrec₂.natPair.comp hμ hν
  have test (n : Nat) := Primrec.eq.comp ht (Primrec.const n)
  have result := Primrec.ite (test 0) (Primrec.nat_le.comp hpa (Primrec.const 6)).decide
    (Primrec.ite ((test 1).or (test 2))
      (positive_primrec.comp ((Primrec.snd.pair hvalid).pair hφ))
      (Primrec.ite (test 3) (Primrec.const true)
        (Primrec.ite (test 4) (positive_primrec.comp ((Primrec.snd.pair horder).pair hinput))
          (Primrec.ite (test 5) (Primrec.const true)
            (positive_primrec.comp ((Primrec.snd.pair hedge).pair hinput))))))
  exact result.of_eq (fun _ => rfl)

theorem branchCheck_correct (p : Parameters) (w : Witness) :
    (∃ cutoff, branchCheck p w cutoff = true) ↔ branch p w := by
  unfold branchCheck branch
  split_ifs <;> simp [positive_iff]

/-- Whole output nesting and the row's positive condition have independent
    finite cutoffs, so completeness requires no synchronized computation. -/
def condition (p : Parameters) (a : Nat) (w : Witness) (k : Cutoffs) : Bool :=
  OrderedRecordedAdmissionProgram.condition p.1 p.2.1.1 (formula a w) k.1 &&
    branchCheck p w k.2

theorem condition_primrec : Primrec (fun p : (Parameters × Nat) × (Witness × Cutoffs) =>
    condition p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × (Witness × Cutoffs) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × (Witness × Cutoffs) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × (Witness × Cutoffs) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : (Parameters × Nat) × (Witness × Cutoffs) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have horder := Primrec.fst.comp hp
  have hAE := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hp))
  have hformula := formula_primrec.comp ha hw
  have result := Primrec.and.comp
    (OrderedRecordedAdmissionProgram.condition_primrec.comp
      (((horder.pair hAE).pair hformula).pair (Primrec.fst.comp hk)))
    (branchCheck_primrec.comp ((hp.pair hw).pair (Primrec.snd.comp hk)))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ k, condition p a w k = true) ↔ side p a w := by
  constructor
  · rintro ⟨k, h⟩
    have hh := Bool.and_eq_true_iff.mp h
    exact ⟨(OrderedRecordedAdmissionProgram.condition_correct p.1 p.2.1.1 _).mp ⟨k.1, hh.1⟩,
      (branchCheck_correct p w).mp ⟨k.2, hh.2⟩⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨k, hk⟩ := (OrderedRecordedAdmissionProgram.condition_correct p.1 p.2.1.1 _).mpr ha
    obtain ⟨l, hl⟩ := (branchCheck_correct p w).mpr hb
    exact ⟨(k, l), by simp only [condition, hk, hl, Bool.true_and]⟩

abbrev Certificate := Witness × Cutoffs

def imageFormula (_p : Parameters) (a : Nat) (c : Certificate) : Syntax := formula a c.1

theorem imageFormula_primrec :
    Primrec (fun p : (Parameters × Nat) × Certificate => imageFormula p.1.1 p.1.2 p.2) :=
  formula_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)

def imageCondition (p : Parameters) (a : Nat) (c : Certificate) : Bool := condition p a c.1 c.2

theorem imageCondition_primrec :
    Primrec (fun p : (Parameters × Nat) × Certificate => imageCondition p.1.1 p.1.2 p.2) :=
  condition_primrec

theorem image_exact (p : Parameters) (a : Nat) (σ : Syntax) :
    RecordedPositiveImage.image imageFormula imageCondition p a σ ↔ admits p a σ := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.1, (condition_correct p a c.1).mp ⟨c.2, hc⟩, rfl⟩
  · rintro ⟨w, hw, hσ⟩
    obtain ⟨k, hk⟩ := (condition_correct p a w).mpr hw
    exact ⟨(w, k), hk, hσ⟩

/-- Actual uniform positive recognition of every existing background row.
    Raw queries are literal closed formulas admissible for the supplied order. -/
theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        (letI : LT Nat := Program.orderLT p.1
         σ.RecordedAdmissible p.2.1.1.1.toFinset p.2.1.1.2.toFinset)) := by
  obtain ⟨compiler, hpr, htyped, hraw⟩ := RecordedPositiveImage.compiler_exists
    (Nat.Partrec.Code.zero, RecordedBackgroundProgram.defaultParameters)
    (RecordedBackgroundProgram.defaultWitness, (0, 0))
    imageFormula imageCondition imageFormula_primrec imageCondition_primrec
  refine ⟨compiler, hpr, ?_, ?_⟩
  · intro p a σ
    exact (htyped p a σ).trans (image_exact p a σ)
  · intro p query h
    obtain ⟨a, σ, hq, hi⟩ := hraw p query h
    have ha := (image_exact p a σ).mp hi
    exact ⟨a, σ, hq, admits_closed ha, admits_admissible ha⟩

end Alexander313.OrderedRecordedBackgroundProgram
