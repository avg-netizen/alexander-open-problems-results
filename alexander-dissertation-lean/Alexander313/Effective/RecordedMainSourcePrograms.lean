import Alexander313.Effective.CommonCorePrograms
import Alexander313.Effective.RecordedGuardPrograms
import Alexander313.RecordedMain

/-!
# Literal formation and finite checks for the three recorded main sources

The common-core formula constructor retains its actual source Program's
compiled unary-column numeral. The accompanying atom is the original modal
atom, before recording. Active/external policies and positive hierarchy
computations are finite tests; no Valid or source soundness test is used.

Identification with a presentation states both canonical arithmetic identity
and actual source Program identity. It does not replace column numerals with
a supplied effectivity contract.
-/

noncomputable section

namespace Alexander313.RecordedMainSourceProgram

open RecordedFormula RecordedGuardProgram

abbrev Witness := CommonCoreProgram.Witness

def formula (source : Program) (tag : Nat) (w : Witness) : Formula Nat :=
  CommonCoreProgram.formula source tag w

theorem formula_primrec : Primrec (fun p : (Program × Nat) × Witness =>
    formula p.1.1 p.1.2 p.2) := CommonCoreProgram.formula_primrec

def atom (tag : Nat) (w : Witness) : Formula Nat :=
  .know (if tag = 1 then 0 else w.1.1.1 + 1) w.2

theorem atom_primrec : Primrec₂ atom := by
  have htag : Primrec (fun p : Nat × Witness => p.1) := Primrec.fst
  have hw : Primrec (fun p : Nat × Witness => p.2) := Primrec.snd
  have hj := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  exact (Formula.know_primrec.comp
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
      (Primrec.const 0) (Primrec.succ.comp hj))
    (Primrec.snd.comp hw)).to₂

def zeroActiveCheck (A : List Nat) : Bool :=
  listMember A 0 && allCheck (fun a => a == 0) A

theorem zeroActiveCheck_primrec : Primrec zeroActiveCheck := by
  have ht : Primrec₂ (fun (_ : Unit) (a : Nat) => a == 0) :=
    (Primrec.beq.comp Primrec.snd (Primrec.const 0)).to₂
  exact Primrec.and.comp (listMember_primrec.comp Primrec.id (Primrec.const 0))
    ((allCheck_primrec _ ht).comp (Primrec.const ()) Primrec.id)

@[simp] theorem zeroActiveCheck_iff (A : List Nat) :
    zeroActiveCheck A = true ↔ A.toFinset = {0} := by
  simp only [zeroActiveCheck, Bool.and_eq_true, listMember, decide_eq_true_eq,
    allCheck_iff, beq_iff_eq]
  constructor
  · rintro ⟨hzero, hall⟩
    apply Finset.ext
    intro a
    simp only [List.mem_toFinset, Finset.mem_singleton]
    exact ⟨hall a, fun h => h ▸ hzero⟩
  · intro h
    have hzero : 0 ∈ A := by
      have : 0 ∈ A.toFinset := by rw [h]; simp
      simpa only [List.mem_toFinset] using this
    refine ⟨hzero, ?_⟩
    intro a ha
    have : a ∈ A.toFinset := by simpa only [List.mem_toFinset] using ha
    rw [h] at this
    simpa only [Finset.mem_singleton] using this

def policy (A E : List Nat) (tag holder : Nat) (w : Witness) : Bool :=
  if tag = 0 then zeroActiveCheck A
  else if tag = 1 then
    listMember A holder && (!listMember A 0 && !listMember E 0)
  else
    listMember A holder &&
      (!listMember A (w.1.1.1 + 1) && !listMember E (w.1.1.1 + 1))

theorem policy_primrec :
    Primrec (fun p : ((List Nat × List Nat) × Nat) × (Nat × Witness) =>
      policy p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  have hAE : Primrec (fun p : ((List Nat × List Nat) × Nat) × (Nat × Witness) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hA := Primrec.fst.comp hAE
  have hE := Primrec.snd.comp hAE
  have ht : Primrec (fun p : ((List Nat × List Nat) × Nat) × (Nat × Witness) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hh : Primrec (fun p : ((List Nat × List Nat) × Nat) × (Nat × Witness) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hw : Primrec (fun p : ((List Nat × List Nat) × Nat) × (Nat × Witness) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hj := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  have howner := Primrec.succ.comp hj
  have hactive := listMember_primrec.comp hA hh
  have hcore := Primrec.and.comp hactive
    (Primrec.and.comp (Primrec.not.comp (listMember_primrec.comp hA (Primrec.const 0)))
      (Primrec.not.comp (listMember_primrec.comp hE (Primrec.const 0))))
  have hsub := Primrec.and.comp hactive
    (Primrec.and.comp (Primrec.not.comp (listMember_primrec.comp hA howner))
      (Primrec.not.comp (listMember_primrec.comp hE howner)))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (zeroActiveCheck_primrec.comp hA)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hcore hsub)

theorem policy_iff (A E : List Nat) (tag holder : Nat) (w : Witness) :
    policy A E tag holder w = true ↔
      if tag = 0 then A.toFinset = {0}
      else if tag = 1 then holder ∈ A.toFinset ∧ 0 ∉ A.toFinset ∧ 0 ∉ E.toFinset
      else holder ∈ A.toFinset ∧ w.1.1.1 + 1 ∉ A.toFinset ∧
        w.1.1.1 + 1 ∉ E.toFinset := by
  by_cases hzero : tag = 0
  · simp [policy, hzero]
  · by_cases hone : tag = 1 <;> simp [policy, hzero, hone, listMember]

def sideCondition (edge : Program) (A E : List Nat) (tag holder : Nat) (w : Witness) : Prop :=
  CommonCoreProgram.sideCondition edge tag holder w ∧ policy A E tag holder w = true

def condition (edge : Program) (A E : List Nat) (tag holder : Nat)
    (w : Witness) (cutoff : Nat) : Bool :=
  CommonCoreProgram.condition edge tag holder w cutoff && policy A E tag holder w

theorem condition_primrec :
    Primrec (fun p : (((Program × (List Nat × List Nat)) × Nat) × Nat) × (Witness × Nat) =>
      condition p.1.1.1.1 p.1.1.1.2.1 p.1.1.1.2.2 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  have hleft : Primrec (fun p : (((Program × (List Nat × List Nat)) × Nat) × Nat) ×
      (Witness × Nat) => p.1) := Primrec.fst
  have hhead := Primrec.fst.comp (Primrec.fst.comp hleft)
  have he := Primrec.fst.comp hhead
  have hAE := Primrec.snd.comp hhead
  have ht := Primrec.snd.comp (Primrec.fst.comp hleft)
  have hh := Primrec.snd.comp hleft
  have hw : Primrec (fun p : (((Program × (List Nat × List Nat)) × Nat) × Nat) ×
      (Witness × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc := CommonCoreProgram.condition_primrec.comp (((he.pair ht).pair hh).pair Primrec.snd)
  have hp := policy_primrec.comp ((hAE.pair ht).pair (hh.pair hw))
  exact Primrec.and.comp hc hp

theorem condition_correct (edge : Program) (A E : List Nat) (tag holder : Nat) (w : Witness) :
    (∃ cutoff, condition edge A E tag holder w cutoff = true) ↔
      sideCondition edge A E tag holder w := by
  constructor
  · rintro ⟨k, h⟩
    have hh := Bool.and_eq_true_iff.mp h
    exact ⟨(CommonCoreProgram.condition_correct edge tag holder w).mp ⟨k, hh.1⟩, hh.2⟩
  · rintro ⟨hc, hp⟩
    obtain ⟨k, hk⟩ := (CommonCoreProgram.condition_correct edge tag holder w).mpr hc
    exact ⟨k, by simp only [condition, hk, hp, Bool.true_and]⟩

def admits (source edge : Program) (A E : List Nat) (holder : Nat)
    (σ distinguished : Formula Nat) : Prop :=
  ∃ tag, ∃ w : Witness, sideCondition edge A E tag holder w ∧
    σ = formula source tag w ∧ distinguished = atom tag w

theorem admits_closed {source edge : Program} {A E : List Nat} {holder : Nat}
    {σ distinguished : Formula Nat} (h : admits source edge A E holder σ distinguished) : σ.Closed := by
  obtain ⟨tag, w, hs, hσ, _⟩ := h
  exact CommonCoreProgram.admits_closed ⟨tag, w, hs.1, hσ⟩

theorem admits_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (source edge : Program) (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = source)
    (hedge : ∀ j i, edge.domain (Nat.pair j i) ↔ R j i)
    (A E : List Nat) (holder : Nat) (σ distinguished : Formula Nat) :
    admits source edge A E holder σ distinguished ↔
      RecordedMainSource C A.toFinset E.toFinset holder σ distinguished := by
  have hcolumn (j : Nat) (φ : UnaryFormula Nat) :
      compiledUnaryColumnCode source j (φ.body.code id) φ.input = C.family.unaryColumnIndex j φ := by
    rw [← hsource]
    exact compiledUnaryColumnCode_family C.family j φ
  constructor
  · rintro ⟨tag, w, hs, rfl, rfl⟩
    have hp := (policy_iff A E tag holder w).mp hs.2
    have hc := hs.1
    by_cases hzero : tag = 0
    · simp only [CommonCoreProgram.sideCondition, if_pos hzero] at hc
      simp only [if_pos hzero] at hp
      rw [formula, CommonCoreProgram.formula, if_pos hzero, hc.1]
      simp only [atom, show tag ≠ 1 by omega, if_false]
      rw [← hArithmetic]
      exact .core_mechanical w.1.1.1 w.1.1.2 w.1.2 w.2 hp hc.2.1 hc.2.2
    · by_cases hone : tag = 1
      · simp only [CommonCoreProgram.sideCondition, if_neg hzero, if_pos hone] at hc
        simp only [if_neg hzero, if_pos hone] at hp
        have hholder : holder = (holder - 1) + 1 := by omega
        let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, hc.2⟩
        rw [formula, CommonCoreProgram.formula, if_neg hzero, if_pos hone]
        simp only [atom, if_pos hone]
        change RecordedMainSource C A.toFinset E.toFinset holder
          (codeSentence (canonicalArithmeticCoding Nat) 0 φ
            (compiledUnaryColumnCode source 0 (φ.body.code id) φ.input)) (.know 0 φ.body)
        rw [hcolumn, ← hArithmetic, hholder]
        exact .core_code (holder - 1) φ
          (by simpa only [← hholder] using hp.1) hp.2.1 hp.2.2
      · simp only [CommonCoreProgram.sideCondition, if_neg hzero, if_neg hone] at hc
        simp only [if_neg hzero, if_neg hone] at hp
        have hholder : holder = (holder - 1) + 1 := by omega
        let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, hc.2.1⟩
        rw [formula, CommonCoreProgram.formula, if_neg hzero, if_neg hone]
        simp only [atom, if_neg hone]
        change RecordedMainSource C A.toFinset E.toFinset holder
          (codeSentence (canonicalArithmeticCoding Nat) (w.1.1.1 + 1) φ
            (compiledUnaryColumnCode source (w.1.1.1 + 1) (φ.body.code id) φ.input))
          (.know (w.1.1.1 + 1) φ.body)
        rw [hcolumn, ← hArithmetic, hholder]
        exact .subordinate_code (holder - 1) w.1.1.1 φ ((hedge _ _).mp hc.2.2)
          (by simpa only [← hholder] using hp.1) hp.2.1 hp.2.2
  · intro h
    cases h with
    | core_mechanical j x e φ core fresh distinct =>
      refine ⟨0, (((j, x), e), φ), ?_, ?_, rfl⟩
      · refine ⟨?_, (policy_iff A E 0 0 _).mpr core⟩
        change 0 = 0 ∧ e ∉ φ.freeVars ∧ e ≠ x
        exact ⟨rfl, fresh, distinct⟩
      · simp only [formula, CommonCoreProgram.formula, ite_true, hArithmetic]
    | core_code i φ active outsideA outsideE =>
      refine ⟨1, (((0, φ.input), 0), φ.body), ?_, ?_, rfl⟩
      · refine ⟨?_, ?_⟩
        · simp only [CommonCoreProgram.sideCondition, show (1 : Nat) ≠ 0 by decide,
            if_false, if_true]
          exact ⟨by omega, φ.freeVars_exact⟩
        · apply (policy_iff A E 1 (i + 1) _).mpr
          exact ⟨active, outsideA, outsideE⟩
      · change codeSentence C.arithmetic 0 φ (C.family.unaryColumnIndex 0 φ) =
          CommonCoreProgram.particularSentence 0 φ.input
            (compiledUnaryColumnCode source 0 (φ.body.code id) φ.input) φ.body
        rw [CommonCoreProgram.particularSentence_unary, hcolumn, hArithmetic]
    | subordinate_code i j φ below active outsideA outsideE =>
      refine ⟨2, (((j, φ.input), 0), φ.body), ?_, ?_, rfl⟩
      · refine ⟨?_, ?_⟩
        · simp only [CommonCoreProgram.sideCondition, show (2 : Nat) ≠ 0 by decide,
            show (2 : Nat) ≠ 1 by decide, if_false, Nat.add_sub_cancel]
          exact ⟨by omega, φ.freeVars_exact, (hedge j i).mpr below⟩
        · apply (policy_iff A E 2 (i + 1) _).mpr
          exact ⟨active, outsideA, outsideE⟩
      · change codeSentence C.arithmetic (j + 1) φ (C.family.unaryColumnIndex (j + 1) φ) =
          CommonCoreProgram.particularSentence (j + 1) φ.input
            (compiledUnaryColumnCode source (j + 1) (φ.body.code id) φ.input) φ.body
        rw [CommonCoreProgram.particularSentence_unary, hcolumn, hArithmetic]

end Alexander313.RecordedMainSourceProgram
