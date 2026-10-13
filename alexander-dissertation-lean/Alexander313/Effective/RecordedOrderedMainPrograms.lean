import Alexander313.Effective.RecordedMainPrograms
import Alexander313.Effective.RecordedOrderedFormation
import Alexander313.Effective.RecordedOrderedGuardPrograms
import Alexander313.Effective.RecordedPositiveImages

/-!
# Actual guarded-main compilation with a supplied executing label order

All source-shared finite recording, hereditary mask, fresh marker and source
formation algorithms are reused literally. The two order-sensitive checks,
whole output admissibility and full main guards, use the order Program's
positive domain. No numerical ordering of label codes is substituted for it.
The actual Wilken public domain/order/relation algorithms remain separate.
-/

noncomputable section

namespace Alexander313.OrderedRecordedMainProgram

open RecordedFormula

abbrev Parameters := RecordedMainProgram.Parameters × Program
abbrev Witness := RecordedMainProgram.Witness
abbrev Certificate := Witness × ((Nat × Nat) × OrderedRecordedGuardProgram.Witness)

def formula (p : Parameters) (a : Nat) (w : Witness) : Syntax :=
  RecordedMainProgram.formula p.1 a w

theorem formula_primrec : Primrec (fun p : (Parameters × Nat) × Witness =>
    formula p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × Witness => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : (Parameters × Nat) × Witness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have result := RecordedMainProgram.formula_primrec.comp ((hp.pair ha).pair Primrec.snd)
  exact result.of_eq (fun _ => rfl)

def guardData (p : Parameters) (w : Witness) : OrderedRecordedGuardProgram.Parameters :=
  let g := RecordedMainProgram.guardData p.1 w
  (g.1, (p.2, g.2))

theorem guardData_primrec : Primrec₂ guardData := by
  have hg : Primrec (fun p : Parameters × Witness => RecordedMainProgram.guardData p.1.1 p.2) :=
    RecordedMainProgram.guardData_primrec.comp
    (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact ((Primrec.fst.comp hg).pair
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp hg))).to₂

def requirements (p : Parameters) (w : Witness) : GuardRequirements Nat :=
  RecordedMainProgram.requirements p.1 w

theorem requirements_primrec : Primrec₂ requirements :=
  (RecordedMainProgram.requirements_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

def structural (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  HereditaryQueries (RecordedTable.mask w.2.1.1) ∧
    Disjoint p.1.1.1.toFinset p.1.1.2.toFinset ∧ (w.2.2.map Prod.snd).Nodup ∧
    (∀ q ∈ w.2.2, (markerTag Nat q.2).shape ∉ (RecordedMainProgram.sourceFormula p.1 w).shape.subshapes) ∧
    (letI : LT Nat := Program.orderLT p.2
     (formula p a w).RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset)

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  RecordedMainSourceProgram.sideCondition p.1.2.1.2 p.1.1.1 p.1.1.2 w.1.1 a w.1.2 ∧
    structural p a w ∧
    (letI : LT Nat := Program.orderLT p.2
     (RecordedMainProgram.guardedAtom p.1 w).MainGuarded
       (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
       (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) p.1.1.2.toFinset (markerPoints w.2.2))

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w, side p a w ∧ σ = formula p a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, hs, rfl⟩ := h
  have hc : (RecordedMainProgram.sourceFormula p.1 w).Closed :=
    RecordedMainSourceProgram.admits_closed ⟨w.1.1, w.1.2, hs.1, rfl, rfl⟩
  exact markerPadding_closed a w.2.2 _ ((Formula.closed_record _ _).mpr hc)

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) :
    letI : LT Nat := Program.orderLT p.2
    σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset := by
  obtain ⟨w, hs, rfl⟩ := h
  exact hs.2.1.2.2.2.2

def finiteCheck (p : Parameters) (w : Witness) : Bool :=
  RecordedTable.hereditaryCheck w.2.1.1 &&
    (RecordedMainProgram.disjointCheck p.1.1 &&
      (RecordedMarkerProgram.markerDistinctCheck w.2.2 &&
        RecordedMarkerProgram.markerFreshCheck (RecordedMainProgram.sourceFormula p.1 w) w.2.2))

theorem finiteCheck_primrec : Primrec₂ finiteCheck := by
  have hp : Primrec (fun p : Parameters × Witness => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : Parameters × Witness => p.2) := Primrec.snd
  have hM := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hw))
  have hms := Primrec.snd.comp (Primrec.snd.comp hw)
  exact (Primrec.and.comp (RecordedTable.hereditaryCheck_primrec.comp hM)
    (Primrec.and.comp (RecordedMainProgram.disjointCheck_primrec.comp (Primrec.fst.comp hp))
      (Primrec.and.comp (RecordedMarkerProgram.markerDistinctCheck_primrec.comp hms)
        (RecordedMarkerProgram.markerFreshCheck_primrec.comp
          (RecordedMainProgram.sourceFormula_primrec.comp hp hw) hms)))).to₂

def structuralCheck (p : Parameters) (a : Nat) (w : Witness) (cutoff : Nat) : Bool :=
  finiteCheck p w && OrderedRecordedAdmissionProgram.condition p.2 p.1.1 (formula p a w) cutoff

theorem structuralCheck_primrec : Primrec (fun p : ((Parameters × Nat) × Witness) × Nat =>
    structuralCheck p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hp : Primrec (fun p : ((Parameters × Nat) × Witness) × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : ((Parameters × Nat) × Witness) × Nat => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hw : Primrec (fun p : ((Parameters × Nat) × Witness) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have horder := Primrec.snd.comp hp
  have hAE := Primrec.fst.comp (Primrec.fst.comp hp)
  have hformula := formula_primrec.comp ((hp.pair ha).pair hw)
  have result := Primrec.and.comp (finiteCheck_primrec.comp hp hw)
    (OrderedRecordedAdmissionProgram.condition_primrec.comp
      (((horder.pair hAE).pair hformula).pair Primrec.snd))
  exact result.of_eq (fun _ => rfl)

theorem structuralCheck_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ cutoff, structuralCheck p a w cutoff = true) ↔ structural p a w := by
  simp only [structuralCheck, Bool.and_eq_true, exists_and_left,
    OrderedRecordedAdmissionProgram.condition_correct, finiteCheck,
    RecordedTable.hereditaryCheck_exact, RecordedMainProgram.disjointCheck_exact,
    RecordedMarkerProgram.markerDistinctCheck_iff, RecordedMarkerProgram.markerFreshCheck_iff,
    structural]
  tauto

theorem guard_condition_exact (p : Parameters) (w : Witness) :
    (∃ g, OrderedRecordedGuardProgram.condition (guardData p w) (requirements p w) g = true) ↔
      (letI : LT Nat := Program.orderLT p.2
       (RecordedMainProgram.guardedAtom p.1 w).MainGuarded
         (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) p.1.1.2.toFinset (markerPoints w.2.2)) := by
  rw [OrderedRecordedGuardProgram.condition_correct]
  simpa only [guardData, RecordedMainProgram.guardData, requirements,
    RecordedMainProgram.requirements, markerPoints] using
      OrderedRecordedGuardProgram.mainRequirementsCode_exact (guardData p w)
        (RecordedMainProgram.guardedAtom p.1 w)

def condition (p : Parameters) (a : Nat) (c : Certificate) : Bool :=
  let w := c.1
  RecordedMainSourceProgram.condition p.1.2.1.2 p.1.1.1 p.1.1.2 w.1.1 a w.1.2 c.2.1.1 &&
    (structuralCheck p a w c.2.1.2 &&
      OrderedRecordedGuardProgram.condition (guardData p w) (requirements p w) c.2.2)

theorem condition_primrec : Primrec (fun q : (Parameters × Nat) × Certificate =>
    condition q.1.1 q.1.2 q.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × Certificate => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × Certificate => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × Certificate => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcutoffs : Primrec (fun p : (Parameters × Nat) × Certificate => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsourceCutoff := Primrec.fst.comp hcutoffs
  have hadmissionCutoff := Primrec.snd.comp hcutoffs
  have hg : Primrec (fun p : (Parameters × Nat) × Certificate => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsourceData := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hp))
  have hedge := Primrec.snd.comp hsourceData
  have hAE := Primrec.fst.comp (Primrec.fst.comp hp)
  have htag := Primrec.fst.comp (Primrec.fst.comp hw)
  have hrow := Primrec.snd.comp (Primrec.fst.comp hw)
  have hsource := RecordedMainSourceProgram.condition_primrec.comp
    ((((hedge.pair hAE).pair htag).pair ha).pair (hrow.pair hsourceCutoff))
  have result := Primrec.and.comp hsource
    (Primrec.and.comp (structuralCheck_primrec.comp (((hp.pair ha).pair hw).pair hadmissionCutoff))
      (OrderedRecordedGuardProgram.condition_primrec.comp
        (((guardData_primrec.comp hp hw).pair (requirements_primrec.comp hp hw)).pair hg)))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ ks ka g, condition p a (w, ((ks, ka), g)) = true) ↔ side p a w := by
  constructor
  · rintro ⟨ks, ka, g, h⟩
    have hs := (Bool.and_eq_true_iff.mp h).1
    have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have hg := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    exact ⟨(RecordedMainSourceProgram.condition_correct _ _ _ _ _ _).mp ⟨ks, hs⟩,
      (structuralCheck_correct _ _ _).mp ⟨ka, ht⟩, (guard_condition_exact _ _).mp ⟨g, hg⟩⟩
  · rintro ⟨hs, ht, hg⟩
    obtain ⟨ks, hks⟩ := (RecordedMainSourceProgram.condition_correct _ _ _ _ _ _).mpr hs
    obtain ⟨ka, hka⟩ := (structuralCheck_correct _ _ _).mpr ht
    obtain ⟨g, hgc⟩ := (guard_condition_exact _ _).mpr hg
    exact ⟨ks, ka, g, by simp only [condition, hks, hka, hgc, Bool.true_and]⟩

def formatter (p : Parameters) (a : Nat) (c : Certificate) : Syntax := formula p a c.1

theorem formatter_primrec : Primrec (fun q : (Parameters × Nat) × Certificate =>
    formatter q.1.1 q.1.2 q.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × Certificate => p.1) := Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × Certificate => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have result := formula_primrec.comp (hp.pair hw)
  exact result.of_eq (fun _ => rfl)

theorem image_exact (p : Parameters) (a : Nat) (σ : Syntax) :
    RecordedPositiveImage.image formatter condition p a σ ↔ admits p a σ := by
  constructor
  · rintro ⟨⟨w, ⟨ks, ka⟩, g⟩, hc, he⟩
    exact ⟨w, (condition_correct p a w).mp ⟨ks, ka, g, hc⟩, he⟩
  · rintro ⟨w, hs, he⟩
    obtain ⟨ks, ka, g, hc⟩ := (condition_correct p a w).mpr hs
    exact ⟨(w, ((ks, ka), g)), hc, he⟩

def defaultParameters : Parameters := (RecordedMainProgram.defaultParameters, Nat.Partrec.Code.zero)
def defaultCertificate : Certificate := (RecordedMainProgram.defaultWitness, ((0, 0), ([], [])))

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        (letI : LT Nat := Program.orderLT p.2
         σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset)) := by
  obtain ⟨compiler, hcompiler, exactCompiler, rawCompiler⟩ :=
    RecordedPositiveImage.compiler_exists defaultParameters defaultCertificate
      formatter condition formatter_primrec condition_primrec
  refine ⟨compiler, hcompiler, ?_, ?_⟩
  · intro p a σ
    exact (exactCompiler p a σ).trans (image_exact p a σ)
  · intro p query h
    obtain ⟨a, σ, he, hs⟩ := rawCompiler p query h
    have ha := (image_exact p a σ).mp hs
    exact ⟨a, σ, he, admits_closed ha, admits_admissible ha⟩

theorem admits_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i) (a : Nat) (σ : Syntax) :
    letI : LT Nat := Program.orderLT p.2
    admits p a σ ↔ RecordedMain C p.1.1.1.toFinset p.1.1.2.toFinset a
      (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) σ := by
  letI : LT Nat := Program.orderLT p.2
  rw [← RecordedFiniteMain_exact 0 C p.1.1.1.toFinset p.1.1.2.toFinset a]
  constructor
  · rintro ⟨w, hs, rfl⟩
    obtain ⟨hm, hd, hn, hf, ha⟩ := hs.2.1
    have hrow := (RecordedMainSourceProgram.admits_exact C p.1.2.1.1 p.1.2.1.2
      hArithmetic hsource hhierarchy p.1.1.1 p.1.1.2 a
      (RecordedMainProgram.sourceFormula p.1 w) (RecordedMainProgram.sourceAtom w)).mp
        ⟨w.1.1, w.1.2, hs.1, rfl, rfl⟩
    exact ⟨RecordedMainProgram.sourceFormula p.1 w, RecordedMainProgram.sourceAtom w,
      w.2.1.1, w.2.1.2, w.2.2, hrow, hm, hd, hn, hf, hs.2.2, rfl, ha⟩
  · rintro ⟨source, atom, M, T, ms, hrow, hm, hd, hn, hf, hg, he, ha⟩
    obtain ⟨tag, row, hs, hσ, hatom⟩ :=
      (RecordedMainSourceProgram.admits_exact C p.1.2.1.1 p.1.2.1.2 hArithmetic hsource
        hhierarchy p.1.1.1 p.1.1.2 a source atom).mpr hrow
    subst source
    subst atom
    rw [he] at ha
    let w : Witness := ((tag, row), ((M, T), ms))
    exact ⟨w, ⟨hs, ⟨hm, hd, hn, hf, ha⟩, hg⟩, he⟩

end Alexander313.OrderedRecordedMainProgram
