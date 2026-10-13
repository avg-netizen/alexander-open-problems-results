import Alexander313.Effective.RecordedOrderedFormation
import Alexander313.Effective.RecordedPositiveImages
import Alexander313.RecordedPrefixClosure

/-!
# Positive own-prefix compilation with an executing label-order Program

The actual output nesting uses the supplied order Program's domain, rather
than the numerical order of label codes. Every required nesting edge has a
positive bounded computation. This constructs the prefix transformer; no
Wilken ordinal domain, order procedure or semantic exactness is assumed.
-/

noncomputable section

namespace Alexander313.OrderedRecordedPrefixProgram

open RecordedFormula

abbrev Parameters := Program × RecordedPrefixProgram.Parameters
abbrev Witness := RecordedPrefixProgram.Witness
abbrev Certificate := Witness × (Nat × Nat)

def formula (a : Nat) (w : Witness) : Syntax := RecordedPrefixProgram.formula a w

theorem formula_primrec : Primrec₂ formula := RecordedPrefixProgram.formula_primrec

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  w.2.Closed ∧
    (letI : LT Nat := Program.orderLT p.1
     (formula a w).RecordedAdmissible p.2.1.1.toFinset p.2.1.2.toFinset) ∧
    p.2.2.domain (Nat.pair a (w.2.code RecordedHead.code))

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w, side p a w ∧ σ = formula a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, hs, rfl⟩ := h
  exact prefix_closed a w.1 w.2 hs.1

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) :
    letI : LT Nat := Program.orderLT p.1
    σ.RecordedAdmissible p.2.1.1.toFinset p.2.1.2.toFinset := by
  obtain ⟨w, hs, rfl⟩ := h
  exact hs.2.1

theorem closure_exact (p : Parameters) (base : Nat → Syntax → Prop)
    (exactBase : ∀ a φ, p.2.2.domain (Nat.pair a (φ.code RecordedHead.code)) ↔ base a φ)
    (closedBase : ∀ a φ, base a φ → φ.Closed)
    (admissibleBase : letI : LT Nat := Program.orderLT p.1
      ∀ a φ, base a φ → φ.RecordedAdmissible p.2.1.1.toFinset p.2.1.2.toFinset)
    (a : Nat) (σ : Syntax) :
    letI : LT Nat := Program.orderLT p.1
    admits p a σ ↔ RecordedPrefixClosure p.2.1.1.toFinset a (base a) σ := by
  letI : LT Nat := Program.orderLT p.1
  constructor
  · rintro ⟨w, hs, rfl⟩
    exact RecordedPrefixClosure.of_list p.2.1.2.toFinset w.1 w.2
      ((exactBase a w.2).mp hs.2.2) hs.2.1
  · intro h
    obtain ⟨θ, L, ht, rfl, hadm⟩ := h.exists_list p.2.1.2.toFinset (admissibleBase a)
    exact ⟨(L, θ), ⟨closedBase a θ ht, hadm, (exactBase a θ).mpr ht⟩, rfl⟩

def condition (p : Parameters) (a : Nat) (c : Certificate) : Bool :=
  Formula.isClosedCode (c.1.2.code RecordedHead.code) &&
    (OrderedRecordedAdmissionProgram.condition p.1 p.2.1 (formula a c.1) c.2.2 &&
      RecordedBackgroundProgram.positive c.2.1 p.2.2 (Nat.pair a (c.1.2.code RecordedHead.code)))

theorem condition_primrec : Primrec (fun q : (Parameters × Nat) × Certificate =>
    condition q.1.1 q.1.2 q.2) := by
  have hp : Primrec (fun q : (Parameters × Nat) × Certificate => q.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun q : (Parameters × Nat) × Certificate => q.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun q : (Parameters × Nat) × Certificate => q.2.1) := Primrec.fst.comp Primrec.snd
  have hks : Primrec (fun q : (Parameters × Nat) × Certificate => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hka : Primrec (fun q : (Parameters × Nat) × Certificate => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hb := code_primrec.comp (Primrec.snd.comp hw)
  have horder := Primrec.fst.comp hp
  have hAE := Primrec.fst.comp (Primrec.snd.comp hp)
  have hsource := Primrec.snd.comp (Primrec.snd.comp hp)
  have hformula := formula_primrec.comp ha hw
  have result := Primrec.and.comp (Formula.isClosedCode_primrec.comp hb)
    (Primrec.and.comp
      (OrderedRecordedAdmissionProgram.condition_primrec.comp
        (((horder.pair hAE).pair hformula).pair hka))
      (RecordedBackgroundProgram.positive_primrec.comp
        ((hks.pair hsource).pair (Primrec₂.natPair.comp ha hb))))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ sourceCutoff admissionCutoff, condition p a (w, (sourceCutoff, admissionCutoff)) = true) ↔
      side p a w := by
  constructor
  · rintro ⟨ks, ka, h⟩
    have hc := Bool.and_eq_true_iff.mp h
    have hs := Bool.and_eq_true_iff.mp hc.2
    exact ⟨(RecordedPrefixProgram.recorded_closed_code w.2).mp hc.1,
      (OrderedRecordedAdmissionProgram.condition_correct p.1 p.2.1 (formula a w)).mp ⟨ka, hs.1⟩,
      (RecordedBackgroundProgram.positive_iff _ _).mp ⟨ks, hs.2⟩⟩
  · rintro ⟨hb, ha, hs⟩
    obtain ⟨ks, hks⟩ := (RecordedBackgroundProgram.positive_iff _ _).mpr hs
    obtain ⟨ka, hka⟩ :=
      (OrderedRecordedAdmissionProgram.condition_correct p.1 p.2.1 (formula a w)).mpr ha
    refine ⟨ks, ka, ?_⟩
    simp only [condition, Bool.and_eq_true]
    exact ⟨(RecordedPrefixProgram.recorded_closed_code w.2).mpr hb, hka, hks⟩

def formatter (_p : Parameters) (a : Nat) (c : Certificate) : Syntax := formula a c.1

theorem formatter_primrec : Primrec (fun p : (Parameters × Nat) × Certificate =>
    formatter p.1.1 p.1.2 p.2) :=
  formula_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)

theorem image_exact (p : Parameters) (a : Nat) (σ : Syntax) :
    RecordedPositiveImage.image formatter condition p a σ ↔ admits p a σ := by
  constructor
  · rintro ⟨⟨w, ks, ka⟩, hc, he⟩
    exact ⟨w, (condition_correct p a w).mp ⟨ks, ka, hc⟩, he⟩
  · rintro ⟨w, hs, he⟩
    obtain ⟨ks, ka, hc⟩ := (condition_correct p a w).mpr hs
    exact ⟨(w, (ks, ka)), hc, he⟩

def defaultParameters : Parameters :=
  (Nat.Partrec.Code.zero, (([], []), Nat.Partrec.Code.zero))
def defaultCertificate : Certificate := (([], .falsum), (0, 0))

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        (letI : LT Nat := Program.orderLT p.1
         σ.RecordedAdmissible p.2.1.1.toFinset p.2.1.2.toFinset)) := by
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

end Alexander313.OrderedRecordedPrefixProgram
