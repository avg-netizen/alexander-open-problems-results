import Alexander313.RecordedErasure
import Alexander313.FreeVariables

/-!
# Reconstruction from one source-shared recorded head table

The table selects a head from the owner and the entire argument skeleton.
It therefore selects the same head for every term variant and numerical
instance of that skeleton. The truth lemma is for arbitrary raw predicates;
it uses neither stage soundness nor source soundness. Full retained predicates
and empty ghost classes are then proved from the actual reconstruction formula.

The final soundness lemma isolates the two later applications: sound indexed
cuts, and full query agreement under retained live arguments. Establishing
the latter from guarded transport remains a separate proof obligation.
-/

namespace Alexander313

namespace Formula

variable {Owner Label : Type}

@[simp] theorem freeVars_record (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (φ.record head).freeVars = φ.freeVars := by
  induction φ <;> simp_all [record, freeVars]

@[simp] theorem closed_record (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (φ.record head).Closed ↔ φ.Closed := by
  simp only [Closed, freeVars_record]

end Formula

/-- Keep an entire argument class, rather than a finite list of its instances. -/
def reconstructedPredicates {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates (RecordedHead Owner Label)) : RawPredicates Owner :=
  fun a θ => P (head a θ.shape) (θ.record head)

@[simp] theorem reconstructed_query {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates (RecordedHead Owner Label))
    (a : Owner) (φ : Formula Owner) (s : Assignment) :
    reconstructedPredicates head P a (φ.close s) ↔
      P (head a φ.shape) ((φ.record head).close s) := by
  simp only [reconstructedPredicates, Formula.shape_close, Formula.record_close]

/-- Note 24 (6), including quantifiers, all numeral instances and all term
    variants. No soundness premise is used in this reconstruction step. -/
theorem truth_reconstructed {Owner Label : Type}
    (filtered : Bool)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates (RecordedHead Owner Label))
    (φ : Formula Owner) (s : Assignment) :
    truth filtered (reconstructedPredicates head P) φ s ↔
      truth filtered P (φ.record head) s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => simp only [truth, Formula.record, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [truth, Formula.record, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [truth, Formula.record, ihφ, ihψ]
  | neg φ ih => simp only [truth, Formula.record, ih]
  | all x φ ih =>
    exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih =>
    exact exists_congr fun n => ih (Function.update s x n)
  | know a φ ih =>
    cases filtered <;>
      simp only [truth, Formula.record, reconstructed_query,
        Bool.false_eq_true, ↓reduceIte, ih]

theorem reconstructed_sentences {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates (RecordedHead Owner Label))
    (sentences : ∀ a θ, P a θ → θ.Closed)
    (a : Owner) (θ : Formula Owner)
    (hθ : reconstructedPredicates head P a θ) : θ.Closed := by
  exact (Formula.closed_record θ head).mp (sentences _ _ hθ)

theorem reconstructed_sound {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates (RecordedHead Owner Label)) (a : Owner)
    (sound : ∀ sh, RawSound P (head a sh)) :
    RawSound (reconstructedPredicates head P) a := by
  intro φ s hp
  have hraw := (reconstructed_query head P a φ s).mp hp
  have ht := sound φ.shape (φ.record head) s hraw
  exact (truth_reconstructed true head P φ s).mpr ht

theorem reconstructed_live {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (hhead : ∀ a sh, (head a sh).erase = a)
    (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a : Owner) (θ : Formula Owner) (hlive : head a θ.shape = .live a) :
    reconstructedPredicates head (sourceQueries P cuts) a θ ↔ P a θ := by
  simp only [reconstructedPredicates, hlive, sourceQueries,
    Formula.erase_record θ head hhead]

theorem reconstructed_full_predicate {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (hhead : ∀ a sh, (head a sh).erase = a)
    (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a : Owner) (hlive : ∀ sh, head a sh = .live a) (θ : Formula Owner) :
    reconstructedPredicates head (sourceQueries P cuts) a θ ↔ P a θ :=
  reconstructed_live head hhead P cuts a θ (hlive θ.shape)

theorem reconstructed_indexed {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a : Owner) (ν : Label) (θ : Formula Owner)
    (hindexed : head a θ.shape = .indexed a ν) :
    reconstructedPredicates head (sourceQueries P cuts) a θ ↔
      cuts a ν (θ.record head) := by
  simp only [reconstructedPredicates, hindexed, sourceQueries]

theorem reconstructed_ghost {Owner Label : Type}
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a b : Owner) (θ : Formula Owner)
    (hghost : head a θ.shape = .ghost b) :
    ¬ reconstructedPredicates head (sourceQueries P cuts) a θ := by
  simp only [reconstructedPredicates, hghost, sourceQueries, not_false_eq_true]

/-- Soundness in note 24 §7: indexed acceptances use stage soundness;
    live acceptances use agreement on every nested raw query class. The
    query-agreement hypothesis covers all term variants and assignments. -/
theorem reconstructed_source_sound {Owner Label : Type} [DecidableEq Owner]
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (hhead : ∀ a sh, (head a sh).erase = a)
    (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a : Owner) (old_sound : RawSound P a)
    (cuts_sound : ∀ ν, RawSound (sourceQueries P cuts) (.indexed a ν))
    (live_agreement : ∀ φ : Formula Owner, head a φ.shape = .live a →
      AgreeOn (reconstructedPredicates head (sourceQueries P cuts)) P φ) :
    RawSound (reconstructedPredicates head (sourceQueries P cuts)) a := by
  intro φ s hp
  cases hh : head a φ.shape with
  | live b =>
    have hba : b = a := by
      simpa only [hh, RecordedHead.erase] using hhead a φ.shape
    subst b
    have hlive : head a (φ.close s).shape = .live a := by
      simpa only [Formula.shape_close] using hh
    have hold := (reconstructed_live head hhead P cuts a (φ.close s) hlive).mp hp
    exact (truth_congr_queries true _ P φ s (live_agreement φ hh)).mpr
      (old_sound φ s hold)
  | indexed b ν =>
    have hba : b = a := by
      simpa only [hh, RecordedHead.erase] using hhead a φ.shape
    subst b
    have hraw : sourceQueries P cuts (.indexed a ν) ((φ.record head).close s) := by
      simpa only [reconstructedPredicates, Formula.shape_close,
        Formula.record_close, hh, sourceQueries] using hp
    exact (truth_reconstructed true head (sourceQueries P cuts) φ s).mpr
      (cuts_sound ν (φ.record head) s hraw)
  | ghost b =>
    have hghost : head a (φ.close s).shape = .ghost b := by
      simpa only [Formula.shape_close] using hh
    exact False.elim (reconstructed_ghost head P cuts a b (φ.close s) hghost hp)

end Alexander313
