import Alexander313.RecordedReconstruction
import Alexander313.Alexander.ModelTransport
import Alexander313.ProofClosure

/-!
# Both logical-certificate maps for recorded syntax

Erasure is an ordinary owner map. Recording is shape-sensitive: its owner
at a knowledge head depends on the source argument skeleton. Pulling back
an arbitrary Alexander structure along that map proves validity preservation
in the correct direction, including merged-variable substitutions. No rule
inferring a recorded validity from its erased validity is introduced.
-/

namespace Alexander313

namespace AlphaFormula

variable {Owner Label : Type}

def record (head : Owner → Shape Owner → RecordedHead Owner Label) :
    AlphaFormula Owner → AlphaFormula (RecordedHead Owner Label)
  | .falsum => .falsum
  | .equal t u => .equal t u
  | .imp φ ψ => .imp (φ.record head) (ψ.record head)
  | .conj φ ψ => .conj (φ.record head) (ψ.record head)
  | .disj φ ψ => .disj (φ.record head) (ψ.record head)
  | .neg φ => .neg (φ.record head)
  | .all φ => .all (φ.record head)
  | .ex φ => .ex (φ.record head)
  | .know a φ => .know (head a φ.shape) (φ.record head)

end AlphaFormula

namespace Formula

variable {Owner Label : Type}

@[simp] theorem alpha_record (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (bound : List Nat) :
    (φ.record head).alpha bound = (φ.alpha bound).record head := by
  induction φ generalizing bound <;>
    simp_all [record, alpha, AlphaFormula.record]

theorem AlphaEquivalent.record {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (φ.record head).AlphaEquivalent (ψ.record head) := by
  unfold AlphaEquivalent at h ⊢
  simpa only [alpha_record] using congrArg (AlphaFormula.record head) h

@[simp] theorem record_substTerm (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (x : Nat) (t : Term) :
    (φ.substTerm x t).record head = (φ.record head).substTerm x t := by
  induction φ with
  | all y φ ih =>
    by_cases h : y = x <;> simp_all [record, substTerm]
  | ex y φ ih =>
    by_cases h : y = x <;> simp_all [record, substTerm]
  | _ => simp_all [record, substTerm]

@[simp] theorem record_substVar (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (x y : Nat) :
    (φ.substVar x y).record head = (φ.record head).substVar x y := by
  simp only [substVar, record_substTerm]

@[simp] theorem varSubstitutable_record (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (x y : Nat) :
    (φ.record head).VarSubstitutable x y ↔ φ.VarSubstitutable x y := by
  induction φ <;> simp_all [record, VarSubstitutable]

@[simp] theorem record_chain (Γ : List (Formula Owner)) (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (chain Γ φ).record head = chain (Γ.map (record head)) (φ.record head) := by
  induction Γ with
  | nil => rfl
  | cons θ Γ ih => simp only [chain, record, List.map_cons, ih]

end Formula

namespace ModalModel

variable {Owner Label D : Type}

def recordPullback (M : ModalModel (RecordedHead Owner Label) D)
    (head : Owner → Shape Owner → RecordedHead Owner Label) : ModalModel Owner D where
  zero := M.zero
  succ := M.succ
  add := M.add
  mul := M.mul
  modal := fun a φ s => M.modal (head a φ.shape) (φ.record head) s
  free_independence := by
    intro a φ s t h
    apply M.free_independence
    simpa only [Formula.freeVars_record] using h
  alphabetic := by
    intro a φ ψ s h
    change M.modal (head a φ.shape) (φ.record head) s ↔
      M.modal (head a ψ.shape) (ψ.record head) s
    rw [h.shape_eq]
    exact M.alphabetic _ _ _ s (h.record head)
  weak_substitution := by
    intro a φ x y s h
    simpa only [Formula.shape_substVar, Formula.record_substVar] using
      M.weak_substitution (head a φ.shape) (φ.record head) x y s
        ((Formula.varSubstitutable_record φ head x y).mpr h)

end ModalModel

theorem generalTermEval_recordPullback {Owner Label D : Type}
    (M : ModalModel (RecordedHead Owner Label) D)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (s : Nat → D) (t : Term) :
    generalTermEval (M.recordPullback head) s t = generalTermEval M s t := by
  induction t <;> simp_all [generalTermEval, ModalModel.recordPullback]

theorem generalTruth_recordPullback {Owner Label D : Type}
    (M : ModalModel (RecordedHead Owner Label) D)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (φ : Formula Owner) (s : Nat → D) :
    generalTruth (M.recordPullback head) φ s ↔ generalTruth M (φ.record head) s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => simp only [generalTruth, Formula.record, generalTermEval_recordPullback]
  | imp φ ψ ihφ ihψ => simp only [generalTruth, Formula.record, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [generalTruth, Formula.record, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [generalTruth, Formula.record, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih s)
  | all x φ ih => exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih (Function.update s x n)
  | know a φ _ => rfl

theorem Valid.record {Owner Label : Type} {φ : Formula Owner} (h : Valid φ)
    (head : Owner → Shape Owner → RecordedHead Owner Label) : Valid (φ.record head) := by
  intro D hD M s
  exact (generalTruth_recordPullback M head φ s).mp
    (h D hD (M.recordPullback head) s)

def Certificate.record {Owner Label : Type} {axioms : Formula Owner → Prop}
    {target : Formula (RecordedHead Owner Label) → Prop} {φ : Formula Owner}
    (c : Certificate axioms φ)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (admission : ∀ θ, axioms θ → target (θ.record head)) :
    Certificate target (φ.record head) where
  premises := c.premises.map (Formula.record head)
  admitted := by
    intro θ hθ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hθ
    exact admission η (c.admitted η hη)
  validity := by
    simpa only [Formula.record_chain] using c.validity.record head

theorem Provable.record {Owner Label : Type} {axioms : Formula Owner → Prop}
    {target : Formula (RecordedHead Owner Label) → Prop} {φ : Formula Owner}
    (h : Provable axioms φ)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (admission : ∀ θ, axioms θ → target (θ.record head)) :
    Provable target (φ.record head) := by
  obtain ⟨c⟩ := h
  exact ⟨c.record head admission⟩

theorem Valid.erase {Owner Label : Type} {φ : Formula (RecordedHead Owner Label)}
    (h : Valid φ) : Valid φ.erase := h.mapOwner RecordedHead.erase

/-- Consequences of source consequences may be combined without postulating
    source membership of each translated generator as an axiom. -/
theorem Provable.chain_elim {Owner : Type} {axioms : Formula Owner → Prop}
    (Γ : List (Formula Owner)) (φ : Formula Owner)
    (premises : ∀ θ ∈ Γ, Provable axioms θ)
    (h : Provable axioms (Formula.chain Γ φ)) : Provable axioms φ := by
  induction Γ with
  | nil => exact h
  | cons θ Γ ih =>
    apply ih (fun η hm => premises η (List.mem_cons_of_mem _ hm))
    exact h.modus_ponens (premises θ List.mem_cons_self)

theorem Certificate.consequences {Owner : Type} {axioms target : Formula Owner → Prop}
    {φ : Formula Owner} (c : Certificate axioms φ)
    (premises : ∀ θ, axioms θ → Provable target θ) : Provable target φ :=
  Provable.chain_elim c.premises φ
    (fun θ hm => premises θ (c.admitted θ hm)) (Provable.of_valid c.validity)

/-- Note 24 (2). Each auxiliary premise erases to a source theorem, including
    generated and derived prefixes; no intersection with an original predicate
    and no converse-to-erasure validity test occurs. -/
theorem Provable.erasure_consequences {Owner Label : Type}
    {auxiliary : Formula (RecordedHead Owner Label) → Prop}
    {source : Formula Owner → Prop} {φ : Formula (RecordedHead Owner Label)}
    (h : Provable auxiliary φ)
    (generators : ∀ θ, auxiliary θ → Provable source θ.erase) :
    Provable source φ.erase := by
  obtain ⟨c⟩ := h
  apply Provable.chain_elim (c.premises.map Formula.erase) φ.erase
  · intro θ hθ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hθ
    exact generators η (c.admitted η hη)
  · apply Provable.of_valid
    simpa only [Formula.erase, Formula.mapOwner_chain] using c.validity.erase

def FilteredRealization.reconstruct {Owner Label : Type}
    {P : RawPredicates (RecordedHead Owner Label)} (M : FilteredRealization P)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    FilteredRealization (reconstructedPredicates head P) where
  model := M.model.recordPullback head
  zero_correct := M.zero_correct
  succ_correct := M.succ_correct
  add_correct := M.add_correct
  mul_correct := M.mul_correct
  modal_correct := fun a φ s =>
    (M.modal_correct (head a φ.shape) (φ.record head) s).trans
      (truth_reconstructed true head P (.know a φ) s).symm

end Alexander313
