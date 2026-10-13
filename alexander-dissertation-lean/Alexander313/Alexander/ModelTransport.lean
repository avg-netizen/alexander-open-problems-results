import Alexander313.Alexander.FilteredModel

/-!
# Transport of Alexander structures along maps of modal owners

The map need not be injective. This gives the admissible pullback needed
for recorded erasure and for first-order reducts. Source: Alexander
Definitions 1.2.3--1.2.5 and the reduct arguments in Chapters 2--3.
-/

namespace Alexander313

namespace AlphaFormula

variable {Owner Other : Type}

def mapOwner (f : Owner → Other) : AlphaFormula Owner → AlphaFormula Other
  | .falsum => .falsum
  | .equal t u => .equal t u
  | .imp φ ψ => .imp (φ.mapOwner f) (ψ.mapOwner f)
  | .conj φ ψ => .conj (φ.mapOwner f) (ψ.mapOwner f)
  | .disj φ ψ => .disj (φ.mapOwner f) (ψ.mapOwner f)
  | .neg φ => .neg (φ.mapOwner f)
  | .all φ => .all (φ.mapOwner f)
  | .ex φ => .ex (φ.mapOwner f)
  | .know a φ => .know (f a) (φ.mapOwner f)

def shape : AlphaFormula Owner → Shape Owner
  | .falsum => .falsum
  | .equal _ _ => .equal
  | .imp φ ψ => .imp φ.shape ψ.shape
  | .conj φ ψ => .conj φ.shape ψ.shape
  | .disj φ ψ => .disj φ.shape ψ.shape
  | .neg φ => .neg φ.shape
  | .all φ => .all φ.shape
  | .ex φ => .ex φ.shape
  | .know a φ => .know a φ.shape

end AlphaFormula

namespace Formula

variable {Owner Other : Type}

@[simp] theorem freeVars_mapOwner (φ : Formula Owner) (f : Owner → Other) :
    (φ.mapOwner f).freeVars = φ.freeVars := by
  induction φ <;> simp_all [mapOwner, freeVars]

@[simp] theorem mapOwner_substTerm (φ : Formula Owner) (f : Owner → Other)
    (x : Nat) (t : Term) :
    (φ.substTerm x t).mapOwner f = (φ.mapOwner f).substTerm x t := by
  induction φ <;> simp_all [substTerm, mapOwner]
  all_goals split_ifs <;> simp_all [mapOwner]

@[simp] theorem mapOwner_substVar (φ : Formula Owner) (f : Owner → Other)
    (x y : Nat) :
    (φ.substVar x y).mapOwner f = (φ.mapOwner f).substVar x y := by
  simp only [substVar, mapOwner_substTerm]

@[simp] theorem varSubstitutable_mapOwner (φ : Formula Owner) (f : Owner → Other)
    (x y : Nat) :
    (φ.mapOwner f).VarSubstitutable x y ↔ φ.VarSubstitutable x y := by
  induction φ <;> simp_all [mapOwner, VarSubstitutable]

@[simp] theorem alpha_mapOwner (φ : Formula Owner) (f : Owner → Other)
    (bound : List Nat) :
    (φ.mapOwner f).alpha bound = (φ.alpha bound).mapOwner f := by
  induction φ generalizing bound <;> simp_all [mapOwner, alpha, AlphaFormula.mapOwner]

theorem AlphaEquivalent.mapOwner {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ) (f : Owner → Other) :
    (φ.mapOwner f).AlphaEquivalent (ψ.mapOwner f) := by
  unfold AlphaEquivalent at h ⊢
  simpa only [alpha_mapOwner] using congrArg (AlphaFormula.mapOwner f) h

@[simp] theorem shape_alpha (φ : Formula Owner) (bound : List Nat) :
    (φ.alpha bound).shape = φ.shape := by
  induction φ generalizing bound <;> simp_all [alpha, shape, AlphaFormula.shape]

theorem AlphaEquivalent.shape_eq {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ) : φ.shape = ψ.shape := by
  simpa only [shape_alpha] using congrArg AlphaFormula.shape h

@[simp] theorem shape_substTerm (φ : Formula Owner) (x : Nat) (t : Term) :
    (φ.substTerm x t).shape = φ.shape := by
  induction φ <;> simp_all [substTerm, shape]
  all_goals split_ifs <;> simp_all [shape]

@[simp] theorem shape_substVar (φ : Formula Owner) (x y : Nat) :
    (φ.substVar x y).shape = φ.shape := shape_substTerm φ x (.var y)

@[simp] theorem mapOwner_chain (Γ : List (Formula Owner)) (φ : Formula Owner)
    (f : Owner → Other) :
    (chain Γ φ).mapOwner f = chain (Γ.map (mapOwner f)) (φ.mapOwner f) := by
  induction Γ with
  | nil => rfl
  | cons θ Γ ih => simp only [chain, mapOwner, List.map_cons, ih]

end Formula

namespace ModalModel

variable {Owner Other D : Type}

/-- Pull back every queried formula as well as its outer owner. -/
def pullback (M : ModalModel Other D) (f : Owner → Other) : ModalModel Owner D where
  zero := M.zero
  succ := M.succ
  add := M.add
  mul := M.mul
  modal := fun a φ s => M.modal (f a) (φ.mapOwner f) s
  free_independence := by
    intro a φ s t h
    apply M.free_independence
    simpa only [Formula.freeVars_mapOwner] using h
  alphabetic := by
    intro a φ ψ s h
    exact M.alphabetic (f a) _ _ s (h.mapOwner f)
  weak_substitution := by
    intro a φ x y s h
    simpa only [Formula.mapOwner_substVar] using
      M.weak_substitution (f a) (φ.mapOwner f) x y s
        ((Formula.varSubstitutable_mapOwner φ f x y).mpr h)

/-- Empty entire modal predicates outside a set of owners. The retained
    interpretation is copied completely, at every formula and assignment. -/
def mask (M : ModalModel Owner D) (keep : Owner → Prop) : ModalModel Owner D where
  zero := M.zero
  succ := M.succ
  add := M.add
  mul := M.mul
  modal := fun a φ s => keep a ∧ M.modal a φ s
  free_independence := fun a φ s t h => and_congr_right fun _ =>
    M.free_independence a φ s t h
  alphabetic := fun a φ ψ s h => and_congr_right fun _ =>
    M.alphabetic a φ ψ s h
  weak_substitution := fun a φ x y s h => and_congr_right fun _ =>
    M.weak_substitution a φ x y s h

@[simp] theorem mask_modal_of_retained (M : ModalModel Owner D) (keep : Owner → Prop)
    {a : Owner} (ha : keep a) (φ : Formula Owner) (s : Nat → D) :
    (M.mask keep).modal a φ s ↔ M.modal a φ s := by
  exact and_iff_right ha

@[simp] theorem mask_modal_of_omitted (M : ModalModel Owner D) (keep : Owner → Prop)
    {a : Owner} (ha : ¬ keep a) (φ : Formula Owner) (s : Nat → D) :
    ¬ (M.mask keep).modal a φ s := fun h => ha h.1

end ModalModel

theorem generalTermEval_pullback {Owner Other D : Type} (M : ModalModel Other D)
    (f : Owner → Other) (s : Nat → D) (t : Term) :
    generalTermEval (M.pullback f) s t = generalTermEval M s t := by
  induction t <;> simp_all [generalTermEval, ModalModel.pullback]

theorem generalTruth_pullback {Owner Other D : Type} (M : ModalModel Other D)
    (f : Owner → Other) (φ : Formula Owner) (s : Nat → D) :
    generalTruth (M.pullback f) φ s ↔ generalTruth M (φ.mapOwner f) s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => simp only [generalTruth, Formula.mapOwner, generalTermEval_pullback]
  | imp φ ψ ihφ ihψ => simp only [generalTruth, Formula.mapOwner, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [generalTruth, Formula.mapOwner, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [generalTruth, Formula.mapOwner, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih s)
  | all x φ ih => exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih (Function.update s x n)
  | know a φ _ => rfl

theorem Valid.mapOwner {Owner Other : Type} {φ : Formula Owner}
    (h : Valid φ) (f : Owner → Other) : Valid (φ.mapOwner f) := by
  intro D hD M s
  exact (generalTruth_pullback M f φ s).mp (h D hD (M.pullback f) s)

def Certificate.mapOwner {Owner Other : Type} {axioms : Formula Owner → Prop}
    {target : Formula Other → Prop} {φ : Formula Owner} (c : Certificate axioms φ)
    (f : Owner → Other) (ha : ∀ θ, axioms θ → target (θ.mapOwner f)) :
    Certificate target (φ.mapOwner f) where
  premises := c.premises.map (Formula.mapOwner f)
  admitted := by
    intro θ hθ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hθ
    exact ha η (c.admitted η hη)
  validity := by
    simpa only [Formula.mapOwner_chain] using c.validity.mapOwner f

theorem Provable.mapOwner {Owner Other : Type} {axioms : Formula Owner → Prop}
    {target : Formula Other → Prop} {φ : Formula Owner} (h : Provable axioms φ)
    (f : Owner → Other) (ha : ∀ θ, axioms θ → target (θ.mapOwner f)) :
    Provable target (φ.mapOwner f) := by
  obtain ⟨c⟩ := h
  exact ⟨c.mapOwner f ha⟩

def RawPredicates.pullback {Owner Other : Type} (P : RawPredicates Other)
    (f : Owner → Other) : RawPredicates Owner :=
  fun a φ => P (f a) (φ.mapOwner f)

theorem truth_pullback {Owner Other : Type} (filtered : Bool) (P : RawPredicates Other)
    (f : Owner → Other) (φ : Formula Owner) (s : Assignment) :
    truth filtered (P.pullback f) φ s ↔ truth filtered P (φ.mapOwner f) s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => simp only [truth, Formula.mapOwner, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [truth, Formula.mapOwner, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [truth, Formula.mapOwner, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih s)
  | all x φ ih => exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih (Function.update s x n)
  | know a φ ih =>
    cases filtered <;> simp only [truth, Formula.mapOwner, RawPredicates.pullback,
      Formula.mapOwner_close, Bool.false_eq_true, ↓reduceIte, ih]

def ActualRealization.pullback {Owner Other : Type} {P : RawPredicates Other}
    (M : ActualRealization P) (f : Owner → Other) : ActualRealization (P.pullback f) where
  model := M.model.pullback f
  zero_correct := M.zero_correct
  succ_correct := M.succ_correct
  add_correct := M.add_correct
  mul_correct := M.mul_correct
  modal_correct := fun a φ s => (M.modal_correct (f a) (φ.mapOwner f) s).trans
    (truth_pullback false P f (.know a φ) s).symm

def FilteredRealization.pullback {Owner Other : Type} {P : RawPredicates Other}
    (M : FilteredRealization P) (f : Owner → Other) :
    FilteredRealization (P.pullback f) where
  model := M.model.pullback f
  zero_correct := M.zero_correct
  succ_correct := M.succ_correct
  add_correct := M.add_correct
  mul_correct := M.mul_correct
  modal_correct := fun a φ s => (M.modal_correct (f a) (φ.mapOwner f) s).trans
    (truth_pullback true P f (.know a φ) s).symm

end Alexander313
