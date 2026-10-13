import Alexander313.Alexander.HilbertWitnessStages

/-!
# A concrete common language and finite support for witness-stage syntax

The common language adds Nat-indexed nullary symbols. The new symbol at
stage n maps to index n. Actual symbol maps commute with each successor
embedding. A bounded retraction fixes every symbol from a given finite stage
and sends later constants to its first constant. Literal support bounds also
put every common-language term and formula in the image of a finite stage.
-/

namespace Alexander313.FirstOrderCalculus.WitnessLimit

universe u v w

def language (L : FirstOrder.Language.{u, v}) := ConstantExtension.language L Nat

variable {L : FirstOrder.Language.{u, v}}

def originalFunction : (n r : Nat) → L.Functions r → (WitnessStages.stageLanguage L n).Functions r
  | 0, _, f => f
  | n + 1, _, f => .inl (originalFunction n _ f)

def originalRelation : (n r : Nat) → L.Relations r → (WitnessStages.stageLanguage L n).Relations r
  | 0, _, r => r
  | n + 1, _, r => originalRelation n _ r

def toLimitFunction : (n r : Nat) → (WitnessStages.stageLanguage L n).Functions r → (language L).Functions r
  | 0, _, f => .inl f
  | n + 1, _, .inl f => toLimitFunction n _ f
  | n + 1, _, .inr (.constant _) => .inr (.constant n)

def toLimitRelation : (n r : Nat) → (WitnessStages.stageLanguage L n).Relations r → L.Relations r
  | 0, _, r => r
  | n + 1, _, r => toLimitRelation n _ r

def toLimit (n : Nat) : SymbolMap (WitnessStages.stageLanguage L n) (language L) where
  onFunction := toLimitFunction n
  onRelation := toLimitRelation n

def constantAt : (n : Nat) → Fin n → (WitnessStages.stageLanguage L n).Functions 0
  | 0, k => k.elim0
  | n + 1, k => if h : k.val < n then .inl (constantAt n ⟨k.val, h⟩)
      else .inr (.constant ())

def functionBound : {r : Nat} → (language L).Functions r → Nat
  | _, .inl _ => 0
  | _, .inr (.constant k) => k + 1

@[simp] theorem toLimit_originalFunction (n r : Nat) (f : L.Functions r) :
    toLimitFunction n r (originalFunction n r f) = .inl f := by
  induction n <;> simp_all [originalFunction, toLimitFunction]

@[simp] theorem toLimit_originalRelation (n r : Nat) (a : L.Relations r) :
    toLimitRelation n r (originalRelation n r a) = a := by
  induction n <;> simp_all [originalRelation, toLimitRelation]

@[simp] theorem original_toLimitRelation (n r : Nat)
    (a : (WitnessStages.stageLanguage L n).Relations r) :
    originalRelation n r (toLimitRelation n r a) = a := by
  revert a
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; exact ih a

@[simp] theorem toLimit_constantAt (n : Nat) (k : Fin n) :
    toLimitFunction (L := L) n 0 (constantAt n k) = .inr (.constant k.val) := by
  revert k
  induction n with
  | zero => intro k; exact k.elim0
  | succ n ih =>
    intro k
    by_cases h : k.val < n
    · simp [constantAt, h, toLimitFunction, ih]
    · have hk : k.val = n := by have := k.isLt; omega
      simp [constantAt, h, toLimitFunction, hk]

theorem toLimit_functionBound (n r : Nat)
    (f : (WitnessStages.stageLanguage L n).Functions r) :
    functionBound (toLimitFunction n r f) ≤ n := by
  revert f
  induction n with
  | zero => intro f; exact le_rfl
  | succ n ih =>
    intro f
    cases f with
    | inl f => exact (ih f).trans (Nat.le_succ n)
    | inr f => cases f; exact le_rfl

theorem toLimitFunction_injective (n r : Nat) :
    Function.Injective (toLimitFunction (L := L) n r) := by
  revert r
  induction n with
  | zero => intro r f g h; exact Sum.inl.inj h
  | succ n ih =>
    intro r f g h
    cases f with
    | inl f =>
      cases g with
      | inl g => exact congrArg Sum.inl (ih r h)
      | inr g =>
        cases g with
        | constant a =>
          have hb := toLimit_functionBound n 0 f
          change toLimitFunction n 0 f = .inr (.constant n) at h
          rw [h] at hb
          change n + 1 ≤ n at hb
          omega
    | inr f =>
      cases f with
      | constant a =>
        cases g with
        | inl g =>
          have hb := toLimit_functionBound n 0 g
          change .inr (.constant n) = toLimitFunction n 0 g at h
          rw [← h] at hb
          change n + 1 ≤ n at hb
          omega
        | inr g =>
          cases g with
          | constant b => cases a; cases b; rfl

def retractFunction (n : Nat) (hn : 0 < n) :
    {r : Nat} → (language L).Functions r → (WitnessStages.stageLanguage L n).Functions r
  | r, .inl f => originalFunction n r f
  | _, .inr (.constant k) => if h : k < n then constantAt n ⟨k, h⟩
      else constantAt n ⟨0, hn⟩

def retract (n : Nat) (hn : 0 < n) : SymbolMap (language L) (WitnessStages.stageLanguage L n) where
  onFunction := fun _ f => retractFunction n hn f
  onRelation := fun r a => originalRelation (L := L) n r a

theorem toLimit_retractFunction (n : Nat) (hn : 0 < n) {r : Nat}
    (f : (language L).Functions r) (hf : functionBound f ≤ n) :
    toLimitFunction n r (retractFunction n hn f) = f := by
  cases f with
  | inl f => exact toLimit_originalFunction n r f
  | inr f =>
    cases f with
    | constant k =>
      have hk : k < n := by change k + 1 ≤ n at hf; omega
      simp [retractFunction, hk, toLimit_constantAt]

@[simp] theorem retract_toLimitFunction (n : Nat) (hn : 0 < n) (r : Nat)
    (f : (WitnessStages.stageLanguage L n).Functions r) :
    retractFunction n hn (toLimitFunction n r f) = f := by
  apply toLimitFunction_injective n r
  exact toLimit_retractFunction n hn _ (toLimit_functionBound n r f)

@[simp] theorem toLimit_succ_termMap_embed (n : Nat) {α : Type w}
    (t : (WitnessStages.stageLanguage L n).Term α) :
    (toLimit (n + 1)).termMap (ConstantExtension.embedTerm (C := Unit) t) =
      (toLimit n).termMap t := by
  induction t <;> simp_all [toLimit, SymbolMap.termMap, ConstantExtension.embedTerm,
    ConstantExtension.inclusion, toLimitFunction]

@[simp] theorem toLimit_succ_formulaMap_embed (n : Nat) {α : Type w} {b : Nat}
    (φ : (WitnessStages.stageLanguage L n).BoundedFormula α b) :
    (toLimit (n + 1)).formulaMap (ConstantExtension.embed (C := Unit) φ) =
      (toLimit n).formulaMap φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    change FirstOrder.Language.BoundedFormula.equal
      ((toLimit (n + 1)).termMap (ConstantExtension.embedTerm t))
      ((toLimit (n + 1)).termMap (ConstantExtension.embedTerm s)) =
      FirstOrder.Language.BoundedFormula.equal ((toLimit n).termMap t) ((toLimit n).termMap s)
    rw [toLimit_succ_termMap_embed, toLimit_succ_termMap_embed]
  | rel r ts =>
    change FirstOrder.Language.BoundedFormula.rel ((toLimit n).onRelation _ r)
      (fun i => (toLimit (n + 1)).termMap (ConstantExtension.embedTerm (ts i))) =
      .rel ((toLimit n).onRelation _ r) (fun i => (toLimit n).termMap (ts i))
    congr 1
    funext i
    exact toLimit_succ_termMap_embed n (ts i)
  | imp φ ψ ihφ ihψ =>
    change ((toLimit (n + 1)).formulaMap (ConstantExtension.embed φ)).imp
      ((toLimit (n + 1)).formulaMap (ConstantExtension.embed ψ)) =
      ((toLimit n).formulaMap φ).imp ((toLimit n).formulaMap ψ)
    rw [ihφ, ihψ]
  | all φ ih => exact congrArg FirstOrder.Language.BoundedFormula.all ih

@[simp] theorem retract_toLimit_termMap (n : Nat) (hn : 0 < n) {α : Type w}
    (t : (WitnessStages.stageLanguage L n).Term α) :
    (retract n hn).termMap ((toLimit n).termMap t) = t := by
  induction t <;> simp_all [toLimit, retract, SymbolMap.termMap]

@[simp] theorem retract_toLimit_formulaMap (n : Nat) (hn : 0 < n)
    {α : Type w} {b : Nat} (φ : (WitnessStages.stageLanguage L n).BoundedFormula α b) :
    (retract n hn).formulaMap ((toLimit n).formulaMap φ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    change FirstOrder.Language.BoundedFormula.equal ((retract n hn).termMap ((toLimit n).termMap t))
      ((retract n hn).termMap ((toLimit n).termMap s)) = FirstOrder.Language.BoundedFormula.equal t s
    rw [retract_toLimit_termMap, retract_toLimit_termMap]
  | rel r ts =>
    change FirstOrder.Language.BoundedFormula.rel
      (originalRelation n _ (toLimitRelation n _ r))
      (fun i => (retract n hn).termMap ((toLimit n).termMap (ts i))) = .rel r ts
    rw [original_toLimitRelation]
    congr 1
    funext i
    exact retract_toLimit_termMap n hn (ts i)
  | imp φ ψ ihφ ihψ =>
    change ((retract n hn).formulaMap ((toLimit n).formulaMap φ)).imp
      ((retract n hn).formulaMap ((toLimit n).formulaMap ψ)) = φ.imp ψ
    rw [ihφ, ihψ]
  | all φ ih => exact congrArg FirstOrder.Language.BoundedFormula.all ih

@[simp] theorem toLimit_liftSentence (σ : L.Sentence) (n : Nat) :
    (toLimit n).formulaMap (WitnessStages.liftSentence σ n) =
      (toLimit 0).formulaMap σ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WitnessStages.liftSentence, toLimit_succ_formulaMap_embed, ih]

@[simp] theorem toLimit_newConstant (n : Nat) {α : Type w} :
    (toLimit (L := L) (n + 1)).termMap
      (ConstantExtension.constant () : (WitnessStages.stageLanguage L (n + 1)).Term α) =
      (ConstantExtension.constant n : (language L).Term α) := by
  change FirstOrder.Language.Term.func (L := language L) (.inr (.constant n)) _ =
    FirstOrder.Language.Term.func (L := language L) (.inr (.constant n)) _
  congr 1
  funext i
  exact i.elim0

def termBound {α : Type w} : (language L).Term α → Nat
  | .var _ => 0
  | .func f ts => max (functionBound f) (Finset.univ.sup (fun i => termBound (ts i)))

def formulaBound {α : Type w} : {b : Nat} → (language L).BoundedFormula α b → Nat
  | _, .falsum => 0
  | _, .equal t s => max (termBound t) (termBound s)
  | _, .rel _ ts => Finset.univ.sup (fun i => termBound (ts i))
  | _, .imp φ ψ => max (formulaBound φ) (formulaBound ψ)
  | _, .all φ => formulaBound φ

theorem toLimit_retract_termMap (n : Nat) (hn : 0 < n) {α : Type w}
    (t : (language L).Term α) (ht : termBound t ≤ n) :
    (toLimit n).termMap ((retract n hn).termMap t) = t := by
  revert ht
  induction t with
  | var x => intro _; rfl
  | func f ts ih =>
    intro ht
    have hf : functionBound f ≤ n := (le_max_left _ _).trans ht
    have hs : Finset.univ.sup (fun i => termBound (ts i)) ≤ n := (le_max_right _ _).trans ht
    change FirstOrder.Language.Term.func (toLimitFunction n _ (retractFunction n hn f))
      (fun i => (toLimit n).termMap ((retract n hn).termMap (ts i))) = .func f ts
    rw [toLimit_retractFunction n hn f hf]
    congr 1
    funext i
    exact ih i ((Finset.le_sup (f := fun j => termBound (ts j)) (Finset.mem_univ i)).trans hs)

theorem toLimit_retract_formulaMap (n : Nat) (hn : 0 < n) {α : Type w} {b : Nat}
    (φ : (language L).BoundedFormula α b) (hφ : formulaBound φ ≤ n) :
    (toLimit n).formulaMap ((retract n hn).formulaMap φ) = φ := by
  revert hφ
  induction φ with
  | falsum => intro _; rfl
  | equal t s =>
    intro hφ
    have ht : termBound t ≤ n := (le_max_left _ _).trans hφ
    have hs : termBound s ≤ n := (le_max_right _ _).trans hφ
    change FirstOrder.Language.BoundedFormula.equal ((toLimit n).termMap ((retract n hn).termMap t))
      ((toLimit n).termMap ((retract n hn).termMap s)) = FirstOrder.Language.BoundedFormula.equal t s
    rw [toLimit_retract_termMap n hn t ht, toLimit_retract_termMap n hn s hs]
  | rel r ts =>
    intro hφ
    change FirstOrder.Language.BoundedFormula.rel (L := language L)
      (toLimitRelation (L := L) n _ (originalRelation (L := L) n _ r))
      (fun i => (toLimit n).termMap ((retract n hn).termMap (ts i))) =
        FirstOrder.Language.BoundedFormula.rel (L := language L) r ts
    rw [toLimit_originalRelation (L := L)]
    congr 1
    funext i
    exact toLimit_retract_termMap n hn (ts i)
      ((Finset.le_sup (f := fun j => termBound (ts j)) (Finset.mem_univ i)).trans hφ)
  | imp φ ψ ihφ ihψ =>
    intro h
    change ((toLimit n).formulaMap ((retract n hn).formulaMap φ)).imp
      ((toLimit n).formulaMap ((retract n hn).formulaMap ψ)) = φ.imp ψ
    rw [ihφ ((le_max_left _ _).trans h), ihψ ((le_max_right _ _).trans h)]
  | all φ ih =>
    intro h
    exact congrArg FirstOrder.Language.BoundedFormula.all (ih h)

theorem term_preimage {α : Type w} (t : (language L).Term α) :
    ∃ n : Nat, ∃ s : (WitnessStages.stageLanguage L n).Term α,
      (toLimit n).termMap s = t := by
  let n := termBound t + 1
  have hn : 0 < n := Nat.zero_lt_succ _
  exact ⟨n, (retract n hn).termMap t, toLimit_retract_termMap n hn t (Nat.le_succ _)⟩

theorem formula_preimage {α : Type w} {b : Nat}
    (φ : (language L).BoundedFormula α b) :
    ∃ n : Nat, ∃ ψ : (WitnessStages.stageLanguage L n).BoundedFormula α b,
      (toLimit n).formulaMap ψ = φ := by
  let n := formulaBound φ + 1
  have hn : 0 < n := Nat.zero_lt_succ _
  exact ⟨n, (retract n hn).formulaMap φ, toLimit_retract_formulaMap n hn φ (Nat.le_succ _)⟩

theorem unaryChoice_preimage (c : WitnessStages.UnaryChoice (language L)) :
    ∃ n : Nat, ∃ d : WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n),
      d.name = c.name ∧ (toLimit n).formulaMap d.matrix = c.matrix := by
  obtain ⟨n, φ, hφ⟩ := formula_preimage c.matrix
  have hs : φ.freeVarFinset ⊆ {c.name} := by
    have hf := SymbolMap.formulaMap_freeVarFinset (toLimit n) φ
    rw [hφ] at hf
    simpa only [hf] using c.support
  exact ⟨n, ⟨c.name, φ, hs⟩, rfl, hφ⟩

end Alexander313.FirstOrderCalculus.WitnessLimit
