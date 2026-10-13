import Alexander313.Alexander.HilbertLanguageMaps

/-!
# Actual model reducts along native symbol maps

The structure on the original alphabet is constructed by interpreting each
function/relation through its actual arity-preserving symbol image. Carrier
and assignments are unchanged. Native realization commutes with the already
defined literal term/formula maps, including every quantifier.

This supplies the final language-reduction step for a constructed Henkin
countermodel. It does not assume Hilbert completeness or existence of a model.
-/

namespace Alexander313.FirstOrderCalculus.SymbolMap

universe u v u' v' w z

variable {L : FirstOrder.Language.{u, v}} {M : FirstOrder.Language.{u', v'}}
    {D : Type w}

def reduct (m : SymbolMap L M) (N : M.Structure D) : L.Structure D where
  funMap := fun f xs => N.funMap (m.onFunction _ f) xs
  RelMap := fun r xs => N.RelMap (m.onRelation _ r) xs

theorem termMap_realize (m : SymbolMap L M) (N : M.Structure D)
    {α : Type z} (t : L.Term α) (s : α → D) :
    letI : M.Structure D := N
    letI : L.Structure D := reduct m N
    (m.termMap t).realize s = t.realize s := by
  letI : M.Structure D := N
  letI : L.Structure D := reduct m N
  induction t with
  | var x => rfl
  | func f ts ih =>
    change N.funMap (m.onFunction _ f)
      (fun i => (m.termMap (ts i)).realize s) =
      N.funMap (m.onFunction _ f) (fun i => (ts i).realize s)
    exact congrArg (N.funMap (m.onFunction _ f)) (funext ih)

theorem formulaMap_realize (m : SymbolMap L M) (N : M.Structure D)
    {α : Type z} {n : Nat} (φ : L.BoundedFormula α n)
    (s : α → D) (v : Fin n → D) :
    letI : M.Structure D := N
    letI : L.Structure D := reduct m N
    (m.formulaMap φ).Realize s v ↔ φ.Realize s v := by
  letI : M.Structure D := N
  letI : L.Structure D := reduct m N
  induction φ with
  | falsum => rfl
  | equal t q =>
    simp only [formulaMap, FirstOrder.Language.BoundedFormula.Realize, termMap_realize]
  | rel r ts =>
    change N.RelMap (m.onRelation _ r)
      (fun i => (m.termMap (ts i)).realize (Sum.elim s v)) ↔
      N.RelMap (m.onRelation _ r) (fun i => (ts i).realize (Sum.elim s v))
    have htuple : (fun i => (m.termMap (ts i)).realize (Sum.elim s v)) =
        fun i => (ts i).realize (Sum.elim s v) :=
      funext (fun i => termMap_realize m N (ts i) (Sum.elim s v))
    rw [htuple]
  | imp φ ψ ihφ ihψ =>
    change ((m.formulaMap φ).Realize s v → (m.formulaMap ψ).Realize s v) ↔
      (φ.Realize s v → ψ.Realize s v)
    exact imp_congr (ihφ v) (ihψ v)
  | all φ ih =>
    change (∀ d : D, (m.formulaMap φ).Realize s (Fin.snoc v d)) ↔
      ∀ d : D, φ.Realize s (Fin.snoc v d)
    exact forall_congr' (fun d => ih (Fin.snoc v d))

theorem sentenceMap_realize (m : SymbolMap L M) (N : M.Structure D)
    (σ : L.Sentence) :
    letI : M.Structure D := N
    letI : L.Structure D := reduct m N
    FirstOrder.Language.Sentence.Realize D (m.formulaMap σ) ↔ σ.Realize D := by
  letI : M.Structure D := N
  letI : L.Structure D := reduct m N
  exact formulaMap_realize m N σ (default : Empty → D) (default : Fin 0 → D)

theorem model_reduct [Nonempty D] (m : SymbolMap L M) (N : M.Structure D)
    (T : L.Theory)
    (h : letI : M.Structure D := N
      FirstOrder.Language.Theory.Model D (m.theoryMap T)) :
    letI : L.Structure D := reduct m N
    FirstOrder.Language.Theory.Model D T := by
  letI : M.Structure D := N
  letI : L.Structure D := reduct m N
  refine ⟨?_⟩
  intro σ hσ
  apply (sentenceMap_realize m N σ).mp
  exact h.realize_of_mem (m.formulaMap σ) (⟨σ, hσ, rfl⟩)

theorem counterexample_reduct [Nonempty D] (m : SymbolMap L M)
    (N : M.Structure D) (σ : L.Sentence)
    (h : letI : M.Structure D := N
      ¬FirstOrder.Language.Sentence.Realize D (m.formulaMap σ)) :
    letI : L.Structure D := reduct m N
    ¬σ.Realize D := by
  letI : M.Structure D := N
  letI : L.Structure D := reduct m N
  exact fun hσ => h ((sentenceMap_realize m N σ).mpr hσ)

end Alexander313.FirstOrderCalculus.SymbolMap
