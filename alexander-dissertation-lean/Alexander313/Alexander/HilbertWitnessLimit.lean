import Alexander313.Alexander.HilbertWitnessLimitSyntax

/-!
# The actual common-language union of witness stages

Successive stage theories embed monotonically into the concrete Nat-constant
language. Induction over a finite native proof bounds all its theory premises
by one stage. The explicit retraction eliminates later intermediate constants,
so finite-stage consistency and old-sentence conservativity pass to the union.
Every scheduled witness is admitted literally. Fairness and quantified model
truth are separate constructions.
-/

namespace Alexander313.FirstOrderCalculus.WitnessLimit

universe u v

variable {L : FirstOrder.Language.{u, v}}

def mappedStageTheory (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    (n : Nat) : (language L).Theory :=
  (toLimit n).theoryMap (WitnessStages.stageTheory T choices n)

def theory (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) :
    (language L).Theory := ⋃ n, mappedStageTheory T choices n

theorem mappedStageTheory_succ (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) (n : Nat) :
    mappedStageTheory T choices n ⊆ mappedStageTheory T choices (n + 1) := by
  rintro σ ⟨τ, hτ, rfl⟩
  refine ⟨ConstantExtension.embed (C := Unit) τ, ?_, toLimit_succ_formulaMap_embed n τ⟩
  exact Set.mem_insert_iff.mpr (Or.inr (⟨τ, hτ, rfl⟩))

theorem mappedStageTheory_mono (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    {n m : Nat} (h : n ≤ m) : mappedStageTheory T choices n ⊆ mappedStageTheory T choices m := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact fun _ h => h
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n; exact fun _ h => h
    · have hnm : n ≤ m := by omega
      exact (ih hnm).trans (mappedStageTheory_succ T choices m)

theorem mappedStageTheory_subset_theory (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) (n : Nat) :
    mappedStageTheory T choices n ⊆ theory T choices :=
  fun _ h => Set.mem_iUnion.mpr ⟨n, h⟩

@[simp] theorem retract_mappedStageTheory (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    (n : Nat) (hn : 0 < n) :
    (retract n hn).theoryMap (mappedStageTheory T choices n) =
      WitnessStages.stageTheory T choices n := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨θ, hθ, rfl⟩, he⟩
    have hθσ : θ = σ := by simpa only [retract_toLimit_formulaMap] using he
    simpa only [hθσ] using hθ
  · intro hσ
    exact ⟨(toLimit n).formulaMap σ, ⟨σ, hσ, rfl⟩, retract_toLimit_formulaMap n hn σ⟩

private theorem mappedStageTheory_consistent_positive (T : L.Theory) (hT : Consistent T)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    (n : Nat) (hn : 0 < n) : Consistent (mappedStageTheory T choices n) := by
  intro hfalse
  have hr := hfalse.map (retract n hn)
  apply WitnessStages.stageTheory_consistent T hT choices n
  simpa only [retract_mappedStageTheory, SymbolMap.formulaMap_falsum] using hr

theorem mappedStageTheory_consistent (T : L.Theory) (hT : Consistent T)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) (n : Nat) :
    Consistent (mappedStageTheory T choices n) :=
  (mappedStageTheory_consistent_positive T hT choices (n + 1) (Nat.zero_lt_succ n)).mono
    (mappedStageTheory_succ T choices n)

/-- The stage bound is obtained from the actual finite native proof. -/
theorem derivation_at_stage (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    {φ : (language L).Formula Nat} (h : Derivation (theory T choices) φ) :
    ∃ n : Nat, Derivation (mappedStageTheory T choices n) φ := by
  induction h with
  | logical h => exact ⟨0, .logical h⟩
  | theory σ hσ =>
    obtain ⟨n, hσn⟩ := Set.mem_iUnion.mp hσ
    exact ⟨n, .theory σ hσn⟩
  | mp hp hq ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨max n m, Derivation.mp
      (hn.mono (mappedStageTheory_mono T choices (le_max_left n m)))
      (hm.mono (mappedStageTheory_mono T choices (le_max_right n m)))⟩
  | generalize x h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, .generalize x hn⟩

theorem theory_consistent (T : L.Theory) (hT : Consistent T)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) :
    Consistent (theory T choices) := by
  intro hfalse
  obtain ⟨n, hn⟩ := derivation_at_stage T choices hfalse
  exact mappedStageTheory_consistent T hT choices n hn

theorem theory_derivation_iff (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    (σ : L.Sentence) :
    Derivation (theory T choices) (sentenceFormula ((toLimit 0).formulaMap σ)) ↔
      Derivation T (sentenceFormula σ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := derivation_at_stage T choices h
    have hp := hn.mono (mappedStageTheory_succ T choices n)
    have hr := hp.map (retract (n + 1) (Nat.zero_lt_succ n))
    have he : (retract (n + 1) (Nat.zero_lt_succ n)).formulaMap
        ((toLimit 0).formulaMap σ) = WitnessStages.liftSentence σ (n + 1) := by
      rw [← toLimit_liftSentence σ (n + 1), retract_toLimit_formulaMap]
    apply (WitnessStages.stageTheory_derivation_iff T choices σ (n + 1)).mp
    simpa only [retract_mappedStageTheory, ← SymbolMap.sentenceFormula_map, he] using hr
  · intro h
    have hm : Derivation (mappedStageTheory T choices 0)
        (sentenceFormula ((toLimit 0).formulaMap σ)) := by
      change Derivation ((toLimit (L := L) 0).theoryMap T)
        (sentenceFormula ((toLimit (L := L) 0).formulaMap σ))
      rw [SymbolMap.sentenceFormula_map]
      exact h.map (toLimit (L := L) 0)
    exact hm.mono (mappedStageTheory_subset_theory T choices 0)

theorem original_sentence_mem (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n))
    (σ : L.Sentence) (hσ : σ ∈ T) : (toLimit 0).formulaMap σ ∈ theory T choices :=
  mappedStageTheory_subset_theory T choices 0 (⟨σ, hσ, rfl⟩)

theorem toLimit_witnessFormula (n x : Nat)
    (φ : (WitnessStages.stageLanguage L n).Formula Nat) :
    (toLimit (n + 1)).formulaMap (ConstantExtension.witnessFormula () x φ) =
      (existsVariable x ((toLimit n).formulaMap φ)).imp
        (substituteVariable x (ConstantExtension.constant n) ((toLimit n).formulaMap φ)) := by
  unfold ConstantExtension.witnessFormula
  change ((toLimit (n + 1)).formulaMap (ConstantExtension.embed (existsVariable x φ))).imp
    ((toLimit (n + 1)).formulaMap
      (substituteVariable x (ConstantExtension.constant ()) (ConstantExtension.embed φ))) = _
  rw [toLimit_succ_formulaMap_embed,
    SymbolMap.formulaMap_existsVariable, SymbolMap.formulaMap_substituteVariable,
    toLimit_newConstant, toLimit_succ_formulaMap_embed]

theorem witness_derivation (T : L.Theory)
    (choices : ∀ n, WitnessStages.UnaryChoice (WitnessStages.stageLanguage L n)) (n : Nat) :
    Derivation (theory T choices)
      ((existsVariable (choices n).name ((toLimit n).formulaMap (choices n).matrix)).imp
        (substituteVariable (choices n).name (ConstantExtension.constant n)
          ((toLimit n).formulaMap (choices n).matrix))) := by
  have h := (WitnessStages.witness_derivation T choices n).map (toLimit (n + 1))
  have hm : Derivation (mappedStageTheory T choices (n + 1))
      ((existsVariable (choices n).name ((toLimit n).formulaMap (choices n).matrix)).imp
        (substituteVariable (choices n).name (ConstantExtension.constant n)
          ((toLimit n).formulaMap (choices n).matrix))) := by
    simpa only [toLimit_witnessFormula, mappedStageTheory] using h
  exact hm.mono (mappedStageTheory_subset_theory T choices (n + 1))

@[simp] theorem closedTerm_embed_constant (k : Nat) :
    ClosedTerm.embed (ConstantExtension.constant k : (language L).Term Empty) =
      (ConstantExtension.constant k : (language L).Term Nat) := by
  change FirstOrder.Language.Term.func (L := language L) (Sum.inr (.constant k)) _ =
    FirstOrder.Language.Term.func (L := language L) (Sum.inr (.constant k)) _
  congr 1
  funext i
  exact i.elim0

end Alexander313.FirstOrderCalculus.WitnessLimit
