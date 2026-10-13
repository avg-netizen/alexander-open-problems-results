import Alexander313.Semantics
import Alexander313.Hierarchy

/-!
# Finite-frontier recovery of the actual full family

The entire lower ideal and the full core predicate are retained. Emptying
outsiders changes semantics only, never theories, compilers or numeric
source codes. This proves note 26 §6 given its whole-ideal genericity lemma.
-/

namespace Alexander313

inductive ExtendedOwner where
  | core : ExtendedOwner
  | machine : Nat → ExtendedOwner
  deriving DecidableEq, Repr

def Formula.originalNames : Formula ExtendedOwner → Finset Nat
  | .falsum => ∅
  | .equal _ _ => ∅
  | .imp φ ψ => φ.originalNames ∪ ψ.originalNames
  | .conj φ ψ => φ.originalNames ∪ ψ.originalNames
  | .disj φ ψ => φ.originalNames ∪ ψ.originalNames
  | .neg φ => φ.originalNames
  | .all _ φ => φ.originalNames
  | .ex _ φ => φ.originalNames
  | .know .core φ => φ.originalNames
  | .know (.machine i) φ => insert i φ.originalNames

theorem Formula.query_owner_in_names (φ : Formula ExtendedOwner) (i : Nat)
    (sh : Shape ExtendedOwner) (h : (.machine i, sh) ∈ φ.queries) :
    i ∈ φ.originalNames := by
  induction φ generalizing sh with
  | falsum => simp [queries] at h
  | equal t u => simp [queries] at h
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union.mpr (Or.inl (ihφ _ h))
    · exact Finset.mem_union.mpr (Or.inr (ihψ _ h))
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union.mpr (Or.inl (ihφ _ h))
    · exact Finset.mem_union.mpr (Or.inr (ihψ _ h))
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union.mpr (Or.inl (ihφ _ h))
    · exact Finset.mem_union.mpr (Or.inr (ihψ _ h))
  | neg φ ih => exact ih _ h
  | all x φ ih => exact ih _ h
  | ex x φ ih => exact ih _ h
  | know a φ ih =>
    cases a with
    | core =>
      simp only [queries, Finset.mem_insert, Prod.mk.injEq] at h
      rcases h with h | h
      · cases h.1
      · exact ih _ h
    | machine j =>
      simp only [queries, Finset.mem_insert, Prod.mk.injEq] at h
      rcases h with h | h
      · cases h.1
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih _ h)

noncomputable def idealMask (R : Nat → Nat → Prop) (J : Finset Nat)
    (P : RawPredicates ExtendedOwner) : RawPredicates ExtendedOwner := by
  classical
  exact fun a θ => match a with
    | .core => P .core θ
    | .machine i => if DownIdeal R J i then P (.machine i) θ else False

theorem idealMask_agrees (R : Nat → Nat → Prop) (J : Finset Nat)
    (P : RawPredicates ExtendedOwner) (φ : Formula ExtendedOwner)
    (kept : ∀ i ∈ φ.originalNames, DownIdeal R J i) :
    AgreeOn (idealMask R J P) P φ := by
  classical
  intro a θ hquery
  cases a with
  | core => rfl
  | machine i =>
    have hi := kept i (φ.query_owner_in_names i θ.shape hquery)
    simp [idealMask, hi]

theorem idealMask_outside_sound (R : Nat → Nat → Prop) (J : Finset Nat)
    (P : RawPredicates ExtendedOwner) (i : Nat) (hi : ¬ DownIdeal R J i) :
    RawSound (idealMask R J P) (.machine i) := by
  classical
  intro φ s hp
  simp [idealMask, hi] at hp

def IdealGenericity (R : Nat → Nat → Prop) (source : RawPredicates ExtendedOwner)
    (Admissible : RawPredicates ExtendedOwner → Prop) (J : Finset Nat) : Prop :=
  ∀ P, Admissible P →
    (∀ θ, P .core θ ↔ source .core θ) →
    (∀ i, DownIdeal R J i → ∀ θ, P (.machine i) θ ↔ source (.machine i) θ) →
    (∀ i, ¬ DownIdeal R J i → RawSound P (.machine i)) →
    ∀ i, DownIdeal R J i → RawSound P (.machine i)

theorem actual_original_sound (R : Nat → Nat → Prop) (wf : WellFounded R)
    (source : RawPredicates ExtendedOwner)
    (Admissible : RawPredicates ExtendedOwner → Prop)
    (mask_admissible : ∀ J, Admissible (idealMask R J source))
    (generic : ∀ J, J.Nonempty → FrontierAntichain R J →
      IdealGenericity R source Admissible J) :
    ∀ i, RawSound source (.machine i) := by
  classical
  intro i φ s hp
  let F := insert i φ.originalNames
  let J := maximalFrontier R F
  have hF : F.Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  have hJ : J.Nonempty := maximalFrontier_nonempty wf F hF
  have hi : DownIdeal R J i := finite_frontier_covers wf F i (Finset.mem_insert_self _ _)
  have kept : ∀ j ∈ φ.originalNames, DownIdeal R J j := by
    intro j hj
    exact finite_frontier_covers wf F j (Finset.mem_insert_of_mem hj)
  have hretained : ∀ j, DownIdeal R J j → ∀ θ,
      idealMask R J source (.machine j) θ ↔ source (.machine j) θ := by
    intro j hj θ
    simp [idealMask, hj]
  have hs := generic J hJ (maximalFrontier_antichain R F)
    (idealMask R J source) (mask_admissible J) (fun _ => Iff.rfl)
    hretained (idealMask_outside_sound R J source) i hi
  have hmasked : filteredTruth (idealMask R J source) φ s :=
    hs φ s ((hretained i hi _).mpr hp)
  exact (truth_congr_queries true (idealMask R J source) source φ s
    (idealMask_agrees R J source φ kept)).mp hmasked

theorem actual_family_sound (R : Nat → Nat → Prop) (wf : WellFounded R)
    (source : RawPredicates ExtendedOwner)
    (Admissible : RawPredicates ExtendedOwner → Prop)
    (source_admissible : Admissible source)
    (mask_admissible : ∀ J, Admissible (idealMask R J source))
    (generic : ∀ J, J.Nonempty → FrontierAntichain R J →
      IdealGenericity R source Admissible J)
    (core_generic : ∀ P, Admissible P →
      (∀ θ, P .core θ ↔ source .core θ) →
      (∀ i, RawSound P (.machine i)) → RawSound P .core) :
    ∀ a, RawSound source a := by
  have originals := actual_original_sound R wf source Admissible mask_admissible generic
  intro a
  cases a with
  | core => exact core_generic source source_admissible (fun _ => Iff.rfl) originals
  | machine i => exact originals i

end Alexander313
