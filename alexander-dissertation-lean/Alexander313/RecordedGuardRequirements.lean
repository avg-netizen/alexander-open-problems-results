import Alexander313.RecordedGuards

/-!
# Exact finite requirements for the literal recorded guards

Each indexed occurrence contributes a rank/base chain requirement and every
label in its argument contributes an R₁ edge requirement. Lists may repeat
requirements. Main inspection adds the entire indexed inspection below each
live external head, including the distinguished outer head and occurrences
under ghosts. No chain point is allowed outside the actual marker set.
-/

namespace Alexander313

abbrev GuardRequirements (Label : Type) := List (Nat × Label) × List (Label × Label)

namespace GuardRequirements

def append {Label : Type} (p q : GuardRequirements Label) : GuardRequirements Label :=
  (p.1 ++ q.1, p.2 ++ q.2)

def Holds {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (p : GuardRequirements Label) : Prop :=
  (∀ q ∈ p.1, GuardChainIn R₂ B q.1 q.2) ∧
    ∀ q ∈ p.2, q.1 < q.2 ∧ R₁ q.1 q.2

@[simp] theorem holds_empty {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) : Holds R₁ R₂ B ([], []) := by
  simp [Holds]

@[simp] theorem holds_append {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (p q : GuardRequirements Label) :
    Holds R₁ R₂ B (append p q) ↔ Holds R₁ R₂ B p ∧ Holds R₁ R₂ B q := by
  constructor
  · intro h
    exact ⟨⟨fun x hx => h.1 x (List.mem_append_left _ hx),
      fun x hx => h.2 x (List.mem_append_left _ hx)⟩,
      ⟨fun x hx => h.1 x (List.mem_append_right _ hx),
      fun x hx => h.2 x (List.mem_append_right _ hx)⟩⟩
  · rintro ⟨hp, hq⟩
    constructor
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hp.1 x hx
      · exact hq.1 x hx
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hp.2 x hx
      · exact hq.2 x hx

theorem holds_indexed {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (k : Nat) (ν : Label)
    (L : List Label) (p : GuardRequirements Label) :
    Holds R₁ R₂ B ((k, ν) :: p.1, (L.map (fun μ => (μ, ν))) ++ p.2) ↔
      GuardChainIn R₂ B k ν ∧ (∀ μ ∈ L, μ < ν ∧ R₁ μ ν) ∧ Holds R₁ R₂ B p := by
  constructor
  · intro h
    refine ⟨h.1 (k, ν) List.mem_cons_self, ?_, ?_, ?_⟩
    · intro μ hμ
      exact h.2 (μ, ν) (List.mem_append_left _ (List.mem_map.mpr ⟨μ, hμ, rfl⟩))
    · intro q hq
      exact h.1 q (List.mem_cons_of_mem _ hq)
    · intro q hq
      exact h.2 q (List.mem_append_right _ hq)
  · rintro ⟨hc, he, hp⟩
    constructor
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hc
      · exact hp.1 q hq
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hq
        exact he μ hμ
      · exact hp.2 q hq

end GuardRequirements

namespace Formula

def labelList {Owner Label : Type} : Formula (RecordedHead Owner Label) → List Label
  | .falsum => []
  | .equal _ _ => []
  | .imp φ ψ => φ.labelList ++ ψ.labelList
  | .conj φ ψ => φ.labelList ++ ψ.labelList
  | .disj φ ψ => φ.labelList ++ ψ.labelList
  | .neg φ => φ.labelList
  | .all _ φ => φ.labelList
  | .ex _ φ => φ.labelList
  | .know (.live _) φ => φ.labelList
  | .know (.ghost _) φ => φ.labelList
  | .know (.indexed _ ν) φ => ν :: φ.labelList

@[simp] theorem mem_labelList_iff {Owner Label : Type} [DecidableEq Label]
    (φ : Formula (RecordedHead Owner Label)) (ν : Label) :
    ν ∈ φ.labelList ↔ ν ∈ φ.labelSupport := by
  induction φ with
  | know a φ ih => cases a <;> simp_all [labelList, labelSupport]
  | _ => simp_all [labelList, labelSupport]

def indexedGuardRequirements {Label : Type} (k : Nat) :
    Formula (RecordedHead Nat Label) → GuardRequirements Label
  | .falsum => ([], [])
  | .equal _ _ => ([], [])
  | .imp φ ψ => GuardRequirements.append (φ.indexedGuardRequirements k) (ψ.indexedGuardRequirements k)
  | .conj φ ψ => GuardRequirements.append (φ.indexedGuardRequirements k) (ψ.indexedGuardRequirements k)
  | .disj φ ψ => GuardRequirements.append (φ.indexedGuardRequirements k) (ψ.indexedGuardRequirements k)
  | .neg φ => φ.indexedGuardRequirements k
  | .all _ φ => φ.indexedGuardRequirements k
  | .ex _ φ => φ.indexedGuardRequirements k
  | .know (.live _) φ => φ.indexedGuardRequirements k
  | .know (.ghost _) φ => φ.indexedGuardRequirements k
  | .know (.indexed _ ν) φ =>
      let p := φ.indexedGuardRequirements k
      ((k, ν) :: p.1, (φ.labelList.map (fun μ => (μ, ν))) ++ p.2)

theorem indexedGuardRequirements_exact {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (k : Nat)
    (φ : Formula (RecordedHead Nat Label)) :
    GuardRequirements.Holds R₁ R₂ B (φ.indexedGuardRequirements k) ↔
      φ.IndexedGuarded R₁ R₂ B k := by
  induction φ with
  | know a φ ih =>
    cases a with
    | live a => exact ih
    | ghost a => exact ih
    | indexed a ν =>
      simp only [indexedGuardRequirements, GuardRequirements.holds_indexed,
        mem_labelList_iff, IndexedGuarded]
      exact and_congr Iff.rfl (and_congr Iff.rfl ih)
  | _ => simp_all [indexedGuardRequirements, IndexedGuarded]

def mainGuardRequirements {Label : Type} [DecidableEq Label] (E : Finset Nat) :
    Formula (RecordedHead Nat Label) → GuardRequirements Label
  | .falsum => ([], [])
  | .equal _ _ => ([], [])
  | .imp φ ψ => GuardRequirements.append (φ.mainGuardRequirements E) (ψ.mainGuardRequirements E)
  | .conj φ ψ => GuardRequirements.append (φ.mainGuardRequirements E) (ψ.mainGuardRequirements E)
  | .disj φ ψ => GuardRequirements.append (φ.mainGuardRequirements E) (ψ.mainGuardRequirements E)
  | .neg φ => φ.mainGuardRequirements E
  | .all _ φ => φ.mainGuardRequirements E
  | .ex _ φ => φ.mainGuardRequirements E
  | .know (.indexed _ _) φ => φ.mainGuardRequirements E
  | .know (.ghost _) φ => φ.mainGuardRequirements E
  | .know (.live e) φ =>
      if e ∈ E then GuardRequirements.append (φ.indexedGuardRequirements φ.erase.shape.rank)
        (φ.mainGuardRequirements E) else φ.mainGuardRequirements E

theorem mainGuardRequirements_exact {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (E : Finset Nat) (B : Finset Label)
    (φ : Formula (RecordedHead Nat Label)) :
    GuardRequirements.Holds R₁ R₂ B (φ.mainGuardRequirements E) ↔
      φ.MainGuarded R₁ R₂ E B := by
  induction φ with
  | know a φ ih =>
    cases a with
    | live e => by_cases he : e ∈ E <;>
        simp [mainGuardRequirements, MainGuarded, he, indexedGuardRequirements_exact, ih]
    | ghost e => exact ih
    | indexed a ν => exact ih
  | _ => simp_all [mainGuardRequirements, MainGuarded]

end Formula
end Alexander313
