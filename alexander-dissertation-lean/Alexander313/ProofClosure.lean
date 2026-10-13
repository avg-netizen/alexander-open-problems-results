import Alexander313.Quantifiers

/-!
# Finite consequence closure and knowledge of consequences

This is the finite-certificate proof of the own-necessity lemma in the
3-1-1 hand proof §2. Knowledge is obtained using admitted own prefixes,
known validity and deduction; it is not a new global necessitation rule.
-/

namespace Alexander313

theorem chain_intro {Owner D : Type} (M : ModalModel Owner D)
    (Γ : List (Formula Owner)) (φ : Formula Owner) (s : Nat → D) :
    ((∀ θ ∈ Γ, generalTruth M θ s) → generalTruth M φ s) →
      generalTruth M (Formula.chain Γ φ) s := by
  induction Γ with
  | nil =>
    intro h
    apply h
    intro θ hθ
    cases hθ
  | cons θ Γ ih =>
    intro h hθ
    apply ih
    intro hΓ
    apply h
    intro η hη
    rcases List.mem_cons.mp hη with rfl | hη
    · exact hθ
    · exact hΓ η hη

theorem Provable.of_axiom {Owner : Type} {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (hφ : axioms φ) : Provable axioms φ := by
  refine ⟨{ premises := [φ], admitted := ?_, validity := ?_ }⟩
  · intro θ hθ
    have heq := List.mem_singleton.mp hθ
    simpa only [heq] using hφ
  · intro D hD M s h
    exact h

theorem Provable.of_valid {Owner : Type} {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (hφ : Valid φ) : Provable axioms φ := by
  exact ⟨{ premises := [], admitted := fun _ h => False.elim (List.not_mem_nil h),
           validity := hφ }⟩

theorem Provable.mono {Owner : Type} {axioms other : Formula Owner → Prop}
    {φ : Formula Owner} (h : Provable axioms φ)
    (ha : ∀ θ, axioms θ → other θ) : Provable other φ := by
  obtain ⟨c⟩ := h
  exact ⟨{ premises := c.premises, admitted := fun θ hθ => ha θ (c.admitted θ hθ),
           validity := c.validity }⟩

theorem Provable.modus_ponens {Owner : Type} {axioms : Formula Owner → Prop}
    {φ ψ : Formula Owner} (himp : Provable axioms (.imp φ ψ))
    (hφ : Provable axioms φ) : Provable axioms ψ := by
  obtain ⟨ci⟩ := himp
  obtain ⟨cp⟩ := hφ
  refine ⟨{ premises := ci.premises ++ cp.premises, admitted := ?_, validity := ?_ }⟩
  · intro θ hθ
    rcases List.mem_append.mp hθ with hi | hp
    · exact ci.admitted θ hi
    · exact cp.admitted θ hp
  · intro D hD M s
    apply chain_intro
    intro hΓ
    have hi := chain_elim M ci.premises (.imp φ ψ) s
      (fun θ hθ => hΓ θ (List.mem_append_left _ hθ)) (ci.validity D hD M s)
    have hp := chain_elim M cp.premises φ s
      (fun θ hθ => hΓ θ (List.mem_append_right _ hθ)) (cp.validity D hD M s)
    exact hi hp

theorem MachineFamily.modus_ponens (F : MachineFamily) (i : Nat)
    {φ ψ : Formula Nat} (himp : F.effective.proves i (.imp φ ψ))
    (hφ : F.effective.proves i φ) : F.effective.proves i ψ := by
  have hc : φ.Closed ∧ ψ.Closed := by
    simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using
      F.sentences i _ himp
  apply (F.theory_closed i ψ hc.2).mp
  exact Provable.modus_ponens (Provable.of_axiom himp) (Provable.of_axiom hφ)

theorem knowledge_of_certificate {Owner : Type} (P : Formula Owner → Prop) (i : Owner)
    (mp : ∀ θ η, P (.imp θ η) → P θ → P η)
    {axioms : Formula Owner → Prop} {φ : Formula Owner} (c : Certificate axioms φ)
    (hφ : φ.Closed)
    (axioms_closed : ∀ θ, axioms θ → θ.Closed)
    (known_axioms : ∀ θ, axioms θ → P (.know i θ))
    (known_validity : ∀ θ, Valid θ → θ.Closed → P (.know i θ))
    (reasoning : ∀ θ η, θ.Closed → η.Closed → P
      (.imp (.know i (.imp θ η)) (.imp (.know i θ) (.know i η)))) :
    P (.know i φ) := by
  have hΓ : ∀ θ ∈ c.premises, θ.Closed := fun θ hθ => axioms_closed θ (c.admitted θ hθ)
  have start := known_validity _ c.validity (Formula.chain_closed _ _ hΓ hφ)
  have distribute : ∀ Γ : List (Formula Owner),
      (∀ θ ∈ Γ, θ.Closed) → P (.know i (Formula.chain Γ φ)) →
      (∀ θ ∈ Γ, P (.know i θ)) → P (.know i φ) := by
    intro Γ
    induction Γ with
    | nil => intro _ h _; exact h
    | cons θ Γ ih =>
      intro hclosed hchain hknown
      have hθ := hclosed θ List.mem_cons_self
      have htail : ∀ η ∈ Γ, η.Closed := fun η hη => hclosed η (List.mem_cons_of_mem _ hη)
      have hd := reasoning θ (Formula.chain Γ φ) hθ (Formula.chain_closed _ _ htail hφ)
      have hrest := mp _ _ (mp _ _ hd hchain)
        (hknown θ List.mem_cons_self)
      exact ih htail hrest (fun η hη => hknown η (List.mem_cons_of_mem _ hη))
  exact distribute c.premises hΓ start (fun θ hθ => known_axioms θ (c.admitted θ hθ))

theorem MachineFamily.knowledge_of_certificate (F : MachineFamily) (i : Nat)
    {axioms : Formula Nat → Prop} {φ : Formula Nat} (c : Certificate axioms φ)
    (hφ : φ.Closed)
    (axioms_closed : ∀ θ, axioms θ → θ.Closed)
    (known_axioms : ∀ θ, axioms θ → F.effective.proves i (.know i θ))
    (known_validity : ∀ θ, Valid θ → θ.Closed → F.effective.proves i (.know i θ))
    (reasoning : ∀ θ η, θ.Closed → η.Closed → F.effective.proves i
      (.imp (.know i (.imp θ η)) (.imp (.know i θ) (.know i η)))) :
    F.effective.proves i (.know i φ) :=
  Alexander313.knowledge_of_certificate (F.effective.proves i) i
    (fun θ η hi ht => F.modus_ponens i hi ht)
    c hφ axioms_closed known_axioms known_validity reasoning

end Alexander313
