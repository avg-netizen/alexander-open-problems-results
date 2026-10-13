import Alexander313.Wilken.AdditiveNormalForm
import Alexander313.Wilken.AdmissibleTerms

/-!
# Hull closure under canonical additive principal components

Wilken Lemma 2.3(c) is proved for the actual constructed finite collapsing
family. No normal-form closure hypothesis is supplied to the hull. The
addition case uses the absorption theorem for the canonical decomposition;
collapsing outputs have singleton ANF because the constructed minima are
positive additive principal ordinals.

The base hypothesis `0 < τ` ensures that the empty sum belongs to the
hull. It holds at each source base τ ∈ {1} ∪ E. It is weaker than the
source-base condition, without extending later source theorems to such
bases. This module is a candidate proof draft, not externally compiled.
-/

namespace Alexander313.Wilken

/-- Hull addition evaluates any finite list whose entries belong to it. -/
theorem hull_principalSum {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α β : Ordinal}
    (hz : Hull omega theta n m α β 0) (xs : List Ordinal)
    (hxs : ∀ a ∈ xs, Hull omega theta n m α β a) :
    Hull omega theta n m α β (principalSum xs) := by
  revert hxs
  induction xs with
  | nil => intro _; exact hz
  | cons a xs ih =>
    intro hxs
    exact .add (hxs a (List.mem_cons_self))
      (ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb)))

theorem source_hull_zero (τ : Ordinal) (hτ : 0 < τ) (n m : Nat) (α β : Ordinal) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β 0 :=
  .below_base (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m)))

/-- Forward direction of Lemma 2.3(c), with actual canonical components. -/
theorem source_hull_canonicalANF (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal) {ξ : Ordinal}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ) :
    ∀ a ∈ canonicalANF ξ,
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β a := by
  induction hξ with
  | below_base hξ =>
    intro a ha
    exact .below_base ((canonicalANF_mem_le ha).trans_lt hξ)
  | below_parameter hξ =>
    intro a ha
    exact .below_parameter ((canonicalANF_mem_le ha).trans_lt hξ)
  | add hξ hη ihξ ihη =>
    intro a ha
    exact (canonicalANF_add_mem ha).elim (ihξ a) (ihη a)
  | @higher k ξ hmk hkn hsort hξ ih =>
    intro a ha
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n k hkn ξ)
      (sourceFiniteCollapse_add_closed τ n k hkn ξ)
    rw [hanf, List.mem_singleton] at ha
    subst a
    exact .higher hmk hkn hsort hξ
  | @«local» ξ hsort hξ ih =>
    intro a ha
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n m hm ξ)
      (sourceFiniteCollapse_add_closed τ n m hm ξ)
    rw [hanf, List.mem_singleton] at ha
    subst a
    exact .«local» hsort hξ

/-- The actual Lemma 2.3(c). The endpoint versions also hold because the
proof uses the inductive hull rules and imposes no strict endpoint bound. -/
theorem source_hull_iff_canonicalANF (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β ξ : Ordinal) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      ∀ a ∈ canonicalANF ξ,
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β a := by
  constructor
  · exact source_hull_canonicalANF τ hτ n m hm α β
  · intro h
    rw [← principalSum_canonicalANF ξ]
    exact hull_principalSum (source_hull_zero τ hτ n m α β) _ h

/-- The formulation with any written ANF is independent of its spelling
because ordered positive principal decompositions are unique. -/
theorem source_hull_iff_additiveNormalForm (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β ξ : Ordinal) (xs : List Ordinal)
    (hxs : IsAdditiveNormalForm xs) (heq : principalSum xs = ξ) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      ∀ a ∈ xs, Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β a := by
  rw [source_hull_iff_canonicalANF τ hτ n m hm α β ξ,
    canonicalANF_eq_of_normal hxs heq]

/-- The finite source domain itself contains every canonical principal
component of each of its elements. -/
theorem sourceNotation_canonicalANF (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {ξ a : Ordinal}
    (hξ : sourceNotation τ n m ξ) (ha : a ∈ canonicalANF ξ) :
    sourceNotation τ n m a := by
  apply (sourceNotation_iff_hull τ n m hm a).mpr
  exact source_hull_canonicalANF τ hτ n m hm _ _
    ((sourceNotation_iff_hull τ n m hm ξ).mp hξ) a ha

/-- At the terminal source domain Tⁿₙ=Ωₙ, canonical components remain
below its parameter bound. -/
theorem sourceNotation_terminal_canonicalANF (τ : Ordinal) (n : Nat) {ξ a : Ordinal}
    (hξ : sourceNotation τ n n ξ) (ha : a ∈ canonicalANF ξ) :
    sourceNotation τ n n a := by
  simp only [sourceNotation, lt_self_iff_false, if_false] at hξ ⊢
  exact (canonicalANF_mem_le ha).trans_lt hξ

/-- Each canonical principal component of an admissible raw term has an
actual admissible relative term. This existence result does not collect
raw leaves or assert uniqueness of the original tree. -/
theorem sourceRelativeTerm_canonical_components (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (t : SourceRelativeTerm τ m)
    (ht : RelativeTerm.Admissible (sourceParameters τ m) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n m t) {a : Ordinal.{0}}
    (ha : a ∈ canonicalANF (t.eval (sourceParameters τ m) (sourceFiniteCollapse τ n))) :
    ∃ s : SourceRelativeTerm τ m,
      RelativeTerm.Admissible (sourceParameters τ m) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n m s ∧
      s.eval (sourceParameters τ m) (sourceFiniteCollapse τ n) = a := by
  apply (sourceNotation_iff_relativeTerm τ n m hm a).mp
  apply sourceNotation_canonicalANF τ hτ n m hm _ ha
  rw [sourceNotation, if_pos hm]
  exact ht.denote

end Alexander313.Wilken
