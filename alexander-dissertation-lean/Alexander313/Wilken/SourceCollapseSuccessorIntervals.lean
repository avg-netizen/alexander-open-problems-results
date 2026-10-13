import Alexander313.Wilken.SourceCollapseSuccessors

/-!
# Actual source successors inside adjacent collapse intervals

If theta(b) lies strictly between theta(a) and theta(a+1), the genuine
source comparison forces b<a. The real argument-star bound for b+1 is
at most theta(b), so the actual comparison also puts theta(b+1) strictly
below theta(a+1). This uses the original source family throughout.

These are finite and direct-limit constructions. They do not assert the
mu interval hypothesis, source base conversion, or a successor bound for
arbitrary values below theta(a+1). Uncompiled source candidates.
-/

namespace Alexander313.Wilken.SourceCollapseSuccessorIntervals

open SourceCollapseSuccessors

/-- A smaller original argument and the actual value bound suffice for
its genuine source successor to remain below the original endpoint. -/
theorem successor_lt_endpoint_of_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hba : b.val < a.val)
    (hbs : sourceFiniteCollapse τ n m b.val < sourceFiniteCollapse τ n m (a.val + 1)) :
    sourceFiniteCollapse τ n m (b.val + 1) < sourceFiniteCollapse τ n m (a.val + 1) := by
  have has : (succArgument τ hτ n m hm a).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  have hbsort : (succArgument τ hτ n m hm b).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt hb
  apply (sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm
    (succArgument τ hτ n m hm b) (succArgument τ hτ n m hm a) hbsort has).mpr
  exact Or.inl ⟨(Order.add_one_le_of_lt hba).trans_lt (lt_add_one a.val),
    (successor_star_le τ hτ n m hm b hb).trans_lt hbs⟩

/-- The whole original adjacent interval is closed under this actual
source successor operation. No argument-descent premise is supplied. -/
theorem adjacent_successor_lt_endpoint (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hab : sourceFiniteCollapse τ n m a.val < sourceFiniteCollapse τ n m b.val)
    (hbs : sourceFiniteCollapse τ n m b.val < sourceFiniteCollapse τ n m (a.val + 1)) :
    sourceFiniteCollapse τ n m (b.val + 1) < sourceFiniteCollapse τ n m (a.val + 1) :=
  successor_lt_endpoint_of_argument_lt τ hτ n m hm a b ha hb
    (adjacent_argument_lt τ hτ n m hm a b ha hb hab hbs) hbs

/-- The same source successor construction in the genuine global family;
its star is the actual canonical direct-limit star. -/
theorem global_successor_lt_endpoint_of_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a b : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hba : b.val < a.val)
    (hbs : globalCollapse τ m b.val < globalCollapse τ m (a.val + 1)) :
    globalCollapse τ m (b.val + 1) < globalCollapse τ m (a.val + 1) := by
  have has : (globalSuccArgument τ hτ m a).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  have hbsort : (globalSuccArgument τ hτ m b).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt hb
  apply (globalCollapse_lt_iff_globalStar τ hτ m
    (globalSuccArgument τ hτ m b) (globalSuccArgument τ hτ m a) hbsort has).mpr
  exact Or.inl ⟨(Order.add_one_le_of_lt hba).trans_lt (lt_add_one a.val),
    (global_successor_star_le τ hτ m b hb).trans_lt hbs⟩

/-- Every genuine global theta value in the adjacent interval has its
original-context Convention 2.28 successor strictly below the endpoint. -/
theorem global_adjacent_successor_lt_endpoint (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a b : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hab : globalCollapse τ m a.val < globalCollapse τ m b.val)
    (hbs : globalCollapse τ m b.val < globalCollapse τ m (a.val + 1)) :
    globalCollapse τ m (b.val + 1) < globalCollapse τ m (a.val + 1) :=
  global_successor_lt_endpoint_of_argument_lt τ hτ m a b ha hb
    (global_adjacent_argument_lt τ hτ m a b ha hb hab hbs) hbs

end Alexander313.Wilken.SourceCollapseSuccessorIntervals
