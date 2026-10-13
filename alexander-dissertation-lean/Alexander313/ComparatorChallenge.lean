import Alexander313.Specification

/-!
# Independent comparator targets

Only the statement definitions are imported. No solution or soundness
assembly is imported. Each target asks for one effective original-language
family for an arbitrary recursively enumerable well-founded hierarchy,
and quantifies over unrestricted formulas, including self-occurrences.

These are propositions, not proofs. Source equivalence remains subject to
comparison, especially arithmetic coding and weak-modal admissibility.
-/

namespace Alexander313.Comparator

def challenge311 : Prop :=
  ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R → Nonempty (Solution311 R)

def challenge312 : Prop :=
  ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R → Nonempty (Solution312 R)

def challenge313 : Prop :=
  ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R → Nonempty (Solution313 R)

end Alexander313.Comparator
