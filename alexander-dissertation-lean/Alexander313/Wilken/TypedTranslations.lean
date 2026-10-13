import Alexander313.Computability
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Typed computable partial conversions

Contracts must be implemented by the source algorithms. The composition
lemma keeps the domain of each actual caller explicit and composes real
partial-recursive programs. It never postulates an arbitrary total cast.
-/

namespace Alexander313.Wilken

structure Representation where
  valid : Nat → Prop
  denote : Nat → Ordinal

structure PartialTranslation (A B : Representation) (allowed : Nat → Prop) where
  implementation : Program
  complete : ∀ n, A.valid n → allowed n → ∃ q, q ∈ implementation.eval n
  correct : ∀ n q, q ∈ implementation.eval n →
    A.valid n ∧ allowed n ∧ B.valid q ∧ A.denote n = B.denote q

theorem partial_translations_compose (A B C : Representation)
    (firstDomain secondDomain : Nat → Prop)
    (first : PartialTranslation A B firstDomain)
    (second : PartialTranslation B C secondDomain)
    (caller_bound : ∀ n q, q ∈ first.implementation.eval n → secondDomain q)
    (n : Nat) (hn : A.valid n) (hd : firstDomain n) :
    ∃ q, q ∈ (Nat.Partrec.Code.comp second.implementation first.implementation).eval n ∧
      C.valid q ∧ A.denote n = C.denote q := by
  obtain ⟨p, hp⟩ := first.complete n hn hd
  have first_ok := first.correct n p hp
  obtain ⟨q, hq⟩ := second.complete p first_ok.2.2.1 (caller_bound n p hp)
  have second_ok := second.correct p q hq
  refine ⟨q, ?_, second_ok.2.2.1, first_ok.2.2.2.trans second_ok.2.2.2⟩
  change q ∈ (first.implementation.eval n).bind (second.implementation.eval)
  exact Part.mem_bind_iff.mpr ⟨p, hp, hq⟩

end Alexander313.Wilken
