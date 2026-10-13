import Alexander313.Wilken.HereditarySourceUpsilonEpsilon
import Alexander313.Wilken.PublicEpsilonSourceDictionary
import Mathlib.Data.Prod.Lex

/-!
# Actual upsilon segmentation on the canonical public domain

Definition 3.23 minimizes the pair (lambda,m) lexicographically among zero
or limit lambda and finite m with alpha < upsilon(lambda+m+1). The genuine
finite endpoint scan constructs that exact least pair for every admitted
canonical public value, including zero and non-epsilons. Actual ordinal
upsilon values, rather than a finite surrogate image, define the candidates.
The computed pair is (0,level); every purported earlier finite candidate is
excluded by the actual unsuccessful endpoint tests. No assignment of ts,
transfinite coding or cross-context mu is asserted. Uncompiled candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicUpsilonSegment

abbrev Segment := Ordinal.{0} × Nat

def Candidate (alpha : Ordinal.{0}) (segment : Segment) : Prop :=
  (segment.1 = 0 ∨ Order.IsSuccLimit segment.1) ∧
    alpha < sourceUpsilon (segment.1 + ((segment.2 + 1 : Nat) : Ordinal.{0}))

def FirstSegment (alpha : Ordinal.{0}) (segment : Segment) : Prop :=
  Candidate alpha segment ∧ ∀ earlier : Segment,
    Prod.Lex (· < ·) (· < ·) earlier segment → ¬ Candidate alpha earlier

def segmentCode (q : Nat) : Nat × Nat := (0, PublicEpsilonSourceDictionary.level q)

theorem segmentCode_primrec : Primrec segmentCode :=
  (Primrec.const 0).pair PublicEpsilonSourceDictionary.level_primrec

def segmentValue (q : Nat) : Segment := (0, PublicEpsilonSourceDictionary.level q)

theorem successor_value (n : Nat) :
    sourceUpsilon ((n + 1 : Nat) : Ordinal.{0}) = finiteBase (n + 1) :=
  (sourceUpsilon_nat (n + 1)).trans (sourceUpsilonFinite_eq_finiteBase_succ n)

theorem segmentValue_candidate (q : Nat) (hq : Canonical.check q = true) :
    Candidate (unionInterpretation q) (segmentValue q) := by
  refine ⟨Or.inl rfl, ?_⟩
  change unionInterpretation q <
    sourceUpsilon (0 + ((PublicEpsilonSourceDictionary.level q + 1 : Nat) : Ordinal.{0}))
  rw [zero_add, successor_value]
  exact (PublicEpsilonSourceDictionary.level_bound q hq).2.1

/-- The actual selected segment contains the original public value; the
zero indexing endpoint is retained even for values below one. -/
theorem segmentValue_interval (q : Nat) (hq : Canonical.check q = true) :
    sourceUpsilon ((PublicEpsilonSourceDictionary.level q : Nat) : Ordinal.{0}) ≤
      unionInterpretation q ∧ unionInterpretation q <
        sourceUpsilon ((PublicEpsilonSourceDictionary.level q + 1 : Nat) : Ordinal.{0}) := by
  have hs := PublicEpsilonSourceDictionary.level_bound q hq
  refine ⟨?_, ?_⟩
  · cases hm : PublicEpsilonSourceDictionary.level q with
    | zero => simpa only [hm, Nat.cast_zero, sourceUpsilon_zero] using
        (bot_le : (0 : Ordinal.{0}) ≤ unionInterpretation q)
    | succ m =>
      have hlt : m < PublicEpsilonSourceDictionary.level q := by
        rw [hm]; exact Nat.lt_succ_self m
      simpa only [hm, successor_value] using hs.2.2 m hlt
  · simpa only [successor_value] using hs.2.1

/-- The genuine scan failures exclude every lexicographically earlier
candidate; no numerical stored-level minimality is assumed. -/
theorem segmentValue_first (q : Nat) (hq : Canonical.check q = true) :
    FirstSegment (unionInterpretation q) (segmentValue q) := by
  refine ⟨segmentValue_candidate q hq, ?_⟩
  intro earlier hlex hc
  have he : earlier.1 < 0 ∨ earlier.1 = 0 ∧
      earlier.2 < PublicEpsilonSourceDictionary.level q := by
    simpa only [segmentValue] using (Prod.lex_def.mp hlex)
  rcases he with hnegative | ⟨hzero, hindex⟩
  · exact (not_lt_of_ge (bot_le : (0 : Ordinal.{0}) ≤ earlier.1)) hnegative
  · have hupper : unionInterpretation q < finiteBase (earlier.2 + 1) := by
      simpa only [Candidate, hzero, zero_add, successor_value] using hc.2
    exact hupper.not_ge ((PublicEpsilonSourceDictionary.level_bound q hq).2.2 earlier.2 hindex)

/-- Any genuine lex-minimal pair on the original public value is the actual
computed finite pair, including its zero limit coordinate. -/
theorem firstSegment_unique (q : Nat) (hq : Canonical.check q = true) (segment : Segment)
    (hs : FirstSegment (unionInterpretation q) segment) : segment = segmentValue q := by
  have hc := segmentValue_candidate q hq
  have hfirst := segmentValue_first q hq
  have hzero : segment.1 = 0 := by
    by_contra hn
    have hp : 0 < segment.1 := lt_of_le_of_ne bot_le (Ne.symm hn)
    have hlex : Prod.Lex (· < ·) (· < ·) (segmentValue q) segment :=
      Prod.lex_def.mpr (Or.inl hp)
    exact hs.2 _ hlex hc
  have hindex : segment.2 = PublicEpsilonSourceDictionary.level q := by
    rcases lt_trichotomy segment.2 (PublicEpsilonSourceDictionary.level q) with hl | he | hg
    · have hlex : Prod.Lex (· < ·) (· < ·) segment (segmentValue q) :=
        Prod.lex_def.mpr (Or.inr ⟨hzero, hl⟩)
      exact False.elim (hfirst.2 _ hlex hs.1)
    · exact he
    · have hlex : Prod.Lex (· < ·) (· < ·) (segmentValue q) segment :=
        Prod.lex_def.mpr (Or.inr ⟨hzero.symm, hg⟩)
      exact False.elim (hs.2 _ hlex hc)
  exact Prod.ext hzero hindex

theorem segmentCode_value (q : Nat) :
    ((segmentCode q).1 : Ordinal.{0}) = (segmentValue q).1 ∧
      (segmentCode q).2 = (segmentValue q).2 := by
  simp only [segmentCode, segmentValue, Nat.cast_zero, and_self]

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicUpsilonSegment
