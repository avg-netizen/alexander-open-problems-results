import Alexander313.Carlson.GeneratingSequenceCovering
import Alexander313.Carlson.FiniteRelabeling
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Equiv.Finset

/-!
# Fair generating sequences on rational labels

Carlson, *Patterns of resemblance of order 2*, Definition 14.7,
printed p. 60 of the author's October 16, 2008 manuscript:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf.

Every rational pattern starts a fair sequence of generating rules. At the
stage indexed by `Nat.pair n e`, the construction considers the finite
rational presentation with code `e` as an extension of stage `n`. If it is
a generating rule, a minimal lifting realizes it over the current stage;
otherwise the next step is the identity rule. Pairing ensures that the
requested source stage already exists.

Finite relation tables, rather than arbitrary predicates on all rationals,
make the family of requests countable. Identity isomorphisms transfer the
result back to every presentation, including arbitrary off-carrier values.

This is a classical existence theorem: deciding whether a requested rule
holds and choosing a lifting use classical choice. No computability of the
resulting sequence, ordinal core realization, or finite tallness is asserted.
-/

noncomputable section

namespace Alexander313.Carlson

namespace PatternLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Changing only the off-carrier presentation of the extended source
preserves a lifting, with the same base, target and total maps. -/
theorem of_source_identity_iso {P A A' : Str α} {Q B : Str β}
    {h f : α → β} (D : PatternLifting P A Q B h f)
    (e : Str.IsIso A' A id) : PatternLifting P A' Q B h f := by
  refine
    { source_pattern := e.symm_id.isPattern D.source_pattern
      target_pattern := D.target_pattern
      source_sub := D.source_sub.trans e.symm_id.isSub_of_id
      target_sub := D.target_sub
      arithmetic := ?_
      relations := ?_ }
  · simpa only [e.universe_eq_of_id] using D.arithmetic
  · intro x hx y hy
    have he := e.2.2 x hx y hy
    have hD := D.relations x (e.mem hx) y (e.mem hy)
    exact ⟨he.1.trans hD.1, he.2.trans hD.2⟩

end PatternLifting

namespace GeneratingSequence

variable {α : Type*} [LinearOrder α]

/-- Definition 14.7: every generating rule from an earlier stage is
eventually lifted over a later stage along the inclusion. -/
def Fair (S : GeneratingSequence α) : Prop :=
  ∀ n (Q : Str α), Str.GeneratingRule (S.stage n) Q →
    ∃ k, n ≤ k ∧ ∃ f : α → α,
      PatternLifting (S.stage n) Q (S.stage k) (S.stage (k + 1)) id f

/-- Every requested rule embeds exactly into the union of a fair
sequence, fixing its old source pointwise. Both relations are reflected
as well as preserved. -/
theorem Fair.realizes {S : GeneratingSequence α} (hS : S.Fair)
    (n : ℕ) (Q : Str α) (hQ : Str.GeneratingRule (S.stage n) Q) :
    ∃ f : α → α,
      (∀ x ∈ Q.U, f x ∈ S.carrier) ∧
      (∀ x ∈ (S.stage n).U, f x = x) ∧
      (∀ x ∈ Q.U, ∀ y ∈ Q.U, x < y → f x < f y) ∧
      ∀ x ∈ Q.U, ∀ y ∈ Q.U,
        (Q.r₁ x y ↔ S.rel .one (f x) (f y)) ∧
        (Q.r₂ x y ↔ S.rel .two (f x) (f y)) := by
  obtain ⟨k, _, f, L⟩ := hS n Q hQ
  refine ⟨f, fun x hx => S.mem_carrier (k + 1) (L.arithmetic.mem x hx),
    L.arithmetic.agrees, L.arithmetic.mono, ?_⟩
  intro x hx y hy
  have hr := L.relations x hx y hy
  exact ⟨hr.1.trans (S.rel_iff (k + 1) (L.arithmetic.mem x hx)
    (L.arithmetic.mem y hy) .one).symm,
    hr.2.trans (S.rel_iff (k + 1) (L.arithmetic.mem x hx)
    (L.arithmetic.mem y hy) .two).symm⟩

/-- The constant generating sequence at a pattern. -/
def constant (P : Str α) (hP : P.IsPattern) : GeneratingSequence α where
  stage := fun _ => P
  step := fun _ => Str.GeneratingRule.refl hP

/-- Replace the tail after stage `k` by one new generating step followed
by identity steps. Earlier stages are preserved exactly. -/
def extendAt (S : GeneratingSequence α) (k : ℕ) (Q : Str α)
    (hQ : Str.GeneratingRule (S.stage k) Q) : GeneratingSequence α where
  stage n := if n ≤ k then S.stage n else Q
  step n := by
    by_cases hnk : n < k
    · have hn : n ≤ k := hnk.le
      have hs : n + 1 ≤ k := hnk
      simpa only [if_pos hn, if_pos hs] using S.step n
    · by_cases heq : n = k
      · subst n
        simpa only [le_refl, if_true, Nat.not_succ_le_self, if_false] using hQ
      · have hn : ¬ n ≤ k := by omega
        have hs : ¬ n + 1 ≤ k := by omega
        simpa only [if_neg hn, if_neg hs] using Str.GeneratingRule.refl hQ.target_pattern

@[simp] theorem extendAt_stage_le (S : GeneratingSequence α) (k : ℕ) (Q : Str α)
    (hQ : Str.GeneratingRule (S.stage k) Q) {n : ℕ} (hn : n ≤ k) :
    (S.extendAt k Q hQ).stage n = S.stage n := by
  simp only [extendAt, if_pos hn]

@[simp] theorem extendAt_stage_succ (S : GeneratingSequence α) (k : ℕ) (Q : Str α)
    (hQ : Str.GeneratingRule (S.stage k) Q) :
    (S.extendAt k Q hQ).stage (k + 1) = Q := by
  simp only [extendAt, Nat.not_succ_le_self, if_false]

private abbrev RationalPresentation :=
  Finset ℚ × Finset (ℚ × ℚ) × Finset (ℚ × ℚ)

private def present (c : RationalPresentation) : Str ℚ :=
  ⟨c.1, fun x y => (x, y) ∈ c.2.1, fun x y => (x, y) ∈ c.2.2⟩

private def presentation (P : Str ℚ) : RationalPresentation := by
  classical
  exact (P.U, (P.U ×ˢ P.U).filter (fun xy => P.r₁ xy.1 xy.2),
    (P.U ×ˢ P.U).filter (fun xy => P.r₂ xy.1 xy.2))

private theorem presentation_iso (P : Str ℚ) :
    Str.IsIso P (present (presentation P)) id := by
  refine ⟨Finset.image_id, fun _ _ _ _ h => h, ?_⟩
  intro x hx y hy
  simp only [present, presentation, id_eq, Finset.mem_filter, Finset.mem_product, hx, hy,
    true_and]

private def request (e : ℕ) : Str ℚ :=
  present ((Encodable.decode (α := RationalPresentation) e).getD (∅, ∅, ∅))

private theorem request_encode (P : Str ℚ) :
    request (Encodable.encode (presentation P)) = present (presentation P) := by
  simp only [request, Encodable.encodek, Option.getD_some]

private structure NextStage (S : GeneratingSequence ℚ) (k : ℕ) where
  target : Str ℚ
  rule : Str.GeneratingRule (S.stage k) target
  realizes : Str.GeneratingRule (S.stage (Nat.unpair k).1) (request (Nat.unpair k).2) →
    ∃ f : ℚ → ℚ, PatternLifting (S.stage (Nat.unpair k).1) (request (Nat.unpair k).2)
      (S.stage k) target id f

private def nextStage (S : GeneratingSequence ℚ) (k : ℕ) : NextStage S k := by
  classical
  by_cases hd : Str.GeneratingRule (S.stage (Nat.unpair k).1) (request (Nat.unpair k).2)
  · have hE := (S.continuous (Nat.unpair_left_le k)).inclusionEmbedding
    have hex := hd.exists_lifting_rat (S.pattern k) hE
    let Q := Classical.choose hex
    have hf := Classical.choose_spec hex
    let f := Classical.choose hf
    have hL := Classical.choose_spec hf
    exact ⟨Q, hL.2.2, fun _ => ⟨f, hL.1⟩⟩
  · exact ⟨S.stage k, Str.GeneratingRule.refl (S.pattern k), fun h => (hd h).elim⟩

private def approximation (P : Str ℚ) (hP : P.IsPattern) : ℕ → GeneratingSequence ℚ
  | 0 => constant P hP
  | k + 1 =>
      let S := approximation P hP k
      let N := nextStage S k
      S.extendAt k N.target N.rule

private theorem approximation_succ_agrees (P : Str ℚ) (hP : P.IsPattern)
    (k : ℕ) {n : ℕ} (hn : n ≤ k) :
    (approximation P hP (k + 1)).stage n = (approximation P hP k).stage n := by
  exact extendAt_stage_le (approximation P hP k) k
    (nextStage (approximation P hP k) k).target
    (nextStage (approximation P hP k) k).rule hn

private theorem approximation_agrees (P : Str ℚ) (hP : P.IsPattern)
    {k l n : ℕ} (hn : n ≤ k) (hkl : k ≤ l) :
    (approximation P hP l).stage n = (approximation P hP k).stage n := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
      exact (approximation_succ_agrees P hP l (hn.trans hkl)).trans ih

private def fairConstruction (P : Str ℚ) (hP : P.IsPattern) : GeneratingSequence ℚ where
  stage n := (approximation P hP n).stage n
  step n := by
    have hs := (approximation P hP (n + 1)).step n
    rw [approximation_succ_agrees P hP n le_rfl] at hs
    exact hs

private theorem fairConstruction_agrees (P : Str ℚ) (hP : P.IsPattern)
    {n k : ℕ} (hn : n ≤ k) :
    (fairConstruction P hP).stage n = (approximation P hP k).stage n :=
  (approximation_agrees P hP le_rfl hn).symm

private theorem fairConstruction_next (P : Str ℚ) (hP : P.IsPattern) (k : ℕ) :
    (fairConstruction P hP).stage (k + 1) =
      (nextStage (approximation P hP k) k).target := by
  exact extendAt_stage_succ (approximation P hP k) k
    (nextStage (approximation P hP k) k).target
    (nextStage (approximation P hP k) k).rule

private theorem fairConstruction_fair (P : Str ℚ) (hP : P.IsPattern) :
    (fairConstruction P hP).Fair := by
  intro n Q hQ
  let e := Encodable.encode (presentation Q)
  let k := Nat.pair n e
  have hnk : n ≤ k := Nat.left_le_pair n e
  have hn : (Nat.unpair k).1 = n := by simp only [k, Nat.unpair_pair]
  have he : request (Nat.unpair k).2 = present (presentation Q) := by
    simpa only [k, Nat.unpair_pair] using request_encode Q
  have hr : Str.GeneratingRule
      ((approximation P hP k).stage (Nat.unpair k).1) (request (Nat.unpair k).2) := by
    rw [hn, he, ← fairConstruction_agrees P hP hnk]
    exact hQ.of_isIso (Str.IsIso.refl _) (presentation_iso Q) (fun _ _ => rfl)
  obtain ⟨f, L⟩ := (nextStage (approximation P hP k) k).realizes hr
  rw [hn, he, ← fairConstruction_agrees P hP hnk,
    ← fairConstruction_agrees P hP (k := k) le_rfl,
    ← fairConstruction_next P hP k] at L
  exact ⟨k, hnk, f, L.of_source_identity_iso (presentation_iso Q)⟩

/-- Every rational pattern begins a fair sequence of generating rules.
The initial structure is preserved exactly, including its off-carrier
relation values. The construction is classical, not an effective program. -/
theorem exists_fair (P : Str ℚ) (hP : P.IsPattern) :
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair :=
  ⟨fairConstruction P hP, rfl, fairConstruction_fair P hP⟩

/-- A covered rational pattern begins a fair generating sequence whose
limit order is an ordinal. This theorem classifies the order;
`FairOrdinalRealization` identifies both relations as well. -/
theorem exists_fair_with_ordinal_limit (P : Str ℚ) (hP : P.IsPattern)
    (hcov : Str.Covered P) :
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair ∧
      ∃ o : Ordinal.{0}, Nonempty (S.Limit ≃o Set.Iio o) := by
  obtain ⟨S, hzero, hfair⟩ := exists_fair P hP
  have hcov₀ : Str.Covered (S.stage 0) := by simpa only [hzero] using hcov
  exact ⟨S, hzero, hfair, S.exists_ordinal_orderIso hcov₀⟩

end GeneratingSequence
end Alexander313.Carlson
