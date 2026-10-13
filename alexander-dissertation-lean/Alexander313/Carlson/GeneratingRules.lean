import Alexander313.Carlson.UpwardExistence
import Alexander313.Carlson.PatternLiftingExistence
import Alexander313.Carlson.GeneratingTransport
import Alexander313.Carlson.CoveringRigidity

/-!
# Generating rules and finite generation

Carlson, *Patterns of resemblance of order 2*, Definition 13.10,
Lemma 13.11, Definition 14.2, and Lemmas 14.3 and 14.6, in the pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 58–61 of the author's October 16, 2008 manuscript.

`GeneratingRule` is an inductive calculus. Its five constructors are the
pure arithmetic rules, downward reflection at either level, upward
2-reflection of an earlier generating rule, restriction of a finite chain
to an extension at one old point, and minimal lifting along a continuous
embedding. In the pure language an arithmetic extension has the same
finite carrier; the arithmetic constructor allows different presentations
of the irrelevant relations outside that carrier.

`ExactlyGenerates` records a finite chain of generating rules. It is
defined mutually with `GeneratingRule` because Definition 13.10(4) uses
such a chain. That clause requires an extension at one point: unrestricted
composition and restriction are not constructors of `GeneratingRule`.
`Generates` is the subsequent restriction relation of Definition 14.2.

No constructor assumes ordinal validity, cofinal validity or coveredness.
The semantic conclusions follow by structural induction, using the
already proved reflection and lifting theorems. The calculus is stated
on a fixed ambient linear order; rational labels provide the established
setting in which the requisite placements always exist.
Coveredness is propagated from a covered source; these results do not
supply an ordinal covering for an arbitrary abstract pattern.
-/

noncomputable section

namespace Alexander313.Carlson
namespace Str

variable {α : Type*} [LinearOrder α]

/-- A pure arithmetic extension has the same finite structure, even when
its irrelevant off-carrier relations are presented differently. -/
theorem IsSub.reverse_of_same_universe {P Q : Str α} (h : IsSub P Q)
    (hU : Q.U = P.U) : IsSub Q P := by
  refine ⟨hU.le, ?_⟩
  intro x hx y hy
  have hxP : x ∈ P.U := hU ▸ hx
  have hyP : y ∈ P.U := hU ▸ hy
  exact ⟨(h.2 x hxP y hyP).1.symm, (h.2 x hxP y hyP).2.symm⟩

/-- Same-carrier extensions are continuous in the pure language. -/
theorem Continuous.of_same_universe {P Q : Str α} (h : IsSub P Q)
    (hU : Q.U = P.U) : Continuous P Q :=
  (Continuous.refl P).restrict (h.reverse_of_same_universe hU) h.1

/-- Same-carrier extensions are cofinally valid: the covering is
unchanged, and there are no new points below any old anchor. -/
theorem CofinallyValid.of_same_universe {P Q : Str α} (h : IsSub P Q)
    (hU : Q.U = P.U) : CofinallyValid P Q := by
  refine ⟨h, fun t ht _ _ => ⟨t, ht.mono (h.reverse_of_same_universe hU),
    fun _ _ => rfl, ?_⟩⟩
  intro a b hb hab
  exact (hab.not_mem (hU ▸ hb)).elim

mutual

/-- Definition 13.10, pure case. This is the least calculus closed under
the five displayed constructors, rather than a semantic validity predicate. -/
inductive GeneratingRule : Str α → Str α → Prop where
  /-- Clause 1: arithmetic extensions in the pure language add no points. -/
  | arithmetic {P Q : Str α} (pattern : P.IsPattern) (sub : IsSub P Q)
      (same_universe : Q.U = P.U) : GeneratingRule P Q
  /-- Clause 2: downward reflection at level one or level two. -/
  | downward {P : Str α} {k : Lvl} {a b : α} {X N : Finset α} {g : α → α}
      (data : DownData P k a b X N g) : GeneratingRule P (P.downward k a b N g)
  /-- Clause 3: upward 2-reflection of a rule already in the calculus. -/
  | upward {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}
      (rule : GeneratingRule P Q) (data : UpData P Q a b N g) :
      GeneratingRule P (P.upward Q a b N g)
  /-- Clause 4: restrict a finite chain to an extension at one old point. -/
  | finiteRestriction {P Q R : Str α} {a : α}
      (chain : ExactlyGenerates P R) (sub : IsSub Q R) (extension_at : ExtensionAt P Q a) :
      GeneratingRule P Q
  /-- Clause 5: lift an earlier rule minimally along a continuous embedding. -/
  | lifting {P Pplus Q Qplus : Str α} {h f : α → α}
      (rule : GeneratingRule P Pplus) (embedding : ContinuousEmbedding P Q h)
      (lift : PatternLifting P Pplus Q Qplus h f)
      (minimal : PatternLifting.IsMinimal P Pplus Q Qplus h) : GeneratingRule Q Qplus

/-- Definition 14.2: a finite chain of generating rules, including the
length-zero chain at any pattern. This relation also supplies the finite
chain used by Definition 13.10(4). -/
inductive ExactlyGenerates : Str α → Str α → Prop where
  | refl {P : Str α} (pattern : P.IsPattern) : ExactlyGenerates P P
  | tail {P Q R : Str α} (chain : ExactlyGenerates P Q) (rule : GeneratingRule Q R) :
      ExactlyGenerates P R

end

/-- Lemma 13.11(2): a generating rule has pattern endpoints, is continuous,
and is cofinally valid. Each ordinal-semantic premise is supplied by a
strictly earlier derivation, rather than by the generating-rule definition. -/
theorem GeneratingRule.sound {P Q : Str α} (d : GeneratingRule P Q) :
    P.IsPattern ∧ Q.IsPattern ∧ Continuous P Q ∧ CofinallyValid P Q := by
  induction d using GeneratingRule.rec
    (motive_2 := fun P Q _ =>
      P.IsPattern ∧ Q.IsPattern ∧ Continuous P Q ∧ CofinallyValid P Q)
  · rename_i hP hsub hU
    exact ⟨hP, hP.mono (hsub.reverse_of_same_universe hU),
      Continuous.of_same_universe hsub hU, CofinallyValid.of_same_universe hsub hU⟩
  · rename_i D
    exact ⟨D.pat, D.isPattern, D.continuous, D.cofinallyValid⟩
  · rename_i d D ih
    exact ⟨ih.1, D.isPattern, D.continuous, D.cofinallyValid ih.2.2.2⟩
  · rename_i c hsub hAt ih
    exact ⟨ih.1, ih.2.1.mono hsub, ih.2.2.1.restrict hsub hAt.1.1,
      ih.2.2.2.restrict hsub hAt.1.1⟩
  · rename_i d he L hM ih
    exact ⟨L.base_target_pattern, L.target_pattern,
      hM.continuous_of_continuous_source L ih.2.2.1 he, L.cofinallyValid hM ih.2.2.2⟩
  · rename_i S hS
    exact ⟨hS, hS, Continuous.refl S,
      CofinallyValid.of_same_universe (IsSub.refl S) rfl⟩
  · rename_i c d hc hd
    exact ⟨hc.1, hd.2.1, hc.2.2.1.trans hd.2.2.1,
      hc.2.2.2.trans hd.2.2.2 hc.2.2.1.2.1⟩

/-- Finite chains preserve pattern endpoints, continuity and cofinal
validity. The middle structure is bounded by continuity, exactly as needed
by the cofinal-composition theorem. -/
theorem ExactlyGenerates.sound {P Q : Str α} (d : ExactlyGenerates P Q) :
    P.IsPattern ∧ Q.IsPattern ∧ Continuous P Q ∧ CofinallyValid P Q := by
  induction d using ExactlyGenerates.rec (motive_1 := fun _ _ _ => True)
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · rename_i S hS
    exact ⟨hS, hS, Continuous.refl S,
      CofinallyValid.of_same_universe (IsSub.refl S) rfl⟩
  · rename_i c d hc _
    have hd := d.sound
    exact ⟨hc.1, hd.2.1, hc.2.2.1.trans hd.2.2.1,
      hc.2.2.2.trans hd.2.2.2 hc.2.2.1.2.1⟩

namespace GeneratingRule

variable {P Q R : Str α}

theorem source_pattern (d : GeneratingRule P Q) : P.IsPattern := d.sound.1

theorem target_pattern (d : GeneratingRule P Q) : Q.IsPattern := d.sound.2.1

theorem continuous (d : GeneratingRule P Q) : Continuous P Q := d.sound.2.2.1

theorem cofinallyValid (d : GeneratingRule P Q) : CofinallyValid P Q := d.sound.2.2.2

theorem isSub (d : GeneratingRule P Q) : IsSub P Q := d.continuous.1

theorem valid (d : GeneratingRule P Q) : Valid P Q := d.cofinallyValid.valid

/-- Identity is the pure arithmetic rule at a pattern. -/
theorem refl (hP : P.IsPattern) : GeneratingRule P P :=
  .arithmetic hP (IsSub.refl P) rfl

/-- A single generating rule is a finite generating chain. -/
theorem exactlyGenerates (d : GeneratingRule P Q) : ExactlyGenerates P Q :=
  .tail (.refl d.source_pattern) d

/-- Lemma 13.11(1): compatible isomorphisms preserve generating rules.
The new presentation is a minimal lifting along the base isomorphism,
so this is a consequence of clause 5 rather than an additional constructor. -/
theorem of_isIso {P Pplus Q Qplus : Str α} {h f : α → α}
    (d : GeneratingRule P Pplus) (e : IsIso P Q h) (eplus : IsIso Pplus Qplus f)
    (hfix : ∀ x ∈ P.U, f x = h x) : GeneratingRule Q Qplus := by
  have L := PatternLifting.of_isIso d.target_pattern d.continuous e eplus hfix
  exact .lifting d e.continuousEmbedding L (L.isMinimal_of_isIso eplus)

end GeneratingRule

namespace ExactlyGenerates

variable {P Q R : Str α}

theorem source_pattern (d : ExactlyGenerates P Q) : P.IsPattern := d.sound.1

theorem target_pattern (d : ExactlyGenerates P Q) : Q.IsPattern := d.sound.2.1

theorem continuous (d : ExactlyGenerates P Q) : Continuous P Q := d.sound.2.2.1

theorem cofinallyValid (d : ExactlyGenerates P Q) : CofinallyValid P Q := d.sound.2.2.2

theorem isSub (d : ExactlyGenerates P Q) : IsSub P Q := d.continuous.1

theorem valid (d : ExactlyGenerates P Q) : Valid P Q := d.cofinallyValid.valid

/-- Concatenate two finite chains. This closure belongs to exact
generation; it is not an unrestricted generating-rule constructor. -/
theorem trans (d : ExactlyGenerates P Q) (e : ExactlyGenerates Q R) :
    ExactlyGenerates P R := by
  induction e using ExactlyGenerates.rec (motive_1 := fun _ _ _ => True) generalizing P
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact d
  · rename_i c r ih _
    exact .tail (ih d) r

/-- Definition 13.10(4) applies in particular to the chain endpoint itself
when the complete extension occurs at one point. -/
theorem generatingRule {a : α} (d : ExactlyGenerates P Q) (hAt : ExtensionAt P Q a) :
    GeneratingRule P Q := .finiteRestriction d (IsSub.refl Q) hAt

end ExactlyGenerates

/-- Definition 14.2: an intermediate structure of a pattern obtained by a
finite chain of generating rules. -/
def Generates (P Q : Str α) : Prop :=
  ∃ R : Str α, ExactlyGenerates P R ∧ IsSub Q R ∧ P.U ⊆ Q.U

namespace Generates

variable {P Q R : Str α}

/-- Lemma 14.3, pure case: generation is continuous and cofinally valid. -/
theorem sound (d : Generates P Q) :
    P.IsPattern ∧ Q.IsPattern ∧ Continuous P Q ∧ CofinallyValid P Q := by
  obtain ⟨R, c, hsub, hPQ⟩ := d
  exact ⟨c.source_pattern, c.target_pattern.mono hsub,
    c.continuous.restrict hsub hPQ, c.cofinallyValid.restrict hsub hPQ⟩

theorem source_pattern (d : Generates P Q) : P.IsPattern := d.sound.1

theorem target_pattern (d : Generates P Q) : Q.IsPattern := d.sound.2.1

theorem continuous (d : Generates P Q) : Continuous P Q := d.sound.2.2.1

theorem cofinallyValid (d : Generates P Q) : CofinallyValid P Q := d.sound.2.2.2

theorem isSub (d : Generates P Q) : IsSub P Q := d.continuous.1

theorem valid (d : Generates P Q) : Valid P Q := d.cofinallyValid.valid

theorem refl (hP : P.IsPattern) : Generates P P :=
  ⟨P, .refl hP, IsSub.refl P, subset_rfl⟩

/-- Generation passes to any intermediate closed substructure. In the
pure language every substructure is closed. -/
theorem restrict (d : Generates P R) (hQR : IsSub Q R) (hPQ : P.U ⊆ Q.U) : Generates P Q := by
  obtain ⟨S, c, hRS, _⟩ := d
  exact ⟨S, c, hQR.trans hRS, hPQ⟩

/-- A generated extension at one old point is itself a generating rule,
by the restricted-composition clause of Definition 13.10. -/
theorem generatingRule {a : α} (d : Generates P Q) (hAt : ExtensionAt P Q a) :
    GeneratingRule P Q := by
  obtain ⟨R, c, hsub, _⟩ := d
  exact .finiteRestriction c hsub hAt

end Generates

theorem ExactlyGenerates.generates {P Q : Str α} (d : ExactlyGenerates P Q) : Generates P Q :=
  ⟨Q, d, IsSub.refl Q, d.isSub.1⟩

theorem GeneratingRule.generates {P Q : Str α} (d : GeneratingRule P Q) : Generates P Q :=
  d.exactlyGenerates.generates

/-- Valid extension rules preserve the existence of an ordinal covering. -/
theorem Valid.covered {P Q : Str α} (d : Valid P Q) (hP : Covered P) : Covered Q := by
  obtain ⟨h, hh⟩ := hP
  obtain ⟨h', hh', _⟩ := d.2 h hh
  exact ⟨h', hh'⟩

/-- Substructures inherit coveredness by restricting the same map. -/
theorem Covered.mono {P Q : Str α} (hQ : Covered Q) (hsub : IsSub P Q) : Covered P := by
  obtain ⟨h, hh⟩ := hQ
  exact ⟨h, hh.mono hsub⟩

theorem GeneratingRule.covered_iff {P Q : Str α} (d : GeneratingRule P Q) :
    Covered P ↔ Covered Q :=
  ⟨d.valid.covered, fun hQ => hQ.mono d.isSub⟩

theorem ExactlyGenerates.covered_iff {P Q : Str α} (d : ExactlyGenerates P Q) :
    Covered P ↔ Covered Q :=
  ⟨d.valid.covered, fun hQ => hQ.mono d.isSub⟩

theorem Generates.covered_iff {P Q : Str α} (d : Generates P Q) : Covered P ↔ Covered Q :=
  ⟨d.valid.covered, fun hQ => hQ.mono d.isSub⟩

/-- Lemma 14.6: every covering of a covered pattern into a pattern it
generates is pointwise inflationary on the old carrier. -/
theorem Generates.le_of_coversInto {P Q : Str α} (d : Generates P Q)
    (hP : Covered P) {f : α → α} (hf : CoversInto P Q f) {x : α} (hx : x ∈ P.U) :
    x ≤ f x :=
  d.valid.le_of_coversInto hP hf hx

theorem ExactlyGenerates.le_of_coversInto {P Q : Str α} (d : ExactlyGenerates P Q)
    (hP : Covered P) {f : α → α} (hf : CoversInto P Q f) {x : α} (hx : x ∈ P.U) :
    x ≤ f x :=
  d.generates.le_of_coversInto hP hf hx

theorem GeneratingRule.le_of_coversInto {P Q : Str α} (d : GeneratingRule P Q)
    (hP : Covered P) {f : α → α} (hf : CoversInto P Q f) {x : α} (hx : x ∈ P.U) :
    x ≤ f x :=
  d.generates.le_of_coversInto hP hf hx

/-- A covering moving an old point down rules out generation from a
covered source. This gives a finite-structure obstruction without assuming
that every abstract pattern is covered. -/
theorem not_generates_of_coversInto_lt {P Q : Str α} (hP : Covered P)
    {f : α → α} (hf : CoversInto P Q f) {x : α} (hx : x ∈ P.U) (hfx : f x < x) :
    ¬ Generates P Q :=
  fun d => (not_lt.mpr (d.le_of_coversInto hP hf hx)) hfx

namespace GeneratingRule

/-- Downward generating rules on rational labels can be constructed from
the source pattern and the nonempty set to be reflected. -/
theorem exists_downward_rat {P : Str ℚ} {k : Lvl} {a b : ℚ} {X : Finset ℚ}
    (hP : P.IsPattern) (ha : a ∈ P.U) (hb : b ∈ P.U) (hab : a < b)
    (hrel : P.rel k a b) (hX : ∀ x ∈ X, x ∈ P.U ∧ a ≤ x ∧ x < b)
    (hne : X.Nonempty) :
    ∃ Q : Str ℚ, GeneratingRule P Q ∧ ExtensionAt P Q a ∧ Q.U.card = P.U.card + X.card := by
  obtain ⟨N, g, D⟩ := DownData.exists_rat hP ha hb hab hrel hX hne
  exact ⟨P.downward k a b N g, .downward D, D.extensionAt, D.card_universe⟩

/-- Upward generating rules on rational labels require a derivation of
the source rule, not a separately assumed semantic validity statement. -/
theorem exists_upward_rat {P Q : Str ℚ} {a b : ℚ} (d : GeneratingRule P Q)
    (hAt : ExtensionAt P Q a) (hb : b ∈ P.U) (hab : a < b) (hrel : P.r₂ a b) :
    ∃ R : Str ℚ, GeneratingRule P R ∧ ExtensionAt P R b ∧ R.U.card = Q.U.card := by
  obtain ⟨N, g, D⟩ := UpData.exists_rat d.target_pattern d.continuous hAt hb hab hrel
  exact ⟨P.upward Q a b N g, .upward d D, D.extensionAt, D.card_universe⟩

/-- The lifting rule on rational labels is available along every continuous
embedding into a pattern; its arithmetic carrier is constructed rather
than supplied as an additional existence hypothesis. -/
theorem exists_lifting_rat {P Pplus Q : Str ℚ} {h : ℚ → ℚ}
    (d : GeneratingRule P Pplus) (hQ : Q.IsPattern) (he : ContinuousEmbedding P Q h) :
    ∃ (Qplus : Str ℚ) (f : ℚ → ℚ), PatternLifting P Pplus Q Qplus h f ∧
      PatternLifting.IsMinimal P Pplus Q Qplus h ∧ GeneratingRule Q Qplus := by
  obtain ⟨Qplus, f, L, hM, _⟩ :=
    PatternLifting.exists_minimal_continuous_rat d.target_pattern hQ d.continuous he
  exact ⟨Qplus, f, L, hM, .lifting d he L hM⟩

end GeneratingRule
end Str
end Alexander313.Carlson
