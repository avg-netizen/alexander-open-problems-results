import Alexander313.Carlson.LeastCopyAgreement
import Alexander313.Carlson.Exactness

/-!
# Existence of finite amalgamations from least ordinal copies

Carlson, Definition 15.8 and Theorem 15.9(1), printed pp. 74--75.
An amalgamation is a pattern covered by the images of its given embeddings,
each of which is exact in the whole pattern. In the pure language there is
no separate arithmetic closure obligation.

Least ordinal copies are exact in any finite induced structure containing
them: they generate their initial spans by Theorem 14.10(5), and their
global correctness makes those spans 1-correct by Theorem 14.10(4).
Taking the union of these copies therefore constructs an actual finite
amalgamation. Uniqueness and pointed comparison are separate obligations.
-/

noncomputable section

namespace Alexander313.Carlson

/-- A finite isominimal ordinal carrier is exact in every induced finite
ordinal structure containing it, with no shared-maximum hypothesis. -/
theorem IsominimalOrdinalSet.exact {U V : Finset Ordinal.{0}}
    (hU : IsominimalOrdinalSet U) (hUV : U ⊆ V) :
    Str.Exact (Str.ofOrdinals U) (Str.ofOrdinals V) := by
  let Q := Str.ofOrdinals V
  have hbase : U ⊆ (Q.initialSpan U).U := by
    intro z hz
    exact Str.mem_initialSpan.mpr ⟨hUV hz, z, hz, le_rfl⟩
  have hbounded : ∀ z ∈ (Q.initialSpan U).U, ∃ p ∈ U, z ≤ p :=
    fun _ hz => (Str.mem_initialSpan.mp hz).2
  refine ⟨Str.ofOrdinals_isPattern V, hU.generates hbase hbounded, ?_⟩
  apply (Str.initialSpan_correct_iff Q U).mpr
  intro x hx y hy hxy
  obtain ⟨hxV, p, hp, hxp⟩ := Str.mem_initialSpan.mp hx
  obtain ⟨a, ha⟩ := Str.LeastGE.exists ⟨p, hp, hxp⟩
  by_cases hay : a < y
  · obtain ⟨b, hb, _⟩ := hU.kCorrect V .one a x y hxV hy ha hay hxy
    exact Str.mem_initialSpan.mpr ⟨hy, b, hb.1, hb.2.1⟩
  · exact Str.mem_initialSpan.mpr ⟨hy, a, ha.1, le_of_not_gt hay⟩

/-- Finite unions of isominimal induced ordinal carriers are isominimal. -/
theorem IsominimalOrdinalSet.biUnion {ι : Type*} (S : Finset ι)
    (U : ι → Finset Ordinal.{0}) (hU : ∀ i ∈ S, IsominimalOrdinalSet (U i)) :
    IsominimalOrdinalSet (S.biUnion U) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.biUnion_empty]
      apply IsominimalOrdinalSet.iff_le_covering.mpr
      simp
  | @insert i S hi ih =>
      rw [Finset.biUnion_insert]
      exact (hU i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => hU j (Finset.mem_insert_of_mem hj)))

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Definition 15.8, pure case, including a family of length zero.
The maps are supplied explicitly; every image is exact in the target. -/
structure Amalgamation {n : ℕ} (P : Fin n → Str α) (Q : Str β)
    (f : Fin n → α → β) : Prop where
  pattern : Q.IsPattern
  embeddings : ∀ i, IsIso (P i) (Q.restrict ((P i).U.image (f i))) (f i)
  union : Q.U = Finset.univ.biUnion (fun i => (P i).U.image (f i))
  exact : ∀ i, Exact (Q.restrict ((P i).U.image (f i))) Q

end Str

/-- Theorem 15.9(1), with coveredness discharged: every finite family of
pure rational patterns has an ordinal amalgamation, constructed by union
of isominimal copies. The union is itself isominimal. -/
theorem exists_ordinal_amalgamation {n : ℕ} (P : Fin n → Str ℚ)
    (hP : ∀ i, (P i).IsPattern) :
    ∃ (U : Finset Ordinal.{0}) (f : Fin n → ℚ → Ordinal.{0}),
      Str.Amalgamation P (Str.ofOrdinals U) f ∧
      (∀ i, IsominimalOrdinalSet ((P i).U.image (f i))) ∧ IsominimalOrdinalSet U := by
  classical
  have hc : ∀ i, ∃ f : ℚ → Ordinal.{0},
      Str.IsIso (P i) (Str.ofOrdinals ((P i).U.image f)) f ∧
      IsominimalOrdinalSet ((P i).U.image f) := by
    intro i
    obtain ⟨f, e, _, hm, _, _⟩ := exists_complete_minimal_ordinal_copy (P i) (hP i)
    exact ⟨f, e, hm⟩
  choose f e hm using hc
  let U := Finset.univ.biUnion (fun i => (P i).U.image (f i))
  have hsub (i : Fin n) : (P i).U.image (f i) ⊆ U := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩
  refine ⟨U, f, ⟨Str.ofOrdinals_isPattern U, ?_, rfl, ?_⟩, hm, ?_⟩
  · intro i
    exact e i
  · intro i
    exact (hm i).exact (hsub i)
  · exact IsominimalOrdinalSet.biUnion Finset.univ _ (fun i _ => hm i)

end Alexander313.Carlson
