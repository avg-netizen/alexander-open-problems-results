import Alexander313.Carlson.PatternTransport
import Alexander313.Carlson.PatternLiftingData

/-!
# Normalizing an arithmetic lifting to its image carriers

Identifying the source and its extension with their images changes both
lifting maps to the identity. The old target and arithmetic carrier remain
fixed. Compatible finite isomorphisms transport the source pattern and its
continuity, so a continuous base embedding supplies exactly the data required
by the common-carrier construction.

This is the change of labels at the beginning of Carlson's Lemma 12.6,
in the pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf.
-/

noncomputable section

namespace Alexander313.Carlson
namespace ArithmeticLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Replacing the source carriers by their images makes both arithmetic
lifting maps the identity. No ambient inverse map is required. -/
theorem normalized {A Aplus : Finset α} {B Bplus : Finset β} {h f : α → β}
    (D : ArithmeticLifting A Aplus B Bplus h f) :
    ArithmeticLifting (A.image h) (Aplus.image f) B Bplus id id := by
  classical
  refine
    { source_sub := ?_
      source_bounded := ?_
      base_mono := fun _ _ _ _ hxy => hxy
      base_mem := ?_
      target_sub := D.target_sub
      mono := fun _ _ _ _ hxy => hxy
      mem := ?_
      agrees := fun _ _ => rfl
      carrier_eq := ?_
      justBelow := ?_ }
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [← D.agrees x hx]
    exact Finset.mem_image_of_mem f (D.source_sub hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, ha, hxa⟩ := D.source_bounded x hx
    refine ⟨h a, Finset.mem_image_of_mem h ha, ?_⟩
    simpa only [D.agrees a ha] using D.le_of_le hx (D.source_sub ha) hxa
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact D.base_mem x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact D.mem x hx
  · simpa only [Finset.image_id] using D.carrier_eq
  · intro a y hy hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxA : x ∉ A := by
      intro hxA
      apply hj.not_mem
      rw [D.agrees x hxA]
      exact Finset.mem_image_of_mem h hxA
    have hup := Str.up_spec (D.source_bounded x hx)
    have hB := D.mapped_justBelow hx hxA
    have hI : Str.JustBelow (A.image h) (h (Str.up A x)) (f x) := by
      refine ⟨Finset.mem_image_of_mem h hup.1, hB.2.1, ?_⟩
      intro b hb hba
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
      exact hB.2.2 (h q) (D.base_mem q hq) hba
    have hea : a = h (Str.up A x) := hj.unique hI
    change Str.JustBelow B a (f x)
    rw [hea]
    exact hB

/-- A continuous source rule and a continuous base embedding give normalized
lifting data on the common target order. -/
theorem normalizedData {P Pplus : Str α} {Q : Str β} {U : Finset β}
    {h f : α → β} (A : ArithmeticLifting P.U Pplus.U Q.U U h f)
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h) :
    PatternLiftingConstruction.Data
      (Q.restrict (P.U.image h)) (Pplus.map f) Q U := by
  refine
    { source_pattern := (Pplus.map_isIso f A.mono).isPattern hS
      target_pattern := hQ
      source_cont := hC.of_isIso hE.1 (Pplus.map_isIso f A.mono) A.agrees
      target_cont := hE.2
      arithmetic := ?_ }
  exact A.normalized

end ArithmeticLifting
end Alexander313.Carlson
