import Alexander313.Wilken.HereditarySkPublicRecurrenceUnique
import Alexander313.Wilken.PublicEpsilonNativeSkTrackingSupport

/-!
# Genuine canonical public reference and tracking certificates

Relative reference entries are actual canonical epsilons outside the source
upsilon image. Their adjacent covers use the independently executing public
mu. A tracking certificate adds the admitted positive additive-principal
final entry and its genuine final cover. No assigned sequence or evaluation
defines these predicates. The finite upsilon prefix of a global sequence is
separate. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences

open SkPublicRecurrence (muValue mu_input_canonical mu_input_epsilon)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton stripLast_singleton
  lastCode_append_singleton stripLast_append_singleton)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support
  (stripLast_cons_nonempty lastCode_cons_nonempty)

inductive Reference : List Nat → Prop
  | nil : Reference []
  | one (a : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true) : Reference [a]
  | cons (a b : Nat) (xs : List Nat) (ha : MuPublicDictionary.Support.inputCheck a = true)
      (hab : unionInterpretation a < unionInterpretation b)
      (hcover : unionInterpretation b ≤ muValue a)
      (ht : Reference (b :: xs)) : Reference (a :: b :: xs)

theorem Reference.nodes {xs : List Nat} (hr : Reference xs) :
    ∀ a ∈ xs, MuPublicDictionary.Support.inputCheck a = true := by
  induction hr with
  | nil => intro a ha; exact False.elim (List.not_mem_nil ha)
  | one a ha =>
    intro c hc
    simpa only [List.mem_singleton.mp hc] using ha
  | cons a b xs ha hab hcover ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact ih c hc

theorem Reference.strict {xs : List Nat} (hr : Reference xs) :
    (xs.map unionInterpretation).Pairwise (· < ·) := by
  induction hr with
  | nil => simp only [List.map_nil, List.pairwise_nil]
  | one a ha => simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
  | cons a b xs ha hab hcover ht ih =>
    rw [List.map_cons]
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro value hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · have hb : ∀ value ∈ xs.map unionInterpretation, unionInterpretation b < value :=
        (List.pairwise_cons.mp (show
          (unionInterpretation b :: xs.map unionInterpretation).Pairwise (· < ·) from
          by simpa only [List.map_cons] using ih)).1
      exact hab.trans (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem Reference.epsilons {xs : List Nat} (hr : Reference xs) :
    ∀ a ∈ xs, Canonical.check a = true ∧
      Ordinal.omega0 ^ unionInterpretation a = unionInterpretation a ∧
        ¬ SourceUpsilonImage (unionInterpretation a) :=
  fun a ha => (MuPublicDictionary.Support.inputCheck_image a).mp (hr.nodes a ha)

def Tracking (codes : List Nat) : Prop :=
  codes ≠ [] ∧ (∀ c ∈ codes, Canonical.check c = true) ∧ Reference (stripLast codes) ∧
    0 < unionInterpretation (lastCode codes) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (lastCode codes)) ∧
        if stripLast codes = [] then 1 ≤ unionInterpretation (lastCode codes)
        else 1 < unionInterpretation (lastCode codes) ∧
          unionInterpretation (lastCode codes) ≤ muValue (lastCode (stripLast codes))

/-- The actual selected source mu formula is a genuine ordinary omega
power in either original source, giving positivity and principalness. -/
theorem muValue_positive_principal (a : Nat)
    (ha : MuPublicDictionary.Support.inputCheck a = true) :
    0 < muValue a ∧ Ordinal.IsPrincipal (· + ·) (muValue a) := by
  rw [muValue, (MuPublicDictionary.publicCode_spec a ha).2, MuPublicDictionary.Support.sourceValue]
  cases hb : PublicEpsilonSourceDictionary.level a == 0 with
  | true =>
    simp only [hb, Bool.cond_true, SourceOneIota.Mu.sourceValue]
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩
  | false =>
    simp only [hb, Bool.cond_false, NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue]
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩

theorem singleton_tracking (a : Nat) (hc : Canonical.check a = true)
    (hp : 0 < unionInterpretation a)
    (ha : Ordinal.IsPrincipal (· + ·) (unionInterpretation a))
    (hb : 1 ≤ unionInterpretation a) : Tracking [a] := by
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hm
    simpa only [List.mem_singleton.mp hm] using hc
  · rw [stripLast_singleton]; exact .nil
  · simpa only [lastCode_singleton] using hp
  · simpa only [lastCode_singleton] using ha
  · simpa only [stripLast_singleton, lastCode_singleton, if_pos rfl] using hb

theorem pair_tracking (a d : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true)
    (hd : Canonical.check d = true) (hp : 0 < unionInterpretation d)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation d))
    (hone : 1 < unionInterpretation d) (hcover : unionInterpretation d ≤ muValue a) :
    Tracking [a, d] := by
  have hprefix : stripLast [a, d] = [a] := stripLast_append_singleton [a] d
  have hlast : lastCode [a, d] = d := lastCode_append_singleton [a] d
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact mu_input_canonical a ha
    · simpa only [List.mem_singleton.mp hc] using hd
  · rw [hprefix]; exact .one a ha
  · rw [hlast]; exact hp
  · rw [hlast]; exact hprincipal
  · rw [hprefix, hlast, if_neg (List.cons_ne_nil _ _), lastCode_singleton]
    exact ⟨hone, hcover⟩

theorem tracking_prepend (a b : Nat) (xs : List Nat)
    (ha : MuPublicDictionary.Support.inputCheck a = true)
    (hab : unionInterpretation a < unionInterpretation b)
    (hcover : unionInterpretation b ≤ muValue a)
    (hbpos : 1 < unionInterpretation b) (ht : Tracking (b :: xs)) :
    Tracking (a :: b :: xs) := by
  cases xs with
  | nil =>
    exact pair_tracking a b ha (ht.2.1 b List.mem_cons_self)
      (by simpa only [lastCode_singleton] using ht.2.2.2.1)
      (by simpa only [lastCode_singleton] using ht.2.2.2.2.1) hbpos hcover
  | cons c cs =>
    have hn : c :: cs ≠ [] := List.cons_ne_nil _ _
    have hprefix : stripLast (b :: c :: cs) = b :: stripLast (c :: cs) :=
      stripLast_cons_nonempty b _ hn
    have hpne : stripLast (b :: c :: cs) ≠ [] := by rw [hprefix]; exact List.cons_ne_nil _ _
    have hnew : stripLast (a :: b :: c :: cs) = a :: stripLast (b :: c :: cs) :=
      stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)
    have hnewne : stripLast (a :: b :: c :: cs) ≠ [] := by rw [hnew]; exact List.cons_ne_nil _ _
    have hlast := lastCode_cons_nonempty a (b :: c :: cs) (List.cons_ne_nil _ _)
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact mu_input_canonical a ha
      · exact ht.2.1 d hd
    · rw [hnew, hprefix]
      exact .cons a b _ ha hab hcover (by rw [← hprefix]; exact ht.2.2.1)
    · rw [hlast]; exact ht.2.2.2.1
    · rw [hlast]; exact ht.2.2.2.2.1
    · rw [if_neg hnewne, hlast, hnew, lastCode_cons_nonempty a _ hpne]
      simpa only [if_neg hpne] using ht.2.2.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences
