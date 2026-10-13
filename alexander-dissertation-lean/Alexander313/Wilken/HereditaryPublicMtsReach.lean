import Alexander313.Wilken.HereditaryPublicMtsReachSupport
import Alexander313.Wilken.HereditaryPublicMtsInfinityHat

/-!
# Genuine reachability forces the independently executed mts covering

An arbitrary independent covering constructs all its own LOW and HIGH
representatives, and thus derives the actual FIRST cut. The already proved
finite table criterion then shows that independently executing mts emits a
covering. On strict multiplicative targets in the whole alpha-infinity
domain, arbitrary reachability is exactly the true original semantic hat
cut. No numerical minimum, chosen path, or supplied localization membership
is used. Shortest-cover and lexicographic optimality remain separate.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Reach

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)

/-- An arbitrary independently checked covering forces FIRST at the
actual separately executing target search, without a path-membership guard. -/
theorem covering_first_cut (gamma beta d : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes)
    (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    FirstSupport.firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma := by
  have hs := (inputCheck_exact gamma beta).mp hi
  have hne : beta ≠ gamma := by
    intro he
    exact hlt.ne (congrArg unionInterpretation he).symm
  have hm := (ReachSupport.covering_marked hc hs.2.1 hs.2.2.1 hs.2.2.2.1).resolve_left hne
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp
    (nativeRoot_spec gamma beta d hi hd).1
  have hp := ReachSupport.parsed_publicCode gamma beta d hi hd
  exact Covering.marked_first gamma (nativeRoot gamma d) hn (hp.symm ▸ hm)

/-- Every actual OWN-domain execution reaches a strict target whenever
any genuine independent covering reaches it. -/
theorem execute_covering_of_reachable (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hr : ∃ codes, Covering gamma beta codes) : Covering gamma beta out := by
  obtain ⟨hi, d, hd, hw⟩ := execute_spec gamma beta out ho
  obtain ⟨codes, hc⟩ := hr
  exact (CoveringConverse.execute_covering_iff_first gamma beta d out hd ho hlt).mpr
    (covering_first_cut gamma beta d codes hc hi hd hlt)

/-- The full-domain actual mts word is a covering exactly when arbitrary
independent public-mu reachability holds. Genuine reach derives OWN first. -/
theorem infinity_execute_covering_iff_reachable (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ Infinity.execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔ ∃ codes, Covering gamma beta codes := by
  constructor
  · intro hc
    exact ⟨out, hc⟩
  · rintro ⟨codes, hc⟩
    have hi := (Infinity.execute_spec gamma beta out ho).1
    have hj := InfinityHat.own_input_of_cut gamma beta hi (ReachBound.covering_lt_own hc)
    have ht : out ∈ execute gamma beta := by
      rw [← Infinity.execute_eq_own gamma beta hj]
      exact ho
    exact execute_covering_of_reachable gamma beta out ht hlt ⟨codes, hc⟩

/-- The genuine full grammar domain supplies a real execution. Existence
of any covering is equivalent to existence of an actually emitted covering. -/
theorem reachable_iff_emitted (gamma beta : Nat)
    (hi : Infinity.inputCheck gamma beta = true)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    (∃ codes, Covering gamma beta codes) ↔
      ∃ out, out ∈ Infinity.execute gamma beta ∧ Covering gamma beta out := by
  constructor
  · intro hr
    obtain ⟨out, ho⟩ := Infinity.execute_returns gamma beta hi
    exact ⟨out, ho, (infinity_execute_covering_iff_reachable gamma beta out ho hlt).mpr hr⟩
  · rintro ⟨out, ho, hc⟩
    exact ⟨out, hc⟩

/-- Arbitrary genuine reachability on strict multiplicative targets is
exactly below the independently constructed original semantic singleton cut. -/
theorem reachable_iff_lt_hat (gamma beta : Nat)
    (hi : Infinity.inputCheck gamma beta = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    (∃ codes, Covering gamma beta codes) ↔ unionInterpretation beta <
      InfinityHat.value gamma ((Infinity.inputCheck_exact gamma beta).mp hi).1 := by
  obtain ⟨out, ho⟩ := Infinity.execute_returns gamma beta hi
  have he := (infinity_execute_covering_iff_reachable gamma beta out ho hlt).symm.trans
    (InfinityHat.execute_covering_iff_lt_value gamma beta out ho hm hlt)
  exact he

theorem not_reachable_at_or_above_hat (gamma beta : Nat)
    (hi : Infinity.inputCheck gamma beta = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hcut : InfinityHat.value gamma ((Infinity.inputCheck_exact gamma beta).mp hi).1 ≤
      unionInterpretation beta) : ¬ ∃ codes, Covering gamma beta codes :=
  fun hr => (hcut.not_gt ((reachable_iff_lt_hat gamma beta hi hm hlt).mp hr))

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Reach
