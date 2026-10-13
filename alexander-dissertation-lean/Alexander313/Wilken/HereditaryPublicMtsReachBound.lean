import Alexander313.Wilken.HereditaryPublicMtsReachBoundSupport
import Alexander313.Wilken.HereditaryPublicMtsCoveringSupport

/-!
# Every genuine public mu covering stays below its initial OWN ceiling

The independent Covering recurrence uses actual public mu edges. Proper
intermediate roots have nested original successors, with their common
selected source derived from the true interval. Its actual final target,
which need not be epsilon, remains below the initial OWN ceiling as well.
This is a reach bound, not an incoming-context mu identity outside OWN.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachBound

open CoveringSupport (Covering)

theorem covering_root_input {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) : MuPublicDictionary.Support.inputCheck gamma = true := by
  induction hc with
  | root hg => exact hg
  | append previous current codes hp hnext ih => exact ih

theorem covering_root_or_lt {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) :
    current = gamma ∨ unionInterpretation gamma < unionInterpretation current := by
  induction hc with
  | root hg => exact Or.inl rfl
  | append previous current codes hp hnext ih =>
    have he := (Support.eligible_exact previous current).mp hnext
    apply Or.inr
    rcases ih with rfl | hlt
    · exact he.2.2.1
    · exact hlt.trans he.2.2.1

/-- Every actually μ-covered target lies below the original starting OWN
successor, even if the target itself is not an epsilon. -/
theorem covering_lt_own {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) :
    unionInterpretation current < ContextSupport.ownCeiling gamma := by
  induction hc with
  | root hg => exact ReachBoundSupport.root_lt_own gamma hg
  | append previous current codes hp hnext ih =>
    have he := (Support.eligible_exact previous current).mp hnext
    have hm : unionInterpretation current < ContextSupport.ownCeiling previous :=
      he.2.2.2.trans_lt (EvaluationReferenceHeight.public_mu_lt_own previous he.1)
    rcases covering_root_or_lt hp with rfl | hlt
    · exact hm
    · exact hm.trans (ReachBoundSupport.own_nested gamma previous
        (covering_root_input hp) he.1 hlt ih)

theorem not_covering_at_or_above_own {gamma beta : Nat} (codes : List Nat)
    (hcut : ContextSupport.ownCeiling gamma ≤ unionInterpretation beta) :
    ¬ Covering gamma beta codes :=
  fun hc => (covering_lt_own hc).not_ge hcut

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachBound
