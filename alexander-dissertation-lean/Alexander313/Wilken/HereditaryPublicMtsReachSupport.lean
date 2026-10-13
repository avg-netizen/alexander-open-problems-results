import Alexander313.Wilken.HereditaryPublicMtsReachBound
import Alexander313.Wilken.HereditaryPublicMtsCoveringConverse

/-!
# Arbitrary genuine coverings derive the actual FIRST cut

Every independent covering stays inside its initial original OWN interval.
The genuine terminating LOW search therefore constructs a native Node for
each positive additive-principal target. Every proper intermediate epsilon
also derives its actual HIGH caller. FIRST transports along the real public
mu edges using those constructed callers; localization membership is never
a premise. Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)
open FirstSupport
open Covering (Marked)

/-- The actual search and parser return the supplied canonical public
target literally, on the whole positive-principal OWN domain. -/
theorem parsed_publicCode (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    UniformPublicReturn.publicCode gamma (nativeRoot gamma d) = beta := by
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp
    (nativeRoot_spec gamma beta d hi hd).1
  have hp := node_public_spec gamma (nativeRoot gamma d) hn
  exact Canonical.check_value_injective _ _ hp.1 ((inputCheck_exact gamma beta).mp hi).2.1
    (hp.2.trans (nativeRoot_spec gamma beta d hi hd).2)

/-- Independent covering and a genuine positive additive-principal final
target derive the complete actual OWN search guard. -/
theorem covering_caller (gamma beta : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes)
    (hb : Canonical.check beta = true)
    (hp : 0 < unionInterpretation beta)
    (ha : Ordinal.IsPrincipal (· + ·) (unionInterpretation beta)) :
    inputCheck gamma beta = true := by
  have hg := ReachBound.covering_root_input hc
  have hfloor : unionInterpretation gamma ≤ unionInterpretation beta := by
    rcases ReachBound.covering_root_or_lt hc with rfl | hlt
    · exact le_rfl
    · exact hlt.le
  exact (inputCheck_exact gamma beta).mpr
    ⟨hg, hb, hp, ha, hfloor, ReachBound.covering_lt_own hc⟩

/-- All intermediate representatives are constructed by real terminating
searches. Genuine epsilon and strict-root order derive their HIGH callers,
before independently queried public mu transports FIRST. -/
theorem covering_marked {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes)
    (hb : Canonical.check current = true)
    (hp : 0 < unionInterpretation current)
    (ha : Ordinal.IsPrincipal (· + ·) (unionInterpretation current)) :
    current = gamma ∨ Marked gamma current := by
  revert hb hp ha
  induction hc with
  | root hg =>
    intro hb hp ha
    exact Or.inl rfl
  | append previous current codes hprevious hedge ih =>
    intro hb hp ha
    have hwhole := Covering.append previous current codes hprevious hedge
    have hg := ReachBound.covering_root_input hprevious
    have hj := covering_caller gamma current _ hwhole hb hp ha
    obtain ⟨d, hd⟩ := search_returns gamma current hj
    have hn := (SourceLocalization.inputCheck_exact gamma _).mp
      (nativeRoot_spec gamma current d hj hd).1
    have hcode := parsed_publicCode gamma current d hj hd
    refine Or.inr ⟨nativeRoot gamma d, hn, hcode, ?_⟩
    have he := (Support.eligible_exact previous current).mp hedge
    have hproper := (MuPublicDictionary.Support.inputCheck_image previous).mp he.1
    have hprincipal := EpsilonOffsets.epsilon_pos_principal hproper.2.1
    rcases ReachBound.covering_root_or_lt hprevious with hroot | hlt
    · have hedge' : PublicTrackingSequences.adjacencyCheck gamma
          (UniformPublicReturn.publicCode gamma (nativeRoot gamma d)) = true := by
        simpa only [hroot, hcode] using hedge
      exact root_edge_first_bound gamma _ hn hedge'
    · have hne : previous ≠ gamma := by
        intro heq
        exact hlt.ne (congrArg unionInterpretation heq).symm
      have hmarked := (ih hproper.1 hprincipal.1 hprincipal.2).resolve_left hne
      have hk := covering_caller gamma previous codes hprevious hproper.1
        hprincipal.1 hprincipal.2
      obtain ⟨e, hs⟩ := search_returns gamma previous hk
      have hprior := (SourceLocalization.inputCheck_exact gamma _).mp
        (nativeRoot_spec gamma previous e hk hs).1
      have hpriorCode := parsed_publicCode gamma previous e hk hs
      have hhigh := EvaluationReferenceHeight.parsed_high gamma previous e hk hs
        hlt hproper.2.1
      have hcut : interpretation gamma (nativeRoot gamma e) < ContextSupport.ownCeiling gamma :=
        (nativeRoot_spec gamma previous e hk hs).2.trans_lt
          (ReachBound.covering_lt_own hprevious)
      have hfirst := Covering.marked_first gamma (nativeRoot gamma e) hprior
        (hpriorCode.symm ▸ hmarked)
      have heq := public_edge_first_eq gamma (nativeRoot gamma e) (nativeRoot gamma d)
        hg hhigh hn hcut (by simpa only [hpriorCode, hcode] using hedge)
      exact heq.symm.le.trans hfirst

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachSupport
