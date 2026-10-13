import Alexander313.Wilken.HereditaryPublicMts
import Alexander313.Wilken.PublicEpsilonNativeSkHeightSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSuccessorIntervals
import Alexander313.Wilken.SourceOneNativeMuBounds

/-!
# Actual proper-reference height descent across genuine public mu calls

The selected original public mu lies below its computed OWN ceiling.
Independent strict epsilon adjacency therefore derives a real literal-base
LOW search and a genuine HIGH parsed root. Its actual canonical beta code
is the supplied next public epsilon; original contextual mu fidelity is
applied only after these callers and the OWN interval are proved. Actual
canonical height calls then strictly decrease at any independently mu-
covered following input. This is a local proper-epsilon descent kernel;
initial-one/finite-endpoint transitions, a common component bound and
recursive lSeq descent remain separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationReferenceHeight

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota

noncomputable def publicMuValue (gamma : Nat) : Ordinal.{0} :=
  unionInterpretation (MuPublicDictionary.publicCode gamma)

theorem public_mu_lt_own (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    publicMuValue gamma < PublicMts.ContextSupport.ownCeiling gamma := by
  have hv := (MuPublicDictionary.publicCode_spec gamma hg).2
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have hr := (MuPublicDictionary.Support.source_one_root gamma hg hl).1
    have hb := SourceOneIota.Mu.Bounds.muCode_lt_source_alphaPlus _ hr
    rw [(SourceOneIota.Mu.muCode_spec _ hr).2.2] at hb
    simpa only [publicMuValue, hv, MuPublicDictionary.Support.sourceValue,
      PublicMts.ContextSupport.ownCeiling, hl, beq_self_eq_true, Bool.cond_true] using hb
  · have hr := (MuPublicDictionary.Support.native_root gamma hg hl).1
    have hb := Mu.SuccessorIntervals.muCode_lt_sourceAlphaPlus _ _ hr
    rw [(Mu.muCode_spec _ _ hr).2.2] at hb
    have hz : (PublicEpsilonSourceDictionary.level gamma == 0) = false :=
      beq_eq_false_iff_ne.mpr hl
    simpa only [publicMuValue, hv, MuPublicDictionary.Support.sourceValue,
      PublicMts.ContextSupport.ownCeiling, hz, Bool.cond_false] using hb

/-- Independent proper public mu coverage derives the actual OWN-interval
checker used by the real numerical search. -/
theorem adjacency_caller (gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : Canonical.check beta = true)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hcover : unionInterpretation beta ≤ publicMuValue gamma) :
    PublicMts.inputCheck gamma beta = true := by
  have hp := EpsilonOffsets.epsilon_pos_principal he
  exact (PublicMts.inputCheck_exact gamma beta).mpr
    ⟨hg, hb, hp.1, hp.2, hlt.le, hcover.trans_lt (public_mu_lt_own gamma hg)⟩

theorem parsed_high (gamma beta d : Nat) (hi : PublicMts.inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta) :
    Mu.inputCheck gamma (PublicMts.nativeRoot gamma d) = true := by
  have hs := (PublicMts.inputCheck_exact gamma beta).mp hi
  have hr := SkNextSearch.Support.search_spec gamma beta d hd
  have hc : SourceLocalization.RootAdapter.inputCheck gamma d = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact gamma d).mpr
      ⟨hr.1, by rw [hr.2.2.2]; exact hlt.le,
        by rw [hr.2.2.2]; exact hs.2.2.2.1⟩
  exact SourceLocalization.RootAdapter.rootCode_high gamma d hc
    (by rw [hr.2.2.2]; exact hlt) (by rw [hr.2.2.2]; exact he)

/-- The actually parsed HIGH root has the literal next canonical public
base; no equality of native spellings is assumed. -/
theorem parsed_betaCode (gamma beta d : Nat) (hi : PublicMts.inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta) :
    betaCode gamma (PublicMts.nativeRoot gamma d) = beta := by
  have hr := parsed_high gamma beta d hi hd hlt he
  have hp := betaCode_spec gamma _ hr
  exact Canonical.check_value_injective _ _ hp.1
    ((PublicMts.inputCheck_exact gamma beta).mp hi).2.1
    (hp.2.trans (PublicMts.nativeRoot_spec gamma beta d hi hd).2)

theorem parsed_height (gamma beta d : Nat) (hi : PublicMts.inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    CanonicalHeight.canonicalHeightCode gamma d =
      CanonicalHeight.canonicalHeightCode gamma (PublicMts.nativeRoot gamma d) := by
  have hs := SkNextSearch.Support.search_spec gamma beta d hd
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp
    (PublicMts.nativeRoot_spec gamma beta d hi hd).1
  have hr := SourceLocalization.node_low gamma _ hn
  exact CanonicalHeight.canonicalHeightCode_invariant gamma d _
    (Bool.and_eq_true.mp hs.1).1 (Bool.and_eq_true.mp hr).1
    (hs.2.2.2.trans (PublicMts.nativeRoot_spec gamma beta d hi hd).2.symm)

/-- Contextual mu is identified only after genuine HIGH admission,
actual beta-code equality and the predecessor's OWN cut are derived. -/
theorem parsed_public_mu (gamma beta d : Nat) (hi : PublicMts.inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta) :
    MuPublicDictionary.Support.inputCheck beta = true ∧
      publicMuValue beta = Mu.sourceValue gamma (PublicMts.nativeRoot gamma d) := by
  have hs := (PublicMts.inputCheck_exact gamma beta).mp hi
  have hr := parsed_high gamma beta d hi hd hlt he
  have hc : interpretation gamma (PublicMts.nativeRoot gamma d) <
      PublicMts.ContextSupport.ownCeiling gamma :=
    (PublicMts.nativeRoot_spec gamma beta d hi hd).2.trans_lt hs.2.2.2.2.2
  have hm := PublicMts.ContextSupport.high_public_mu gamma _ hs.1 hr hc
  change MuPublicDictionary.Support.inputCheck (betaCode gamma (PublicMts.nativeRoot gamma d)) = true ∧
    unionInterpretation (MuPublicDictionary.publicCode
      (betaCode gamma (PublicMts.nativeRoot gamma d))) = _ at hm
  rw [parsed_betaCode gamma beta d hi hd hlt he] at hm
  exact hm

def execute (gamma beta : Nat) : Part Nat := cond (PublicMts.inputCheck gamma beta)
  ((SkNextSearch.Support.search gamma beta).map (CanonicalHeight.canonicalHeightCode gamma)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hm : Computable₂ (fun p : Nat × Nat => fun d : Nat =>
      CanonicalHeight.canonicalHeightCode p.1 d) :=
    (CanonicalHeight.canonicalHeightCode_primrec.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd).to_comp.to₂
  exact (Partrec.cond PublicMts.inputCheck_primrec.to_comp
    (Partrec.map SkNextSearch.Support.search_partrec hm) Partrec.none).to₂

theorem execute_graph (gamma beta height : Nat) : height ∈ execute gamma beta ↔
    PublicMts.inputCheck gamma beta = true ∧ ∃ d,
      d ∈ SkNextSearch.Support.search gamma beta ∧
        height = CanonicalHeight.canonicalHeightCode gamma d := by
  constructor
  · intro ho
    have hi : PublicMts.inputCheck gamma beta = true := by
      cases hc : PublicMts.inputCheck gamma beta with
      | true => rfl
      | false => exact False.elim (by
          simpa only [execute, hc, Bool.cond_false, Part.notMem_none] using ho)
    have hm : height ∈ (SkNextSearch.Support.search gamma beta).map
        (CanonicalHeight.canonicalHeightCode gamma) := by
      simpa only [execute, hi, Bool.cond_true] using ho
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp hm
    exact ⟨hi, d, hd, he.symm⟩
  · rintro ⟨hi, d, hd, rfl⟩
    simpa only [execute, hi, Bool.cond_true] using
      Part.mem_map (CanonicalHeight.canonicalHeightCode gamma) hd

theorem execute_returns (gamma beta : Nat) (hi : PublicMts.inputCheck gamma beta = true) :
    ∃ height, height ∈ execute gamma beta := by
  obtain ⟨d, hd⟩ := PublicMts.search_returns gamma beta hi
  exact ⟨_, (execute_graph gamma beta _).mpr ⟨hi, d, hd, rfl⟩⟩

/-- Both heights come from actual searches. The next LOW and incoming
HIGH callers, literal changed base and contextual mu equality are derived
internally; the only numerical bound is independent public mu coverage. -/
theorem execute_strict_descent (gamma beta next height nextHeight : Nat)
    (hh : height ∈ execute gamma beta) (hn : nextHeight ∈ execute beta next)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta)
    (hcover : unionInterpretation next ≤ publicMuValue beta) : nextHeight < height := by
  obtain ⟨hi, d, hd, hheight⟩ := (execute_graph gamma beta height).mp hh
  obtain ⟨hj, e, hs, hnextHeight⟩ := (execute_graph beta next nextHeight).mp hn
  have hr := parsed_high gamma beta d hi hd hlt he
  have hb := parsed_betaCode gamma beta d hi hd hlt he
  have hm := (parsed_public_mu gamma beta d hi hd hlt he).2
  have hl := SkNextSearch.Support.search_spec beta next e hs
  have hmu : interpretation (betaCode gamma (PublicMts.nativeRoot gamma d)) e ≤
      Mu.sourceValue gamma (PublicMts.nativeRoot gamma d) := by
    rw [hb, hl.2.2.2, ← hm]
    exact hcover
  have hdesc := SkHeight.low_next_height_lt_root gamma (PublicMts.nativeRoot gamma d) e hr
    (by rw [hb]; exact hl.1) hmu
  rw [hb, ← parsed_height gamma beta d hi hd] at hdesc
  simpa only [hheight, hnextHeight] using hdesc

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationReferenceHeight
