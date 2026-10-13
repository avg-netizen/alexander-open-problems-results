import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaEnclosure
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuHeightSupport
import Alexander313.Wilken.HereditaryNativeMuSuccessorIntervals

/-!
# The genuine beta-context theta successor branch of source3.7

The original ANY-q high-root guard bounds the actual mu below the genuine
original source alpha-plus. When mu is at least beta, its actual beta LOW
Normal principal presentation supplies a genuine theta-zero argument.
The real Convention2.28 successor at that SAME beta is strictly between mu
and the source endpoint. The original Delta is a genuine proper limit,
and the endpoint's same-value carrier has no exposed zero support, so
actual comparison derives argument descent before successor comparison.
No parameter successor is defined for mu<beta; no whole3.7 claim follows.
All proof candidates are source-only and uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.SuccessorIntervals

open ThetaCourse Enclosure

/-- Every original mu output is below the true original-q successor
endpoint, with no target presentation or endpoint premise. -/
theorem muCode_lt_sourceAlphaPlus (q root : Nat) (ha : inputCheck q root = true) :
    interpretation (betaCode q root) (muCode q root) < sourceAlphaPlus q root := by
  have hm : interpretation (betaCode q root) (mappedCoefficient q root) < sourceAlphaPlus q root := by
    rw [← delta_enclosure_value q root ha]
    exact (HeightSupport.mappedCoefficient_le_delta q root ha).trans_lt
      (literalDelta_lt_enclosure q root ha)
  have he := sourceAlphaPlus_epsilon q root ha
  have hp : Ordinal.IsPrincipal (· + ·) (sourceAlphaPlus q root) := by
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hn : (tail q root : Ordinal.{0}) < sourceAlphaPlus q root :=
    (Ordinal.natCast_lt_omega0 _).trans (epsilon_omega_lt he)
  have hf := OmegaPowerHeight.finiteTailCode_spec (betaCode q root)
    (mappedCoefficient q root) (tail q root) (mappedCoefficient_spec q root ha).1
  have hex : interpretation (betaCode q root) (exponentCode q root) < sourceAlphaPlus q root := by
    rw [hf.2.2.1]
    exact hp hm hn
  have hs := OmegaPowers.powerCode_spec (betaCode q root) (exponentCode q root)
    (exponentCode_spec q root ha).1
  rw [muCode_literal q root ha, hs.2.2]
  exact (omegaPower_strictMono hex).trans_eq he

theorem execute_lt_sourceAlphaPlus (q root out : Nat) (ho : out ∈ execute q root) :
    interpretation (betaCode q root) out < sourceAlphaPlus q root := by
  obtain ⟨ha, rfl⟩ := (execute_graph q root out).mp ho
  exact muCode_lt_sourceAlphaPlus q root ha

/-- The nonzero Omega-one divisible Delta is a genuine proper limit.
This fact is derived from the actual original high-part decomposition. -/
theorem delta_isSuccLimit (q root : Nat) (ha : inputCheck q root = true) :
    IsSuccLimit (interpretation q (OmegaQuotient.deltaCode root)) := by
  have hd := Decomposition.highPart_dvd q 0 _ (OmegaQuotient.Support.argument_accepted q root ha)
  change omegaSequence (base q) 1 ∣ interpretation q (OmegaQuotient.deltaCode root) at hd
  obtain ⟨d, he⟩ := hd
  have hp : 0 < d := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hh := RootEndpointCollapse.delta_positive q root ha
    rw [he, hz, mul_zero] at hh
    exact (lt_irrefl (0 : Ordinal.{0})) hh
  rw [he]
  exact Ordinal.isSuccLimit_mul_left (omegaSequence_isSuccLimit (base q) 0) hp

/-- A theta-zero beta presentation of the actual mu, when that branch is
applicable, has its ORIGINAL argument strictly below actual Delta. -/
theorem theta_argument_lt_delta (q root : Nat) (ha : inputCheck q root = true)
    (b : RelativeTerm Nat) (hb : check (betaCode q root) (.theta 0 b) = true)
    (hbn : Comparison.Normal (betaCode q root) b)
    (hv : denote (betaCode q root) (.theta 0 b) =
      interpretation (betaCode q root) (muCode q root)) :
    denote (betaCode q root) b < interpretation q (OmegaQuotient.deltaCode root) := by
  have hd := delta_original q root ha
  have hs := delta_enclosure_spec q root ha
  have hlt : denote (betaCode q root) (.theta 0 b) <
      denote (betaCode q root) (.theta 0 (unshifted q root (deltaTerm root))) := by
    change denote (betaCode q root) (.theta 0 b) <
      denote (betaCode q root) (deltaEnclosureTerm q root)
    rw [hv, delta_enclosure_value q root ha]
    exact muCode_lt_sourceAlphaPlus q root ha
  have hc := (Iota.OrderInduction.checked_theta_lt_iff_exposed _ 0 b
    (unshifted q root (deltaTerm root)) hb hs.1 hbn hs.2.1).mp hlt
  have harg : denote (betaCode q root) b <
      denote (betaCode q root) (unshifted q root (deltaTerm root)) := by
    rcases hc with hc | ⟨x, hx, hle⟩
    · exact hc.1
    · rw [unshifted_exposed_zero q root ha _ hd.1 hd.2.2] at hx
      exact False.elim (List.not_mem_nil hx)
  rw [unshifted_value q root ha _ hd.1 hd.2.2] at harg
  have hcode := ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).1
  exact harg.trans_eq (Arithmetic.raw_value q _ hcode)

/-- The real active-beta Convention2.28 successor is bounded on its theta
branch. The successor star is controlled by the actual source recursion. -/
theorem theta_successor_lt_sourceAlphaPlus (q root : Nat) (ha : inputCheck q root = true)
    (b : RelativeTerm Nat) (hb : check (betaCode q root) (.theta 0 b) = true)
    (hbn : Comparison.Normal (betaCode q root) b)
    (hv : denote (betaCode q root) (.theta 0 b) =
      interpretation (betaCode q root) (muCode q root)) :
    denote (betaCode q root) (NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm
      (betaCode q root) b) < sourceAlphaPlus q root := by
  let beta := betaCode q root
  have hbeta := base_pos beta (betaCode_baseCheck q root ha)
  have hd := delta_original q root ha
  have hu := unshifted_checked q root ha _ hd.1 hd.2.2
  have htarget := (delta_enclosure_spec q root ha).1
  have hbarg := FixedPoint.checked_theta_argument beta 0 b hb
  let ba := FixedPoint.sourceOrdinal beta 0 b hbarg
  let da := FixedPoint.sourceOrdinal beta 0 (unshifted q root (deltaTerm root)) hu
  have hbsort := FixedPoint.checked_theta_sort beta 0 b hb
  have hdsort := FixedPoint.checked_theta_sort beta 0 _ htarget
  have harg : ba.val + 1 < da.val := by
    change denote beta b + 1 < denote beta (unshifted q root (deltaTerm root))
    rw [unshifted_value q root ha _ hd.1 hd.2.2,
      Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp
        (LambdaSource.delta_accepted q root ha)).1]
    exact (delta_isSuccLimit q root ha).add_one_lt (theta_argument_lt_delta q root ha b hb hbn hv)
  have hmu : globalCollapse (base beta) 0 ba.val < globalCollapse (base beta) 0 da.val := by
    change denote beta (.theta 0 b) < denote beta (deltaEnclosureTerm q root)
    rw [hv, delta_enclosure_value q root ha]
    exact muCode_lt_sourceAlphaPlus q root ha
  have hcollapse : globalCollapse (base beta) 0 (ba.val + 1) <
      globalCollapse (base beta) 0 da.val := by
    apply (globalCollapse_lt_iff_globalStar (base beta) hbeta 0
      (SourceCollapseSuccessors.globalSuccArgument (base beta) hbeta 0 ba) da
      ((omegaSequence_isSuccLimit (base beta) 1).add_one_lt hbsort) hdsort).mpr
    exact Or.inl ⟨harg,
      (SourceCollapseSuccessors.global_successor_star_le (base beta) hbeta 0 ba hbsort).trans_lt hmu⟩
  rw [(NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm_spec beta b hb).2.2.2,
    ← delta_enclosure_value q root ha]
  exact hcollapse

/-- The genuine theta branch is derived from the actual beta LOW Normal
principal output, not supplied as an additional representation hypothesis. -/
theorem execute_theta_successor_interval (q root out : Nat) (ho : out ∈ execute q root)
    (hbase : base (betaCode q root) ≤ interpretation (betaCode q root) out) :
    ∃ b : RelativeTerm Nat, check (betaCode q root) (.theta 0 b) = true ∧
      Comparison.Normal (betaCode q root) b ∧
      denote (betaCode q root) (.theta 0 b) = interpretation (betaCode q root) out ∧
      interpretation (betaCode q root) out <
        denote (betaCode q root) (NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm
          (betaCode q root) b) ∧
      denote (betaCode q root) (NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm
        (betaCode q root) b) < sourceAlphaPlus q root := by
  obtain ⟨ha, rfl⟩ := (execute_graph q root out).mp ho
  have hs := muCode_spec q root ha
  have hc := (Comparison.acceptedCode_exact _ _).mp hs.2.1
  have ht := Arithmetic.raw_checked _ _ hc.1
  have hp : Ordinal.IsPrincipal (· + ·) (denote (betaCode q root) (rawTree (muCode q root))) := by
    rw [Arithmetic.raw_value _ _ hc.1, hs.2.2]
    exact Ordinal.isPrincipal_add_omega0_opow _
  obtain ⟨b, hb, hbn, hv⟩ := NativeContext.Mu.SuccessorIntervals.principal_theta_zero _ _ ht hc.2
    (by rw [Arithmetic.raw_value _ _ hc.1]; exact hbase)
    (by rw [Arithmetic.raw_value _ _ hc.1]; exact (HeightBoundary.input_spec _ _ hs.1).2.2) hp
  have hbv : denote (betaCode q root) (.theta 0 b) =
      interpretation (betaCode q root) (muCode q root) := hv.trans (Arithmetic.raw_value _ _ hc.1)
  refine ⟨b, hb, hbn, hbv, ?_, theta_successor_lt_sourceAlphaPlus q root ha b hb hbn hbv⟩
  have harg := FixedPoint.checked_theta_argument _ 0 b hb
  have he := SourceCollapseSuccessors.global_collapse_lt_successor _
    (base_pos _ (betaCode_baseCheck q root ha)) 0 (FixedPoint.sourceOrdinal _ 0 b harg)
    (FixedPoint.checked_theta_sort _ 0 b hb)
  rw [← hbv, (NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm_spec _ b hb).2.2.2]
  exact he

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.SuccessorIntervals
