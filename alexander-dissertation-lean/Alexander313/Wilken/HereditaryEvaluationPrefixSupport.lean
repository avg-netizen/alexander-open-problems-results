import Alexander313.Wilken.HereditaryGlobalHSmallSupport
import Alexander313.Wilken.HereditaryEvaluationComponents
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativePrincipal

/-!
# The genuine reference prefix and its final epsilon component

Every nonempty independent global reference is itself an independent global
tracker. Thus stripping the last component of a real tracker supplies the
next genuine evaluation caller whenever its reference prefix is nonempty.
The real original MNF program returns a literal singleton on every canonical
epsilon. Its actual final-component dispatcher consequently equals the real
relative component at a strictly lower previous base. These are ingredients
for the prefix recursion of Definition3.35; no evaluation, inverse or lexical
decrease of an actual recursive call is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixSupport

open GlobalTrackingSequences
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)
open NativeContext.PublicEpsilonUnboundedIota

theorem reference_tracking (codes : List Nat) (hr : Reference codes) (hne : codes ≠ []) :
    Tracking codes := by
  obtain ⟨m, tail, he, ht, hg⟩ := hr
  by_cases hn : tail = []
  · have hm : m ≠ 0 := by
      intro hz
      apply hne
      simp only [he, hn, hz, GlobalAdditiveTracking.Source.baseWord,
        List.range_zero, List.map_nil, List.append_nil]
    simpa only [he, hn, List.append_nil] using AssignmentSupport.tracking_baseWord m hm
  · have hrelative := (SmallHSupport.epsilonReference_in_gap m tail ht hg).1
    have hl : lastCode codes = lastCode tail := by
      rw [he, AssignmentSupport.lastCode_append_nonempty _ _ hn]
    obtain ⟨gamma, hcodes, hreverse⟩ := stripLast_split codes hne
    have hgamma : lastCode codes = gamma := by
      simp only [lastCode, hreverse, Option.getD_some]
    have ha : MuPublicDictionary.Support.inputCheck gamma = true := by
      rw [← hgamma, hl]
      exact hrelative.nodes _ (lastCode_mem tail hn)
    have hs := (MuPublicDictionary.Support.inputCheck_image gamma).mp ha
    have hp := EpsilonOffsets.epsilon_pos_principal hs.2.1
    have hone := EpsilonOffsets.epsilon_one_lt hs.2.1
    have hsingleton := PublicTrackingSequences.singleton_tracking gamma hs.1 hp.1 hp.2 hone.le
    have href : Reference (stripLast codes ++ [gamma]) := by
      rw [← hcodes]
      exact ⟨m, tail, he, ht, hg⟩
    have hspliced := SmallHSupport.global_tracking_splice (stripLast codes) gamma [] href ha hsingleton
    simpa only [← hcodes] using hspliced

theorem stripLast_reference (codes : List Nat) (hr : Reference codes) (hne : codes ≠ []) :
    Reference (stripLast codes) := (reference_tracking codes hr hne).2.2.1

theorem stripLast_tracking (codes : List Nat) (ht : Tracking codes) (hne : stripLast codes ≠ []) :
    Tracking (stripLast codes) := reference_tracking _ ht.2.2.1 hne

/-- Canonical reduced MNF uniqueness and canonical code injection force
the literal input epsilon, rather than just a same-valued representative. -/
theorem epsilon_factors (beta : Nat) (fs : List Nat)
    (hb : GlobalMuDictionary.Support.inputCheck beta = true)
    (hf : fs ∈ EvaluationFinalComponent.Support.factors beta) : fs = [beta] := by
  have hs := (GlobalMuDictionary.Support.inputCheck_exact beta).mp hb
  have hm := NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _ hs.2
  have hone := EpsilonOffsets.epsilon_one_lt hs.2
  have hform := EvaluationFinalComponent.Support.factors_spec beta fs hf
  have hv := MultiplicativeNormalForm.formSpec_values beta fs hform
  have hcanonical := Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF_multiplicative hm hone
  apply SkPublicValueInvariance.canonical_words_eq fs [beta] hform.2.1
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact hs.1)
  simpa only [List.map_singleton] using hv.trans hcanonical

theorem epsilon_factors_returns (beta : Nat)
    (hb : GlobalMuDictionary.Support.inputCheck beta = true) :
    [beta] ∈ EvaluationFinalComponent.Support.factors beta := by
  have hs := (GlobalMuDictionary.Support.inputCheck_exact beta).mp hb
  have hp := EpsilonOffsets.epsilon_pos_principal hs.2
  have hi := (Principal.unionPrincipalCheck_exact beta).mpr
    ⟨Canonical.check_original hs.1, hp.1, hp.2⟩
  obtain ⟨fs, hf⟩ := EvaluationFinalComponent.Support.factors_returns beta hi
  simpa only [epsilon_factors beta fs hb hf] using hf

/-- The actual final epsilon dispatcher executes precisely the genuine
relative block; its true MNF has no second factor to append. -/
theorem epsilon_final_block (gamma beta : Nat) (word : List Nat)
    (hg : EvaluationFinalComponent.Support.startCheck gamma = true)
    (hb : GlobalMuDictionary.Support.inputCheck beta = true)
    (hless : unionInterpretation gamma < unionInterpretation beta)
    (hw : word ∈ EvaluationRelativeCallers.blockExecute gamma beta) :
    word ∈ EvaluationFinalComponent.execute gamma beta := by
  have hc := EvaluationFinalComponent.Support.start_checked gamma hg
  have hs := (GlobalMuDictionary.Support.inputCheck_exact beta).mp hb
  have hp := EpsilonOffsets.epsilon_pos_principal hs.2
  have hi : EvaluationFinalComponent.inputCheck gamma beta = true := by
    apply Bool.and_eq_true.mpr
    exact ⟨hg, (PublicTrackingSequences.principalCheck_exact beta).mpr ⟨hs.1, hp.1, hp.2⟩⟩
  have hlt := (Canonical.less_exact gamma beta).mpr ⟨hc, hs.1, hless⟩
  apply (EvaluationFinalComponent.execute_clauses gamma beta word).mpr
  refine ⟨hi, Or.inr ⟨hlt, [beta], word, epsilon_factors_returns beta hb, ?_, ?_⟩⟩
  · simpa only [EvaluationFinalComponent.firstCode, List.head?_cons, Option.getD_some] using hw
  · simp only [EvaluationFinalComponent.finish, EvaluationFinalComponent.appendCheck,
      List.tail_cons, List.tail_nil, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixSupport
