import Alexander313.Wilken.HereditaryEvaluationComponentsSupport

/-!
# All executing components and chronological lengths of Definition3.35

Independent global Tracking is the sole admission predicate. A genuine
finite numerical scan computes its maximal initial endpoint chain;
actual relative execution constructs each proper component and the real
MNF routine constructs the final one. Thus this program computes all
gamma1 through gamma_n+1 and all of their positive lengths without a
supplied decomposition, factorization, component or length witness.
The common height, strict lSeq descent and evaluation o remain separate.
Source-only uncompiled candidates on the represented lambda-zero domain.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponents

open Support GlobalTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec)

def properExecute (codes : List Nat) : Part (List EvaluationBlocks.Block) :=
  EvaluationBlocks.execute (endpointCode (segmentIndex (stripLast codes))) (properTail codes)

theorem properExecute_partrec : Partrec properExecute :=
  EvaluationBlocks.execute_partrec.comp
    (PublicEpsilonSourceDictionary.endpointCode_primrec.comp
      (segmentIndex_primrec.comp stripLast_primrec)).to_comp properTail_primrec.to_comp

def finalExecute (codes : List Nat) : Part (List Nat) :=
  EvaluationFinalComponent.execute (EvaluationFinalComponent.previousCode codes) (lastCode codes)

theorem finalExecute_partrec : Partrec finalExecute :=
  EvaluationFinalComponent.execute_partrec.comp EvaluationFinalComponent.previousCode_primrec.to_comp
    lastCode_primrec.to_comp

def admittedExecute (codes : List Nat) : Part (List EvaluationBlocks.Block) :=
  (properExecute codes).bind fun words =>
    (finalExecute codes).map (fun final => words ++ [final])

theorem admittedExecute_partrec : Partrec admittedExecute := by
  have hf := finalExecute_partrec.comp Computable.fst
  have hm : Computable₂ (fun p : List Nat × List EvaluationBlocks.Block =>
      fun final : List Nat => p.2 ++ [final]) :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).to_comp.to₂
  exact Partrec.bind properExecute_partrec (Partrec.map hf hm).to₂

def execute (codes : List Nat) : Part (List EvaluationBlocks.Block) :=
  cond (trackingCheck codes) (admittedExecute codes) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond trackingCheck_primrec.to_comp admittedExecute_partrec Partrec.none

/-- The complete graph identifies every chronological proper component
and the actual final MNF component. No output certificate is a premise. -/
theorem execute_graph (codes : List Nat) (out : List EvaluationBlocks.Block) :
    out ∈ execute codes ↔ Tracking codes ∧ ∃ words final,
      EvaluationBlocks.Assigned (endpointCode (segmentIndex (stripLast codes)))
        (properTail codes) words ∧ final ∈ finalExecute codes ∧ out = words ++ [final] := by
  constructor
  · intro ho
    have hi : trackingCheck codes = true := by
      cases hc : trackingCheck codes with
      | true => rfl
      | false =>
        have hn : False := by
          simpa only [execute, hc, Bool.cond_false, Part.notMem_none] using ho
        exact False.elim hn
    have ha : out ∈ admittedExecute codes := by
      simpa only [execute, hi, Bool.cond_true] using ho
    obtain ⟨words, hw, hm⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨final, hf, he⟩ := (Part.mem_map_iff _).mp hm
    exact ⟨(trackingCheck_exact codes).mp hi, words, final,
      (EvaluationBlocks.execute_graph _ _ _).mp hw, hf, he.symm⟩
  · rintro ⟨ht, words, final, hw, hf, rfl⟩
    have hi := (trackingCheck_exact codes).mpr ht
    simpa only [execute, hi, Bool.cond_true, admittedExecute] using
      Part.mem_bind ((EvaluationBlocks.execute_graph _ _ _).mpr hw)
        (Part.mem_map (fun final => words ++ [final]) hf)

/-- Independently defined global Tracking derives every actual caller
and termination of the entire component producer. -/
theorem execute_returns (codes : List Nat) (ht : Tracking codes) :
    ∃ out, out ∈ execute codes := by
  have hs := tracking_segment codes ht
  obtain ⟨words, hw⟩ := EvaluationBlocks.global_returns _ _ hs.2.1 hs.2.2
  obtain ⟨final, hf⟩ := EvaluationFinalComponent.global_returns codes ht
  exact ⟨words ++ [final], (execute_graph codes _).mpr
    ⟨ht, words, final, (EvaluationBlocks.execute_graph _ _ _).mp hw, hf, rfl⟩⟩

theorem execute_domain (codes : List Nat) : (execute codes).Dom ↔ Tracking codes := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact ((execute_graph codes out).mp ho).1
  · intro ht
    exact Part.dom_iff_mem.mpr (execute_returns codes ht)

theorem execute_count (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ execute codes) : out.length = (properTail codes).length + 1 := by
  obtain ⟨ht, words, final, hw, hf, rfl⟩ := (execute_graph codes out).mp ho
  simp only [List.length_append, List.length_singleton, EvaluationBlocks.assigned_length hw]

theorem execute_nonempty_components (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ execute codes) : ∀ word ∈ out, word ≠ [] := by
  obtain ⟨ht, words, final, hw, hf, rfl⟩ := (execute_graph codes out).mp ho
  intro word hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (EvaluationBlocks.assigned_tracking hw word hm).1
  · have he : word = final := List.mem_singleton.mp hm
    subst word
    exact final_nonempty _ _ final hf

def executeLengths (codes : List Nat) : Part (List Nat) :=
  (execute codes).map EvaluationBlocks.lengths

theorem executeLengths_partrec : Partrec executeLengths :=
  Partrec.map execute_partrec (EvaluationBlocks.lengths_primrec.to_comp.comp Computable.snd).to₂

theorem executeLengths_graph (codes ns : List Nat) : ns ∈ executeLengths codes ↔
    ∃ words, words ∈ execute codes ∧ EvaluationBlocks.lengths words = ns := by
  rw [executeLengths, Part.mem_map_iff]

theorem executeLengths_returns (codes : List Nat) (ht : Tracking codes) :
    ∃ ns, ns ∈ executeLengths codes := by
  obtain ⟨words, hw⟩ := execute_returns codes ht
  exact ⟨EvaluationBlocks.lengths words, Part.mem_map _ hw⟩

/-- These are the lengths of all real gamma components, including the
actual final normal-form component; exactly n+1 positive entries result.
Membership in a common [h]^<=h and recursive lexical descent are not
asserted by this theorem. -/
theorem executeLengths_spec (codes ns : List Nat) (ho : ns ∈ executeLengths codes) :
    ns.length = (properTail codes).length + 1 ∧ ∀ n ∈ ns, 0 < n := by
  obtain ⟨words, hw, he⟩ := (executeLengths_graph codes ns).mp ho
  refine ⟨?_, ?_⟩
  · rw [← he, EvaluationBlocks.lengths, List.length_map]
    exact execute_count codes words hw
  · intro n hn
    rw [← he, EvaluationBlocks.lengths] at hn
    obtain ⟨word, hm, rfl⟩ := List.mem_map.mp hn
    have hne := execute_nonempty_components codes words hw word hm
    cases word with
    | nil => exact False.elim (hne rfl)
    | cons a rest => simp only [List.length_cons]; omega

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponents
