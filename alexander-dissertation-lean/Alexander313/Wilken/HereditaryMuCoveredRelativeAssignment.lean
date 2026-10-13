import Alexander313.Wilken.HereditaryMuCoveredRelativeAssignmentSupport

/-!
# Actual relative assignments on every finite extended-mu-covered caller

The finite LOW search produces an original Normal code, then the complete
source factor/insertion assignment runs at the literal public epsilon base.
Every output entry is returned canonically with the SAME ordinal value.
The actual upper-boundary branch instead executes Definition3.19's singleton.
No returned assignment, source selection, LOW witness or termination measure
is an input. Public relative-tracker fidelity and evaluation remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuCoveredRelativeAssignment

open NativeContext
open Support

def publicWord (gamma : Nat) (word : List Nat) : List Nat :=
  word.map (UniformPublicReturn.publicCode gamma)

theorem publicWord_primrec : Primrec₂ publicWord :=
  (Primrec.list_map Primrec.snd
    (UniformPublicReturn.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem publicWord_spec (gamma raw : Nat) (word : List Nat)
    (ho : word ∈ SourceAdditiveTracking.Assignment.execute gamma raw) :
    publicWord gamma word ≠ [] ∧
      (∀ c ∈ publicWord gamma word, Canonical.check c = true) ∧
        (publicWord gamma word).map unionInterpretation = word.map (interpretation gamma) := by
  have ht := SourceAdditiveTracking.Assignment.execute_tracking gamma raw word ho
  have hl := GlobalAdditiveTracking.Return.native_word_low gamma word ht
  have hs : ∀ d ∈ word, Canonical.check (UniformPublicReturn.publicCode gamma d) = true ∧
      unionInterpretation (UniformPublicReturn.publicCode gamma d) = interpretation gamma d :=
    fun d hd => UniformPublicReturn.publicCode_spec gamma d
      ((UniformPublicReturn.inputCheck_exact gamma d).mpr (hl d hd))
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact SourceAdditiveTracking.Assignment.execute_nonempty gamma raw word ho
      (List.map_eq_nil_iff.mp he)
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (hs d hd).1
  · rw [publicWord, List.map_map]
    exact List.map_congr_left (fun d hd => (hs d hd).2)

def ordinaryExecute (gamma beta : Nat) : Part (List Nat) :=
  (PublicEpsilonUnboundedIota.SkNextSearch.Support.search gamma beta).bind fun raw =>
    (SourceAdditiveTracking.Assignment.execute gamma raw).map (publicWord gamma)

theorem ordinaryExecute_partrec : Partrec₂ ordinaryExecute := by
  have hs := PublicEpsilonUnboundedIota.SkNextSearch.Support.search_partrec
  have ha := SourceAdditiveTracking.Assignment.execute_partrec.comp
    (Primrec.fst.comp Primrec.fst).to_comp Computable.snd
  have hm : Computable₂ (fun p : (Nat × Nat) × Nat => fun word : List Nat => publicWord p.1.1 word) :=
    (publicWord_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp.to₂
  exact (Partrec.bind hs (Partrec.map ha hm).to₂).to₂

def execute (gamma beta : Nat) : Part (List Nat) := cond (inputCheck gamma beta)
  (cond (boundaryCheck gamma beta) (Part.some [beta]) (ordinaryExecute gamma beta)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond boundaryCheck_primrec.to_comp
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to_comp.partrec
      ordinaryExecute_partrec) Partrec.none).to₂

/-- Independent numerical mu coverage derives the original search and
full assignment callers; the actual boundary singleton terminates directly. -/
theorem execute_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    ∃ out, out ∈ execute gamma beta := by
  cases hb : boundaryCheck gamma beta with
  | true =>
    refine ⟨[beta], ?_⟩
    simp only [execute, hi, hb, Bool.cond_true, Part.mem_some_iff]
  | false =>
    obtain ⟨raw, hr⟩ := search_returns gamma beta hi hb
    obtain ⟨word, hw⟩ := SourceAdditiveTracking.Assignment.execute_returns gamma raw
      (assignment_caller gamma beta raw hi hr)
    refine ⟨publicWord gamma word, ?_⟩
    simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false, ordinaryExecute] using
      Part.mem_bind hr (Part.mem_map (publicWord gamma) hw)

theorem execute_domain (gamma beta : Nat) : (execute gamma beta).Dom ↔ inputCheck gamma beta = true := by
  constructor
  · intro hd
    cases hi : inputCheck gamma beta with
    | true => rfl
    | false =>
      have hn : (Part.none : Part (List Nat)).Dom := by
        simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    exact Part.dom_iff_mem.mpr (execute_returns gamma beta hi)

/-- The exact graph uses either the literal boundary singleton or an
independently executing original Normal search and complete source assignment. -/
theorem execute_clauses (gamma beta : Nat) (out : List Nat) : out ∈ execute gamma beta ↔
    inputCheck gamma beta = true ∧
      ((boundaryCheck gamma beta = true ∧ out = [beta]) ∨
        (boundaryCheck gamma beta = false ∧ ∃ raw word,
          raw ∈ PublicEpsilonUnboundedIota.SkNextSearch.Support.search gamma beta ∧
            word ∈ SourceAdditiveTracking.Assignment.execute gamma raw ∧
              out = publicWord gamma word)) := by
  constructor
  · intro ho
    have hi := (execute_domain gamma beta).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
    refine ⟨hi, ?_⟩
    cases hb : boundaryCheck gamma beta with
    | true => exact Or.inl ⟨hb, by simpa only
        [execute, hi, hb, Bool.cond_true, Part.mem_some_iff] using ho⟩
    | false =>
      have hordinary : out ∈ ordinaryExecute gamma beta := by
        simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho
      obtain ⟨raw, hr, hm⟩ := Part.mem_bind_iff.mp hordinary
      obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hm
      exact Or.inr ⟨hb, raw, word, hr, hw, he.symm⟩
  · rintro ⟨hi, ⟨hb, rfl⟩ | ⟨hb, raw, word, hr, hw, rfl⟩⟩
    · simp only [execute, hi, hb, Bool.cond_true, Part.mem_some_iff]
    · simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false, ordinaryExecute] using
        Part.mem_bind hr (Part.mem_map (publicWord gamma) hw)

theorem execute_spec (gamma beta : Nat) (out : List Nat) (ho : out ∈ execute gamma beta) :
    inputCheck gamma beta = true ∧ out ≠ [] ∧ ∀ c ∈ out, Canonical.check c = true := by
  have hs := (execute_clauses gamma beta out).mp ho
  refine ⟨hs.1, ?_⟩
  rcases hs.2 with ⟨hb, rfl⟩ | ⟨hb, raw, word, hr, hw, rfl⟩
  · exact ⟨List.cons_ne_nil _ _, fun c hc => by
      simpa only [List.mem_singleton.mp hc] using ((inputCheck_exact gamma beta).mp hs.1).2.1⟩
  · exact ⟨(publicWord_spec gamma raw word hw).1, (publicWord_spec gamma raw word hw).2.1⟩

/-- Each ordinary output really comes from the full source assignment at
the literal gamma, with original LOW/Normal input of value beta and RAW tracking.
This conclusion derives all witnesses; no independent public tracker is assumed. -/
theorem execute_ordinary_source (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ execute gamma beta) (hb : boundaryCheck gamma beta = false) :
    ∃ raw word, lowCheckCode gamma raw = true ∧ Comparison.acceptedCode gamma raw = true ∧
      interpretation gamma raw = unionInterpretation beta ∧
        word ∈ SourceAdditiveTracking.Assignment.execute gamma raw ∧
          SourceTrackingRaw.trackingCheck gamma word = true ∧
            out = publicWord gamma word ∧ out.map unionInterpretation = word.map (interpretation gamma) := by
  have hs := (execute_clauses gamma beta out).mp ho
  rcases hs.2 with ⟨ht, he⟩ | ⟨ht, raw, word, hr, hw, he⟩
  · rw [hb] at ht; cases ht
  · have hc := PublicEpsilonUnboundedIota.SkNextSearch.Support.search_spec gamma beta raw hr
    refine ⟨raw, word, hc.1, hc.2.1, hc.2.2.2, hw,
      SourceAdditiveTracking.Assignment.execute_tracking gamma raw word hw, he, ?_⟩
    rw [he]
    exact (publicWord_spec gamma raw word hw).2.2

/-- Definition3.19's actual upper-boundary extension on every represented
finite upsilon base; no original LOW code is invented at this boundary. -/
theorem execute_endpoint_boundary (n : Nat) :
    [PublicEpsilonSourceDictionary.endpointCode ((n + 1) + 1)] ∈
      execute (PublicEpsilonSourceDictionary.endpointCode (n + 1))
        (PublicEpsilonSourceDictionary.endpointCode ((n + 1) + 1)) := by
  let gamma := PublicEpsilonSourceDictionary.endpointCode (n + 1)
  let beta := PublicEpsilonSourceDictionary.endpointCode ((n + 1) + 1)
  have hg : GlobalMuDictionary.Support.inputCheck gamma = true :=
    GlobalMuDictionary.Support.endpoint_input n
  have he : PublicEpsilonSourceDictionary.basePoint gamma = true :=
    GlobalMuDictionary.Support.endpoint_basePoint n
  have hb : Canonical.check beta = true := PublicEpsilonSourceDictionary.endpointCode_checked _
  have hvalue : unionInterpretation beta = finiteBase ((n + 1) + 1) :=
    PublicEpsilonSourceDictionary.endpointCode_value _
  have hp : 0 < unionInterpretation beta ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) := by
    rw [hvalue]
    exact ⟨finiteBase_pos _, by
      rw [← finiteBase_succ_omegaPower_eq_self (n + 1)]
      exact Ordinal.isPrincipal_add_omega0_opow _⟩
  have hmu : GlobalMuDictionary.publicCode gamma = beta := GlobalMuDictionary.publicCode_endpoint n
  have hi : inputCheck gamma beta = true := (inputCheck_exact gamma beta).mpr
    ⟨hg, hb, hp.1, hp.2, by
      simpa only [gamma, beta, PublicEpsilonSourceDictionary.endpointCode_value] using
        (finiteBase_step (n + 1)).le,
      by simp only [GlobalTrackingSequences.muValue, hmu]; exact le_rfl⟩
  have hboundary : boundaryCheck gamma beta = true := by
    simp only [boundaryCheck, he, hmu, beq_self_eq_true, Bool.true_and]
  exact (execute_clauses gamma beta [beta]).mpr ⟨hi, Or.inl ⟨hboundary, rfl⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.MuCoveredRelativeAssignment
