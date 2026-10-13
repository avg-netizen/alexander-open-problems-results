import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingReturn
import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingCancellation

/-!
# Executing all finite-stage cases of global Definition 3.24

The least genuine upsilon segment determines its entire base chain. The
zero segment runs the original source-one full assignment. Positive segments
return the base chain at its endpoint, cancel the actual lead factor below
gamma^omega, or prepend the base chain to the independently executed original
gamma assignment. All relative inputs, quotient existence and source bounds
are derived internally. Full global TS recognition, evaluation and order
isomorphism remain separate theorems. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking

open Source Return

def endpointCheck (alpha : Nat) : Bool := alpha == endpointCode (level alpha)

theorem endpointCheck_primrec : Primrec endpointCheck := Primrec.beq.comp Primrec.id
  (PublicEpsilonSourceDictionary.endpointCode_primrec.comp PublicEpsilonSourceDictionary.level_primrec)

theorem endpointCheck_exact (alpha : Nat) (hi : inputCheck alpha = true) : endpointCheck alpha = true ↔
    unionInterpretation alpha = finiteBase (level alpha) := by
  simp only [endpointCheck, beq_iff_eq]
  constructor
  · intro he
    exact (congrArg unionInterpretation he).trans (PublicEpsilonSourceDictionary.endpointCode_value _)
  · intro he
    exact Canonical.check_value_injective _ _ ((inputCheck_exact alpha).mp hi).1
      (PublicEpsilonSourceDictionary.endpointCode_checked _) (he.trans
        (PublicEpsilonSourceDictionary.endpointCode_value _).symm)

def smallCheck (alpha : Nat) : Bool := Canonical.less alpha (cutoffCode alpha)

theorem smallCheck_primrec : Primrec smallCheck := Canonical.Effective.less_primrec.comp Primrec.id cutoffCode_primrec

theorem smallCheck_exact (alpha : Nat) (hi : inputCheck alpha = true) : smallCheck alpha = true ↔
    unionInterpretation alpha < NativeContext.base (contextCode alpha) ^ Ordinal.omega0 := by
  simp only [smallCheck, Canonical.less_exact, ((inputCheck_exact alpha).mp hi).1,
    (cutoffCode_spec alpha).1, (cutoffCode_spec alpha).2, true_and]

theorem strict_endpoint (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0)
    (he : endpointCheck alpha = false) : unionInterpretation (endpointCode (level alpha)) < unionInterpretation alpha := by
  have hle : unionInterpretation (endpointCode (level alpha)) ≤ unionInterpretation alpha :=
    (endpoint_context alpha hl).trans_le (native_base_le alpha hi hl)
  refine lt_of_le_of_ne hle ?_
  intro hv
  have ht := (endpointCheck_exact alpha hi).mpr
    (hv.symm.trans (PublicEpsilonSourceDictionary.endpointCode_value _))
  rw [he] at ht
  cases ht

theorem cancellation_caller (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0)
    (he : endpointCheck alpha = false) : CancellationSupport.inputCheck (endpointCode (level alpha)) alpha = true := by
  have hc := (inputCheck_exact alpha).mp hi
  have hepsilon : Ordinal.omega0 ^ unionInterpretation (endpointCode (level alpha)) =
      unionInterpretation (endpointCode (level alpha)) := by
    cases hm : level alpha with
    | zero => exact False.elim (hl hm)
    | succ s => simpa only [PublicEpsilonSourceDictionary.endpointCode_value, hm] using
        finiteBase_succ_omegaPower_eq_self s
  exact (CancellationSupport.inputCheck_exact _ _).mpr
    ⟨PublicEpsilonSourceDictionary.endpointCode_checked _, hepsilon, hc.1, hc.2.1, hc.2.2,
      strict_endpoint alpha hi hl he⟩

def execute (alpha : Nat) : Part (List Nat) := cond (inputCheck alpha)
  (cond (level alpha == 0) (sourceOneExecute alpha)
    (cond (endpointCheck alpha) (Part.some (baseWord (level alpha)))
      (cond (smallCheck alpha)
        ((Cancellation.execute (endpointCode (level alpha)) alpha).map
          (fun out => baseWord (level alpha) ++ [out]))
        ((nativeExecute alpha).map (fun word => baseWord (level alpha) ++ word))))) Part.none

theorem execute_partrec : Partrec execute := by
  have hb := baseWord_primrec.comp PublicEpsilonSourceDictionary.level_primrec
  have hd := Partrec.comp Cancellation.execute_partrec
    ((PublicEpsilonSourceDictionary.endpointCode_primrec.comp PublicEpsilonSourceDictionary.level_primrec).pair Primrec.id).to_comp
  have hsmall : Computable₂ (fun alpha : Nat => fun out : Nat => baseWord (level alpha) ++ [out]) :=
    (Primrec.list_append.comp (hb.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).to_comp.to₂
  have hlarge : Computable₂ (fun alpha : Nat => fun word : List Nat => baseWord (level alpha) ++ word) :=
    (Primrec.list_append.comp (hb.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond (Primrec.beq.comp PublicEpsilonSourceDictionary.level_primrec (Primrec.const 0)).to_comp
      sourceOneExecute_partrec (Partrec.cond endpointCheck_primrec.to_comp hb.to_comp.partrec
        (Partrec.cond smallCheck_primrec.to_comp (Partrec.map hd hsmall)
          (Partrec.map nativeExecute_partrec hlarge)))) Partrec.none

theorem execute_returns (alpha : Nat) (hi : inputCheck alpha = true) : ∃ codes, codes ∈ execute alpha := by
  cases hz : level alpha == 0 with
  | true =>
    obtain ⟨codes, hc⟩ := sourceOneExecute_returns alpha hi (beq_iff_eq.mp hz)
    exact ⟨codes, by simpa only [execute, hi, hz, Bool.cond_true] using hc⟩
  | false =>
    have hl : level alpha ≠ 0 := by intro he; have ht : (level alpha == 0) = true := beq_iff_eq.mpr he; rw [hz] at ht; cases ht
    cases he : endpointCheck alpha with
    | true =>
      exact ⟨baseWord (level alpha), by simp only [execute, hi, hz, he, Bool.cond_true, Bool.cond_false]; exact Part.mem_some _⟩
    | false =>
      cases hs : smallCheck alpha with
      | true =>
        obtain ⟨out, ho⟩ := Cancellation.execute_returns _ alpha (cancellation_caller alpha hi hl he)
        refine ⟨baseWord (level alpha) ++ [out], ?_⟩
        simpa only [execute, hi, hz, he, hs, Bool.cond_true, Bool.cond_false] using
          Part.mem_map (fun out => baseWord (level alpha) ++ [out]) ho
      | false =>
        obtain ⟨word, hw⟩ := nativeExecute_returns alpha hi hl
        refine ⟨baseWord (level alpha) ++ word, ?_⟩
        simpa only [execute, hi, hz, he, hs, Bool.cond_true, Bool.cond_false] using
          Part.mem_map (fun word => baseWord (level alpha) ++ word) hw

theorem execute_domain (alpha : Nat) : (execute alpha).Dom ↔ inputCheck alpha = true := by
  constructor
  · intro hd
    cases hi : inputCheck alpha with
    | true => rfl
    | false =>
      have hn : (Part.none : Part (List Nat)).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    exact Part.dom_iff_mem.mpr (execute_returns alpha hi)

/-- These are the actual original source clauses of Definition3.24. Each
relative tail or quotient comes from its independently executing procedure. -/
def SourceClauses (alpha : Nat) (codes : List Nat) : Prop :=
  (level alpha = 0 ∧ codes ∈ sourceOneExecute alpha) ∨
  (level alpha ≠ 0 ∧ unionInterpretation alpha = finiteBase (level alpha) ∧ codes = baseWord (level alpha)) ∨
  (level alpha ≠ 0 ∧ unionInterpretation (endpointCode (level alpha)) < unionInterpretation alpha ∧
    unionInterpretation alpha < unionInterpretation (endpointCode (level alpha)) ^ Ordinal.omega0 ∧
      ∃ quotient, quotient ∈ Cancellation.execute (endpointCode (level alpha)) alpha ∧
        codes = baseWord (level alpha) ++ [quotient]) ∨
  (level alpha ≠ 0 ∧ unionInterpretation (endpointCode (level alpha)) ^ Ordinal.omega0 ≤ unionInterpretation alpha ∧
    ∃ tail, tail ∈ nativeExecute alpha ∧ codes = baseWord (level alpha) ++ tail)

theorem execute_clauses (alpha : Nat) (codes : List Nat) (ho : codes ∈ execute alpha) :
    inputCheck alpha = true ∧ SourceClauses alpha codes := by
  have hi := (execute_domain alpha).mp (Part.dom_iff_mem.mpr ⟨codes, ho⟩)
  refine ⟨hi, ?_⟩
  cases hz : level alpha == 0 with
  | true => exact Or.inl ⟨beq_iff_eq.mp hz, by simpa only [execute, hi, hz, Bool.cond_true] using ho⟩
  | false =>
    have hl : level alpha ≠ 0 := by intro he; have ht : (level alpha == 0) = true := beq_iff_eq.mpr he; rw [hz] at ht; cases ht
    cases he : endpointCheck alpha with
    | true =>
      have hc : codes = baseWord (level alpha) := by
        simpa only [execute, hi, hz, he, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using ho
      exact Or.inr (Or.inl ⟨hl, (endpointCheck_exact alpha hi).mp he, hc⟩)
    | false =>
      cases hs : smallCheck alpha with
      | true =>
        have hrun : codes ∈ (Cancellation.execute (endpointCode (level alpha)) alpha).map
            (fun out => baseWord (level alpha) ++ [out]) := by
          simpa only [execute, hi, hz, he, hs, Bool.cond_true, Bool.cond_false] using ho
        obtain ⟨out, hout, hcodes⟩ := (Part.mem_map_iff _).mp hrun
        exact Or.inr (Or.inr (Or.inl ⟨hl, strict_endpoint alpha hi hl he,
          by rw [endpoint_context alpha hl]; exact (smallCheck_exact alpha hi).mp hs,
          out, hout, hcodes.symm⟩))
      | false =>
        have hbound : NativeContext.base (contextCode alpha) ^ Ordinal.omega0 ≤ unionInterpretation alpha :=
          le_of_not_gt (fun h => by have ht := (smallCheck_exact alpha hi).mpr h; rw [hs] at ht; cases ht)
        have hrun : codes ∈ (nativeExecute alpha).map (fun word => baseWord (level alpha) ++ word) := by
          simpa only [execute, hi, hz, he, hs, Bool.cond_true, Bool.cond_false] using ho
        obtain ⟨tail, htail, hcodes⟩ := (Part.mem_map_iff _).mp hrun
        exact Or.inr (Or.inr (Or.inr ⟨hl, by rw [endpoint_context alpha hl]; exact hbound,
          tail, htail, hcodes.symm⟩))

theorem execute_canonical (alpha : Nat) (codes : List Nat) (ho : codes ∈ execute alpha) :
    ∀ c ∈ codes, Canonical.check c = true := by
  rcases (execute_clauses alpha codes ho).2 with ⟨hl, hc⟩ | ⟨hl, he, rfl⟩ |
    ⟨hl, hlt, hb, quotient, hq, rfl⟩ | ⟨hl, hb, tail, ht, rfl⟩
  · exact (sourceOneExecute_spec alpha codes hc).1
  · exact baseWord_canonical _
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact baseWord_canonical _ c hc
    · simpa only [List.mem_singleton.mp hc] using (Cancellation.execute_spec _ _ quotient hq).2.1
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact baseWord_canonical _ c hc
    · exact (nativeExecute_spec alpha tail ht).1 c hc

theorem execute_segment (alpha : Nat) (codes : List Nat) (ho : codes ∈ execute alpha) :
    PublicUpsilonSegment.FirstSegment (unionInterpretation alpha) (PublicUpsilonSegment.segmentValue alpha) :=
  segment_spec alpha (execute_clauses alpha codes ho).1

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking
