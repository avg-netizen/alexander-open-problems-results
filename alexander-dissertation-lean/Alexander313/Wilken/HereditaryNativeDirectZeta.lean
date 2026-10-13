import Alexander313.Wilken.HereditaryNativeLogEnd
import Alexander313.Wilken.HereditaryNativeSourceZeta

/-!
# Direct original zeta execution at every coded epsilon

The original checked Normal theta-zero root supplies its true cardinal
div/mod pieces. The genuine STRICT residual-supremum test selects the
actual native last logarithm on the LOW residual, or the actual zero
numeral. A genuine finite fragment of the derived high part transports
the source tail theorem and proves that the output is below the root.
Every caller is derived from the original root guard. No public recoder,
strictness, logarithm, fragment or output oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta

def inputCheck (q c : Nat) : Bool := Comparison.acceptedCode q c && Localization.rootShape c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp Comparison.acceptedCode_primrec
    (Localization.rootShape_primrec.comp Primrec.snd)).to₂

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check q (.theta 0 a) = true ∧
      Comparison.Normal q (.theta 0 a) := by
  constructor
  · intro hc
    obtain ⟨ht, hs⟩ := Bool.and_eq_true.mp hc
    have hn := (Comparison.acceptedCode_exact q c).mp ht
    obtain ⟨t, he, ha⟩ := (checkCode_exact q c).mp hn.1
    obtain ⟨a, hta⟩ := (Localization.rootShape_code t).mp (by simpa only [← he] using hs)
    subst t
    exact ⟨a, he.symm, ha, by simpa only [← he, ThetaCourse.rawTree_code] using hn.2⟩
  · rintro ⟨a, rfl, ha, hn⟩
    exact Bool.and_eq_true.mpr ⟨(Comparison.acceptedCode_exact q _).mpr
      ⟨by simpa only [checkCode_code] using ha, by simpa only [ThetaCourse.rawTree_code] using hn⟩,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩

def argumentCode (c : Nat) : Nat := Localization.argumentCode c

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem argument_input (q c : Nat) (hc : inputCheck q c = true) :
    Decomposition.inputCheck q (argumentCode c) = true := by
  obtain ⟨a, rfl, ha, hn⟩ := (inputCheck_exact q c).mp hc
  apply (Decomposition.inputCheck_exact q _).mpr
  exact ⟨by simpa only [argumentCode, Localization.argumentCode_theta, checkCode_code] using
      FixedPoint.checked_theta_argument q 0 a ha,
    by simpa only [argumentCode, Localization.argumentCode_theta, ThetaCourse.rawTree_code,
      Comparison.Normal] using hn⟩

theorem argument_sorted (q c : Nat) (hc : inputCheck q c = true) :
    interpretation q (argumentCode c) < omegaSequence (base q) 2 := by
  obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact q c).mp hc
  simpa only [argumentCode, Localization.argumentCode_theta, interpretation_code] using
    FixedPoint.checked_theta_sort q 0 a ha

theorem argument_fixedPoint_input (q c : Nat) (hc : inputCheck q c = true) :
    FixedPoint.inputCheck q 0 (argumentCode c) = true := by
  have ha := (Decomposition.inputCheck_exact q _).mp (argument_input q c hc)
  exact (FixedPoint.inputCheck_exact q 0 _).mpr ⟨ha.1, ha.2, argument_sorted q c hc⟩

def residualCode (c : Nat) : Nat := Decomposition.lowCode 0 (argumentCode c)

theorem residualCode_primrec : Primrec residualCode :=
  Decomposition.lowCode_primrec.comp (Primrec.const 0) argumentCode_primrec

theorem residualCode_spec (q c : Nat) (hc : inputCheck q c = true) :
    lowCheckCode q (residualCode c) = true ∧
      Comparison.acceptedCode q (residualCode c) = true ∧
      interpretation q (residualCode c) = FixedPoint.residual q 0 (argumentCode c) := by
  have hi := argument_input q c hc
  have ha := (Decomposition.parts_accepted q 0 _ hi).2
  exact ⟨OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp ha).1
      (Decomposition.lowPart_bound q 0 _ hi), ha, (Decomposition.parts_code_value q 0 _ hi).2⟩

def strictCheck (q c : Nat) : Bool := FixedPoint.strictCode q 0 (argumentCode c)

theorem strictCheck_primrec : Primrec₂ strictCheck :=
  (FixedPoint.strictCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair (argumentCode_primrec.comp Primrec.snd)))).to₂

theorem strictCheck_exact (q c : Nat) (hc : inputCheck q c = true) :
    strictCheck q c = true ↔ FixedPoint.SourceStrict q 0 (argumentCode c) :=
  FixedPoint.strictCode_correct q 0 _ (argument_fixedPoint_input q c hc)

noncomputable def sourceValue (q c : Nat) : Ordinal.{0} :=
  if FixedPoint.SourceStrict q 0 (argumentCode c) then
    Hereditary.SourceZeta.lastExponent (FixedPoint.residual q 0 (argumentCode c)) else 0

theorem sourceValue_argument_congr (q c d : Nat)
    (he : interpretation q (argumentCode c) = interpretation q (argumentCode d)) :
    sourceValue q c = sourceValue q d := by
  simp only [sourceValue, FixedPoint.SourceStrict, FixedPoint.delta, FixedPoint.residual, he]

def execute (q c : Nat) : Part Nat := cond (inputCheck q c)
  (cond (strictCheck q c) (LogEnd.execute q (residualCode c))
    (Part.some (OmegaPowerHeight.numeralCode 0))) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond strictCheck_primrec.to_comp
      (LogEnd.execute_partrec.comp Computable.fst (residualCode_primrec.comp Primrec.snd).to_comp)
      (Computable.const (OmegaPowerHeight.numeralCode 0)).partrec) Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ inputCheck q c = true := by
  cases hi : inputCheck q c with
  | false => simp only [execute, hi, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hs : strictCheck q c <;>
      simp only [execute, hi, hs, Bool.cond_true, Bool.cond_false, LogEnd.execute_domain,
        (residualCode_spec q c hi).1, Part.some_dom]

theorem execute_returns (q c : Nat) (hc : inputCheck q c = true) : ∃ out, out ∈ execute q c :=
  Part.dom_iff_mem.mp ((execute_domain q c).mpr hc)

theorem lastExponent_of_spec (ξ η : Ordinal.{0})
    (hs : Hereditary.LogEnd.SourceLogSpec true ξ η) : η = Hereditary.SourceZeta.lastExponent ξ := by
  by_cases hz : ξ = 0
  · have he : η = 0 := by simpa only [Hereditary.LogEnd.SourceLogSpec, if_pos hz] using hs
    rw [he, hz, Hereditary.SourceZeta.lastExponent_zero]
  · have hp : Ordinal.omega0 ^ η = Hereditary.LogEnd.endValue ξ := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz, Hereditary.LogEnd.endValue] using hs
    rw [Hereditary.SourceZeta.lastExponent, ← hp, Ordinal.log_opow Ordinal.one_lt_omega0]

/-- The executing finite branches realize the original Definition 2.42
using its actual STRICT residual supremum at the same coded epsilon. -/
theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    inputCheck q c = true ∧ lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      interpretation q out = sourceValue q c := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hs : strictCheck q c with
  | true =>
    have hm : out ∈ LogEnd.execute q (residualCode c) := by
      simpa only [execute, hc, hs, Bool.cond_true] using ho
    have hv := LogEnd.execute_spec q _ out hm
    refine ⟨hc, hv.2.1, hv.2.2.1, ?_⟩
    rw [sourceValue, if_pos ((strictCheck_exact q c hc).mp hs)]
    exact (lastExponent_of_spec _ _ hv.2.2.2).trans
      (congrArg Hereditary.SourceZeta.lastExponent (residualCode_spec q c hc).2.2)
  | false =>
    have he : out = OmegaPowerHeight.numeralCode 0 := by
      simpa only [execute, hc, hs, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using ho
    subst out
    obtain ⟨a, ht, ha, hn⟩ := (inputCheck_exact q c).mp hc
    have hz := OmegaPowerHeight.numeralCode_spec q 0 (Bool.and_eq_true.mp ha).1
    have hns : ¬ FixedPoint.SourceStrict q 0 (argumentCode c) := by
      intro h
      have hp := (strictCheck_exact q c hc).mpr h
      simp only [hs, Bool.false_eq_true] at hp
    exact ⟨hc, hz.1, hz.2.1, by simp only [sourceValue, if_neg hns, hz.2.2.1, Nat.cast_zero]⟩

/-- The original low tail bound is transported from a genuinely derived
finite fragment of the actual high part; no fragment is supplied. -/
theorem residual_lt_root (q c : Nat) (hc : inputCheck q c = true) :
    FixedPoint.residual q 0 (argumentCode c) < interpretation q c := by
  have hi := argument_input q c hc
  have hq := (Bool.and_eq_true.mp (Decomposition.input_tree q _ hi).1).1
  have hpos := base_pos q hq
  let δ := FixedPoint.delta q 0 (argumentCode c)
  let η := FixedPoint.residual q 0 (argumentCode c)
  have hp := Decomposition.parts_checked q 0 _ hi
  have hhigh : denote q (Decomposition.highPartTerm 0 (argumentCode c)) = δ := by
    simpa only [Decomposition.highCode, interpretation_code, δ, FixedPoint.delta] using
      (Decomposition.parts_code_value q 0 _ hi).1
  let d : GlobalNotationOrdinal (base q) 1 :=
    ⟨δ, hhigh ▸ FixedPoint.checked_notation_at q
      (Decomposition.highPartTerm 0 (argumentCode c)) hp.1 1⟩
  have hδ : δ < omegaSequence (base q) 2 :=
    (Ordinal.mul_div_le _ _).trans_lt (argument_sorted q c hc)
  have hdvd : omegaSequence (base q) 1 ∣ δ :=
    ⟨interpretation q (argumentCode c) / omegaSequence (base q) 1, rfl⟩
  have hη : η < omegaSequence (base q) 1 := by
    have hb := Decomposition.lowPart_bound q 0 _ hi
    rw [(Decomposition.parts_code_value q 0 _ hi).2] at hb
    exact hb
  let n := globalSupportFragment (base q) hpos 0 d
  have hmn : 1 < n := (globalSupportFragment_spec (base q) hpos 0 d).1
  have hm : 0 < n := by omega
  let dn : SourceNotationOrdinal (base q) n 1 :=
    ⟨δ, (globalSupportFragment_spec (base q) hpos 0 d).2⟩
  have ht := SourceFixedPointLimits.tail_lt_collapse (base q) hpos n 0 hm dn hδ hdvd η hη
  have hb := source_finite_notation_sorted_lt_boundary (base q) hpos n 1 1 le_rfl hmn
    (SourceFixedPointLimits.shiftArgument (base q) n 0 hm dn η hη).property
    (SourceFixedPointLimits.shiftArgument_sort (base q) n 0 hm dn hδ η hη)
  rw [← globalCollapse_finite_agreement (base q) hpos n 0 hm (δ + η) hb] at ht
  have hrec : δ + η = interpretation q (argumentCode c) := Ordinal.div_add_mod _ _
  rw [hrec] at ht
  obtain ⟨a, rfl, _, _⟩ := (inputCheck_exact q c).mp hc
  simpa only [argumentCode, Localization.argumentCode_theta, interpretation_code, denote,
    RelativeTerm.eval] using ht

theorem execute_bound (q c out : Nat) (ho : out ∈ execute q c) :
    interpretation q out < interpretation q c := by
  have hc := (execute_spec q c out ho).1
  cases hs : strictCheck q c with
  | true =>
    have hl : out ∈ LogEnd.execute q (residualCode c) := by
      simpa only [execute, hc, hs, Bool.cond_true] using ho
    exact ((LogEnd.execute_bound q _ out hl).trans_eq
      (residualCode_spec q c hc).2.2).trans_lt (residual_lt_root q c hc)
  | false =>
    have he : out = OmegaPowerHeight.numeralCode 0 := by
      simpa only [execute, hc, hs, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using ho
    subst out
    obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact q c).mp hc
    have hq := (Bool.and_eq_true.mp ha).1
    rw [(OmegaPowerHeight.numeralCode_spec q 0 hq).2.2.1, Nat.cast_zero, interpretation_code]
    exact (base_pos q hq).trans_le (by
      simpa only [omegaSequence_zero] using (FixedPoint.checked_theta_range q 0 a ha).1)

theorem execute_standard_value (s c out : Nat)
    (ho : out ∈ execute (NativePublicBridge.contextCode s) c) :
    interpretation (NativePublicBridge.contextCode s) out = SourceZeta.sourceValue s c :=
  (execute_spec _ c out ho).2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta
