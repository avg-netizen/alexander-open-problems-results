import Alexander313.Wilken.HereditarySourceFixedPoint
import Alexander313.Wilken.HereditaryLogEnd

/-!
# Executing source zeta at every original public base

Definition 2.42 uses the STRICT ordinary residual-image supremum test.
The actual cardinal decomposition and fixed-point decision supply that test
on the full argument of a literal admitted normal theta-zero root. Only its
genuinely low residual is passed to the executing last logarithm. The other
branch returns canonical zero. Base one and the base root are included.

The returned code is canonical in the original tagged union; its value has
a derived low representative at the input level. No same-level recoding,
ordinal evaluator, supplied graph or logarithm termination oracle is used.
Execution is partial recursive; its exact numerical graph is PR. The raw
adapter normalizes a literal original theta-zero root with the proved actual
normalizer. No arbitrary-spelling support or localization invariance is used.
These are uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceZeta

open scoped Classical

def inputCheck (r c : Nat) : Bool := Localization.inputCheck r c

theorem inputCheck_primrec : Primrec₂ inputCheck := Localization.inputCheck_primrec

theorem inputCheck_exact (r c : Nat) : inputCheck r c = true ↔ Localization.Node r c :=
  Localization.inputCheck_exact r c

def argumentCode (c : Nat) : Nat := Localization.argumentCode c

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem argument_input (r c : Nat) (hc : inputCheck r c = true) :
    SourceDecomposition.inputCheck r (argumentCode c) = true :=
  (SourceDecomposition.inputCheck_exact r _).mpr
    (Localization.node_argument r c ((inputCheck_exact r c).mp hc))

theorem argument_sorted (r c : Nat) (hc : inputCheck r c = true) :
    interpretation r (argumentCode c) < omegaSequence (finiteBase r) 2 := by
  obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact r c).mp hc
  simpa only [argumentCode, Localization.argumentCode_theta, interpretation_code] using
    SourceFixedPoint.checked_theta_sort r 0 a ha

theorem argument_fixedPoint_input (r c : Nat) (hc : inputCheck r c = true) :
    SourceFixedPoint.inputCheck r 0 (argumentCode c) = true := by
  have ha := (SourceDecomposition.inputCheck_exact r _).mp (argument_input r c hc)
  exact (SourceFixedPoint.inputCheck_exact r 0 _).mpr ⟨ha.1, ha.2, argument_sorted r c hc⟩

def residualCode (r c : Nat) : Nat := Nat.pair r (SourceDecomposition.lowCode r 0 (argumentCode c))

theorem residualCode_primrec : Primrec₂ residualCode :=
  (Primrec₂.natPair.comp Primrec.fst (SourceDecomposition.lowCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair (argumentCode_primrec.comp Primrec.snd))))).to₂

theorem residualCode_checked (r c : Nat) (hc : inputCheck r c = true) :
    unionCheck (residualCode r c) = true := by
  have hi := argument_input r c hc
  have ht := (SourceDecomposition.parts_checked r 0 _ hi).2
  have hs := SourceDecomposition.lowPart_sort r 0 _ hi
  simpa only [residualCode, unionCheck_pair, SourceDecomposition.lowCode,
    lowCheckCode_code, lowCheck, ht, hs, decide_true, Bool.true_and]

theorem residualCode_value (r c : Nat) (hc : inputCheck r c = true) :
    unionInterpretation (residualCode r c) = SourceFixedPoint.residual r 0 (argumentCode c) := by
  simpa only [residualCode, unionInterpretation_pair, SourceFixedPoint.residual] using
    (SourceDecomposition.parts_code_value r 0 _ (argument_input r c hc)).2

theorem residualCode_low (r c : Nat) (hc : inputCheck r c = true) :
    unionInterpretation (residualCode r c) < omegaSequence (finiteBase r) 1 := by
  simpa only [residualCode, unionInterpretation_pair] using
    SourceDecomposition.lowPart_bound r 0 _ (argument_input r c hc)

def strictCheck (r c : Nat) : Bool := SourceFixedPoint.strictCode r 0 (argumentCode c)

theorem strictCheck_primrec : Primrec₂ strictCheck :=
  (SourceFixedPoint.strictCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair (argumentCode_primrec.comp Primrec.snd)))).to₂

theorem strictCheck_exact (r c : Nat) (hc : inputCheck r c = true) :
    strictCheck r c = true ↔ SourceFixedPoint.SourceStrict r 0 (argumentCode c) :=
  SourceFixedPoint.strictCode_correct r 0 _ (argument_fixedPoint_input r c hc)

/-- The mathematical last CNF exponent, with the source convention at zero.
This definition is used only in semantics, never in the executing kernel. -/
noncomputable def lastExponent (η : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.log Ordinal.omega0 (LogEnd.endValue η)

theorem lastExponent_zero : lastExponent 0 = 0 := by
  simp only [lastExponent, LogEnd.endValue, LogEnd.componentValue, canonicalANF_zero,
    List.reverse_nil, Bool.cond_true, List.getElem?_nil, Option.getD_none,
    Ordinal.log_zero_right]

theorem logend_lastExponent (q d : Nat) (hd : d ∈ LogEnd.logend q) :
    unionInterpretation d = lastExponent (unionInterpretation q) := by
  have hs := LogEnd.logend_value q d hd
  by_cases hz : unionInterpretation q = 0
  · have ho : unionInterpretation d = 0 := by
      simpa only [LogEnd.SourceLogSpec, if_pos hz] using hs.2.2
    rw [ho, hz, lastExponent_zero]
  · have hp : Ordinal.omega0 ^ unionInterpretation d = LogEnd.endValue (unionInterpretation q) := by
      simpa only [LogEnd.SourceLogSpec, if_neg hz, LogEnd.endValue] using hs.2.2
    rw [lastExponent, ← hp, Ordinal.log_opow Ordinal.one_lt_omega0]

/-- Literal Definition 2.42 on the actual argument's div/mod pieces. -/
noncomputable def sourceValue (r c : Nat) : Ordinal.{0} :=
  if SourceFixedPoint.SourceStrict r 0 (argumentCode c) then
    lastExponent (SourceFixedPoint.residual r 0 (argumentCode c)) else 0

theorem sourceValue_argument_congr (r c v : Nat)
    (he : interpretation r (argumentCode c) = interpretation r (argumentCode v)) :
    sourceValue r c = sourceValue r v := by
  simp only [sourceValue, SourceFixedPoint.SourceStrict, SourceFixedPoint.delta,
    SourceFixedPoint.residual, he]

def zeta (r c : Nat) : Part Nat := cond (inputCheck r c)
  (cond (strictCheck r c) (LogEnd.logend (residualCode r c)) (Part.some LogEnd.zeroCode)) Part.none

theorem zeta_partrec : Partrec₂ zeta :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond strictCheck_primrec.to_comp
      (LogEnd.logend_partrec.comp residualCode_primrec.to_comp)
      (Computable.const LogEnd.zeroCode).partrec) Partrec.none).to₂

theorem zeta_domain (r c : Nat) : (zeta r c).Dom ↔ inputCheck r c = true := by
  cases hi : inputCheck r c with
  | false => simp only [zeta, hi, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hs : strictCheck r c <;>
      simp only [zeta, hi, hs, Bool.cond_true, Bool.cond_false, LogEnd.logend_domain,
        residualCode_checked r c hi, Part.some_dom]

def graph (r c d : Nat) : Bool := inputCheck r c && cond (strictCheck r c)
  (LogEnd.logGraph true (residualCode r c) d) (d == LogEnd.zeroCode)

theorem graph_primrec : Primrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (inputCheck_primrec.comp hr hc)
    ((strictCheck_primrec.comp hr hc).cond
      (LogEnd.logGraph_primrec.comp ((Primrec.const true).pair
        ((residualCode_primrec.comp hr hc).pair hd)))
      (Primrec.beq.comp hd (Primrec.const LogEnd.zeroCode)))

theorem zeta_graph_iff (r c d : Nat) : d ∈ zeta r c ↔ graph r c d = true := by
  cases hi : inputCheck r c with
  | false => simp only [zeta, graph, hi, Bool.cond_false, Bool.false_and,
      Part.notMem_none, Bool.false_eq_true]
  | true =>
    cases hs : strictCheck r c with
    | false => simp only [zeta, graph, hi, hs, Bool.cond_true, Bool.cond_false,
        Bool.true_and, Part.mem_some_iff, beq_iff_eq]
    | true =>
      simp only [zeta, graph, hi, hs, Bool.cond_true, Bool.true_and]
      exact LogEnd.componentLog_graph_iff true _ d

theorem zeta_value (r c d : Nat) (hd : d ∈ zeta r c) :
    inputCheck r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = sourceValue r c := by
  have hc := (zeta_domain r c).mp (Part.dom_iff_mem.mpr ⟨d, hd⟩)
  refine ⟨hc, ?_⟩
  cases hs : strictCheck r c with
  | false =>
    have he : d = LogEnd.zeroCode := by simpa only [zeta, hc, hs,
      Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using hd
    have hn : ¬ SourceFixedPoint.SourceStrict r 0 (argumentCode c) := by
      intro hp
      have ht := (strictCheck_exact r c hc).mpr hp
      rw [hs] at ht
      contradiction
    rw [he]
    exact ⟨LogEnd.zeroCode_checked, by simp only [sourceValue, if_neg hn, LogEnd.zeroCode_value]⟩
  | true =>
    have hl : d ∈ LogEnd.logend (residualCode r c) := by
      simpa only [zeta, hc, hs, Bool.cond_true] using hd
    exact ⟨(LogEnd.logend_value _ d hl).2.1, by
      rw [sourceValue, if_pos ((strictCheck_exact r c hc).mp hs)]
      exact (logend_lastExponent _ d hl).trans (congrArg lastExponent (residualCode_value r c hc))⟩

theorem zeta_original (r c d : Nat) (hd : d ∈ zeta r c) :
    unionCheck d = true ∧ Theta.Normal d.unpair.1 (ThetaCourse.rawTree d.unpair.2) := by
  have hs := (zeta_value r c d hd).2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem zeta_returns (r c : Nat) (hc : inputCheck r c = true) :
    ∃ d, d ∈ zeta r c ∧ Canonical.check d = true ∧ unionInterpretation d = sourceValue r c := by
  obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp ((zeta_domain r c).mpr hc)
  exact ⟨d, hd, (zeta_value r c d hd).2⟩

theorem graph_exact (r c d : Nat) : graph r c d = true ↔
    inputCheck r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = sourceValue r c := by
  constructor
  · intro hg
    exact zeta_value r c d ((zeta_graph_iff r c d).mpr hg)
  · rintro ⟨hc, hd, hv⟩
    obtain ⟨e, he, hce, hve⟩ := zeta_returns r c hc
    have hde := Canonical.check_value_injective d e hd hce (hv.trans hve.symm)
    rw [hde]
    exact (zeta_graph_iff r c e).mp he

theorem graph_unique (r c : Nat) (hc : inputCheck r c = true) : ∃! d, graph r c d = true := by
  obtain ⟨d, hd, _⟩ := zeta_returns r c hc
  exact ⟨d, (zeta_graph_iff r c d).mp hd, fun e he =>
    Part.mem_unique ((zeta_graph_iff r c e).mpr he) hd⟩

theorem zeta_cnf (r c d : Nat) (hd : d ∈ zeta r c) (xs : List Ordinal.{0})
    (hx : xs.Pairwise (fun a b => b ≤ a))
    (hv : SourceFixedPoint.residual r 0 (argumentCode c) = principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) :
    unionInterpretation d = if SourceFixedPoint.SourceStrict r 0 (argumentCode c) then xs.reverse[0]?.getD 0 else 0 := by
  have hc := (zeta_value r c d hd).1
  cases hs : strictCheck r c with
  | false =>
    have hn : ¬ SourceFixedPoint.SourceStrict r 0 (argumentCode c) := by
      intro hp; have ht := (strictCheck_exact r c hc).mpr hp; rw [hs] at ht; contradiction
    simpa only [sourceValue, if_neg hn] using (zeta_value r c d hd).2.2
  | true =>
    rw [if_pos ((strictCheck_exact r c hc).mp hs)]
    have hl : d ∈ LogEnd.logend (residualCode r c) := by
      simpa only [zeta, hc, hs, Bool.cond_true] using hd
    exact LogEnd.logend_cnf _ d hl xs hx ((residualCode_value r c hc).trans hv)

/-- The actual low residual is below the root, by the original source-hull
tail theorem transported from one genuine finite fragment. -/
theorem residual_lt_root (r c : Nat) (hc : inputCheck r c = true) :
    SourceFixedPoint.residual r 0 (argumentCode c) < interpretation r c := by
  have hi := argument_input r c hc
  let δ := SourceFixedPoint.delta r 0 (argumentCode c)
  let η := SourceFixedPoint.residual r 0 (argumentCode c)
  have hp := SourceDecomposition.parts_checked r 0 _ hi
  have hhigh : denote r (SourceDecomposition.highPartTerm r 0 (argumentCode c)) = δ := by
    simpa only [SourceDecomposition.highCode, interpretation_code, δ,
      SourceFixedPoint.delta] using (SourceDecomposition.parts_code_value r 0 _ hi).1
  let d : GlobalNotationOrdinal (finiteBase r) 1 :=
    ⟨δ, hhigh ▸ SourceFixedPoint.checked_notation_at r
      (SourceDecomposition.highPartTerm r 0 (argumentCode c)) hp.1 1⟩
  have hδ : δ < omegaSequence (finiteBase r) 2 :=
    (Ordinal.mul_div_le _ _).trans_lt (argument_sorted r c hc)
  have hdvd : omegaSequence (finiteBase r) 1 ∣ δ :=
    ⟨interpretation r (argumentCode c) / omegaSequence (finiteBase r) 1, rfl⟩
  have hη : η < omegaSequence (finiteBase r) 1 := by
    have hb := SourceDecomposition.lowPart_bound r 0 _ hi
    rw [(SourceDecomposition.parts_code_value r 0 _ hi).2] at hb
    exact hb
  let n := globalSupportFragment (finiteBase r) (finiteBase_pos r) 0 d
  have hmn : 1 < n := (globalSupportFragment_spec (finiteBase r) (finiteBase_pos r) 0 d).1
  have hm : 0 < n := by omega
  let dn : SourceNotationOrdinal (finiteBase r) n 1 :=
    ⟨δ, (globalSupportFragment_spec (finiteBase r) (finiteBase_pos r) 0 d).2⟩
  have ht := SourceFixedPointLimits.tail_lt_collapse (finiteBase r) (finiteBase_pos r)
    n 0 hm dn hδ hdvd η hη
  have hb := source_finite_notation_sorted_lt_boundary (finiteBase r) (finiteBase_pos r)
    n 1 1 le_rfl hmn
    (SourceFixedPointLimits.shiftArgument (finiteBase r) n 0 hm dn η hη).property
    (SourceFixedPointLimits.shiftArgument_sort (finiteBase r) n 0 hm dn hδ η hη)
  rw [← globalCollapse_finite_agreement (finiteBase r) (finiteBase_pos r) n 0 hm (δ + η) hb] at ht
  have hrec : δ + η = interpretation r (argumentCode c) := Ordinal.div_add_mod _ _
  rw [hrec] at ht
  obtain ⟨a, rfl, _, _⟩ := (inputCheck_exact r c).mp hc
  simpa only [argumentCode, Localization.argumentCode_theta, interpretation_code, denote,
    RelativeTerm.eval] using ht

theorem zeta_bound (r c d : Nat) (hd : d ∈ zeta r c) :
    unionInterpretation d < interpretation r c := by
  have hc := (zeta_value r c d hd).1
  cases hs : strictCheck r c with
  | true =>
    have hl : d ∈ LogEnd.logend (residualCode r c) := by
      simpa only [zeta, hc, hs, Bool.cond_true] using hd
    exact ((LogEnd.componentLog_bound true _ d hl).trans_eq
      (residualCode_value r c hc)).trans_lt (residual_lt_root r c hc)
  | false =>
    have he : d = LogEnd.zeroCode := by simpa only [zeta, hc, hs,
      Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using hd
    rw [he, LogEnd.zeroCode_value]
    obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact r c).mp hc
    simpa only [interpretation_code, omegaSequence_zero] using
      (finiteBase_pos r).trans_le (SourceFixedPoint.checked_theta_range r 0 a ha).1

theorem zeta_level_representative (r c d : Nat) (hd : d ∈ zeta r c) :
    ∃ e : Nat, lowCheckCode r e = true ∧ interpretation r e = unionInterpretation d := by
  have hc := (inputCheck_exact r c).mp (zeta_value r c d hd).1
  have hr : interpretation r c < finiteBase (r + 1) :=
    (lt_nextBase_iff_code r _).mpr ⟨c, Localization.node_low r c hc, rfl⟩
  exact (lt_nextBase_iff_code r _).mp ((zeta_bound r c d hd).trans hr)

theorem zeta_zero_residual (r c : Nat) (hc : inputCheck r c = true)
    (hz : SourceFixedPoint.residual r 0 (argumentCode c) = 0) :
    zeta r c = Part.some LogEnd.zeroCode := by
  have hn : ¬ SourceFixedPoint.SourceStrict r 0 (argumentCode c) := by
    simp only [SourceFixedPoint.SourceStrict, hz, SourceFixedPointLimits.globalResidualImageSup,
      Ordinal.bsup_zero, lt_self_iff_false, not_false_eq_true]
  have hs : strictCheck r c = false := by
    cases hs : strictCheck r c with
    | false => rfl
    | true => exact False.elim (hn ((strictCheck_exact r c hc).mp hs))
  simp only [zeta, hc, hs, Bool.cond_true, Bool.cond_false]

theorem zeta_base (r : Nat) : zeta r (Localization.baseRaw r) = Part.some LogEnd.zeroCode := by
  apply zeta_zero_residual r _ ((inputCheck_exact r _).mpr (Localization.baseRaw_node r))
  simp only [SourceFixedPoint.residual, argumentCode, Localization.baseRaw,
    Localization.argumentCode_theta, interpretation_code, zeroTree_denote, Ordinal.zero_mod]

/-- The base-one residual-one ordinary supremum is fixed, so it also
returns zero rather than entering the last-logarithm branch. -/
theorem zeta_unit_boundary (c : Nat) (hc : inputCheck 0 c = true)
    (hd : SourceFixedPoint.delta 0 0 (argumentCode c) = 0)
    (he : SourceFixedPoint.residual 0 0 (argumentCode c) = 1) :
    zeta 0 c = Part.some LogEnd.zeroCode := by
  have hsup : SourceFixedPointLimits.globalResidualImageSup 1 0 0 1 = 1 := by
    rw [SourceFixedPointLimits.globalResidualImageSup, Ordinal.bsup_one, zero_add]
    simpa only [omegaSequence_zero] using
      globalCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one 0
  have hn : ¬ SourceFixedPoint.SourceStrict 0 0 (argumentCode c) := by
    simp only [SourceFixedPoint.SourceStrict, hd, he, finiteBase_zero, hsup,
      lt_self_iff_false, not_false_eq_true]
  have hs : strictCheck 0 c = false := by
    cases hs : strictCheck 0 c with
    | false => rfl
    | true => exact False.elim (hn ((strictCheck_exact 0 c hc).mp hs))
  simp only [zeta, hc, hs, Bool.cond_true, Bool.cond_false]

def rawInputCheck (r c : Nat) : Bool := checkCode r c && Localization.rootShape c

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck :=
  (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (Localization.rootShape_primrec.comp Primrec.snd)).to₂

theorem rawInputCheck_exact (r c : Nat) : rawInputCheck r c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true := by
  constructor
  · intro hc
    obtain ⟨ht, hs⟩ := Bool.and_eq_true.mp hc
    obtain ⟨t, he, ha⟩ := (checkCode_iff r c).mp ht
    obtain ⟨a, hta⟩ := (Localization.rootShape_code t).mp (by simpa only [← he] using hs)
    subst t
    exact ⟨a, he.symm, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact Bool.and_eq_true.mpr ⟨by simpa only [checkCode_code] using ha,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩

theorem raw_normalized_input (r c : Nat) (hc : rawInputCheck r c = true) :
    inputCheck r (Theta.Normalization.normalizeCode r c) = true := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact r c).mp hc
  have hn := Theta.Normalization.normalizeCode_checked r (.theta 0 a).code
    (by simpa only [checkCode_code] using ha)
  apply (inputCheck_exact r _).mpr
  refine ⟨Theta.Normalization.normalize r a, ?_, ?_, ?_⟩
  · simp only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta]
  · simpa only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta,
      checkCode_code] using hn.1
  · simpa only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta,
      ThetaCourse.rawTree_code] using hn.2.1

theorem raw_argument_value (r c : Nat) (hc : rawInputCheck r c = true) :
    interpretation r (argumentCode (Theta.Normalization.normalizeCode r c)) = interpretation r (argumentCode c) := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact r c).mp hc
  have haa := SourceFixedPoint.checked_theta_argument r 0 a ha
  have hn := Theta.Normalization.normalizeCode_checked r a.code (by simpa only [checkCode_code] using haa)
  simpa only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta,
    argumentCode, Localization.argumentCode_theta] using hn.2.2

def rawZeta (r c : Nat) : Part Nat := cond (rawInputCheck r c)
  (zeta r (Theta.Normalization.normalizeCode r c)) Part.none

theorem rawZeta_partrec : Partrec₂ rawZeta :=
  (Partrec.cond rawInputCheck_primrec.to_comp
    (zeta_partrec.comp Computable.fst Theta.Normalization.Effective.normalizeCode_primrec.to_comp)
    Partrec.none).to₂

theorem rawZeta_domain (r c : Nat) : (rawZeta r c).Dom ↔ rawInputCheck r c = true := by
  cases hc : rawInputCheck r c with
  | false => simp only [rawZeta, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [rawZeta, hc, Bool.cond_true, zeta_domain, raw_normalized_input r c hc]

def rawGraph (r c d : Nat) : Bool := rawInputCheck r c &&
  graph r (Theta.Normalization.normalizeCode r c) d

theorem rawGraph_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawGraph p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (rawInputCheck_primrec.comp hr hc)
    (graph_primrec.comp (hr.pair ((Theta.Normalization.Effective.normalizeCode_primrec.comp hr hc).pair hd)))

theorem rawZeta_graph_iff (r c d : Nat) : d ∈ rawZeta r c ↔ rawGraph r c d = true := by
  cases hc : rawInputCheck r c <;> simp only [rawZeta, rawGraph, hc, Bool.cond_true,
    Bool.cond_false, Bool.true_and, Bool.false_and, Part.notMem_none, Bool.false_eq_true, zeta_graph_iff]

theorem rawZeta_value (r c d : Nat) (hd : d ∈ rawZeta r c) :
    rawInputCheck r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = sourceValue r c := by
  have hc := (rawZeta_domain r c).mp (Part.dom_iff_mem.mpr ⟨d, hd⟩)
  have hm : d ∈ zeta r (Theta.Normalization.normalizeCode r c) := by
    simpa only [rawZeta, hc, Bool.cond_true] using hd
  have hs := zeta_value r _ d hm
  exact ⟨hc, hs.2.1, hs.2.2.trans (sourceValue_argument_congr r _ c (raw_argument_value r c hc))⟩

theorem rawGraph_exact (r c d : Nat) : rawGraph r c d = true ↔
    rawInputCheck r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = sourceValue r c := by
  constructor
  · intro hg
    exact rawZeta_value r c d ((rawZeta_graph_iff r c d).mpr hg)
  · rintro ⟨hc, hd, hv⟩
    apply Bool.and_eq_true.mpr
    refine ⟨hc, (graph_exact r _ d).mpr ⟨raw_normalized_input r c hc, hd, ?_⟩⟩
    exact hv.trans (sourceValue_argument_congr r _ c (raw_argument_value r c hc)).symm

theorem rawZeta_bound (r c d : Nat) (hd : d ∈ rawZeta r c) :
    unionInterpretation d < interpretation r c := by
  have hc := (rawZeta_value r c d hd).1
  have hm : d ∈ zeta r (Theta.Normalization.normalizeCode r c) := by
    simpa only [rawZeta, hc, Bool.cond_true] using hd
  have hn := Theta.Normalization.normalizeCode_checked r c (Bool.and_eq_true.mp hc).1
  exact (zeta_bound r _ d hm).trans_eq hn.2.2

theorem rawGraph_unique (r c : Nat) (hc : rawInputCheck r c = true) : ∃! d, rawGraph r c d = true := by
  obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp ((rawZeta_domain r c).mpr hc)
  exact ⟨d, (rawZeta_graph_iff r c d).mp hd, fun e he =>
    Part.mem_unique ((rawZeta_graph_iff r c e).mpr he) hd⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceZeta
