import Alexander313.Wilken.HereditaryCanonicalCoefficients
import Alexander313.Wilken.HereditaryPrincipalLogarithm

/-!
# Actual greatest/end components and first/last exponents

Wilken's Section 2 preliminaries define mc and end as the first and last
summands of actual ANF, with zero at zero. Logend is zero at zero and the last
exponent of actual expanded CNF. The canonical coefficient word supplies real
canonical principal heads. A PR first/reversed-first selection returns those
heads, with a canonical zero fallback. The admitted zero branch returns zero;
the nonzero branch executes the previously constructed principal logarithm.
No component parser, logarithm graph, ordinal chooser or termination oracle is
an input. The literal CNF specification below proves the source correspondence.
All terms are uncompiled. The inherited Nat.rfind_spec signature has been
verified by reading the exact pinned local Mathlib source.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.LogEnd

def zeroCode : Nat := Canonical.canonicalize Alexander313.HereditaryOrdinalLabels.zeroCode

theorem zeroCode_checked : Canonical.check zeroCode = true :=
  Canonical.canonicalize_check _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked

theorem zeroCode_value : unionInterpretation zeroCode = 0 :=
  (Canonical.canonicalize_value _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked).trans
    Alexander313.HereditaryOrdinalLabels.zeroCode_value

/-- False selects mc; true selects end. -/
def orientedWord (last : Bool) (q : Nat) : List Nat :=
  cond last (CanonicalCoefficients.word q).reverse (CanonicalCoefficients.word q)

theorem orientedWord_primrec : Primrec₂ orientedWord :=
  (Primrec.fst.cond
    (Primrec.list_reverse.comp (CanonicalCoefficients.word_primrec.comp Primrec.snd))
    (CanonicalCoefficients.word_primrec.comp Primrec.snd)).to₂

def componentCode (last : Bool) (q : Nat) : Nat := (orientedWord last q)[0]?.getD zeroCode

theorem componentCode_primrec : Primrec₂ componentCode :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp orientedWord_primrec (Primrec.const 0))
    (Primrec.const zeroCode)).to₂

def mcCode (q : Nat) : Nat := componentCode false q

def endCode (q : Nat) : Nat := componentCode true q

theorem mcCode_primrec : Primrec mcCode := componentCode_primrec.comp (Primrec.const false) Primrec.id

theorem endCode_primrec : Primrec endCode := componentCode_primrec.comp (Primrec.const true) Primrec.id

noncomputable def componentValue (last : Bool) (ξ : Ordinal.{0}) : Ordinal.{0} :=
  (cond last (canonicalANF ξ).reverse (canonicalANF ξ))[0]?.getD 0

noncomputable def mc (ξ : Ordinal.{0}) : Ordinal.{0} := componentValue false ξ

noncomputable def endValue (ξ : Ordinal.{0}) : Ordinal.{0} := componentValue true ξ

theorem componentValue_of_anf (last : Bool) (ξ : Ordinal.{0}) (xs : List Ordinal.{0})
    (hn : IsAdditiveNormalForm xs) (hv : ξ = principalSum xs) :
    componentValue last ξ = (cond last xs.reverse xs)[0]?.getD 0 := by
  rw [componentValue, canonicalANF_eq_of_normal hn hv.symm]

theorem mc_of_anf (ξ : Ordinal.{0}) (xs : List Ordinal.{0})
    (hn : IsAdditiveNormalForm xs) (hv : ξ = principalSum xs) : mc ξ = xs[0]?.getD 0 :=
  componentValue_of_anf false ξ xs hn hv

theorem endValue_of_anf (ξ : Ordinal.{0}) (xs : List Ordinal.{0})
    (hn : IsAdditiveNormalForm xs) (hv : ξ = principalSum xs) : endValue ξ = xs.reverse[0]?.getD 0 :=
  componentValue_of_anf true ξ xs hn hv

theorem word_nil_iff (q : Nat) (hq : unionCheck q = true) :
    CanonicalCoefficients.word q = [] ↔ unionInterpretation q = 0 := by
  constructor
  · intro hw
    have h := principalSum_canonicalANF (unionInterpretation q)
    rw [← CanonicalCoefficients.word_anf q hq, hw] at h
    exact h.symm
  · intro hz
    have h := CanonicalCoefficients.word_anf q hq
    rw [hz, canonicalANF_zero] at h
    exact List.map_eq_nil_iff.mp h

theorem orientedWord_nil_iff (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    orientedWord last q = [] ↔ unionInterpretation q = 0 := by
  cases last <;> simpa [orientedWord] using word_nil_iff q hq

theorem orientedWord_mem_iff (last : Bool) (q c : Nat) :
    c ∈ orientedWord last q ↔ c ∈ CanonicalCoefficients.word q := by
  cases last <;> simp [orientedWord]

theorem componentCode_zero (last : Bool) (q : Nat) (hq : unionCheck q = true)
    (hz : unionInterpretation q = 0) : componentCode last q = zeroCode := by
  rw [componentCode, (orientedWord_nil_iff last q hq).mpr hz]
  rfl

theorem componentCode_mem (last : Bool) (q : Nat) (hq : unionCheck q = true)
    (hn : unionInterpretation q ≠ 0) : componentCode last q ∈ CanonicalCoefficients.word q := by
  apply (orientedWord_mem_iff last q _).mp
  have hne : orientedWord last q ≠ [] := fun h => hn ((orientedWord_nil_iff last q hq).mp h)
  cases hw : orientedWord last q with
  | nil => exact False.elim (hne hw)
  | cons c cs =>
    rw [componentCode, hw]
    exact List.mem_cons_self

theorem componentCode_principal (last : Bool) (q : Nat) (hq : unionCheck q = true)
    (hn : unionInterpretation q ≠ 0) :
    Canonical.check (componentCode last q) = true ∧ 0 < unionInterpretation (componentCode last q) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (componentCode last q)) :=
  CanonicalCoefficients.word_head_spec q hq _ (componentCode_mem last q hq hn)

theorem componentCode_checked (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (componentCode last q) = true := by
  by_cases hz : unionInterpretation q = 0
  · rw [componentCode_zero last q hq hz]; exact zeroCode_checked
  · exact (componentCode_principal last q hq hz).1

theorem componentCode_original (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    unionCheck (componentCode last q) = true := Canonical.check_original (componentCode_checked last q hq)

theorem componentCode_normal (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    Theta.Normal (componentCode last q).unpair.1 (ThetaCourse.rawTree (componentCode last q).unpair.2) :=
  Canonical.check_normal (componentCode_checked last q hq)

theorem mcCode_checked (q : Nat) (hq : unionCheck q = true) : Canonical.check (mcCode q) = true :=
  componentCode_checked false q hq

theorem endCode_checked (q : Nat) (hq : unionCheck q = true) : Canonical.check (endCode q) = true :=
  componentCode_checked true q hq

theorem mcCode_principal (q : Nat) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q) :
    Canonical.check (mcCode q) = true ∧ 0 < unionInterpretation (mcCode q) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (mcCode q)) :=
  componentCode_principal false q hq (ne_of_gt hp)

theorem endCode_principal (q : Nat) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q) :
    Canonical.check (endCode q) = true ∧ 0 < unionInterpretation (endCode q) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (endCode q)) :=
  componentCode_principal true q hq (ne_of_gt hp)

private theorem first_map (f : Nat → Ordinal.{0}) (xs : List Nat) (z : Nat) :
    f (xs[0]?.getD z) = (xs.map f)[0]?.getD (f z) := by
  cases xs <;> rfl

theorem orientedWord_anf (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    (orientedWord last q).map unionInterpretation =
      cond last (canonicalANF (unionInterpretation q)).reverse (canonicalANF (unionInterpretation q)) := by
  cases last <;> simp only [orientedWord, Bool.cond_false, Bool.cond_true, List.map_reverse,
    CanonicalCoefficients.word_anf q hq]

theorem componentCode_value (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (componentCode last q) = componentValue last (unionInterpretation q) := by
  rw [componentCode, first_map unionInterpretation (orientedWord last q) zeroCode, zeroCode_value, orientedWord_anf last q hq]
  rfl

theorem mcCode_value (q : Nat) (hq : unionCheck q = true) : unionInterpretation (mcCode q) = mc (unionInterpretation q) :=
  componentCode_value false q hq

theorem mcCode_anf_cons (q : Nat) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q) :
    ∃ xs : List Ordinal.{0}, canonicalANF (unionInterpretation q) = unionInterpretation (mcCode q) :: xs := by
  have hne : CanonicalCoefficients.word q ≠ [] := fun hw =>
    (ne_of_gt hp) ((word_nil_iff q hq).mp hw)
  cases hw : CanonicalCoefficients.word q with
  | nil => exact False.elim (hne hw)
  | cons c cs =>
    refine ⟨cs.map unionInterpretation, ?_⟩
    rw [← CanonicalCoefficients.word_anf q hq, hw]
    have hmc : mcCode q = c := congrArg (fun xs : List Nat => xs[0]?.getD zeroCode) hw
    simpa only [List.map_cons, hmc]

theorem mcCode_greatest (q : Nat) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q)
    (a : Ordinal.{0}) (ha : a ∈ canonicalANF (unionInterpretation q)) : a ≤ unionInterpretation (mcCode q) := by
  obtain ⟨xs, hxs⟩ := mcCode_anf_cons q hq hp
  have hn := canonicalANF_normal (unionInterpretation q)
  rw [hxs] at hn ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact le_rfl
  · exact additiveNormalForm_head_ge hn ha

theorem endCode_value (q : Nat) (hq : unionCheck q = true) : unionInterpretation (endCode q) = endValue (unionInterpretation q) :=
  componentCode_value true q hq

theorem componentCode_anf (last : Bool) (q : Nat) (hq : unionCheck q = true)
    (hn : unionInterpretation q ≠ 0) :
    unionInterpretation (componentCode last q) ∈ canonicalANF (unionInterpretation q) := by
  rw [← CanonicalCoefficients.word_anf q hq]
  exact List.mem_map.mpr ⟨_, componentCode_mem last q hq hn, rfl⟩

theorem componentCode_le (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (componentCode last q) ≤ unionInterpretation q := by
  by_cases hz : unionInterpretation q = 0
  · rw [componentCode_zero last q hq hz, zeroCode_value, hz]
  · exact canonicalANF_mem_le (componentCode_anf last q hq hz)

theorem componentCode_invariant (last : Bool) (q v : Nat) (hq : unionCheck q = true)
    (hv : unionCheck v = true) (he : unionInterpretation q = unionInterpretation v) :
    componentCode last q = componentCode last v := by
  simp only [componentCode, orientedWord, CanonicalCoefficients.word_invariant q v hq hv he]

def componentGraph (last : Bool) (q c : Nat) : Bool := unionCheck q && (c == componentCode last q)

theorem componentGraph_primrec : Primrec (fun p : Bool × (Nat × Nat) => componentGraph p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Uniform.unionCheck_primrec.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.snd)
      (componentCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))

theorem componentGraph_exact (last : Bool) (q c : Nat) : componentGraph last q c = true ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = componentValue last (unionInterpretation q) := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    have hc := beq_iff_eq.mp hs.2
    rw [hc]
    exact ⟨hs.1, componentCode_checked last q hs.1, componentCode_value last q hs.1⟩
  · rintro ⟨hq, hc, hv⟩
    exact Bool.and_eq_true_iff.mpr ⟨hq, beq_iff_eq.mpr (Canonical.check_value_injective c _ hc
      (componentCode_checked last q hq) (hv.trans (componentCode_value last q hq).symm))⟩

theorem componentGraph_unique (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, componentGraph last q c = true := by
  refine ⟨componentCode last q, Bool.and_eq_true_iff.mpr ⟨hq, beq_iff_eq.mpr rfl⟩, ?_⟩
  intro c hc
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2

def zeroCheck (q : Nat) : Bool := (CanonicalCoefficients.word q).length == 0

theorem zeroCheck_primrec : Primrec zeroCheck :=
  Primrec.beq.comp (Primrec.list_length.comp CanonicalCoefficients.word_primrec) (Primrec.const 0)

theorem zeroCheck_exact (q : Nat) (hq : unionCheck q = true) :
    zeroCheck q = true ↔ unionInterpretation q = 0 := by
  simp only [zeroCheck, beq_iff_eq, List.length_eq_zero_iff, word_nil_iff q hq]

/-- Original admission is checked even when the computed word is empty. -/
def componentLog (last : Bool) (q : Nat) : Part Nat :=
  cond (unionCheck q)
    (cond (zeroCheck q) (Part.some zeroCode) (PrincipalLogarithm.logarithm (componentCode last q))) Part.none

theorem componentLog_partrec : Partrec₂ componentLog := by
  have hu : Computable (fun p : Bool × Nat => unionCheck p.2) := (Uniform.unionCheck_primrec.comp Primrec.snd).to_comp
  have hz : Computable (fun p : Bool × Nat => zeroCheck p.2) := (zeroCheck_primrec.comp Primrec.snd).to_comp
  have hl := PrincipalLogarithm.logarithm_partrec.comp componentCode_primrec.to_comp
  exact (Partrec.cond hu (Partrec.cond hz (Computable.const zeroCode).partrec hl) Partrec.none).to₂

theorem componentLog_domain (last : Bool) (q : Nat) :
    (componentLog last q).Dom ↔ unionCheck q = true := by
  cases hq : unionCheck q with
  | false => simp [componentLog, hq]
  | true =>
    cases hz : zeroCheck q with
    | true => simp [componentLog, hq, hz]
    | false =>
      have hn : unionInterpretation q ≠ 0 := by
        intro he
        have ht := (zeroCheck_exact q hq).mpr he
        rw [hz] at ht
        contradiction
      have hs := componentCode_principal last q hq hn
      have hp := (Principal.unionPrincipalCheck_exact _).mpr
        ⟨Canonical.check_original hs.1, hs.2.1, hs.2.2⟩
      simp [componentLog, hq, hz, PrincipalLogarithm.logarithm_domain, hp]

def logGraph (last : Bool) (q c : Nat) : Bool :=
  unionCheck q && cond (zeroCheck q) (c == zeroCode) (PrincipalLogarithm.graph (componentCode last q) c)

theorem logGraph_primrec : Primrec (fun p : Bool × (Nat × Nat) => logGraph p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Bool × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Bool × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Uniform.unionCheck_primrec.comp hq)
    ((zeroCheck_primrec.comp hq).cond (Primrec.beq.comp hc (Primrec.const zeroCode))
      (PrincipalLogarithm.graph_primrec.comp (componentCode_primrec.comp Primrec.fst hq) hc))

/-- The literal source logarithm relation, including source log(0)=0. -/
def SourceLogSpec (last : Bool) (ξ η : Ordinal.{0}) : Prop :=
  if ξ = 0 then η = 0 else Ordinal.omega0 ^ η = componentValue last ξ

theorem logGraph_exact (last : Bool) (q c : Nat) : logGraph last q c = true ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      SourceLogSpec last (unionInterpretation q) (unionInterpretation c) := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    have hq := hs.1
    cases hz : zeroCheck q with
    | true =>
      have hc : c = zeroCode := by simpa only [logGraph, hz, Bool.cond_true, beq_iff_eq] using hs.2
      subst c
      exact ⟨hq, zeroCode_checked, by simp only [SourceLogSpec, (zeroCheck_exact q hq).mp hz,
        ite_true, zeroCode_value]⟩
    | false =>
      have hn : unionInterpretation q ≠ 0 := by
        intro he; have ht := (zeroCheck_exact q hq).mpr he; rw [hz] at ht; contradiction
      have hg : PrincipalLogarithm.graph (componentCode last q) c = true :=
        by simpa only [hz, Bool.cond_false] using hs.2
      have hv := (PrincipalLogarithm.graph_exact _ _).mp hg
      exact ⟨hq, hv.2.2.2.1, by
        simp only [SourceLogSpec, if_neg hn]
        exact hv.2.2.2.2.trans (componentCode_value last q hq)⟩
  · rintro ⟨hq, hc, hs⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hq, ?_⟩
    cases hz : zeroCheck q with
    | true =>
      have he := (zeroCheck_exact q hq).mp hz
      have hv : unionInterpretation c = 0 := by simpa only [SourceLogSpec, he, ite_true] using hs
      have hcz := Canonical.check_value_injective c zeroCode hc zeroCode_checked (hv.trans zeroCode_value.symm)
      simp only [hz, Bool.cond_true, beq_iff_eq]
      exact hcz
    | false =>
      have hn : unionInterpretation q ≠ 0 := by
        intro he; have ht := (zeroCheck_exact q hq).mpr he; rw [hz] at ht; contradiction
      have hp := componentCode_principal last q hq hn
      simp only [hz, Bool.cond_false]
      apply (PrincipalLogarithm.graph_exact _ _).mpr
      refine ⟨Canonical.check_original hp.1, hp.2.1, hp.2.2, hc, ?_⟩
      have he : Ordinal.omega0 ^ unionInterpretation c = componentValue last (unionInterpretation q) :=
        by simpa only [SourceLogSpec, if_neg hn] using hs
      exact he.trans (componentCode_value last q hq).symm

theorem logGraph_output_unique (last : Bool) (q c d : Nat)
    (hc : logGraph last q c = true) (hd : logGraph last q d = true) : c = d := by
  have hcs := (logGraph_exact last q c).mp hc
  have hds := (logGraph_exact last q d).mp hd
  apply Canonical.check_value_injective c d hcs.2.1 hds.2.1
  by_cases hz : unionInterpretation q = 0
  · have hc0 : unionInterpretation c = 0 := by simpa only [SourceLogSpec, if_pos hz] using hcs.2.2
    have hd0 : unionInterpretation d = 0 := by simpa only [SourceLogSpec, if_pos hz] using hds.2.2
    exact hc0.trans hd0.symm
  · have hec : Ordinal.omega0 ^ unionInterpretation c = componentValue last (unionInterpretation q) :=
      by simpa only [SourceLogSpec, if_neg hz] using hcs.2.2
    have hed : Ordinal.omega0 ^ unionInterpretation d = componentValue last (unionInterpretation q) :=
      by simpa only [SourceLogSpec, if_neg hz] using hds.2.2
    exact omegaPower_strictMono.injective (hec.trans hed.symm)

theorem componentLog_graph (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q) :
    logGraph last q c = true := by
  have hd : (componentLog last q).Dom := by obtain ⟨hd, _⟩ := hc; exact hd
  have hq := (componentLog_domain last q).mp hd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hq, ?_⟩
  cases hz : zeroCheck q with
  | true =>
    have he : c = zeroCode := by simpa [componentLog, hq, hz] using hc
    simp only [hz, Bool.cond_true, beq_iff_eq]; exact he
  | false =>
    have hm : c ∈ PrincipalLogarithm.logarithm (componentCode last q) :=
      by simpa only [componentLog, hq, hz, Bool.cond_true, Bool.cond_false] using hc
    simpa only [hz, Bool.cond_false] using PrincipalLogarithm.logarithm_graph _ c hm

theorem componentLog_graph_iff (last : Bool) (q c : Nat) :
    c ∈ componentLog last q ↔ logGraph last q c = true := by
  constructor
  · exact componentLog_graph last q c
  · intro hg
    have hq := ((logGraph_exact last q c).mp hg).1
    have hd := (componentLog_domain last q).mpr hq
    have hm : (componentLog last q).get hd ∈ componentLog last q := ⟨hd, rfl⟩
    have he := logGraph_output_unique last q c _ hg (componentLog_graph last q _ hm)
    rw [he]; exact hm

theorem logGraph_unique (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, logGraph last q c = true := by
  have hd := (componentLog_domain last q).mpr hq
  have hm : (componentLog last q).get hd ∈ componentLog last q := ⟨hd, rfl⟩
  exact ⟨_, componentLog_graph last q _ hm, fun c hc =>
    logGraph_output_unique last q c _ hc (componentLog_graph last q _ hm)⟩

theorem componentLog_value (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q) :
    unionCheck q = true ∧ Canonical.check c = true ∧
      SourceLogSpec last (unionInterpretation q) (unionInterpretation c) :=
  (logGraph_exact last q c).mp (componentLog_graph last q c hc)

theorem componentLog_original (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := componentLog_value last q c hc
  exact ⟨Canonical.check_original hs.2.1, Canonical.check_normal hs.2.1⟩

theorem componentLog_zero (last : Bool) (q : Nat) (hq : unionCheck q = true)
    (hz : unionInterpretation q = 0) : componentLog last q = Part.some zeroCode := by
  simp only [componentLog, hq, (zeroCheck_exact q hq).mpr hz, Bool.cond_true]

theorem componentLog_power (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q)
    (hp : 0 < unionInterpretation q) : Ordinal.omega0 ^ unionInterpretation c = unionInterpretation (componentCode last q) := by
  have hs := componentLog_value last q c hc
  have he : Ordinal.omega0 ^ unionInterpretation c = componentValue last (unionInterpretation q) :=
    by simpa only [SourceLogSpec, if_neg (ne_of_gt hp)] using hs.2.2
  exact he.trans (componentCode_value last q hs.1).symm

theorem componentLog_bound (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q) :
    unionInterpretation c ≤ unionInterpretation q := by
  have hs := componentLog_value last q c hc
  by_cases hz : unionInterpretation q = 0
  · have hc0 : unionInterpretation c = 0 := by simpa only [SourceLogSpec, if_pos hz] using hs.2.2
    rw [hc0, hz]
  · exact ((omegaPower_self_le _).trans_eq
      (componentLog_power last q c hc (pos_iff_ne_zero.mpr hz))).trans (componentCode_le last q hs.1)

theorem logGraph_invariant (last : Bool) (q v c : Nat) (hq : unionCheck q = true)
    (hv : unionCheck v = true) (he : unionInterpretation q = unionInterpretation v) :
    logGraph last q c = logGraph last v c := by
  apply Bool.eq_iff_iff.mpr
  simp only [logGraph_exact, hq, hv, true_and, he]

theorem componentLog_returns (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    ∃ c : Nat, c ∈ componentLog last q ∧ Canonical.check c = true ∧
      SourceLogSpec last (unionInterpretation q) (unionInterpretation c) := by
  have hd := (componentLog_domain last q).mpr hq
  have hm : (componentLog last q).get hd ∈ componentLog last q := ⟨hd, rfl⟩
  have hs := componentLog_value last q _ hm
  exact ⟨_, hm, hs.2.1, hs.2.2⟩

theorem componentLog_output_invariant (last : Bool) (q v c d : Nat)
    (hc : c ∈ componentLog last q) (hd : d ∈ componentLog last v)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  have hcs := componentLog_value last q c hc
  have hds := componentLog_value last v d hd
  apply logGraph_output_unique last q c d (componentLog_graph last q c hc)
  apply (logGraph_exact last q d).mpr
  exact ⟨hcs.1, hds.2.1, by rw [he]; exact hds.2.2⟩

def leadingLog (q : Nat) : Part Nat := componentLog false q

def logend (q : Nat) : Part Nat := componentLog true q

theorem leadingLog_partrec : Partrec leadingLog := componentLog_partrec.comp (Computable.const false) Computable.id

theorem logend_partrec : Partrec logend := componentLog_partrec.comp (Computable.const true) Computable.id

theorem leadingLog_domain (q : Nat) : (leadingLog q).Dom ↔ unionCheck q = true := componentLog_domain false q

theorem logend_domain (q : Nat) : (logend q).Dom ↔ unionCheck q = true := componentLog_domain true q

theorem leadingLog_value (q c : Nat) (hc : c ∈ leadingLog q) :
    unionCheck q = true ∧ Canonical.check c = true ∧ SourceLogSpec false (unionInterpretation q) (unionInterpretation c) :=
  componentLog_value false q c hc

theorem logend_value (q c : Nat) (hc : c ∈ logend q) :
    unionCheck q = true ∧ Canonical.check c = true ∧ SourceLogSpec true (unionInterpretation q) (unionInterpretation c) :=
  componentLog_value true q c hc

theorem leadingLog_power (q c : Nat) (hc : c ∈ leadingLog q) (hp : 0 < unionInterpretation q) :
    Ordinal.omega0 ^ unionInterpretation c = unionInterpretation (mcCode q) := componentLog_power false q c hc hp

theorem logend_power (q c : Nat) (hc : c ∈ logend q) (hp : 0 < unionInterpretation q) :
    Ordinal.omega0 ^ unionInterpretation c = unionInterpretation (endCode q) := componentLog_power true q c hc hp

theorem leadingLog_zero (q : Nat) (hq : unionCheck q = true) (hz : unionInterpretation q = 0) :
    leadingLog q = Part.some zeroCode := componentLog_zero false q hq hz

theorem logend_zero (q : Nat) (hq : unionCheck q = true) (hz : unionInterpretation q = 0) :
    logend q = Part.some zeroCode := componentLog_zero true q hq hz

/-- Expanded CNF keeps each finite repetition of its omega-power summand.
Weak decrease of exponents makes this the genuine unique additive normal form. -/
theorem canonicalANF_expandedCNF (xs : List Ordinal.{0})
    (hx : xs.Pairwise (fun a b => b ≤ a)) :
    canonicalANF (principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) =
      xs.map (fun a => Ordinal.omega0 ^ a) := by
  apply canonicalANF_eq_of_normal
  · constructor
    · intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩
    · revert hx
      induction xs with
      | nil => intro _; exact List.Pairwise.nil
      | cons a as ih =>
        intro hx
        have ht := List.pairwise_cons.mp hx
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih ht.2⟩
        intro b hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        exact omegaPower_strictMono.monotone (ht.1 c hc)
  · rfl

private theorem expandedCNF_nonzero (xs : List Ordinal.{0}) (hx : xs ≠ []) :
    principalSum (xs.map (fun a => Ordinal.omega0 ^ a)) ≠ 0 := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a as =>
    exact ne_of_gt ((Ordinal.opow_pos a Ordinal.omega0_pos).trans_le (by
      change Ordinal.omega0 ^ a ≤ Ordinal.omega0 ^ a + principalSum (as.map (fun b => Ordinal.omega0 ^ b))
      exact le_self_add))

private theorem componentValue_expandedCNF (last : Bool) (xs : List Ordinal.{0})
    (hx : xs.Pairwise (fun a b => b ≤ a)) (hne : xs ≠ []) :
    componentValue last (principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) =
      Ordinal.omega0 ^ ((cond last xs.reverse xs)[0]?.getD (0 : Ordinal.{0})) := by
  have hm : cond last (xs.map (fun a => Ordinal.omega0 ^ a)).reverse
      (xs.map (fun a => Ordinal.omega0 ^ a)) =
      (cond last xs.reverse xs).map (fun a => Ordinal.omega0 ^ a) := by
    cases last <;> simp only [Bool.cond_false, Bool.cond_true, List.map_reverse]
  have hn : cond last xs.reverse xs ≠ [] := by
    cases last with
    | false => exact hne
    | true => exact fun h => hne (List.reverse_eq_nil_iff.mp h)
  rw [componentValue, canonicalANF_expandedCNF xs hx, hm]
  cases he : cond last xs.reverse xs with
  | nil => exact False.elim (hn he)
  | cons a as => rfl

/-- For actual expanded CNF, the execution returns its first/last exponent.
This includes the empty CNF: both exponents are literally zero. -/
theorem componentLog_cnf (last : Bool) (q c : Nat) (hc : c ∈ componentLog last q)
    (xs : List Ordinal.{0}) (hx : xs.Pairwise (fun a b => b ≤ a))
    (hv : unionInterpretation q = principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) :
    unionInterpretation c = (cond last xs.reverse xs)[0]?.getD 0 := by
  have hs := componentLog_value last q c hc
  by_cases hn : xs = []
  · subst xs
    have hz : unionInterpretation q = 0 := hv
    have hc0 : unionInterpretation c = 0 := by simpa only [SourceLogSpec, if_pos hz] using hs.2.2
    cases last <;> simpa using hc0
  · have hz : unionInterpretation q ≠ 0 := by rw [hv]; exact expandedCNF_nonzero xs hn
    have hp : Ordinal.omega0 ^ unionInterpretation c = componentValue last (unionInterpretation q) :=
      by simpa only [SourceLogSpec, if_neg hz] using hs.2.2
    apply omegaPower_strictMono.injective
    change Ordinal.omega0 ^ unionInterpretation c = Ordinal.omega0 ^ ((cond last xs.reverse xs)[0]?.getD (0 : Ordinal.{0}))
    rw [hp, hv, componentValue_expandedCNF last xs hx hn]

theorem leadingLog_cnf (q c : Nat) (hc : c ∈ leadingLog q)
    (xs : List Ordinal.{0}) (hx : xs.Pairwise (fun a b => b ≤ a))
    (hv : unionInterpretation q = principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) :
    unionInterpretation c = xs[0]?.getD 0 := componentLog_cnf false q c hc xs hx hv

/-- Literal Section 2 definition: zero for empty CNF, last CNF exponent otherwise. -/
theorem logend_cnf (q c : Nat) (hc : c ∈ logend q)
    (xs : List Ordinal.{0}) (hx : xs.Pairwise (fun a b => b ≤ a))
    (hv : unionInterpretation q = principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) :
    unionInterpretation c = xs.reverse[0]?.getD 0 := componentLog_cnf true q c hc xs hx hv

end Alexander313.Wilken.RelativeTerm.Hereditary.LogEnd
