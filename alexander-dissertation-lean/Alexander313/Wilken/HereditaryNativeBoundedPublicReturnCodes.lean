import Alexander313.Wilken.HereditaryNativeBoundedPublicReturn
import Alexander313.Wilken.HereditaryNativeMuBounds

/-!
# Exact executing guard for the full bounded same-value public return

The literal finite SAME-index presentation computes the actual target
Delta enclosure. Its proved value is ORIGINAL source alpha-plus. Actual
target comparison therefore recognizes the full original raw LOW interval
before the finite converter executes. No Normal or hidden-call guard is
added. Both code and Part executions return an actual canonical public
code at the SAME value. Output zero is retained by the complete graph.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn

open NativePublicBridge (contextCode)
open Iota Iota.HeightSupport

def unshiftedThetaState (ctx : Nat × Nat) (k : Nat) (x : Iota.State) : Iota.State :=
  let t := RelativeTerm.theta k x.2.1
  (ctx, (t, cond (small ctx.1 ctx.2 t) (.parameter (parameterCode ctx.1 t)) (.theta k x.2.2)))

theorem unshiftedThetaState_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Iota.State) => unshiftedThetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : (Nat × Nat) × (Nat × Iota.State) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × Iota.State) => RelativeTerm.theta p.2.1 p.2.2.2.1) :=
    theta_primrec.comp hk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hsmall := small_primrec.comp Primrec.fst ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp (Primrec.fst.comp Primrec.fst) ht)
  have ho := theta_primrec.comp hk (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.fst.pair (ht.pair (hsmall.cond hp ho))

def unshiftedStateCode (s a c : Nat) : Iota.State := ValueFold.code
  Iota.parameterState Iota.sumState unshiftedThetaState
  ((0, 0), (Normalization.zeroTree, Normalization.zeroTree)) (s, a) c

theorem unshiftedStateCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => unshiftedStateCode p.1.1 p.1.2 p.2) :=
  ValueFold.code_primrec Iota.parameterState Iota.sumState unshiftedThetaState
    ((0, 0), (Normalization.zeroTree, Normalization.zeroTree))
    Iota.parameterState_primrec Iota.sumState_primrec unshiftedThetaState_primrec

theorem unshiftedStateCode_code (s a : Nat) (t : RelativeTerm Nat) :
    unshiftedStateCode s a t.code = ((s, a), (t, unshifted s a t)) := by
  rw [unshiftedStateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, Iota.parameterState, Iota.sumState,
    unshiftedThetaState, unshifted]

def enclosureCode (s a : Nat) : Nat :=
  (.theta 0 (unshiftedStateCode s a (Lambda.deltaCode a)).2.2 : RelativeTerm Nat).code

theorem enclosureCode_primrec : Primrec₂ enclosureCode :=
  (code_primrec.comp (theta_primrec.comp (Primrec.const 0)
    (Primrec.snd.comp (Primrec.snd.comp (unshiftedStateCode_primrec.comp
      (Primrec.id.pair (Lambda.deltaCode_primrec.comp Primrec.snd))))))).to₂

theorem enclosureCode_eq (s a : Nat) : enclosureCode s a = (Enclosure.deltaEnclosureTerm s a).code := by
  rw [enclosureCode, show Lambda.deltaCode a = (Enclosure.deltaTerm a).code from rfl,
    unshiftedStateCode_code]
  rfl

def inputCheck (s a c : Nat) : Bool :=
  (rootCheck s a && lowCheckCode (alphaCode s a) c) &&
    Normalization.lessRawCode (alphaCode s a) c (enclosureCode s a)

theorem inputCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => inputCheck p.1.1 p.1.2 p.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have ha := Primrec.snd.comp Primrec.fst
  have hα := alphaCode_primrec.comp hs ha
  have hc := lowCheckCode_primrec.comp hα Primrec.snd
  have he := enclosureCode_primrec.comp hs ha
  exact Primrec.and.comp (Primrec.and.comp (rootCheck_primrec.comp hs ha) hc)
    (Normalization.Effective.lessRawCode_primrec.comp (hα.pair (Primrec.snd.pair he)))

/-- The literal recognizer has EXACTLY the original raw LOW bound domain.
Every hidden-call and target Normal premise is constructed by the producer. -/
theorem inputCheck_exact (s a c : Nat) : inputCheck s a c = true ↔
    rootCheck s a = true ∧ lowCheckCode (alphaCode s a) c = true ∧
      interpretation (alphaCode s a) c < AlphaPlus.sourceValue s a := by
  constructor
  · intro h
    obtain ⟨hfirst, hless⟩ := Bool.and_eq_true.mp h
    obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hfirst
    have hs := (Normalization.lessRawCode_exact _ _ _).mp hless
    refine ⟨ha, hc, ?_⟩
    simpa only [enclosureCode_eq, interpretation_code,
      AlphaPlus.delta_enclosure_eq_sourceValue s a ha] using hs.2.2
  · rintro ⟨ha, hc, hb⟩
    have he := Enclosure.delta_enclosure_spec s a ha
    have hech : checkCode (alphaCode s a) (enclosureCode s a) = true := by
      simpa only [enclosureCode_eq, checkCode_code] using he.1
    refine Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha, hc⟩, ?_⟩
    apply (Normalization.lessRawCode_exact _ _ _).mpr
    refine ⟨(Bool.and_eq_true.mp hc).1, hech, ?_⟩
    simpa only [enclosureCode_eq, interpretation_code,
      AlphaPlus.delta_enclosure_eq_sourceValue s a ha] using hb

def publicCode (s a c : Nat) : Nat := cond (inputCheck s a c) (rawPublicCode s a c) 0

theorem publicCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => publicCode p.1.1 p.1.2 p.2) :=
  inputCheck_primrec.cond rawPublicCode_primrec (Primrec.const 0)

theorem publicCode_spec (s a c : Nat) (hi : inputCheck s a c = true) :
    Canonical.check (publicCode s a c) = true ∧
      unionInterpretation (publicCode s a c) = interpretation (alphaCode s a) c := by
  have hs := (inputCheck_exact s a c).mp hi
  simpa only [publicCode, hi, Bool.cond_true] using rawPublicCode_spec s a c hs.1 hs.2.1 hs.2.2

theorem publicCode_rejected (s a c : Nat) (hi : inputCheck s a c = false) : publicCode s a c = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

def execute (s a c : Nat) : Part Nat :=
  cond (inputCheck s a c) (Part.some (publicCode s a c)) Part.none

theorem execute_partrec : Partrec
    (fun p : (Nat × Nat) × Nat => execute p.1.1 p.1.2 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none

theorem execute_dom (s a c : Nat) : (execute s a c).Dom ↔ inputCheck s a c = true := by
  cases h : inputCheck s a c <;> simp [execute, h]

theorem execute_graph (s a c out : Nat) : out ∈ execute s a c ↔
    inputCheck s a c = true ∧ out = publicCode s a c := by
  cases h : inputCheck s a c <;> simp [execute, h]

theorem execute_spec (s a c out : Nat) (ho : out ∈ execute s a c) :
    Canonical.check out = true ∧ unionInterpretation out = interpretation (alphaCode s a) c := by
  obtain ⟨hi, rfl⟩ := (execute_graph s a c out).mp ho
  exact publicCode_spec s a c hi

def graphBool (s a c out : Nat) : Bool := inputCheck s a c && (out == publicCode s a c)

theorem graphBool_primrec : Primrec
    (fun p : ((Nat × Nat) × Nat) × Nat => graphBool p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (publicCode_primrec.comp Primrec.fst))

theorem graphBool_exact (s a c out : Nat) : graphBool s a c out = true ↔ out ∈ execute s a c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

theorem lowCode_of_bounded (s a c : Nat) (ha : rootCheck s a = true)
    (hc : checkCode (alphaCode s a) c = true)
    (hb : interpretation (alphaCode s a) c < AlphaPlus.sourceValue s a) :
    lowCheckCode (alphaCode s a) c = true := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hc
  have hb' : denote (alphaCode s a) t < AlphaPlus.sourceValue s a := by
    simpa only [← he, interpretation_code] using hb
  have hsmall : denote (alphaCode s a) t < omegaSequence (base (alphaCode s a)) 1 := by
    rw [← root_omegaSequence_succ s a 0 ha]
    exact hb'.trans
      ((Lambda.SourceReturn.alphaPlus_lt_source_boundary s a (Bool.and_eq_true.mp ha).1).trans
        (globalBoundary_lt_cardinal _ (base_pos _ (NativePublicBridge.contextCode_checked s)) 0))
  have hl := (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp hsmall
  simp only [← he, lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]

/-- The entire genuine epsilon lambda output supplies the actual SAME-value
public-return caller, with no elementary or hidden-argument restriction. -/
theorem lambda_caller (s a out : Nat) (ho : out ∈ Lambda.execute s a) : inputCheck s a out = true := by
  have hs := Lambda.execute_spec s a out ho
  have hb := AlphaPlus.lambda_lt_sourceValue s a out ho
  exact (inputCheck_exact s a out).mpr ⟨hs.1,
    lowCode_of_bounded s a out hs.1 ((Comparison.acceptedCode_exact _ _).mp hs.2.1).1 hb, hb⟩

theorem lambda_public_spec (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    Canonical.check (publicCode s a out) = true ∧
      unionInterpretation (publicCode s a out) = interpretation (alphaCode s a) out :=
  publicCode_spec s a out (lambda_caller s a out ho)

/-- Every actual original native mu output has a genuine finite public
caller; its complete high arguments are handled by the proved recursion. -/
theorem mu_caller (s a out : Nat) (ho : out ∈ Mu.execute s a) : inputCheck s a out = true := by
  have hs := Mu.execute_spec s a out ho
  exact (inputCheck_exact s a out).mpr ⟨hs.1, hs.2.1, Mu.Bounds.execute_lt_source_alphaPlus s a out ho⟩

theorem mu_public_spec (s a out : Nat) (ho : out ∈ Mu.execute s a) :
    Canonical.check (publicCode s a out) = true ∧
      unionInterpretation (publicCode s a out) = interpretation (alphaCode s a) out :=
  publicCode_spec s a out (mu_caller s a out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn
