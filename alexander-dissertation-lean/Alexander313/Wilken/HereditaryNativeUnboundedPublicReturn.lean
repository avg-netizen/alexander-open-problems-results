import Alexander313.Wilken.HereditaryNativeUnboundedPublicReturnSupport

/-!
# Executing unbounded SAME-value return at an actual positive source

Every originally checked tree at alphaCode(s,a) is translated to the SAME
original contextCode s. Public payloads use the genuine finite LOW return;
sums use actual normalizing addition; each theta uses the complete relative
scalar construction at its original index. Recursive source Normality and
SAME value derive every hidden theta caller. No target Normality, relative
endpoint, supplied output representation or cross-context value oracle.

Every original RAW LOW input then returns a canonical public code at the
SAME value. Invalid inputs have no Part result; complete graphs retain zero.
No source height bound or chosen smaller-parameter-cutoff preservation is
claimed. Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UnboundedPublicReturn

open NativePublicBridge (contextCode contextCode_primrec)
open ThetaCourse

def sourceTreeCode (s a : Nat) : RelativeTerm Nat → Nat
  | .parameter p => LowArithmetic.returnCode s (Canonical.canonicalize p)
  | .sum t u => Arithmetic.addCode (contextCode s) (sourceTreeCode s a t) (sourceTreeCode s a u)
  | .theta k t => RootCompleteScalarCollapse.collapseCode (contextCode s) a k (sourceTreeCode s a t)

abbrev State := (Nat × Nat) × Nat

def parameterState (ctx : Nat × Nat) (p : Nat) : State :=
  (ctx, LowArithmetic.returnCode ctx.1 (Canonical.canonicalize p))

def sumState (x y : State) : State :=
  (x.1, Arithmetic.addCode (contextCode x.1.1) x.2 y.2)

def thetaState (ctx : Nat × Nat) (k : Nat) (x : State) : State :=
  (ctx, RootCompleteScalarCollapse.collapseCode (contextCode ctx.1) ctx.2 k x.2)

theorem parameterState_primrec : Primrec₂ parameterState :=
  (Primrec.fst.pair (LowArithmetic.returnCode_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Canonical.Effective.canonicalize_primrec.comp Primrec.snd))).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hctx : Primrec (fun p : State × State => p.1.1) := Primrec.fst.comp Primrec.fst
  have hq := contextCode_primrec.comp (Primrec.fst.comp hctx)
  have hc := Primrec.snd.comp Primrec.fst
  have hd := Primrec.snd.comp Primrec.snd
  exact (hctx.pair (Arithmetic.addCode_primrec.comp (hq.pair (hc.pair hd)))).to₂

theorem thetaState_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hq := contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)
  have ha := Primrec.snd.comp Primrec.fst
  have hk := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.fst.pair
    (RootCompleteScalarCollapse.collapseCode_primrec.comp (hq.pair (ha.pair (hk.pair hc))))

def stateCode (s a c : Nat) : State := ValueFold.code parameterState sumState thetaState
  ((0, 0), 0) (s, a) c

theorem stateCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => stateCode p.1.1 p.1.2 p.2) :=
  ValueFold.code_primrec parameterState sumState thetaState ((0, 0), 0)
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (s a : Nat) (t : RelativeTerm Nat) :
    stateCode s a t.code = ((s, a), sourceTreeCode s a t) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, sourceTreeCode]

def sourceTermCode (s a c : Nat) : Nat := (stateCode s a c).2

theorem sourceTermCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => sourceTermCode p.1.1 p.1.2 p.2) :=
  Primrec.snd.comp stateCode_primrec

theorem sourceTermCode_code (s a : Nat) (t : RelativeTerm Nat) :
    sourceTermCode s a t.code = sourceTreeCode s a t := by rw [sourceTermCode, stateCode_code]

/-- EVERY original checked tree has a finite SAME-source Normal return.
There is no Normal or LOW premise on the input tree. -/
theorem sourceTreeCode_spec (s a : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (Iota.alphaCode s a) t = true) :
    Comparison.acceptedCode (contextCode s) (sourceTreeCode s a t) = true ∧
      interpretation (contextCode s) (sourceTreeCode s a t) = denote (Iota.alphaCode s a) t := by
  induction t with
  | parameter p =>
    have hp : parameterCheck (Iota.alphaCode s a) p = true :=
      (checked_admissible _ (.parameter p) ht).1
    have hs := parameter_return s a p ha hp
    exact ⟨hs.1, hs.2.2⟩
  | sum t u iht ihu =>
    have hc := BaseTransformation.sum_checks _ t u ht
    have ht' := iht hc.1
    have hu' := ihu hc.2
    have hs := Arithmetic.addCode_spec (contextCode s) _ _
      ((Comparison.acceptedCode_exact _ _).mp ht'.1).1
      ((Comparison.acceptedCode_exact _ _).mp hu'.1).1
    exact ⟨hs.1, by
      change interpretation (contextCode s) (Arithmetic.addCode _ _ _) = _
      rw [hs.2.1, ht'.2, hu'.2]; rfl⟩
  | theta k t ih =>
    have hs := ih (FixedPoint.checked_theta_argument _ k t ht)
    have hc := scalar_caller s a k ha t ht _ hs.1 hs.2
    have hr := RootCompleteScalarCollapse.collapseCode_spec _ a k _ hc
    refine ⟨hr.1, ?_⟩
    change interpretation (contextCode s) (RootCompleteScalarCollapse.collapseCode _ _ _ _) = _
    rw [hr.2, hs.2, ← Iota.alpha_base s a ha]
    rfl

theorem sourceTermCode_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : checkCode (Iota.alphaCode s a) c = true) :
    Comparison.acceptedCode (contextCode s) (sourceTermCode s a c) = true ∧
      interpretation (contextCode s) (sourceTermCode s a c) = interpretation (Iota.alphaCode s a) c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact _ c).mp hc
  simpa only [sourceTermCode_code, interpretation_code] using sourceTreeCode_spec s a ha t ht

theorem sourceTermCode_sort (s a c k : Nat) (ha : Iota.rootCheck s a = true)
    (hc : checkCode (Iota.alphaCode s a) c = true) (hk : 0 < k)
    (hs : (rawTree c).outerSort ≤ k) : (rawTree (sourceTermCode s a c)).outerSort ≤ k := by
  have hr := sourceTermCode_spec s a c ha hc
  apply returned_sort s a ha (rawTree c) (Arithmetic.raw_checked _ c hc) _ k hr.1
    (hr.2.trans (Arithmetic.raw_value _ c hc).symm) hk hs

theorem sourceTermCode_low (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : lowCheckCode (Iota.alphaCode s a) c = true) :
    lowCheckCode (contextCode s) (sourceTermCode s a c) = true := by
  obtain ⟨t, he, ht⟩ := (lowCheckCode_exact _ c).mp hc
  have hs := Bool.and_eq_true.mp ht
  have hsort : t.outerSort ≤ 1 := of_decide_eq_true hs.2
  have hraw : (rawTree c).outerSort ≤ 1 := by simpa only [← he, rawTree_code] using hsort
  have hcheck : checkCode (Iota.alphaCode s a) c = true := (Bool.and_eq_true.mp hc).1
  have hr := sourceTermCode_spec s a c ha hcheck
  have hout := ((Comparison.acceptedCode_exact _ _).mp hr.1).1
  apply (lowCheckCode_exact _ _).mpr
  refine ⟨rawTree (sourceTermCode s a c), ?_, ?_⟩
  · obtain ⟨u, hu, _⟩ := (checkCode_exact _ _).mp hout
    rw [← hu, rawTree_code]
  · exact Bool.and_eq_true.mpr ⟨Arithmetic.raw_checked _ _ hout,
      decide_eq_true (sourceTermCode_sort s a c 1 ha hcheck (by omega) hraw)⟩

def inputCheck (s a c : Nat) : Bool := Iota.rootCheck s a && lowCheckCode (Iota.alphaCode s a) c

theorem inputCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => inputCheck p.1.1 p.1.2 p.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have ha := Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp (Iota.rootCheck_primrec.comp hs ha)
    (lowCheckCode_primrec.comp (Iota.alphaCode_primrec.comp hs ha) Primrec.snd)

theorem inputCheck_exact (s a c : Nat) : inputCheck s a c = true ↔
    Iota.rootCheck s a = true ∧ lowCheckCode (Iota.alphaCode s a) c = true := Bool.and_eq_true

def publicCode (s a c : Nat) : Nat := cond (inputCheck s a c)
  (Canonical.canonicalize (LowArithmetic.publicCode s (sourceTermCode s a c))) 0

theorem publicCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => publicCode p.1.1 p.1.2 p.2) :=
  inputCheck_primrec.cond (Canonical.Effective.canonicalize_primrec.comp
    (LowArithmetic.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) sourceTermCode_primrec))
      (Primrec.const 0)

/-- The exact original RAW LOW domain returns a canonical public code at
the SAME value, without any selected source endpoint bound. -/
theorem publicCode_spec (s a c : Nat) (hi : inputCheck s a c = true) :
    Canonical.check (publicCode s a c) = true ∧
      unionInterpretation (publicCode s a c) = interpretation (Iota.alphaCode s a) c := by
  have hg := (inputCheck_exact s a c).mp hi
  have hr := sourceTermCode_spec s a c hg.1 (Bool.and_eq_true.mp hg.2).1
  have hs := LowArithmetic.publicCode_spec s (sourceTermCode s a c)
    (sourceTermCode_low s a c hg.1 hg.2)
  simpa only [publicCode, hi, Bool.cond_true] using
    (show Canonical.check (Canonical.canonicalize (LowArithmetic.publicCode s (sourceTermCode s a c))) = true ∧
      unionInterpretation (Canonical.canonicalize (LowArithmetic.publicCode s (sourceTermCode s a c))) =
        interpretation (Iota.alphaCode s a) c from
      ⟨Canonical.canonicalize_check _ hs.1, (Canonical.canonicalize_value _ hs.1).trans (hs.2.trans hr.2)⟩)

theorem publicCode_value_invariant (s a c d : Nat) (hc : inputCheck s a c = true)
    (hd : inputCheck s a d = true) (hv : interpretation (Iota.alphaCode s a) c = interpretation (Iota.alphaCode s a) d) :
    publicCode s a c = publicCode s a d :=
  Canonical.check_value_injective _ _ (publicCode_spec s a c hc).1 (publicCode_spec s a d hd).1
    ((publicCode_spec s a c hc).2.trans (hv.trans (publicCode_spec s a d hd).2.symm))

theorem publicCode_rejected (s a c : Nat) (hi : inputCheck s a c = false) : publicCode s a c = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

def execute (s a c : Nat) : Part Nat := cond (inputCheck s a c) (Part.some (publicCode s a c)) Part.none

theorem execute_partrec : Partrec
    (fun p : (Nat × Nat) × Nat => execute p.1.1 p.1.2 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none

theorem execute_dom (s a c : Nat) : (execute s a c).Dom ↔ inputCheck s a c = true := by
  cases hi : inputCheck s a c <;> simp [execute, hi]

theorem execute_graph (s a c out : Nat) : out ∈ execute s a c ↔
    inputCheck s a c = true ∧ out = publicCode s a c := by
  cases hi : inputCheck s a c <;> simp [execute, hi]

theorem execute_spec (s a c out : Nat) (ho : out ∈ execute s a c) :
    Canonical.check out = true ∧ unionInterpretation out = interpretation (Iota.alphaCode s a) c := by
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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UnboundedPublicReturn
