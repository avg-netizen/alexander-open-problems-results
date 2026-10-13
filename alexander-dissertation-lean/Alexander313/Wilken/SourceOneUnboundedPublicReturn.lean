import Alexander313.Wilken.SourceOneUnboundedPublicReturnSupport

/-!
# Unbounded finite SAME-value return at the ORIGINAL source one

Every originally checked target tree at the genuine alphaCode root is
translated to an actual accepted Normal original source0 code. Parameters
use genuine bounded return0; sums use original normalizing addition; every
theta uses the complete original source-one scalar at its SAME index.
Every RAW LOW target then executes a canonical SAME-value public return.
No input Normality, selected endpoint or Native base-one parser. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.UnboundedPublicReturn

open ThetaCourse

def sourceTreeCode (b : Nat) : RelativeTerm Nat → Nat
  | .parameter p => SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p)
  | .sum t u => Addition.normalizedSumCode 0 (sourceTreeCode b t) (sourceTreeCode b u)
  | .theta k t => RootScalar.collapseCode b k (sourceTreeCode b t)

abbrev State := Nat × Nat

def parameterState (b p : Nat) : State :=
  (b, SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p))
def sumState (x y : State) : State :=
  (x.1, Addition.normalizedSumCode 0 x.2 y.2)
def thetaState (b k : Nat) (x : State) : State := (b, RootScalar.collapseCode b k x.2)

theorem parameterState_primrec : Primrec₂ parameterState :=
  (Primrec.fst.pair (SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
    (Canonical.Effective.canonicalize_primrec.comp Primrec.snd))).to₂
theorem sumState_primrec : Primrec₂ sumState :=
  ((Primrec.fst.comp Primrec.fst).pair (Addition.normalizedSumCode_primrec.comp
    ((Primrec.const 0).pair ((Primrec.snd.comp Primrec.fst).pair
      (Primrec.snd.comp Primrec.snd))))).to₂
theorem thetaState_primrec : Primrec
    (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) :=
  Primrec.fst.pair (RootScalar.collapseCode_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

def stateCode (b c : Nat) : State := ValueFold.code parameterState sumState thetaState (0, 0) b c

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (0, 0)
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (b : Nat) (t : RelativeTerm Nat) : stateCode b t.code = (b, sourceTreeCode b t) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, sourceTreeCode]

def sourceTermCode (b c : Nat) : Nat := (stateCode b c).2
theorem sourceTermCode_primrec : Primrec₂ sourceTermCode := (Primrec.snd.comp stateCode_primrec).to₂
theorem sourceTermCode_code (b : Nat) (t : RelativeTerm Nat) :
    sourceTermCode b t.code = sourceTreeCode b t := by rw [sourceTermCode, stateCode_code]

/-- EVERY originally checked target tree has a finite SAME-value original
source-one Normal representation, without a Normal or LOW input premise. -/
theorem sourceTreeCode_spec (b : Nat) (hb : rootCheck b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode b) t = true) :
    RootScalar.argumentCheck (sourceTreeCode b t) = true ∧
      interpretation 0 (sourceTreeCode b t) = NativeContext.denote (alphaCode b) t := by
  induction t with
  | parameter p =>
    have hp : NativeContext.parameterCheck (alphaCode b) p = true :=
      (NativeContext.checked_admissible _ (.parameter p) ht).1
    have hs := parameter_return b p hb hp
    exact ⟨hs.1, hs.2.2⟩
  | sum t u iht ihu =>
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    have hl := iht hc.1
    have hr := ihu hc.2
    have hs := Addition.normalizedSumCode_checked 0 _ _
      ((SourceDecomposition.inputCheck_exact 0 _).mp hl.1).1
      ((SourceDecomposition.inputCheck_exact 0 _).mp hr.1).1
    exact ⟨hs.1, hs.2.trans (congrArg₂ (fun x y : Ordinal.{0} => x + y) hl.2 hr.2)⟩
  | theta k t ih =>
    have hr := ih (NativeContext.FixedPoint.checked_theta_argument _ k t ht)
    have hc := scalar_caller b k hb t ht _ hr.1 hr.2
    have hs := RootScalar.collapseCode_spec b k _ hc
    refine ⟨hs.1, hs.2.trans ((congrArg (globalCollapse (interpretation 0 b) k) hr.2).trans ?_)⟩
    change globalCollapse (interpretation 0 b) k (NativeContext.denote (alphaCode b) t) =
      globalCollapse (NativeContext.base (alphaCode b)) k (NativeContext.denote (alphaCode b) t)
    rw [alpha_base b hb]

theorem sourceTermCode_spec (b c : Nat) (hb : rootCheck b = true)
    (hc : NativeContext.checkCode (alphaCode b) c = true) :
    RootScalar.argumentCheck (sourceTermCode b c) = true ∧
      interpretation 0 (sourceTermCode b c) = NativeContext.interpretation (alphaCode b) c := by
  obtain ⟨t, rfl, ht⟩ := (NativeContext.checkCode_exact _ c).mp hc
  simpa only [sourceTermCode_code, NativeContext.interpretation_code] using sourceTreeCode_spec b hb t ht

theorem sourceTermCode_sort (b c k : Nat) (hb : rootCheck b = true)
    (hc : NativeContext.checkCode (alphaCode b) c = true) (hk : 0 < k)
    (hs : (rawTree c).outerSort ≤ k) : (rawTree (sourceTermCode b c)).outerSort ≤ k := by
  have hr := sourceTermCode_spec b c hb hc
  exact returned_sort b hb (rawTree c) (NativeContext.Arithmetic.raw_checked _ c hc) _ k hr.1
    (hr.2.trans (NativeContext.Arithmetic.raw_value _ c hc).symm) hk hs

theorem sourceTermCode_low (b c : Nat) (hb : rootCheck b = true)
    (hc : NativeContext.lowCheckCode (alphaCode b) c = true) : lowCheckCode 0 (sourceTermCode b c) = true := by
  obtain ⟨t, he, ht⟩ := (NativeContext.lowCheckCode_exact _ c).mp hc
  have hp := Bool.and_eq_true.mp ht
  have hsort : (rawTree c).outerSort ≤ 1 := by
    simpa only [← he, rawTree_code] using of_decide_eq_true hp.2
  have hcheck := (Bool.and_eq_true.mp hc).1
  have hr := sourceTermCode_spec b c hb hcheck
  have hbound : interpretation 0 (sourceTermCode b c) < omegaSequence 1 1 := by
    rw [← RootScalar.raw_value _ hr.1, ← finiteBase_zero]
    exact (denote_lt_iff_outerSort_le 0 _ (RootScalar.raw_checked _ hr.1) 1 (by omega)).mpr
      (sourceTermCode_sort b c 1 hb hcheck (by omega) hsort)
  exact RootScalar.low_of_bound _ hr.1 hbound

def inputCheck (b c : Nat) : Bool := rootCheck b && NativeContext.lowCheckCode (alphaCode b) c
theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (NativeContext.lowCheckCode_primrec.comp (alphaCode_primrec.comp Primrec.fst) Primrec.snd)).to₂
theorem inputCheck_exact (b c : Nat) : inputCheck b c = true ↔
    rootCheck b = true ∧ NativeContext.lowCheckCode (alphaCode b) c = true := Bool.and_eq_true

def publicCode (b c : Nat) : Nat := cond (inputCheck b c)
  (Canonical.canonicalize (Nat.pair 0 (sourceTermCode b c))) 0
theorem publicCode_primrec : Primrec₂ publicCode :=
  (inputCheck_primrec.cond (Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp (Primrec.const 0) sourceTermCode_primrec)) (Primrec.const 0)).to₂

/-- The WHOLE original RAW LOW target interval executes a genuine
canonical SAME-value public return through the ORIGINAL source one. -/
theorem publicCode_spec (b c : Nat) (hi : inputCheck b c = true) :
    Canonical.check (publicCode b c) = true ∧
      unionInterpretation (publicCode b c) = NativeContext.interpretation (alphaCode b) c := by
  have h := (inputCheck_exact b c).mp hi
  have hs := sourceTermCode_spec b c h.1 (Bool.and_eq_true.mp h.2).1
  have hl := sourceTermCode_low b c h.1 h.2
  have hpublic : unionCheck (Nat.pair 0 (sourceTermCode b c)) = true := by
    simpa only [unionCheck_pair] using hl
  simp only [publicCode, hi, Bool.cond_true]
  exact ⟨Canonical.canonicalize_check _ hpublic,
    (Canonical.canonicalize_value _ hpublic).trans (by simpa only [unionInterpretation_pair] using hs.2)⟩

theorem publicCode_value_invariant (b c d : Nat) (hc : inputCheck b c = true)
    (hd : inputCheck b d = true)
    (hv : NativeContext.interpretation (alphaCode b) c = NativeContext.interpretation (alphaCode b) d) :
    publicCode b c = publicCode b d :=
  Canonical.check_value_injective _ _ (publicCode_spec b c hc).1 (publicCode_spec b d hd).1
    ((publicCode_spec b c hc).2.trans (hv.trans (publicCode_spec b d hd).2.symm))
theorem publicCode_rejected (b c : Nat) (hi : inputCheck b c = false) : publicCode b c = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

def execute (b c : Nat) : Part Nat := cond (inputCheck b c) (Part.some (publicCode b c)) Part.none
theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none).to₂
theorem execute_dom (b c : Nat) : (execute b c).Dom ↔ inputCheck b c = true := by
  cases hi : inputCheck b c <;> simp [execute, hi]
theorem execute_graph (b c out : Nat) : out ∈ execute b c ↔ inputCheck b c = true ∧ out = publicCode b c := by
  cases hi : inputCheck b c <;> simp [execute, hi]
theorem execute_spec (b c out : Nat) (ho : out ∈ execute b c) :
    Canonical.check out = true ∧ unionInterpretation out = NativeContext.interpretation (alphaCode b) c := by
  obtain ⟨hi, rfl⟩ := (execute_graph b c out).mp ho
  exact publicCode_spec b c hi

def graphBool (b c out : Nat) : Bool := inputCheck b c && (out == publicCode b c)
theorem graphBool_primrec : Primrec (fun p : (Nat × Nat) × Nat => graphBool p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Primrec.comp inputCheck_primrec Primrec.fst)
    (Primrec.beq.comp Primrec.snd (Primrec.comp publicCode_primrec Primrec.fst))
theorem graphBool_exact (b c out : Nat) : graphBool b c out = true ↔ out ∈ execute b c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.UnboundedPublicReturn
