import Alexander313.Wilken.PublicEpsilonNativeContextTranslationSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaEnclosure
import Mathlib.Computability.Partrec

/-!
# Executing original-source to intermediate-context root translation

The ORIGINAL source roots alpha and beta, with alpha < beta < alphaPlus,
derive a genuine admitted LOW ceiling at the actual alpha context. Native
coverage and the constructed high-root parser therefore give a finite
SAME-value alpha-context beta root. An actual terminating Nat.rfind tests
high-root admission and equality of the two concrete canonical public
returns. Its finite output is computable, with no supplied representation,
translation, endpoint or semantic equality oracle. This constructs the
root caller of the printed t_alpha^tau; mu fidelity is a separate theorem.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation

open ThetaCourse
open PublicEpsilonUnboundedIota (betaCode betaCode_primrec betaCode_baseCheck beta_base)

abbrev Query := (Nat × Nat) × Nat

def sourceSuccessorCode (q alpha : Nat) : Nat :=
  OmegaPowers.thetaCode (RootEndpointCollapse.firstCode q alpha)

theorem sourceSuccessorCode_primrec : Primrec₂ sourceSuccessorCode :=
  (Primrec.comp OmegaPowers.thetaCode_primrec RootEndpointCollapse.firstCode_primrec).to₂

theorem sourceSuccessorCode_spec (q alpha : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true) :
    lowCheckCode q (sourceSuccessorCode q alpha) = true ∧
      Comparison.acceptedCode q (sourceSuccessorCode q alpha) = true ∧
      interpretation q (sourceSuccessorCode q alpha) =
        PublicEpsilonUnboundedIota.Enclosure.sourceAlphaPlus q alpha := by
  have hf := RootEndpointCollapse.firstCode_spec q alpha ha
  have hs : interpretation q (RootEndpointCollapse.firstCode q alpha) < omegaSequence (base q) 2 := by
    rw [hf.2]
    exact (omegaSequence_isSuccLimit (base q) 1).add_one_lt
      (RootEndpointCollapse.argument_sorted q alpha ha)
  have ht := RootEndpointCollapse.thetaCode_sorted_spec q _ hf.1 hs
  refine ⟨ht.1, ht.2.1, ?_⟩
  simpa only [sourceSuccessorCode, hf.2, PublicEpsilonUnboundedIota.Enclosure.sourceAlphaPlus,
    RootEndpointCollapse.argumentCode] using ht.2.2

def inputCheck (q alpha beta : Nat) : Bool :=
  (RootLowCollapse.rootCheck q alpha && RootLowCollapse.rootCheck q beta) &&
    (Normalization.lessRawCode q alpha beta &&
      Normalization.lessRawCode q beta (sourceSuccessorCode q alpha))

theorem inputCheck_primrec : Primrec
    (fun p : Query => inputCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have ha := Primrec.snd.comp Primrec.fst
  have hb := Primrec.snd
  have hfirst := sourceSuccessorCode_primrec.comp hq ha
  have hlow := Normalization.Effective.lessRawCode_primrec.comp (hq.pair (ha.pair hb))
  have hhigh := Normalization.Effective.lessRawCode_primrec.comp (hq.pair (hb.pair hfirst))
  exact Primrec.and.comp
    (Primrec.and.comp (RootLowCollapse.rootCheck_primrec.comp hq ha)
      (RootLowCollapse.rootCheck_primrec.comp hq hb)) (Primrec.and.comp hlow hhigh)

/-- The executing guard retains exactly the original two high-root callers
and the printed ORIGINAL interval alpha < beta < alphaPlus. -/
theorem inputCheck_exact (q alpha beta : Nat) : inputCheck q alpha beta = true ↔
    RootLowCollapse.rootCheck q alpha = true ∧ RootLowCollapse.rootCheck q beta = true ∧
      interpretation q alpha < interpretation q beta ∧
      interpretation q beta < PublicEpsilonUnboundedIota.Enclosure.sourceAlphaPlus q alpha := by
  constructor
  · intro hi
    obtain ⟨hroot, hinterval⟩ := Bool.and_eq_true.mp hi
    obtain ⟨ha, hb⟩ := Bool.and_eq_true.mp hroot
    obtain ⟨hl, hu⟩ := Bool.and_eq_true.mp hinterval
    have hp := (Normalization.lessRawCode_exact q alpha beta).mp hl
    have hs := (Normalization.lessRawCode_exact q beta (sourceSuccessorCode q alpha)).mp hu
    exact ⟨ha, hb, hp.2.2, hs.2.2.trans_eq (sourceSuccessorCode_spec q alpha ha).2.2⟩
  · rintro ⟨ha, hb, hl, hu⟩
    have hs := sourceSuccessorCode_spec q alpha ha
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha, hb⟩,
      Bool.and_eq_true.mpr
        ⟨(Normalization.lessRawCode_exact q alpha beta).mpr
          ⟨RootLowCollapse.root_original q alpha ha, RootLowCollapse.root_original q beta hb, hl⟩,
        (Normalization.lessRawCode_exact q beta (sourceSuccessorCode q alpha)).mpr
          ⟨RootLowCollapse.root_original q beta hb,
            ((Comparison.acceptedCode_exact q _).mp hs.2.1).1, by rw [hs.2.2]; exact hu⟩⟩⟩

/-- The actual alpha-context ceiling supplies the boundary witness, hence
an admitted high root of the SAME beta value without a representation input. -/
theorem target_root_exists (q alpha beta : Nat) (hi : inputCheck q alpha beta = true) :
    ∃ d, RootLowCollapse.rootCheck (betaCode q alpha) d = true ∧
      interpretation (betaCode q alpha) d = interpretation q beta := by
  obtain ⟨ha, hb, hp, hu⟩ := (inputCheck_exact q alpha beta).mp hi
  have hc := PublicEpsilonUnboundedIota.Enclosure.delta_enclosure_code_spec q alpha ha
  have hboundary := checked_low_bound (betaCode q alpha) _ hc.1
  rw [hc.2.2] at hboundary
  exact Support.root_exists_of_boundary (betaCode q alpha) (betaCode_baseCheck q alpha ha)
    (interpretation q beta) (by rw [beta_base q alpha ha]; exact hp)
    (RootLowCollapse.root_epsilon q beta hb) (hu.trans hboundary)

def candidate (q alpha beta d : Nat) : Bool :=
  RootLowCollapse.rootCheck (betaCode q alpha) d &&
    (UniformPublicReturn.publicCode (betaCode q alpha) d == UniformPublicReturn.publicCode q beta)

theorem candidate_primrec : Primrec₂
    (fun p : Query => candidate p.1.1 p.1.2 p.2) := by
  have hctx : Primrec (fun p : Query × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hq := Primrec.fst.comp hctx
  have ha := Primrec.snd.comp hctx
  have hb := Primrec.snd.comp Primrec.fst
  have hv := betaCode_primrec.comp hq ha
  have hleft := UniformPublicReturn.publicCode_primrec.comp hv Primrec.snd
  have hright := UniformPublicReturn.publicCode_primrec.comp hq hb
  exact (Primrec.and.comp (RootLowCollapse.rootCheck_primrec.comp hv Primrec.snd)
    (Primrec.beq.comp hleft hright)).to₂

theorem candidate_exact (q alpha beta d : Nat)
    (hb : RootLowCollapse.rootCheck q beta = true) : candidate q alpha beta d = true ↔
    RootLowCollapse.rootCheck (betaCode q alpha) d = true ∧
      interpretation (betaCode q alpha) d = interpretation q beta := by
  constructor
  · intro hi
    obtain ⟨hd, he⟩ := Bool.and_eq_true.mp hi
    have hs := UniformPublicReturn.publicCode_spec q beta
      ((UniformPublicReturn.inputCheck_exact q beta).mpr (RootLowCollapse.root_low q beta hb))
    have ht := UniformPublicReturn.publicCode_spec (betaCode q alpha) d
      ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low _ _ hd))
    have hc : UniformPublicReturn.publicCode (betaCode q alpha) d =
        UniformPublicReturn.publicCode q beta := beq_iff_eq.mp he
    exact ⟨hd, ht.2.symm.trans ((congrArg unionInterpretation hc).trans hs.2)⟩
  · rintro ⟨hd, hv⟩
    exact Bool.and_eq_true.mpr ⟨hd, beq_iff_eq.mpr
      (UniformPublicReturn.publicCode_value_invariant _ _ _ _
        ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low _ _ hd))
        ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low _ _ hb)) hv)⟩

theorem candidate_exists (q alpha beta : Nat) (hi : inputCheck q alpha beta = true) :
    ∃ d, candidate q alpha beta d = true := by
  obtain ⟨d, hd, hv⟩ := target_root_exists q alpha beta hi
  exact ⟨d, (candidate_exact q alpha beta d ((inputCheck_exact q alpha beta).mp hi).2.1).mpr ⟨hd, hv⟩⟩

def searchTest (p : Query) (d : Nat) : Bool :=
  cond (inputCheck p.1.1 p.1.2 p.2) (candidate p.1.1 p.1.2 p.2 d) (d == 0)

theorem searchTest_primrec : Primrec₂ searchTest :=
  ((inputCheck_primrec.comp Primrec.fst).cond candidate_primrec
    (Primrec.beq.comp Primrec.snd (Primrec.const 0))).to₂

theorem searchTest_exists (p : Query) : ∃ d, searchTest p d = true := by
  cases hi : inputCheck p.1.1 p.1.2 p.2 with
  | false => exact ⟨0, by simp only [searchTest, hi, Bool.cond_false, beq_self_eq_true]⟩
  | true =>
    obtain ⟨d, hd⟩ := candidate_exists p.1.1 p.1.2 p.2 hi
    exact ⟨d, by simpa only [searchTest, hi, Bool.cond_true] using hd⟩

def search (p : Query) : Part Nat := Nat.rfind (fun d => Part.some (searchTest p d))

theorem search_partrec : Partrec search :=
  Partrec.rfind searchTest_primrec.to_comp.partrec.to₂

theorem search_total (p : Query) : (search p).Dom := by
  obtain ⟨d, hd⟩ := searchTest_exists p
  exact Nat.rfind_dom.mpr ⟨d, by simpa only [Part.mem_some_iff] using hd.symm,
    fun {_} _ => trivial⟩

def translatedRootCode (q alpha beta : Nat) : Nat :=
  (search ((q, alpha), beta)).get (search_total ((q, alpha), beta))

theorem translatedRootCode_computable : Computable
    (fun p : Query => translatedRootCode p.1.1 p.1.2 p.2) :=
  search_partrec.of_eq_tot (fun p => Part.get_mem (search_total p))

theorem translatedRootCode_test (q alpha beta : Nat) :
    searchTest ((q, alpha), beta) (translatedRootCode q alpha beta) = true := by
  have h := Nat.rfind_spec (Part.get_mem (search_total ((q, alpha), beta)))
  exact (Part.mem_some_iff.mp h).symm

/-- The ACTUAL computed t_alpha^tau root is a genuine original alpha-context
high root and has the SAME original beta value on the full original interval. -/
theorem translatedRootCode_spec (q alpha beta : Nat) (hi : inputCheck q alpha beta = true) :
    RootLowCollapse.rootCheck (betaCode q alpha) (translatedRootCode q alpha beta) = true ∧
      interpretation (betaCode q alpha) (translatedRootCode q alpha beta) = interpretation q beta := by
  have ht : candidate q alpha beta (translatedRootCode q alpha beta) = true := by
    simpa only [searchTest, hi, Bool.cond_true] using translatedRootCode_test q alpha beta
  exact (candidate_exact q alpha beta _ ((inputCheck_exact q alpha beta).mp hi).2.1).mp ht

/-- Both actual beta contexts have literally the same canonical public
base code; no chosen spelling or base equality is supplied. -/
theorem translatedRootCode_betaCode (q alpha beta : Nat) (hi : inputCheck q alpha beta = true) :
    betaCode (betaCode q alpha) (translatedRootCode q alpha beta) = betaCode q beta := by
  have ht := translatedRootCode_test q alpha beta
  have hc : candidate q alpha beta (translatedRootCode q alpha beta) = true := by
    simpa only [searchTest, hi, Bool.cond_true] using ht
  exact beq_iff_eq.mp (Bool.and_eq_true.mp hc).2

def execute (p : Query) : Part Nat := cond (inputCheck p.1.1 p.1.2 p.2)
  (Part.some (translatedRootCode p.1.1 p.1.2 p.2)) Part.none

theorem execute_partrec : Partrec execute := by
  have h := inputCheck_primrec.to_comp.cond
    (Computable.option_some.comp translatedRootCode_computable) (Computable.const Option.none)
  exact (Computable.ofOption h).of_eq (fun p => by
    cases hi : inputCheck p.1.1 p.1.2 p.2 <;>
      simp only [execute, hi, Bool.cond_true, Bool.cond_false] <;> rfl)

theorem execute_graph (q alpha beta out : Nat) : out ∈ execute ((q, alpha), beta) ↔
    inputCheck q alpha beta = true ∧ out = translatedRootCode q alpha beta := by
  cases hi : inputCheck q alpha beta <;>
    simp only [execute, hi, Bool.cond_true, Bool.cond_false, Part.mem_some_iff,
      Part.notMem_none, Bool.false_eq_true, false_and, true_and, eq_comm]

theorem execute_domain (q alpha beta : Nat) : (execute ((q, alpha), beta)).Dom ↔
    inputCheck q alpha beta = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact ((execute_graph q alpha beta out).mp ho).1
  · intro hi
    exact Part.dom_iff_mem.mpr ⟨translatedRootCode q alpha beta,
      (execute_graph q alpha beta _).mpr ⟨hi, rfl⟩⟩

theorem execute_spec (q alpha beta out : Nat) (ho : out ∈ execute ((q, alpha), beta)) :
    inputCheck q alpha beta = true ∧ RootLowCollapse.rootCheck (betaCode q alpha) out = true ∧
      interpretation (betaCode q alpha) out = interpretation q beta := by
  obtain ⟨hi, rfl⟩ := (execute_graph q alpha beta out).mp ho
  exact ⟨hi, translatedRootCode_spec q alpha beta hi⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation
