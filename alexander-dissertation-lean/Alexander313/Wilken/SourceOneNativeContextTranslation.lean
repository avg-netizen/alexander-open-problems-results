import Alexander313.Wilken.SourceOneNativeContextTranslationSupport
import Alexander313.Wilken.SourceOneNativeMuValueInvariance
import Mathlib.Computability.Partrec

/-!
# Full genuine original-source-one contextual mu equality

The unchanged original check-zero high roots and printed alpha<beta<alphaPlus
interval derive a finite HIGH beta root at the genuine epsilon alphaCode.
The actual Nat.rfind uses target admission and computed canonical beta equality.
Its domain witnesses follow from coverage and the ORIGINAL selected endpoint
identity. The real original-source-one return/coefficient/iota/chi equations
then compare mu of this constructed translation with mu of the original beta,
using proved SAME-source mu spelling invariance. No Native base-one parser,
representation, endpoint, coefficient, indicator or mu-fidelity oracle.
Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ContextTranslation

open Support

abbrev Query := Nat × Nat

def inputCheck (alpha beta : Nat) : Bool :=
  (rootCheck alpha && rootCheck beta) &&
    (Theta.Normalization.lessRawCode 0 alpha beta &&
      Theta.Normalization.lessRawCode 0 beta (sourceSuccessorCode alpha))

theorem inputCheck_primrec : Primrec₂ inputCheck := by
  have hfirst := sourceSuccessorCode_primrec.comp Primrec.fst
  have hlow := Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair (Primrec.fst.pair Primrec.snd))
  have hhigh := Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair (Primrec.snd.pair hfirst))
  exact (Primrec.and.comp
    (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst) (rootCheck_primrec.comp Primrec.snd))
    (Primrec.and.comp hlow hhigh)).to₂

theorem inputCheck_exact (alpha beta : Nat) : inputCheck alpha beta = true ↔
    rootCheck alpha = true ∧ rootCheck beta = true ∧
      interpretation 0 alpha < interpretation 0 beta ∧
      interpretation 0 beta < Enclosure.sourceAlphaPlus alpha := by
  constructor
  · intro hi
    obtain ⟨hroot, hinterval⟩ := Bool.and_eq_true.mp hi
    obtain ⟨ha, hb⟩ := Bool.and_eq_true.mp hroot
    obtain ⟨hl, hu⟩ := Bool.and_eq_true.mp hinterval
    have hs := sourceSuccessorCode_spec alpha ha
    have hp := (Theta.Normalization.lessRawCode_correct 0 alpha beta
      (root_original alpha ha) (root_original beta hb)).mp hl
    have he := (Theta.Normalization.lessRawCode_correct 0 beta (sourceSuccessorCode alpha)
      (root_original beta hb) ((Theta.acceptedCode_iff 0 _).mp hs.1).1).mp hu
    exact ⟨ha, hb, hp, he.trans_eq hs.2⟩
  · rintro ⟨ha, hb, hl, hu⟩
    have hs := sourceSuccessorCode_spec alpha ha
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha, hb⟩,
      Bool.and_eq_true.mpr
        ⟨(Theta.Normalization.lessRawCode_correct 0 alpha beta
          (root_original alpha ha) (root_original beta hb)).mpr hl,
        (Theta.Normalization.lessRawCode_correct 0 beta (sourceSuccessorCode alpha)
          (root_original beta hb) ((Theta.acceptedCode_iff 0 _).mp hs.1).1).mpr
          (by rw [hs.2]; exact hu)⟩⟩

def candidate (alpha beta d : Nat) : Bool :=
  NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) d &&
    (NativeContext.PublicEpsilonIota.betaCode (alphaCode alpha) d == alphaCode beta)

theorem candidate_primrec : Primrec₂ (fun p : Query => candidate p.1 p.2) := by
  have ha := Primrec.fst.comp Primrec.fst
  have hb := Primrec.snd.comp Primrec.fst
  have hctx := alphaCode_primrec.comp ha
  have hleft := NativeContext.PublicEpsilonIota.betaCode_primrec.comp hctx Primrec.snd
  have hright := alphaCode_primrec.comp hb
  exact (Primrec.and.comp (NativeContext.PublicEpsilonIota.rootCheck_primrec.comp hctx Primrec.snd)
    (Primrec.beq.comp hleft hright)).to₂

theorem candidate_exact (alpha beta d : Nat) (hb : rootCheck beta = true) :
    candidate alpha beta d = true ↔
      NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) d = true ∧
        NativeContext.interpretation (alphaCode alpha) d = interpretation 0 beta := by
  constructor
  · intro hi
    obtain ⟨hd, he⟩ := Bool.and_eq_true.mp hi
    have hs := alphaCode_spec beta hb
    have ht := NativeContext.PublicEpsilonIota.betaCode_spec (alphaCode alpha) d hd
    have hc : NativeContext.PublicEpsilonIota.betaCode (alphaCode alpha) d = alphaCode beta := beq_iff_eq.mp he
    exact ⟨hd, ht.2.symm.trans ((congrArg unionInterpretation hc).trans hs.2)⟩
  · rintro ⟨hd, hv⟩
    have hs := alphaCode_spec beta hb
    have ht := NativeContext.PublicEpsilonIota.betaCode_spec (alphaCode alpha) d hd
    exact Bool.and_eq_true.mpr ⟨hd, beq_iff_eq.mpr
      (Canonical.check_value_injective _ _ ht.1 hs.1 (ht.2.trans (hv.trans hs.2.symm)))⟩

theorem candidate_exists (alpha beta : Nat) (hi : inputCheck alpha beta = true) :
    ∃ d, candidate alpha beta d = true := by
  obtain ⟨ha, hb, hp, hu⟩ := (inputCheck_exact alpha beta).mp hi
  obtain ⟨d, hd, hv⟩ := target_root_exists alpha beta ha hb hp hu
  exact ⟨d, (candidate_exact alpha beta d hb).mpr ⟨hd, hv⟩⟩

def searchTest (p : Query) (d : Nat) : Bool :=
  cond (inputCheck p.1 p.2) (candidate p.1 p.2 d) (d == 0)

theorem searchTest_primrec : Primrec₂ searchTest :=
  ((Primrec.comp inputCheck_primrec Primrec.fst).cond candidate_primrec
    (Primrec.beq.comp Primrec.snd (Primrec.const 0))).to₂

theorem searchTest_exists (p : Query) : ∃ d, searchTest p d = true := by
  cases hi : inputCheck p.1 p.2 with
  | false => exact ⟨0, by simp only [searchTest, hi, Bool.cond_false, beq_self_eq_true]⟩
  | true =>
    obtain ⟨d, hd⟩ := candidate_exists p.1 p.2 hi
    exact ⟨d, by simpa only [searchTest, hi, Bool.cond_true] using hd⟩

def search (p : Query) : Part Nat := Nat.rfind (fun d => Part.some (searchTest p d))

theorem search_partrec : Partrec search := Partrec.rfind searchTest_primrec.to_comp.partrec.to₂

theorem search_total (p : Query) : (search p).Dom := by
  obtain ⟨d, hd⟩ := searchTest_exists p
  exact Nat.rfind_dom.mpr ⟨d, by simpa only [Part.mem_some_iff] using hd.symm,
    fun {_} _ => trivial⟩

def translatedRootCode (alpha beta : Nat) : Nat :=
  (search (alpha, beta)).get (search_total (alpha, beta))

theorem translatedRootCode_computable : Computable₂ translatedRootCode :=
  (search_partrec.of_eq_tot (fun p => Part.get_mem (search_total p))).to₂

theorem translatedRootCode_test (alpha beta : Nat) :
    searchTest (alpha, beta) (translatedRootCode alpha beta) = true := by
  have h := Nat.rfind_spec (Part.get_mem (search_total (alpha, beta)))
  exact (Part.mem_some_iff.mp h).symm

theorem translatedRootCode_spec (alpha beta : Nat) (hi : inputCheck alpha beta = true) :
    NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) (translatedRootCode alpha beta) = true ∧
      NativeContext.interpretation (alphaCode alpha) (translatedRootCode alpha beta) = interpretation 0 beta := by
  have ht : candidate alpha beta (translatedRootCode alpha beta) = true := by
    simpa only [searchTest, hi, Bool.cond_true] using translatedRootCode_test alpha beta
  exact (candidate_exact alpha beta _ ((inputCheck_exact alpha beta).mp hi).2.1).mp ht

theorem translatedRootCode_betaCode (alpha beta : Nat) (hi : inputCheck alpha beta = true) :
    NativeContext.PublicEpsilonIota.betaCode (alphaCode alpha) (translatedRootCode alpha beta) = alphaCode beta := by
  have hc : candidate alpha beta (translatedRootCode alpha beta) = true := by
    simpa only [searchTest, hi, Bool.cond_true] using translatedRootCode_test alpha beta
  exact beq_iff_eq.mp (Bool.and_eq_true.mp hc).2

def execute (p : Query) : Part Nat := cond (inputCheck p.1 p.2)
  (Part.some (translatedRootCode p.1 p.2)) Part.none

theorem execute_partrec : Partrec execute := by
  have h := inputCheck_primrec.to_comp.cond
    (Computable.comp Computable.option_some translatedRootCode_computable) (Computable.const Option.none)
  exact (Computable.ofOption h).of_eq (fun p => by
    cases hi : inputCheck p.1 p.2 <;>
      simp only [execute, hi, Bool.cond_true, Bool.cond_false] <;> rfl)

theorem execute_graph (alpha beta out : Nat) : out ∈ execute (alpha, beta) ↔
    inputCheck alpha beta = true ∧ out = translatedRootCode alpha beta := by
  cases hi : inputCheck alpha beta <;>
    simp only [execute, hi, Bool.cond_true, Bool.cond_false, Part.mem_some_iff,
      Part.notMem_none, Bool.false_eq_true, false_and, true_and, eq_comm]

theorem execute_domain (alpha beta : Nat) : (execute (alpha, beta)).Dom ↔ inputCheck alpha beta = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact ((execute_graph alpha beta out).mp ho).1
  · intro hi
    exact Part.dom_iff_mem.mpr ⟨translatedRootCode alpha beta,
      (execute_graph alpha beta _).mpr ⟨hi, rfl⟩⟩

theorem execute_spec (alpha beta out : Nat) (ho : out ∈ execute (alpha, beta)) :
    inputCheck alpha beta = true ∧ NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) out = true ∧
      NativeContext.interpretation (alphaCode alpha) out = interpretation 0 beta := by
  obtain ⟨hi, rfl⟩ := (execute_graph alpha beta out).mp ho
  exact ⟨hi, translatedRootCode_spec alpha beta hi⟩

/-- The actual original-source-one returned root and genuine alpha-context
root have equal mu values by the real coefficient/iota/indicator theorem. -/
theorem returned_sourceValue_eq (alpha d : Nat) (ha : rootCheck alpha = true)
    (hd : NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) d = true) :
    Mu.sourceValue (BoundedContextReturn.returnedRoot alpha d) =
      NativeContext.PublicEpsilonIota.Mu.sourceValue (alphaCode alpha) d := by
  have hr := BoundedContextReturn.returnedRoot_iota_caller alpha d ha hd
  have hs := Mu.muCode_spec (BoundedContextReturn.returnedRoot alpha d) hr
  rw [BoundedContextReturn.returnedRoot_alphaCode alpha d ha hd] at hs
  exact hs.2.2.symm.trans ((BoundedContextReturn.MuTranslation.muCode_value alpha d ha hd).trans
    (NativeContext.PublicEpsilonIota.Mu.muCode_spec (alphaCode alpha) d hd).2.2)

/-- Full actual contextual Lemma3.8 at the ORIGINAL source base one. -/
theorem sourceValue_translation (alpha beta : Nat) (hi : inputCheck alpha beta = true) :
    Mu.sourceValue beta = NativeContext.PublicEpsilonIota.Mu.sourceValue (alphaCode alpha) (translatedRootCode alpha beta) := by
  have hs := (inputCheck_exact alpha beta).mp hi
  have ht := translatedRootCode_spec alpha beta hi
  have hr := BoundedContextReturn.returnedRoot_iota_caller alpha _ hs.1 ht.1
  have hv := (BoundedContextReturn.returnedRoot_spec alpha _ hs.1 ht.1).2.2
  have he : interpretation 0 beta = interpretation 0
      (BoundedContextReturn.returnedRoot alpha (translatedRootCode alpha beta)) := ht.2.symm.trans hv.symm
  exact (Mu.ValueInvariance.sourceValue_eq beta _ hs.2.1 hr he).trans
    (returned_sourceValue_eq alpha _ hs.1 ht.1)

theorem execute_translation (alpha beta out : Nat) (hi : inputCheck alpha beta = true)
    (ho : out ∈ Mu.execute beta) :
    ∃ translatedOut : Nat,
      translatedOut ∈ NativeContext.PublicEpsilonIota.Mu.execute (alphaCode alpha) (translatedRootCode alpha beta) ∧
      NativeContext.interpretation (alphaCode beta) out = NativeContext.interpretation (alphaCode beta) translatedOut := by
  have ht := translatedRootCode_spec alpha beta hi
  let targetOut := NativeContext.PublicEpsilonIota.Mu.muCode (alphaCode alpha) (translatedRootCode alpha beta)
  have he : targetOut ∈ NativeContext.PublicEpsilonIota.Mu.execute (alphaCode alpha) (translatedRootCode alpha beta) :=
    (NativeContext.PublicEpsilonIota.Mu.execute_graph _ _ targetOut).mpr ⟨ht.1, rfl⟩
  have hs := Mu.execute_spec beta out ho
  have hv := (NativeContext.PublicEpsilonIota.Mu.muCode_spec (alphaCode alpha) (translatedRootCode alpha beta) ht.1).2.2
  rw [translatedRootCode_betaCode alpha beta hi] at hv
  exact ⟨targetOut, he, hs.2.2.2.trans ((sourceValue_translation alpha beta hi).trans hv.symm)⟩

theorem execute_value_eq (alpha beta out translatedOut : Nat) (hi : inputCheck alpha beta = true)
    (ho : out ∈ Mu.execute beta)
    (ht : translatedOut ∈ NativeContext.PublicEpsilonIota.Mu.execute (alphaCode alpha) (translatedRootCode alpha beta)) :
    NativeContext.interpretation (alphaCode beta) out = NativeContext.interpretation (alphaCode beta) translatedOut := by
  have hs := Mu.execute_spec beta out ho
  have hu := NativeContext.PublicEpsilonIota.Mu.execute_spec _ _ translatedOut ht
  rw [translatedRootCode_betaCode alpha beta hi] at hu
  exact hs.2.2.2.trans ((sourceValue_translation alpha beta hi).trans hu.2.2.2.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ContextTranslation
