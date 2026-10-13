import Alexander313.Wilken.HereditaryGlobalHLarge
import Alexander313.Wilken.HereditaryGlobalHSmall
import Alexander313.Wilken.HereditaryFinitePowers

/-!
# The three actual global h clauses on the represented source domain

The true multiplicative cutoff guard and original segmented reference are
checked independently. A strict larger cutoff uses the actual mts covering
and penultimate epsilon; the two smaller-cutoff alternatives use the actual
public mu test. The exact partial recursive domain is the genuine semantic
singleton cut, and every emitted word has an independent global tracker.
No numerical minimum, arbitrary-reach sufficiency or transfinite code is
asserted. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalH

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open GlobalTrackingSequences (Reference Tracking referenceCheck referenceCheck_primrec
  referenceCheck_exact trackingCheck trackingCheck_exact)
open PublicMts
open FinitePowers (oneCode oneCode_checked oneCode_value)

abbrev Query := List Nat × (Nat × Nat)

/-- The independently constructed least original singleton is strictly
above the original root, in both genuine selected source dictionaries. -/
theorem root_lt_hat (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    unionInterpretation gamma < InfinityHat.value gamma hg := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have ha := ContextSupport.source_one_base gamma hg hl
    have hp := SourceOneIota.alphaCode_spec _ ha.1
    have hv : unionInterpretation gamma =
        Hereditary.interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
      rw [← ha.2]; exact hp.2
    obtain ⟨c, hc, he, ho, hroot, hmu, hupper⟩ := SourceOneIota.GammaHat.value_spec _ ha.1
    simpa only [InfinityHat.value, dif_pos hl, SourceOneHat.value, hv] using hroot
  · have ha := ContextSupport.positive_base gamma hg hl
    have hp := betaCode_spec _ _ ha.1
    have hv : unionInterpretation gamma = interpretation
        (MuPublicDictionary.Support.nativeContext gamma) (MuPublicDictionary.Support.nativeRoot gamma) := by
      rw [← ha.2]; exact hp.2
    obtain ⟨c, hc, he, ho, hroot, hmu, hupper⟩ := GammaHat.value_spec _ _ ha.1
    simpa only [InfinityHat.value, dif_neg hl, PositiveHat.value, hv] using hroot

def inputCheck (p : Query) : Bool :=
  referenceCheck (p.1 ++ [p.2.1]) &&
    (MuPublicDictionary.Support.inputCheck p.2.1 &&
      (Multiplicative.canonicalCheck p.2.2 && Canonical.less oneCode p.2.2))

theorem inputCheck_computable : Computable inputCheck := by
  have hg := Primrec.fst.comp Primrec.snd
  have hb := Primrec.snd.comp Primrec.snd
  have hw := Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp hg (Primrec.const []))
  have hm := Primrec.and.to_comp.comp (Multiplicative.canonicalCheck_computable.comp hb.to_comp)
    (Canonical.Effective.less_primrec.comp (Primrec.const oneCode) hb).to_comp
  exact Primrec.and.to_comp.comp (referenceCheck_primrec.comp hw).to_comp
    (Primrec.and.to_comp.comp (MuPublicDictionary.Support.inputCheck_primrec.comp hg).to_comp hm)

theorem inputCheck_exact (p : Query) : inputCheck p = true ↔
    Reference (p.1 ++ [p.2.1]) ∧ MuPublicDictionary.Support.inputCheck p.2.1 = true ∧
      Canonical.check p.2.2 = true ∧
        MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2) ∧
          1 < unionInterpretation p.2.2 := by
  rw [inputCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    referenceCheck_exact, Multiplicative.canonicalCheck_exact, Canonical.less_exact]
  simp only [oneCode_checked, oneCode_value, true_and]
  tauto

def execute (p : Query) : Part (List Nat) := cond (inputCheck p)
  (cond (Canonical.less p.2.1 p.2.2) (GlobalHLarge.execute p) (GlobalHSmall.execute p)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_computable
    (Partrec.cond (Canonical.Effective.less_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
      GlobalHLarge.execute_partrec GlobalHSmall.execute_partrec) Partrec.none

/-- The branch is derived by the genuine canonical comparison. Its two
small cases are then selected by the independently executing public mu. -/
theorem execute_branches (p : Query) (out : List Nat) : out ∈ execute p ↔
    inputCheck p = true ∧
      ((unionInterpretation p.2.1 < unionInterpretation p.2.2 ∧ out ∈ GlobalHLarge.execute p) ∨
        (unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 ∧ out ∈ GlobalHSmall.execute p)) := by
  constructor
  · intro ho
    have hi : inputCheck p = true := by
      cases hc : inputCheck p with
      | true => rfl
      | false => exact False.elim (by
          simpa only [execute, hc, Bool.cond_false, Part.notMem_none] using ho)
    have hs := (inputCheck_exact p).mp hi
    have hg := ((MuPublicDictionary.Support.inputCheck_image _).mp hs.2.1).1
    refine ⟨hi, ?_⟩
    cases hc : Canonical.less p.2.1 p.2.2 with
    | true =>
      exact Or.inl ⟨((Canonical.less_exact _ _).mp hc).2.2,
        by simpa only [execute, hi, hc, Bool.cond_true] using ho⟩
    | false =>
      have hb : unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 := by
        apply le_of_not_gt
        intro hlt
        have ht := (Canonical.less_exact _ _).mpr ⟨hg, hs.2.2.1, hlt⟩
        rw [hc] at ht; cases ht
      exact Or.inr ⟨hb, by simpa only [execute, hi, hc, Bool.cond_true, Bool.cond_false] using ho⟩
  · rintro ⟨hi, ⟨hlt, ho⟩ | ⟨hle, ho⟩⟩
    · have hs := (inputCheck_exact p).mp hi
      have hg := ((MuPublicDictionary.Support.inputCheck_image _).mp hs.2.1).1
      have hc := (Canonical.less_exact _ _).mpr ⟨hg, hs.2.2.1, hlt⟩
      simpa only [execute, hi, hc, Bool.cond_true] using ho
    · have hc : Canonical.less p.2.1 p.2.2 = false := Bool.eq_false_of_not_eq_true (by
        intro ht; exact hle.not_gt ((Canonical.less_exact _ _).mp ht).2.2)
      simpa only [execute, hi, hc, Bool.cond_true, Bool.cond_false] using ho

/-- The three literal source clauses use actual independent procedures:
the large mts/sk splice, the covered small sk splice, and the unchanged
original reference when the true public mu does not cover the cutoff. -/
theorem execute_clauses (p : Query) (out : List Nat) : out ∈ execute p ↔
    inputCheck p = true ∧
      ((unionInterpretation p.2.1 < unionInterpretation p.2.2 ∧ ∃ codes,
          codes ∈ Infinity.execute p.2.1 p.2.2 ∧
            CoveringSupport.Covering p.2.1 p.2.2 codes ∧ ∃ word,
              word ∈ SkPublicDictionary.execute (GlobalHLarge.epsilon codes, p.2.2) ∧
                out = GlobalHLarge.retained p codes ++ word) ∨
        (unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 ∧
          unionInterpretation p.2.2 ≤ SkPublicRecurrence.muValue p.2.1 ∧
            ∃ word, word ∈ SkPublicDictionary.execute p.2 ∧ out = p.1 ++ word) ∨
        (unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 ∧
          SkPublicRecurrence.muValue p.2.1 < unionInterpretation p.2.2 ∧
            out = p.1 ++ [p.2.1])) := by
  constructor
  · intro ho
    obtain ⟨hi, hbranch⟩ := (execute_branches p out).mp ho
    refine ⟨hi, ?_⟩
    rcases hbranch with ⟨hlt, hl⟩ | ⟨hle, hl⟩
    · exact Or.inl ⟨hlt, ((GlobalHLarge.execute_spec p out).mp hl).2⟩
    · rcases ((GlobalHSmall.execute_clauses p out).mp hl).2 with hs | hs
      · exact Or.inr (Or.inl ⟨hle, hs⟩)
      · exact Or.inr (Or.inr ⟨hle, hs⟩)
  · rintro ⟨hi, ⟨hlt, codes, hc, ht, word, hw, he⟩ | ⟨hle, hs⟩ | ⟨hle, hs⟩⟩
    · have hg := (inputCheck_exact p).mp hi
      have hm := (Infinity.execute_spec _ _ _ hc).1
      have hl := (GlobalHLarge.inputCheck_exact p).mpr ⟨hg.1, hm, hlt, hg.2.2.2.1⟩
      exact (execute_branches p out).mpr ⟨hi, Or.inl ⟨hlt,
        (GlobalHLarge.execute_spec p out).mpr ⟨hl, codes, hc, ht, word, hw, he⟩⟩⟩
    · have hg := (inputCheck_exact p).mp hi
      have hl := (GlobalHSmall.inputCheck_exact p).mpr ⟨hg.1, hg.2.1, hg.2.2.1, hle⟩
      exact (execute_branches p out).mpr ⟨hi, Or.inr ⟨hle,
        (GlobalHSmall.execute_clauses p out).mpr ⟨hl, Or.inl hs⟩⟩⟩
    · have hg := (inputCheck_exact p).mp hi
      have hl := (GlobalHSmall.inputCheck_exact p).mpr ⟨hg.1, hg.2.1, hg.2.2.1, hle⟩
      exact (execute_branches p out).mpr ⟨hi, Or.inr ⟨hle,
        (GlobalHSmall.execute_clauses p out).mpr ⟨hl, Or.inr hs⟩⟩⟩

/-- This is the complete represented Definition3.34 domain; an infinity
bound, reached word, penultimate caller or numerical hat is not supplied. -/
theorem execute_domain_exact (p : Query) : (execute p).Dom ↔
    ∃ hg : MuPublicDictionary.Support.inputCheck p.2.1 = true,
      Reference (p.1 ++ [p.2.1]) ∧ Canonical.check p.2.2 = true ∧
        MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2) ∧
          1 < unionInterpretation p.2.2 ∧ unionInterpretation p.2.2 < InfinityHat.value p.2.1 hg := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨hi, hbranch⟩ := (execute_branches p out).mp ho
    have hs := (inputCheck_exact p).mp hi
    refine ⟨hs.2.1, hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
    rcases hbranch with ⟨hlt, hl⟩ | ⟨hle, hl⟩
    · obtain ⟨hg, hr, hb, hm, hlt, hcut⟩ :=
        (GlobalHLarge.execute_domain_exact p).mp (Part.dom_iff_mem.mpr ⟨out, hl⟩)
      exact hcut
    · exact hle.trans_lt (root_lt_hat _ hs.2.1)
  · rintro ⟨hg, hr, hb, hm, hone, hcut⟩
    have hi := (inputCheck_exact p).mpr ⟨hr, hg, hb, hm, hone⟩
    by_cases hlt : unionInterpretation p.2.1 < unionInterpretation p.2.2
    · have hd := (GlobalHLarge.execute_domain_exact p).mpr ⟨hg, hr, hb, hm, hlt, hcut⟩
      obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
      exact Part.dom_iff_mem.mpr ⟨out, (execute_branches p out).mpr ⟨hi, Or.inl ⟨hlt, ho⟩⟩⟩
    · have hle := le_of_not_gt hlt
      have hs := (GlobalHSmall.inputCheck_exact p).mpr ⟨hr, hg, hb, hle⟩
      obtain ⟨out, ho⟩ := GlobalHSmall.execute_returns p hs
      exact Part.dom_iff_mem.mpr ⟨out, (execute_branches p out).mpr ⟨hi, Or.inr ⟨hle, ho⟩⟩⟩

theorem execute_tracking (p : Query) (out : List Nat) (ho : out ∈ execute p) : Tracking out := by
  obtain ⟨hi, hbranch⟩ := (execute_branches p out).mp ho
  have hs := (inputCheck_exact p).mp hi
  rcases hbranch with ⟨hlt, hl⟩ | ⟨hle, hl⟩
  · exact GlobalHLarge.execute_tracking p out hl
  · exact GlobalHSmall.execute_tracking p out hl hs.2.2.2.1 hs.2.2.2.2

theorem execute_trackingCheck (p : Query) (out : List Nat) (ho : out ∈ execute p) :
    trackingCheck out = true := (trackingCheck_exact out).mpr (execute_tracking p out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalH
