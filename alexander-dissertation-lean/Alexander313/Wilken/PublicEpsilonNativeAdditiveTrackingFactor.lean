import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorSupport
import Alexander313.Wilken.PublicEpsilonNativeTrackingRaw

/-!
# Literal singleton and factor-removal callers of Definition3.20

The singleton test is the original non-M principal guard and the computed
literal tau^omega cutoff. The factor-removal branch has the same original
guard and the opposite strict cutoff. Its actual logarithm and finite ANF
produce a checked Normal prefix and final factor at the original context.
Actual MNF uniqueness derives the printed decomposition and strictly
smaller recursive prefix. Later branches2.1/2.2 are not assigned here.
All candidates are source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Factor

open FactorSupport
open MultiplicativeNormalForm MultiplicativePrincipalArithmetic
open SourceLocalization

def singletonCheck (q c : Nat) : Bool :=
  (RootAdapter.inputCheck q c && !SourceMultiplicativePrincipal.inputCheck q c) &&
    !Normalization.lessRawCode q (cutoffCode q) c

def splitCheck (q c : Nat) : Bool :=
  (RootAdapter.inputCheck q c && !SourceMultiplicativePrincipal.inputCheck q c) &&
    Normalization.lessRawCode q (cutoffCode q) c

theorem singletonCheck_primrec : Primrec₂ singletonCheck := by
  have hg := Primrec.and.comp RootAdapter.inputCheck_primrec
    (Primrec.not.comp SourceMultiplicativePrincipal.inputCheck_primrec)
  have hl := Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((cutoffCode_primrec.comp Primrec.fst).pair Primrec.snd))
  exact (Primrec.and.comp hg (Primrec.not.comp hl)).to₂

theorem splitCheck_primrec : Primrec₂ splitCheck := by
  have hg := Primrec.and.comp RootAdapter.inputCheck_primrec
    (Primrec.not.comp SourceMultiplicativePrincipal.inputCheck_primrec)
  have hl := Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((cutoffCode_primrec.comp Primrec.fst).pair Primrec.snd))
  exact (Primrec.and.comp hg hl).to₂

private theorem nonM_exact (q c : Nat) (hc : RootAdapter.inputCheck q c = true) :
    !SourceMultiplicativePrincipal.inputCheck q c = true ↔
      ¬IsMultiplicativePrincipal (interpretation q c) := by
  have hs := (RootAdapter.inputCheck_exact q c).mp hc
  rw [Bool.not_eq_true', ← Bool.not_eq_true]
  apply not_congr
  rw [SourceMultiplicativePrincipal.inputCheck_exact]
  simp only [hs.1, hs.2.1, true_and]

private theorem cutoff_less_exact (q c : Nat) (hc : RootAdapter.inputCheck q c = true) :
    Normalization.lessRawCode q (cutoffCode q) c = true ↔
      base q ^ Ordinal.omega0 < interpretation q c := by
  have hs := (RootAdapter.inputCheck_exact q c).mp hc
  have ht := cutoffCode_spec q (HeightBoundary.input_spec q c hs.1).2.1
  simpa only [((Comparison.acceptedCode_exact q _).mp ht.2.1).1,
    (Bool.and_eq_true.mp hs.1).1, ht.2.2, true_and] using
      Normalization.lessRawCode_exact q (cutoffCode q) c

theorem singletonCheck_exact (q c : Nat) : singletonCheck q c = true ↔
    lowCheckCode q c = true ∧ base q ≤ interpretation q c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q c) ∧
        ¬IsMultiplicativePrincipal (interpretation q c) ∧
          interpretation q c ≤ base q ^ Ordinal.omega0 := by
  rw [singletonCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hc, hm⟩, hcut⟩
    have hs := (RootAdapter.inputCheck_exact q c).mp hc
    have hnot : ¬Normalization.lessRawCode q (cutoffCode q) c = true := by
      simpa only [Bool.not_eq_true', ← Bool.not_eq_true] using hcut
    exact ⟨hs.1, hs.2.1, hs.2.2, (nonM_exact q c hc).mp hm,
      le_of_not_gt (fun h => hnot ((cutoff_less_exact q c hc).mpr h))⟩
  · rintro ⟨hl, hb, hp, hm, hcut⟩
    have hc := (RootAdapter.inputCheck_exact q c).mpr ⟨hl, hb, hp⟩
    refine ⟨⟨hc, (nonM_exact q c hc).mpr hm⟩, ?_⟩
    have hn : ¬Normalization.lessRawCode q (cutoffCode q) c = true := by
      intro h
      exact (not_lt_of_ge hcut) ((cutoff_less_exact q c hc).mp h)
    simpa only [Bool.not_eq_true', ← Bool.not_eq_true] using hn

theorem splitCheck_exact (q c : Nat) : splitCheck q c = true ↔
    lowCheckCode q c = true ∧ base q ≤ interpretation q c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q c) ∧
        ¬IsMultiplicativePrincipal (interpretation q c) ∧
          base q ^ Ordinal.omega0 < interpretation q c := by
  rw [splitCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hc, hm⟩, hcut⟩
    have hs := (RootAdapter.inputCheck_exact q c).mp hc
    exact ⟨hs.1, hs.2.1, hs.2.2, (nonM_exact q c hc).mp hm,
      (cutoff_less_exact q c hc).mp hcut⟩
  · rintro ⟨hl, hb, hp, hm, hcut⟩
    have hc := (RootAdapter.inputCheck_exact q c).mpr ⟨hl, hb, hp⟩
    exact ⟨⟨hc, (nonM_exact q c hc).mpr hm⟩, (cutoff_less_exact q c hc).mpr hcut⟩

theorem branches_exhaustive (q c : Nat) (hc : RootAdapter.inputCheck q c = true)
    (hm : ¬IsMultiplicativePrincipal (interpretation q c)) :
    singletonCheck q c = true ∨ splitCheck q c = true := by
  have hs := (RootAdapter.inputCheck_exact q c).mp hc
  rcases le_or_gt (interpretation q c) (base q ^ Ordinal.omega0) with h | h
  · exact Or.inl ((singletonCheck_exact q c).mpr ⟨hs.1, hs.2.1, hs.2.2, hm, h⟩)
  · exact Or.inr ((splitCheck_exact q c).mpr ⟨hs.1, hs.2.1, hs.2.2, hm, h⟩)

def singletonWord (c : Nat) : List Nat := [c]

theorem singletonWord_primrec : Primrec singletonWord :=
  Primrec.list_cons.comp Primrec.id (Primrec.const [])

theorem singletonWord_original (q c : Nat) (hc : singletonCheck q c = true) :
    singletonWord c = [c] ∧ (singletonWord c).map (interpretation q) = [interpretation q c] ∧
      SourceTrackingSequences.lastCode (singletonWord c) = c := ⟨rfl, rfl, rfl⟩

theorem singletonWord_checked (q c : Nat) (hc : singletonCheck q c = true) :
    SourceTrackingRaw.trackingCheck q (singletonWord c) = true := by
  have hi := (singletonCheck_exact q c).mp hc
  have hpos := (base_pos q (HeightBoundary.input_spec q c hi.1).2.1).trans_le hi.2.1
  have ht : SourceTrackingSequences.Tracking q [c] := by
    change [c] ≠ [] ∧ SourceTrackingSequences.Reference q [] ∧ lowCheckCode q c = true ∧
      0 < interpretation q c ∧ Ordinal.IsPrincipal (· + ·) (interpretation q c) ∧
        base q ≤ interpretation q c
    exact ⟨by simp, .nil, hi.1, hpos, hi.2.2.1, hi.2.1⟩
  apply (SourceTrackingRaw.trackingCheck_exact q _).mpr
  refine ⟨by simp only [singletonWord, List.cons_ne_nil, not_false_eq_true], ?_, ?_⟩
  · intro d hd
    exact False.elim (List.not_mem_nil hd)
  · simpa only [singletonWord, SourceTrackingRaw.trackingWord,
      SourceTrackingSequences.stripLast_singleton, SourceTrackingRaw.Support.rootWord_nil,
      SourceTrackingSequences.lastCode_singleton, List.nil_append] using ht

abbrev Output := Nat × Nat

def execute (q c : Nat) : Part Output := cond (splitCheck q c)
  ((LogEnd.execute q c).map fun d => (prefixCode q d, lastCode q d)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have ho : Computable₂ (fun p : Nat × Nat => fun d : Nat => (prefixCode p.1 d, lastCode p.1 d)) :=
    ((prefixCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
      (lastCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to_comp.to₂
  exact (Partrec.cond splitCheck_primrec.to_comp
    (Partrec.map LogEnd.execute_partrec ho) Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ splitCheck q c = true := by
  cases hc : splitCheck q c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hl := ((splitCheck_exact q c).mp hc).1
    rw [execute, hc, Bool.cond_true]
    change (LogEnd.execute q c).Dom ↔ true = true
    have hd := (LogEnd.execute_domain q c).mpr hl
    exact ⟨fun _ => rfl, fun _ => hd⟩

/-- The actual finite outputs realize the source NF split and its smaller
recursive caller. All output admission, the final factor class and the
source interval are consequences of the unchanged original raw guard. -/
theorem execute_spec (q c : Nat) (out : Output) (ho : out ∈ execute q c) :
    splitCheck q c = true ∧
      lowCheckCode q out.1 = true ∧ Comparison.acceptedCode q out.1 = true ∧
      lowCheckCode q out.2 = true ∧ Comparison.acceptedCode q out.2 = true ∧
      RootAdapter.inputCheck q out.1 = true ∧
      base q ≤ interpretation q out.1 ∧ interpretation q out.1 < interpretation q c ∧
      IsMultiplicativePrincipal (interpretation q out.2) ∧ 1 < interpretation q out.2 ∧
      interpretation q c = interpretation q out.1 * interpretation q out.2 ∧
      interpretation q out.2 = lf (interpretation q c) ∧
      (canonicalMNF (interpretation q out.1)).length < (canonicalMNF (interpretation q c)).length := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hi := (splitCheck_exact q c).mp hc
  have hq := (HeightBoundary.input_spec q c hi.1).2.1
  have hpos := (base_pos q hq).trans_le hi.2.1
  have hlarge := (LogEndZero.one_lt_base q hq).trans_le hi.2.1
  rw [execute, hc, Bool.cond_true] at ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := LogEnd.execute_spec q c d hd
  have hlog : Ordinal.omega0 ^ interpretation q d = interpretation q c := by
    have h : Ordinal.omega0 ^ interpretation q d = Hereditary.LogEnd.endValue (interpretation q c) := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hpos),
        Hereditary.LogEnd.endValue] using hs.2.2.2
    exact h.trans (SourceChi.Powers.endValue_principal _ hpos hi.2.2.1)
  have hz : interpretation q d ≠ 0 := by
    intro h
    have hu : interpretation q c = 1 := by simpa only [h, Ordinal.opow_zero] using hlog.symm
    rw [hu] at hlarge
    exact lt_irrefl _ hlarge
  have hword : omegaFactors (interpretation q d) = canonicalMNF (interpretation q c) := by
    rw [← hlog, canonicalMNF_omegaPower]
  have hp := prefixCode_spec q d hs.2.1 hs.2.2.1
  have ht := lastCode_spec q d hs.2.1 hs.2.2.1 hz
  rw [hword] at hp ht
  have hbase := SourceMultiplicativePrincipal.epsilon_multiplicative _ (SourceChi.epsilon_base q hq)
  have hm := MultiplicativeFactorRemoval.source_prefix_last_interval hbase hpos hi.2.2.1
    hi.2.1 hi.2.2.2.1
  have hpre := MultiplicativeFactorRemoval.factorPrefix_reduced _ (canonicalMNF_reduced (interpretation q c))
  have hprincipal := isMNF_product_principal hpre.1
  have hpcaller := (RootAdapter.inputCheck_exact q _).mpr
    ⟨hp.1, by rw [hp.2.2]; exact hm.1, by rw [hp.2.2]; exact hprincipal.2⟩
  refine ⟨hc, hp.1, hp.2.1, ht.1, ht.2.1, hpcaller, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp.2.2]; exact hm.1
  · rw [hp.2.2]; exact hm.2.1
  · rw [ht.2.2]; exact hm.2.2.1
  · rw [ht.2.2]; exact hm.2.2.2.1
  · rw [hp.2.2, ht.2.2]; exact hm.2.2.2.2
  · exact ht.2.2
  · rw [hp.2.2]
    exact MultiplicativeFactorRemoval.source_prefix_factor_count_lt hpos hi.2.2.1 hi.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Factor
