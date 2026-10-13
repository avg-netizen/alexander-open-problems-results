import Alexander313.Wilken.HereditaryPublicMtsInfinitySupport

/-!
# Executing mts on the genuine full alpha-infinity interval

A proper canonical epsilon gamma and a canonical positive additive principal
gamma <= beta < gamma-infinity supply an actual LOW search at literal gamma.
The genuine normalized root and native localization provide the chronological
table input. Every proper intermediate epsilon derives its independent actual
public mu query inside the original finite gap; no incoming native-gamma mu
identity outside OWN is assumed. The same least-passing table therefore
executes Definition3.28 on its full representable domain and agrees literally
with the existing OWN-domain execution. Covering/hat/reach outside OWN remain
separate mathematical statements. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Infinity

open NativeContext
open InfinitySupport

def inputCheck (gamma beta : Nat) : Bool :=
  (MuPublicDictionary.Support.inputCheck gamma && PublicTrackingSequences.principalCheck beta) &&
    (!(Canonical.less beta gamma) && Canonical.less beta (infinityCode gamma))

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp Primrec.fst)
      (PublicTrackingSequences.principalCheck_primrec.comp Primrec.snd))
    (Primrec.and.comp (Primrec.not.comp (Canonical.Effective.less_primrec.comp Primrec.snd Primrec.fst))
      (Canonical.Effective.less_primrec.comp Primrec.snd (infinityCode_primrec.comp Primrec.fst)))).to₂

/-- Exact source domain uses the actual grammar boundary, rather than
the smaller original successor ceiling. -/
theorem inputCheck_exact (gamma beta : Nat) : inputCheck gamma beta = true ↔
    MuPublicDictionary.Support.inputCheck gamma = true ∧ Canonical.check beta = true ∧
      0 < unionInterpretation beta ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) ∧
        unionInterpretation gamma ≤ unionInterpretation beta ∧
          unionInterpretation beta < globalBoundary (base gamma) 0 := by
  constructor
  · intro hi
    have hs := Bool.and_eq_true.mp hi
    have hp := Bool.and_eq_true.mp hs.1
    have hb := (PublicTrackingSequences.principalCheck_exact beta).mp hp.2
    have hc := infinityCode_spec gamma hp.1
    have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hp.1).1
    have ht := Bool.and_eq_true.mp hs.2
    refine ⟨hp.1, hb.1, hb.2.1, hb.2.2, ?_, ?_⟩
    · exact (SourceTrackingSequences.Support.canonical_not_less_exact beta gamma hb.1 hgcanon).mp
        (Bool.not_eq_true'.mp ht.1)
    · exact ((Canonical.less_exact beta (infinityCode gamma)).mp ht.2).2.2.trans_eq hc.2
  · rintro ⟨hg, hb, hp, ha, hf, hu⟩
    have hc := infinityCode_spec gamma hg
    have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr
      ⟨hg, (PublicTrackingSequences.principalCheck_exact beta).mpr ⟨hb, hp, ha⟩⟩,
      Bool.and_eq_true.mpr ⟨Bool.not_eq_true'.mpr
        ((SourceTrackingSequences.Support.canonical_not_less_exact beta gamma hb hgcanon).mpr hf),
        (Canonical.less_exact beta (infinityCode gamma)).mpr ⟨hb, hc.1, hu.trans_eq hc.2.symm⟩⟩⟩

theorem gamma_baseCheck (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    baseCheck gamma = true := by
  have hg := (MuPublicDictionary.Support.inputCheck_image gamma).mp ((inputCheck_exact gamma beta).mp hi).1
  exact (baseCheck_exact gamma).mpr ⟨Canonical.check_original hg.1, hg.2.1⟩

theorem search_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    ∃ d, d ∈ SkNextSearch.Support.search gamma beta := by
  have hs := (inputCheck_exact gamma beta).mp hi
  exact SkNextSearch.Support.search_returns gamma beta (gamma_baseCheck gamma beta hi)
    hs.2.1 hs.2.2.2.2.2

abbrev nativeRoot := PublicMts.nativeRoot
abbrev localization := PublicMts.localization

theorem nativeRoot_primrec : Primrec₂ nativeRoot := PublicMts.nativeRoot_primrec
theorem localization_primrec : Primrec₂ localization := PublicMts.localization_primrec

theorem nativeRoot_spec (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    SourceLocalization.inputCheck gamma (nativeRoot gamma d) = true ∧
      interpretation gamma (nativeRoot gamma d) = unionInterpretation beta := by
  have hs := (inputCheck_exact gamma beta).mp hi
  have hr := SkNextSearch.Support.search_spec gamma beta d hd
  have hc : SourceLocalization.RootAdapter.inputCheck gamma d = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact gamma d).mpr
      ⟨hr.1, by rw [hr.2.2.2]; exact hs.2.2.2.2.1,
        by rw [hr.2.2.2]; exact hs.2.2.2.1⟩
  have hn := SourceLocalization.RootAdapter.rootCode_spec gamma d hc
  exact ⟨(SourceLocalization.inputCheck_exact gamma _).mpr hn.1, hn.2.trans hr.2.2.2⟩

theorem localization_checked (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∀ c ∈ localization gamma d, Canonical.check c = true := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact (PublicMts.node_public_spec gamma e
    (SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 e he)).1

theorem localization_values (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    (localization gamma d).map unionInterpretation =
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (interpretation gamma) := by
  rw [PublicMts.localization, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (PublicMts.node_public_spec gamma c
    (SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 c hc)).2

theorem localization_head (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∃ tail : List Nat, localization gamma d = gamma :: tail := by
  obtain ⟨tail, he⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
  have hc := PublicMts.node_public_spec gamma (SourceLocalization.baseRaw gamma)
    (SourceLocalization.baseRaw_node gamma (gamma_baseCheck gamma beta hi))
  have hg := ((MuPublicDictionary.Support.inputCheck_image gamma).mp ((inputCheck_exact gamma beta).mp hi).1).1
  have hroot : UniformPublicReturn.publicCode gamma (SourceLocalization.baseRaw gamma) = gamma :=
    Canonical.check_value_injective _ _ hc.1 hg
      (hc.2.trans (SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi)))
  exact ⟨tail.map (UniformPublicReturn.publicCode gamma), by
    simp only [PublicMts.localization, he, List.map_cons, hroot]⟩

theorem localization_bounded (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∀ c ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d),
      interpretation gamma c ≤ unionInterpretation beta := by
  have hs := nativeRoot_spec gamma beta d hi hd
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp hs.1
  have hp := SourceLocalization.nativePath_source gamma _ hs.1
  obtain ⟨tail, he⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
  rw [he] at hp ⊢
  exact hp.bounded _ ((SourceLocalization.baseRaw_le gamma _ hn).trans_eq hs.2)
    (fun c hc => (SourceLocalization.support_bound gamma _ c hn hc).trans_eq hs.2)

/-- Every proper intermediate node in the WHOLE alpha-infinity interval
derives an independently executing actual original-source public mu query. -/
theorem localization_mu_callers (gamma beta d c : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hc : c ∈ FinePredecessor.stripLast
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma c) = true ∧
      Canonical.check (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma c)) = true := by
  have hs := nativeRoot_spec gamma beta d hi hd
  have hh := (SourceLocalization.Properties.nativePath_proper_prefix_spec gamma _ hs.1 c hc).1
  have hcaller := high_public_caller gamma c ((inputCheck_exact gamma beta).mp hi).1 hh
  exact ⟨hcaller, (MuPublicDictionary.publicCode_spec _ hcaller).1⟩

def execute (gamma beta : Nat) : Part (List Nat) := cond (inputCheck gamma beta)
  ((SkNextSearch.Support.search gamma beta).map
    (fun d => Support.word gamma (localization gamma d).tail)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hm : Computable₂ (fun p : Nat × Nat => fun d : Nat => Support.word p.1 (localization p.1 d).tail) :=
    (Support.word_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_tail.comp (localization_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd))).to_comp.to₂
  exact (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.map SkNextSearch.Support.search_partrec hm) Partrec.none).to₂

theorem execute_spec (gamma beta : Nat) (out : List Nat) (ho : out ∈ execute gamma beta) :
    inputCheck gamma beta = true ∧ ∃ d, d ∈ SkNextSearch.Support.search gamma beta ∧
      out = Support.word gamma (localization gamma d).tail := by
  have hi : inputCheck gamma beta = true := by
    cases h : inputCheck gamma beta with
    | true => rfl
    | false => exact False.elim (by
        simpa only [execute, h, Bool.cond_false, Part.notMem_none] using ho)
  have hm : out ∈ (SkNextSearch.Support.search gamma beta).map
      (fun d => Support.word gamma (localization gamma d).tail) := by
    simpa only [execute, hi, Bool.cond_true] using ho
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp hm
  exact ⟨hi, d, hd, he.symm⟩

theorem execute_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    ∃ out, out ∈ execute gamma beta := by
  obtain ⟨d, hd⟩ := search_returns gamma beta hi
  exact ⟨_, by simpa only [execute, hi, Bool.cond_true] using
    Part.mem_map (fun d => Support.word gamma (localization gamma d).tail) hd⟩

theorem execute_domain (gamma beta : Nat) : (execute gamma beta).Dom ↔ inputCheck gamma beta = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact (execute_spec gamma beta out ho).1
  · intro hi
    exact Part.dom_iff_mem.mpr (execute_returns gamma beta hi)

theorem own_input (gamma beta : Nat) (hi : PublicMts.inputCheck gamma beta = true) :
    inputCheck gamma beta = true := by
  have hs := (PublicMts.inputCheck_exact gamma beta).mp hi
  exact (inputCheck_exact gamma beta).mpr ⟨hs.1, hs.2.1, hs.2.2.1,
    hs.2.2.2.1, hs.2.2.2.2.1,
    hs.2.2.2.2.2.trans (ContextSupport.ownCeiling_boundary gamma hs.1)⟩

/-- On every original OWN-domain caller, the full-domain procedure is
literally the already reviewed actual Part computation. -/
theorem execute_eq_own (gamma beta : Nat) (hi : PublicMts.inputCheck gamma beta = true) :
    execute gamma beta = PublicMts.execute gamma beta := by
  simp only [execute, PublicMts.execute, hi, own_input gamma beta hi, Bool.cond_true]

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Infinity
