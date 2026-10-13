import Alexander313.Wilken.HereditaryPublicMtsSupport
import Alexander313.Wilken.HereditaryPublicMtsContextSupport
import Alexander313.Wilken.PublicEpsilonNativeSkNextSearchSupport
import Alexander313.Wilken.PublicEpsilonNativeLocalizationProperties
import Alexander313.Wilken.PublicEpsilonNativeLocalizationRootAdapter

/-!
# Executing least-cover words on genuine public epsilon localization

An original selected proper epsilon and a canonical positive principal
below its computed OWN successor ceiling supply a genuine LOW search at
the literal epsilon. Its real normalized principal parser and finite
localization compute the chronological input to the least-cover table.
Every proper intermediate node derives its HIGH caller and original mu
column from the true OWN interval. No localization, representation, mu
column, finite output or recursive predecessor is supplied to execution.
This implements the finite recursion; covering and gamma-hat equivalence
remain separate mathematical statements. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open ContextSupport

def inputCheck (gamma beta : Nat) : Bool :=
  (MuPublicDictionary.Support.inputCheck gamma && PublicTrackingSequences.principalCheck beta) &&
    (!(Canonical.less beta gamma) && Canonical.less beta (ceilingCode gamma))

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp Primrec.fst)
      (PublicTrackingSequences.principalCheck_primrec.comp Primrec.snd))
    (Primrec.and.comp (Primrec.not.comp (Canonical.Effective.less_primrec.comp Primrec.snd Primrec.fst))
      (Canonical.Effective.less_primrec.comp Primrec.snd (ceilingCode_primrec.comp Primrec.fst)))).to₂

theorem inputCheck_exact (gamma beta : Nat) : inputCheck gamma beta = true ↔
    MuPublicDictionary.Support.inputCheck gamma = true ∧ Canonical.check beta = true ∧
      0 < unionInterpretation beta ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) ∧
      unionInterpretation gamma ≤ unionInterpretation beta ∧ unionInterpretation beta < ownCeiling gamma := by
  constructor
  · intro hi
    have h := Bool.and_eq_true.mp hi
    obtain ⟨hg, hp⟩ := Bool.and_eq_true.mp h.1
    obtain ⟨hfloor, hupper⟩ := Bool.and_eq_true.mp h.2
    have hb := (PublicTrackingSequences.principalCheck_exact beta).mp hp
    have hc := ceilingCode_spec gamma hg
    have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
    have hf := (SourceTrackingSequences.Support.canonical_not_less_exact beta gamma hb.1 hgcanon).mp
      (Bool.not_eq_true'.mp hfloor)
    have hu := ((Canonical.less_exact beta (ceilingCode gamma)).mp hupper).2.2
    exact ⟨hg, hb.1, hb.2.1, hb.2.2, hf, hu.trans_eq hc.2⟩
  · rintro ⟨hg, hb, hp, ha, hf, hu⟩
    have hc := ceilingCode_spec gamma hg
    have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr
      ⟨hg, (PublicTrackingSequences.principalCheck_exact beta).mpr ⟨hb, hp, ha⟩⟩,
      Bool.and_eq_true.mpr ⟨Bool.not_eq_true'.mpr
        ((SourceTrackingSequences.Support.canonical_not_less_exact beta gamma hb hgcanon).mpr hf),
        (Canonical.less_exact beta (ceilingCode gamma)).mpr ⟨hb, hc.1, hu.trans_eq hc.2.symm⟩⟩⟩

theorem gamma_baseCheck (gamma beta : Nat) (hi : inputCheck gamma beta = true) : baseCheck gamma = true := by
  have hg := (MuPublicDictionary.Support.inputCheck_image gamma).mp ((inputCheck_exact gamma beta).mp hi).1
  exact (baseCheck_exact gamma).mpr ⟨Canonical.check_original hg.1, hg.2.1⟩

theorem search_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    ∃ d, d ∈ SkNextSearch.Support.search gamma beta := by
  have hs := (inputCheck_exact gamma beta).mp hi
  exact SkNextSearch.Support.search_returns gamma beta (gamma_baseCheck gamma beta hi) hs.2.1
    (hs.2.2.2.2.2.trans (ownCeiling_boundary gamma hs.1))

def nativeRoot (gamma d : Nat) : Nat := SourceLocalization.RootAdapter.rootCode gamma d

theorem nativeRoot_primrec : Primrec₂ nativeRoot := SourceLocalization.RootAdapter.rootCode_primrec

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

def localization (gamma d : Nat) : List Nat :=
  (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (UniformPublicReturn.publicCode gamma)

theorem localization_primrec : Primrec₂ localization := by
  have hp := SourceLocalization.nativePath_primrec.comp Primrec.fst
    (nativeRoot_primrec.comp Primrec.fst Primrec.snd)
  have hm : Primrec₂ (fun p : Nat × Nat => fun c : Nat => UniformPublicReturn.publicCode p.1 c) :=
    (UniformPublicReturn.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hp hm).to₂

theorem node_public_spec (gamma c : Nat) (hc : SourceLocalization.Node gamma c) :
    Canonical.check (UniformPublicReturn.publicCode gamma c) = true ∧
      unionInterpretation (UniformPublicReturn.publicCode gamma c) = interpretation gamma c :=
  UniformPublicReturn.publicCode_spec gamma c ((UniformPublicReturn.inputCheck_exact gamma c).mpr
    (SourceLocalization.node_low gamma c hc))

theorem localization_checked (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∀ c ∈ localization gamma d, Canonical.check c = true := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact (node_public_spec gamma e
    (SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 e he)).1

theorem localization_values (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    (localization gamma d).map unionInterpretation =
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (interpretation gamma) := by
  rw [localization, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (node_public_spec gamma c
    (SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 c hc)).2

theorem localization_head (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∃ tail : List Nat, localization gamma d = gamma :: tail := by
  obtain ⟨tail, he⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
  have hc := node_public_spec gamma (SourceLocalization.baseRaw gamma)
    (SourceLocalization.baseRaw_node gamma (gamma_baseCheck gamma beta hi))
  have hg := ((MuPublicDictionary.Support.inputCheck_image gamma).mp ((inputCheck_exact gamma beta).mp hi).1).1
  have hroot : UniformPublicReturn.publicCode gamma (SourceLocalization.baseRaw gamma) = gamma :=
    Canonical.check_value_injective _ _ hc.1 hg
      (hc.2.trans (SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi)))
  exact ⟨tail.map (UniformPublicReturn.publicCode gamma), by simp only [localization, he, List.map_cons, hroot]⟩

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

/-- Every actual proper localization entry derives its independently
queryable proper public mu and the original contextual value equation. -/
theorem localization_mu_columns (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) (c : Nat)
    (hc : c ∈ FinePredecessor.stripLast
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma c) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma c)) =
        Mu.sourceValue gamma c := by
  have hs := nativeRoot_spec gamma beta d hi hd
  have hh := (SourceLocalization.Properties.nativePath_proper_prefix_spec gamma _ hs.1 c hc).1
  have hm : c ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d) :=
    List.mem_of_mem_tail (FinePredecessor.stripLast_mem _ _ hc)
  have hv := localization_bounded gamma beta d hi hd c hm
  exact high_public_mu gamma c ((inputCheck_exact gamma beta).mp hi).1 hh
    (hv.trans_lt ((inputCheck_exact gamma beta).mp hi).2.2.2.2.2)

def execute (gamma beta : Nat) : Part (List Nat) := cond (inputCheck gamma beta)
  ((SkNextSearch.Support.search gamma beta).map (fun d => Support.word gamma (localization gamma d).tail)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hm : Computable₂ (fun p : Nat × Nat => fun d : Nat => Support.word p.1 (localization p.1 d).tail) :=
    (Support.word_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_tail.comp (localization_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))).to_comp.to₂
  exact (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.map SkNextSearch.Support.search_partrec hm) Partrec.none).to₂

theorem execute_spec (gamma beta : Nat) (out : List Nat) (ho : out ∈ execute gamma beta) :
    inputCheck gamma beta = true ∧ ∃ d, d ∈ SkNextSearch.Support.search gamma beta ∧
      out = Support.word gamma (localization gamma d).tail := by
  have hi : inputCheck gamma beta = true := by
    cases h : inputCheck gamma beta with
    | true => rfl
    | false => exact False.elim (by simpa only [execute, h, Bool.cond_false, Part.notMem_none] using ho)
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

theorem execute_domain (gamma beta : Nat) : (execute gamma beta).Dom ↔ inputCheck gamma beta = true :=
  by
    constructor
    · intro hd
      obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
      exact (execute_spec gamma beta out ho).1
    · intro hi
      exact Part.dom_iff_mem.mpr (execute_returns gamma beta hi)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts
