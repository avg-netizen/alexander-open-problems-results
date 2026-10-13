import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactor
import Alexander313.Wilken.PublicEpsilonNativeSkNextSearchSupport
import Alexander313.Wilken.HereditaryNativeLowPublicCoverageSupport
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTracking

/-!
# Actual replacement callers for source Definition 3.20

The genuine finite-boundary comparison derives LOW admission after raising
the source to a written epsilon reference. The existing terminating native
search returns the same original factor value in that literal epsilon
context. Independent native logarithms, real addition and omega power
also construct multiplication of positive additive principals. These are
the two actual operations needed by the printed replacement branches.
No chosen endpoint, representation, product or tracking oracle is supplied.
This is a source-only uncompiled candidate, not the full recursive assignment.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ReplacementSupport

open PublicEpsilonUnboundedIota
open MultiplicativePrincipalArithmetic

/-- Genuine finite comparison implies the whole LOW-boundary comparison. -/
theorem globalBoundary_mono_base (tau alpha : Ordinal.{0}) (htau : 0 < tau)
    (hle : tau ≤ alpha) (hlt : alpha < omegaSequence tau 1) :
    globalBoundary tau 0 ≤ globalBoundary alpha 0 := by
  unfold globalBoundary
  apply Ordinal.iSup_le
  intro j
  exact (LowPublicCoverage.Support.finiteBoundary_mono_base tau alpha htau hle hlt
    (0 + 1 + j) (by omega)).trans
      (Ordinal.le_iSup (fun k : Nat => finiteBoundary alpha (0 + 1 + k) 0) j)

def raisedBaseCode (q head : Nat) : Nat := UniformPublicReturn.publicCode q head

theorem raisedBaseCode_primrec : Primrec₂ raisedBaseCode := UniformPublicReturn.publicCode_primrec

theorem raisedBaseCode_spec (q head : Nat) (hh : SourceTrackingRaw.Support.inputCheck q head = true) :
    baseCheck (raisedBaseCode q head) = true ∧
      base (raisedBaseCode q head) = interpretation q head ∧
      globalBoundary (base q) 0 ≤ globalBoundary (base (raisedBaseCode q head)) 0 := by
  have hs := (SourceTrackingRaw.Support.inputCheck_exact q head).mp hh
  have hp := UniformPublicReturn.publicCode_spec q head
    ((UniformPublicReturn.inputCheck_exact q head).mpr hs.1)
  have hbase : base (raisedBaseCode q head) = interpretation q head := hp.2
  have hcheck : baseCheck (raisedBaseCode q head) = true := by
    apply (baseCheck_exact _).mpr
    refine ⟨Canonical.check_original hp.1, ?_⟩
    rw [hbase]
    exact hs.2.2
  have hq := (HeightBoundary.input_spec q head hs.1).2.1
  refine ⟨hcheck, hbase, ?_⟩
  rw [hbase]
  exact globalBoundary_mono_base (base q) (interpretation q head) (base_pos q hq)
    hs.2.1.le (HeightBoundary.input_spec q head hs.1).2.2

def raisedSearch (q head factor : Nat) : Part Nat :=
  SkNextSearch.Support.search (raisedBaseCode q head) (UniformPublicReturn.publicCode q factor)

theorem raisedSearch_partrec : Partrec (fun p : (Nat × Nat) × Nat =>
    raisedSearch p.1.1 p.1.2 p.2) :=
  SkNextSearch.Support.search_partrec.comp
    (raisedBaseCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)).to_comp
    (UniformPublicReturn.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp

/-- Every original LOW factor has a real terminating return at the raised
epsilon reference; the boundary is derived from the original written head. -/
theorem raisedSearch_returns (q head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true) : ∃ out, out ∈ raisedSearch q head factor := by
  have hs := raisedBaseCode_spec q head hh
  have hp := UniformPublicReturn.publicCode_spec q factor
    ((UniformPublicReturn.inputCheck_exact q factor).mpr hf)
  exact SkNextSearch.Support.search_returns _ _ hs.1 hp.1 (by
    rw [hp.2]
    exact (checked_low_bound q factor hf).trans_le hs.2.2)

theorem raisedSearch_spec (q head factor out : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true) (ho : out ∈ raisedSearch q head factor) :
    lowCheckCode (raisedBaseCode q head) out = true ∧
      Comparison.acceptedCode (raisedBaseCode q head) out = true ∧
      interpretation (raisedBaseCode q head) out = interpretation q factor := by
  have hs := SkNextSearch.Support.search_spec _ _ out ho
  have hp := UniformPublicReturn.publicCode_spec q factor
    ((UniformPublicReturn.inputCheck_exact q factor).mpr hf)
  exact ⟨hs.1, hs.2.1, hs.2.2.2.trans hp.2⟩

/-- The actual multiplicative assignment caller is derived after the real
search, using the original factor class and its displayed strict comparison. -/
theorem raisedSearch_multiplicative (q head factor out : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (ho : out ∈ raisedSearch q head factor) :
    SourceMultiplicativePrincipal.inputCheck (raisedBaseCode q head) out = true := by
  have hs := raisedSearch_spec q head factor out hh hf ho
  apply (SourceMultiplicativePrincipal.inputCheck_exact _ _).mpr
  rw [hs.2.2, (raisedBaseCode_spec q head hh).2.1]
  exact ⟨hs.1, hlt.le, hm⟩

/-- Every written member of the actual multiplicative word comes from
the genuine proper localization prefix or its unchanged final raw code. -/
theorem rawWord_member (q current c : Nat)
    (hc : c ∈ SourceMultiplicativeTracking.rawWord q current) :
    c = current ∨ c ∈ SourceMultiplicativeTracking.properPrefix q
      (SourceLocalization.RootAdapter.rootCode q current) := by
  rw [SourceMultiplicativeTracking.rawWord] at hc
  cases hs : SourceMultiplicativeTracking.Support.select q current
      (SourceMultiplicativeTracking.Support.table q
        (SourceMultiplicativeTracking.properPrefix q (SourceLocalization.RootAdapter.rootCode q current))) with
  | none =>
    exact Or.inl (by simpa only [SourceMultiplicativeTracking.Support.extend, hs,
      List.mem_singleton] using hc)
  | some e =>
    have hm := SourceMultiplicativeTracking.Support.select_mem q current _ e hs
    have hx : c ∈ e.2 ++ [current] := by
      simpa only [SourceMultiplicativeTracking.Support.extend, hs] using hc
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (List.mem_reverse.mp
        (SourceMultiplicativeTracking.Support.buildRev_word_mem q _ e hm c hx))
    · exact Or.inl (List.mem_singleton.mp hx)

theorem rawWord_low_bound (q current : Nat)
    (hi : SourceLocalization.RootAdapter.inputCheck q current = true) :
    ∀ c ∈ SourceMultiplicativeTracking.rawWord q current,
      lowCheckCode q c = true ∧ interpretation q c ≤ interpretation q current := by
  have hs := SourceLocalization.RootAdapter.rootCode_spec q current hi
  have hr := SourceLocalization.RootAdapter.rootInput q current hi
  have hcur := (SourceLocalization.RootAdapter.inputCheck_exact q current).mp hi
  have hp : ∀ c ∈ SourceLocalization.nativePath q
      (SourceLocalization.RootAdapter.rootCode q current),
      SourceLocalization.value q c ≤ SourceLocalization.value q
        (SourceLocalization.RootAdapter.rootCode q current) := by
    obtain ⟨tail, he⟩ := SourceLocalization.nativePath_head q _
    have hpath := SourceLocalization.nativePath_source q _ hr
    rw [he] at hpath ⊢
    exact hpath.bounded _ (SourceLocalization.baseRaw_le q _ hs.1)
      (fun d hd => SourceLocalization.support_bound q _ d hs.1 hd)
  intro c hc
  rcases rawWord_member q current c hc with rfl | hc
  · exact ⟨hcur.1, le_rfl⟩
  · have hroot := SourceMultiplicativeTracking.properPrefix_roots q _ hr c hc
    have hmem : c ∈ (SourceLocalization.nativePath q
        (SourceLocalization.RootAdapter.rootCode q current)).tail :=
      Hereditary.FinePredecessor.stripLast_mem _ _ hc
    exact ⟨RootLowCollapse.root_low q c hroot,
      (hp c (List.mem_of_mem_tail hmem)).trans_eq hs.2⟩

def raisedWord (q head factor : Nat) : Part (List Nat) :=
  (raisedSearch q head factor).map fun c =>
    SourceMultiplicativeTracking.rawWord (raisedBaseCode q head) c

theorem raisedWord_partrec : Partrec (fun p : (Nat × Nat) × Nat =>
    raisedWord p.1.1 p.1.2 p.2) := by
  have hword : Computable₂ (fun p : (Nat × Nat) × Nat => fun c : Nat =>
      SourceMultiplicativeTracking.rawWord (raisedBaseCode p.1.1 p.1.2) c) :=
    (SourceMultiplicativeTracking.rawWord_primrec.comp
      (raisedBaseCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to_comp.to₂
  exact Partrec.map raisedSearch_partrec hword

theorem raisedWord_returns (q head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true) :
    ∃ word, word ∈ raisedWord q head factor := by
  obtain ⟨c, hc⟩ := raisedSearch_returns q head factor hh hf
  exact ⟨_, Part.mem_map _ hc⟩

/-- The computed replacement is the actual independently localized M
procedure at the written epsilon context. Every member stays below the
original factor value, supplying its later original-q return caller. -/
theorem raisedWord_spec (q head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hw : word ∈ raisedWord q head factor) :
    SourceTrackingSequences.trackingCheck (raisedBaseCode q head) word = true ∧
      interpretation (raisedBaseCode q head) (SourceTrackingSequences.lastCode word) =
        interpretation q factor ∧
      ∀ c ∈ word, lowCheckCode (raisedBaseCode q head) c = true ∧
        interpretation (raisedBaseCode q head) c ≤ interpretation q factor := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := raisedSearch_multiplicative q head factor c hh hf hm hlt hc
  have hs := raisedSearch_spec q head factor c hh hf hc
  refine ⟨SourceMultiplicativeTracking.rawWord_checked _ c
    (SourceMultiplicativePrincipal.rootAdapter_input _ c hi), ?_, ?_⟩
  · rw [SourceMultiplicativeTracking.rawWord_last]
    exact hs.2.2
  · intro d hd
    have hb := rawWord_low_bound _ c (SourceMultiplicativePrincipal.rootAdapter_input _ c hi) d hd
    exact ⟨hb.1, hb.2.trans_eq hs.2.2⟩

def product (q left right : Nat) : Part Nat :=
  (LogEnd.execute q left).bind fun a => (LogEnd.execute q right).map fun b =>
    OmegaPowers.powerCode q (Arithmetic.addCode q a b)

theorem product_partrec : Partrec (fun p : (Nat × Nat) × Nat =>
    product p.1.1 p.1.2 p.2) := by
  have hq : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have he := LogEnd.execute_partrec.comp hq.to_comp hr.to_comp
  have hmap : Computable₂ (fun p : ((Nat × Nat) × Nat) × Nat => fun b : Nat =>
      OmegaPowers.powerCode p.1.1.1 (Arithmetic.addCode p.1.1.1 p.2 b)) := by
    have hq' := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have ha := Arithmetic.addCode_primrec.comp
      (hq'.pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    exact (OmegaPowers.powerCode_primrec.comp hq' ha).to_comp.to₂
  exact Partrec.bind
    (LogEnd.execute_partrec.comp (Primrec.fst.comp Primrec.fst).to_comp
      (Primrec.snd.comp Primrec.fst).to_comp)
    (Partrec.map he hmap).to₂

theorem product_returns (q left right : Nat)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true) :
    ∃ out, out ∈ product q left right := by
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp ((LogEnd.execute_domain q left).mpr hl)
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp ((LogEnd.execute_domain q right).mpr hr)
  exact ⟨_, Part.mem_bind_iff.mpr ⟨a, ha, Part.mem_map _ hb⟩⟩

theorem product_domain (q left right : Nat) : (product q left right).Dom ↔
    lowCheckCode q left = true ∧ lowCheckCode q right = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨a, ha, hb⟩ := Part.mem_bind_iff.mp ho
    obtain ⟨b, hb, _⟩ := (Part.mem_map_iff _).mp hb
    exact ⟨(LogEnd.execute_domain q left).mp (Part.dom_iff_mem.mpr ⟨a, ha⟩),
      (LogEnd.execute_domain q right).mp (Part.dom_iff_mem.mpr ⟨b, hb⟩)⟩
  · rintro ⟨hl, hr⟩
    exact Part.dom_iff_mem.mpr (product_returns q left right hl hr)

private theorem log_principal_value (q c out : Nat) (ho : out ∈ LogEnd.execute q c)
    (hp : 0 < interpretation q c) (hc : Ordinal.IsPrincipal (· + ·) (interpretation q c)) :
    Ordinal.omega0 ^ interpretation q out = interpretation q c := by
  have hs := LogEnd.execute_spec q c out ho
  have he : Ordinal.omega0 ^ interpretation q out = Hereditary.LogEnd.endValue (interpretation q c) := by
    simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hp),
      Hereditary.LogEnd.endValue] using hs.2.2.2
  exact he.trans (SourceChi.Powers.endValue_principal _ hp hc)

/-- The actual independent logarithms and actual source addition construct
ordinary multiplication of the two original positive additive principals. -/
theorem product_spec (q left right out : Nat) (ho : out ∈ product q left right)
    (hlp : 0 < interpretation q left)
    (hl : Ordinal.IsPrincipal (· + ·) (interpretation q left))
    (hrp : 0 < interpretation q right)
    (hr : Ordinal.IsPrincipal (· + ·) (interpretation q right)) :
    lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      interpretation q out = interpretation q left * interpretation q right := by
  obtain ⟨a, ha, hb⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hb
  have hla := LogEnd.execute_spec q left a ha
  have hrb := LogEnd.execute_spec q right b hb
  have hs := Arithmetic.addCode_spec q a b
    ((Comparison.acceptedCode_exact q _).mp hla.2.2.1).1
    ((Comparison.acceptedCode_exact q _).mp hrb.2.2.1).1
  have hlow := (OmegaPowerHeight.addCode_low_height q a b hla.2.1 hrb.2.1).1
  have hp := OmegaPowers.powerCode_spec q _ hlow
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [hp.2.2, hs.2.1, Ordinal.opow_add,
    log_principal_value q left a ha hlp hl, log_principal_value q right b hb hrp hr]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ReplacementSupport
