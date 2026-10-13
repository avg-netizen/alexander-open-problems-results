import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingReplacementSupport
import Alexander313.Wilken.SourceOneNativeTrackingRaw
import Alexander313.Wilken.SourceOneNativeSkSourceWordSupport

/-!
# Actual raised multiplicative replacements of original source-one heads

Literal check-zero public tagging supplies the raised epsilon base and
factor. Genuine boundary monotonicity at source base one derives the
terminating native LOW search caller. The independently localized native
multiplicative word has every value at most the original factor, hence
strictly below finiteBase1. These bounds license actual original source-zero
lowering of its entire chronological word. No Native base-one parser,
chosen replacement or endpoint/mu oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ReplacementSupport

open MultiplicativePrincipalArithmetic

def raisedBaseCode (head : Nat) : Nat := SourceTrackingRaw.Support.publicCode head

theorem raisedBaseCode_primrec : Primrec raisedBaseCode :=
  SourceTrackingRaw.Support.publicCode_primrec

theorem raisedBaseCode_spec (head : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true) :
    NativeContext.baseCheck (raisedBaseCode head) = true ∧
      NativeContext.base (raisedBaseCode head) = interpretation 0 head ∧
      finiteBase 1 ≤ globalBoundary (NativeContext.base (raisedBaseCode head)) 0 := by
  have hs := (SourceTrackingRaw.Support.inputCheck_exact head).mp hh
  have hp := SourceTrackingRaw.Support.publicCode_spec head hs.1
  have hb : NativeContext.base (raisedBaseCode head) = interpretation 0 head := hp.2
  refine ⟨(NativeContext.baseCheck_exact _).mpr ⟨Canonical.check_original hp.1, ?_⟩,
    hb, ?_⟩
  · rw [hb]; exact hs.2.2
  · rw [hb, finiteBase_succ]
    apply NativeContext.SourceAdditiveTracking.ReplacementSupport.globalBoundary_mono_base
      (finiteBase 0) (interpretation 0 head) (finiteBase_pos 0)
    · simpa only [finiteBase_zero] using hs.2.1.le
    · exact (SourceTrackingRaw.Support.original_bound head hs.1).trans
        (finiteBase_lt_cardinal 0)

def raisedSearch (head factor : Nat) : Part Nat :=
  NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search
    (raisedBaseCode head) (SourceTrackingRaw.Support.publicCode factor)

theorem raisedSearch_partrec : Partrec₂ raisedSearch :=
  NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search_partrec.comp
    (raisedBaseCode_primrec.comp Primrec.fst).to_comp
    (SourceTrackingRaw.Support.publicCode_primrec.comp Primrec.snd).to_comp

theorem raisedSearch_returns (head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true) : ∃ out, out ∈ raisedSearch head factor := by
  have hs := raisedBaseCode_spec head hh
  have hp := SourceTrackingRaw.Support.publicCode_spec factor hf
  exact NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search_returns
    _ _ hs.1 hp.1 (by
      rw [hp.2]
      exact (SourceTrackingRaw.Support.original_bound factor hf).trans_le hs.2.2)

theorem raisedSearch_spec (head factor out : Nat)
    (hf : lowCheckCode 0 factor = true) (ho : out ∈ raisedSearch head factor) :
    NativeContext.lowCheckCode (raisedBaseCode head) out = true ∧
      NativeContext.Comparison.acceptedCode (raisedBaseCode head) out = true ∧
      NativeContext.interpretation (raisedBaseCode head) out = interpretation 0 factor := by
  have hs := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search_spec _ _ out ho
  have hp := SourceTrackingRaw.Support.publicCode_spec factor hf
  exact ⟨hs.1, hs.2.1, hs.2.2.2.trans hp.2⟩

theorem raisedSearch_multiplicative (head factor out : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ raisedSearch head factor) :
    NativeContext.SourceMultiplicativePrincipal.inputCheck (raisedBaseCode head) out = true := by
  have hs := raisedSearch_spec head factor out hf ho
  apply (NativeContext.SourceMultiplicativePrincipal.inputCheck_exact _ _).mpr
  rw [hs.2.2, (raisedBaseCode_spec head hh).2.1]
  exact ⟨hs.1, hlt.le, hm⟩

def raisedWord (head factor : Nat) : Part (List Nat) :=
  (raisedSearch head factor).map fun c =>
    NativeContext.SourceMultiplicativeTracking.rawWord (raisedBaseCode head) c

theorem raisedWord_partrec : Partrec₂ raisedWord := by
  have hw : Computable₂ (fun p : Nat × Nat => fun c : Nat =>
      NativeContext.SourceMultiplicativeTracking.rawWord (raisedBaseCode p.1) c) :=
    (NativeContext.SourceMultiplicativeTracking.rawWord_primrec.comp
      (raisedBaseCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp.to₂
  exact Partrec.map raisedSearch_partrec hw

theorem raisedWord_returns (head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true) : ∃ word, word ∈ raisedWord head factor := by
  obtain ⟨c, hc⟩ := raisedSearch_returns head factor hh hf
  exact ⟨_, Part.mem_map _ hc⟩

theorem raisedWord_spec (head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (hw : word ∈ raisedWord head factor) :
    NativeContext.SourceTrackingSequences.trackingCheck (raisedBaseCode head) word = true ∧
      NativeContext.interpretation (raisedBaseCode head)
        (NativeContext.SourceTrackingSequences.lastCode word) = interpretation 0 factor ∧
      ∀ c ∈ word, NativeContext.lowCheckCode (raisedBaseCode head) c = true ∧
        NativeContext.interpretation (raisedBaseCode head) c ≤ interpretation 0 factor ∧
        NativeContext.interpretation (raisedBaseCode head) c < finiteBase 1 := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := raisedSearch_multiplicative head factor c hh hf hm hlt hc
  have hs := raisedSearch_spec head factor c hf hc
  have hr := NativeContext.SourceMultiplicativePrincipal.rootAdapter_input _ c hi
  refine ⟨NativeContext.SourceMultiplicativeTracking.rawWord_checked _ c hr, ?_, ?_⟩
  · rw [NativeContext.SourceMultiplicativeTracking.rawWord_last]
    exact hs.2.2
  · intro d hd
    have hb := NativeContext.SourceAdditiveTracking.ReplacementSupport.rawWord_low_bound _ c hr d hd
    have hv := hb.2.trans_eq hs.2.2
    exact ⟨hb.1, hv, hv.trans_lt (SourceTrackingRaw.Support.original_bound factor hf)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ReplacementSupport
