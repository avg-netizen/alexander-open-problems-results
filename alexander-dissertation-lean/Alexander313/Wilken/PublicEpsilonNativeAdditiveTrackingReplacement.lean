import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingReplacementSupport
import Alexander313.Wilken.PublicEpsilonNativeSkSourceWordSupport

/-!
# Returning the printed raised-context replacement to its original source

The actual raised-context multiplicative word is computed first. Each of
its entries is bounded by the original final factor. The generic finite
returning loop therefore searches genuine Normal LOW spellings at the
original q, retaining exactly that whole value word. The other printed
replacement is the independently computed original-q principal product.
No representation, endpoint, tracking or product oracle is supplied.
The greatest insertion selector and full additive assignment are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Replacement

open PublicEpsilonUnboundedIota
open MultiplicativePrincipalArithmetic
open ReplacementSupport

abbrev Query := (Nat × Nat) × Nat

def contextWord (r : Nat) (word : List Nat) : SkSourceWord.Support.Word :=
  word.map fun c => (r, c)

theorem contextWord_primrec : Primrec₂ contextWord :=
  (Primrec.list_map Primrec.snd
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂).to₂

def returnWord (q r : Nat) (word : List Nat) : Part (List Nat) :=
  SkSourceWord.Support.loop (q, (contextWord r word, []))

theorem returnWord_partrec : Partrec (fun p : Nat × (Nat × List Nat) =>
    returnWord p.1 p.2.1 p.2.2) :=
  SkSourceWord.Support.loop_partrec.comp
    (Primrec.fst.pair ((contextWord_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).pair (Primrec.const []))).to_comp

/-- Each genuine source boundary supplies an actual finite returning-search
caller; the finite list loop then terminates without a numerical bound. -/
theorem returnWord_returns (q r : Nat) (word : List Nat) (hq : baseCheck q = true)
    (hw : ∀ c ∈ word, lowCheckCode r c = true ∧
      interpretation r c < globalBoundary (base q) 0) :
    ∃ out, out ∈ returnWord q r word := by
  apply SkSourceWord.Support.loop_returns q (contextWord r word) []
  intro entry he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  have hp := UniformPublicReturn.publicCode_spec r c
    ((UniformPublicReturn.inputCheck_exact r c).mpr (hw c hc).1)
  exact SkNextSearch.Support.search_returns q _ hq hp.1
    (by rw [hp.2]; exact (hw c hc).2)

theorem returnWord_relation (q r : Nat) (word out : List Nat)
    (ho : out ∈ returnWord q r word)
    (hw : ∀ c ∈ word, lowCheckCode r c = true) :
    List.Forall₂ (SkSourceWord.Support.EntryMatches q) (contextWord r word) out := by
  obtain ⟨tail, he, hr⟩ := SkSourceWord.Support.loop_relation
    (q, (contextWord r word, [])) out ho (by
      intro entry hm
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
      exact hw c hc)
  have hout : out = tail := by simpa only [List.nil_append] using he
  simpa only [hout] using hr

/-- The search returns actual original-q Normal LOW syntax and exactly the
original order of values; no equality of written spellings is asserted. -/
theorem returnWord_spec (q r : Nat) (word out : List Nat)
    (ho : out ∈ returnWord q r word)
    (hw : ∀ c ∈ word, lowCheckCode r c = true) :
    (∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) ∧
      out.map (interpretation q) = word.map (interpretation r) ∧
      out.length = word.length := by
  have hr := returnWord_relation q r word out ho hw
  refine ⟨SkSourceWord.Support.relation_checked q hr, ?_, ?_⟩
  · simpa only [contextWord, List.map_map, Function.comp_def] using
      SkSourceWord.Support.relation_values q hr
  · simpa only [contextWord, List.length_map] using hr.length_eq.symm

theorem returnWord_bound (q r : Nat) (word out : List Nat) (bound : Ordinal.{0})
    (ho : out ∈ returnWord q r word)
    (hw : ∀ c ∈ word, lowCheckCode r c = true ∧ interpretation r c ≤ bound) :
    ∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
      interpretation q d ≤ bound := by
  have hs := returnWord_spec q r word out ho (fun c hc => (hw c hc).1)
  intro d hd
  have hv : interpretation q d ∈ word.map (interpretation r) := by
    rw [← hs.2.1]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hv
  exact ⟨(hs.1 d hd).1, (hs.1 d hd).2, he ▸ (hw c hc).2⟩

def raisedReplacement (q head factor : Nat) : Part (List Nat) :=
  (raisedWord q head factor).bind fun word => returnWord q (raisedBaseCode q head) word

theorem raisedReplacement_partrec : Partrec (fun p : Query =>
    raisedReplacement p.1.1 p.1.2 p.2) := by
  have hr : Partrec₂ (fun p : Query => fun word : List Nat =>
      returnWord p.1.1 (raisedBaseCode p.1.1 p.1.2) word) := by
    have hq := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hh := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact (returnWord_partrec.comp
      (hq.pair ((raisedBaseCode_primrec.comp hq hh).pair Primrec.snd)).to_comp).to₂
  exact Partrec.bind raisedWord_partrec hr

/-- The original last-factor LOW bound derives every original-q returning
caller for the independently computed raised-context multiplicative word. -/
theorem raisedReplacement_returns (q head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor) :
    ∃ out, out ∈ raisedReplacement q head factor := by
  obtain ⟨word, hw⟩ := raisedWord_returns q head factor hh hf
  have hs := raisedWord_spec q head factor word hh hf hm hlt hw
  have hq := (HeightBoundary.input_spec q factor hf).2.1
  obtain ⟨out, ho⟩ := returnWord_returns q (raisedBaseCode q head) word hq (by
    intro c hc
    have hb := hs.2.2 c hc
    exact ⟨hb.1, hb.2.trans_lt (checked_low_bound q factor hf)⟩)
  exact ⟨out, Part.mem_bind hw ho⟩

/-- The result is the printed ts at the genuine raised epsilon in VALUES,
represented entirely by finite Normal LOW codes at the original q. -/
theorem raisedReplacement_spec (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (ho : out ∈ raisedReplacement q head factor) :
    ∃ word, word ∈ raisedWord q head factor ∧
      SourceTrackingSequences.trackingCheck (raisedBaseCode q head) word = true ∧
      out.map (interpretation q) = word.map (interpretation (raisedBaseCode q head)) ∧
      out.length = word.length ∧
      ∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
        interpretation q d ≤ interpretation q factor := by
  obtain ⟨word, hw, hout⟩ := Part.mem_bind_iff.mp ho
  have hs := raisedWord_spec q head factor word hh hf hm hlt hw
  have hr := returnWord_spec q _ word out hout (fun c hc => (hs.2.2 c hc).1)
  exact ⟨word, hw, hs.1, hr.2.1, hr.2.2,
    returnWord_bound q _ word out _ hout hs.2.2⟩

def smallReplacement (q head factor : Nat) : Part (List Nat) :=
  (product q head factor).map fun out => [out]

theorem smallReplacement_partrec : Partrec (fun p : Query =>
    smallReplacement p.1.1 p.1.2 p.2) :=
  Partrec.map product_partrec
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to_comp.to₂

theorem smallReplacement_returns (q head factor : Nat)
    (hh : lowCheckCode q head = true) (hf : lowCheckCode q factor = true) :
    ∃ out, out ∈ smallReplacement q head factor := by
  obtain ⟨out, ho⟩ := product_returns q head factor hh hf
  exact ⟨[out], Part.mem_map _ ho⟩

/-- The other printed replacement is literally the singleton produced by
the real principal product, retaining the original source context. -/
theorem smallReplacement_spec (q head factor : Nat) (out : List Nat)
    (ho : out ∈ smallReplacement q head factor)
    (hp : 0 < interpretation q head)
    (ha : Ordinal.IsPrincipal (· + ·) (interpretation q head))
    (hf : IsMultiplicativePrincipal (interpretation q factor)) :
    ∃ d, out = [d] ∧ lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
      interpretation q d = interpretation q head * interpretation q factor := by
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := product_spec q head factor d hd hp ha hf.1 hf.2.1
  exact ⟨d, rfl, hs⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Replacement
