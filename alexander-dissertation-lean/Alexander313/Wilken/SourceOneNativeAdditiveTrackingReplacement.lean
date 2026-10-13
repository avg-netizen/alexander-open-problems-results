import Alexander313.Wilken.SourceOneNativeAdditiveTrackingReplacementSupport

/-!
# Executing complete raised replacements in original source-one syntax

Every actual raised multiplicative entry lies below the original factor,
which lies below finiteBase1. The real public return and source-zero
lowering therefore produce checked Normal LOW original syntax for the
entire finite word. The chronological value word, last factor value and
length agree with the independently executing raised assignment.
Original mu fidelity and the RAW tracking splice are separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Replacement

open ReplacementSupport

abbrev EntryMatches (r c d : Nat) : Prop :=
  Theta.acceptedLowCode 0 d = true ∧ interpretation 0 d = NativeContext.interpretation r c

def returnWord (head : Nat) (word : List Nat) : List Nat :=
  word.map (SkSourcePathSupport.entryCode (raisedBaseCode head))

theorem returnWord_primrec : Primrec₂ returnWord := by
  have he : Primrec₂ (fun p : Nat × List Nat => fun c : Nat =>
      SkSourcePathSupport.entryCode (raisedBaseCode p.1) c) :=
    (SkSourcePathSupport.entryCode_primrec.comp
      (raisedBaseCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  exact (Primrec.list_map Primrec.snd he).to₂

theorem returnWord_relation (head : Nat) (word : List Nat)
    (hc : ∀ c ∈ word, NativeContext.lowCheckCode (raisedBaseCode head) c = true)
    (hb : ∀ c ∈ word, NativeContext.interpretation (raisedBaseCode head) c < finiteBase 1) :
    List.Forall₂ (EntryMatches (raisedBaseCode head)) word (returnWord head word) := by
  revert hc hb
  induction word with
  | nil => intro hc hb; exact .nil
  | cons c xs ih =>
    intro hc hb
    have hd := SkSourcePathSupport.entryCode_spec _ c
      (hc c List.mem_cons_self) (hb c List.mem_cons_self)
    have ht := ih (fun d hm => hc d (List.mem_cons_of_mem _ hm))
      (fun d hm => hb d (List.mem_cons_of_mem _ hm))
    simpa only [returnWord, List.map_cons] using List.Forall₂.cons hd ht

theorem returnWord_values (head : Nat) (word : List Nat)
    (hc : ∀ c ∈ word, NativeContext.lowCheckCode (raisedBaseCode head) c = true)
    (hb : ∀ c ∈ word, NativeContext.interpretation (raisedBaseCode head) c < finiteBase 1) :
    (returnWord head word).map (interpretation 0) =
      word.map (NativeContext.interpretation (raisedBaseCode head)) := by
  rw [returnWord, List.map_map]
  apply List.map_congr_left
  intro c hm
  exact (SkSourcePathSupport.entryCode_spec _ c (hc c hm) (hb c hm)).2

theorem returnWord_checked (head : Nat) (word : List Nat)
    (hc : ∀ c ∈ word, NativeContext.lowCheckCode (raisedBaseCode head) c = true)
    (hb : ∀ c ∈ word, NativeContext.interpretation (raisedBaseCode head) c < finiteBase 1) :
    ∀ d ∈ returnWord head word, Theta.acceptedLowCode 0 d = true := by
  intro d hd
  obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hd
  exact (SkSourcePathSupport.entryCode_spec _ c (hc c hm) (hb c hm)).1

def raisedReplacement (head factor : Nat) : Part (List Nat) :=
  (raisedWord head factor).map (returnWord head)

theorem raisedReplacement_partrec : Partrec₂ raisedReplacement := by
  have hr : Computable₂ (fun p : Nat × Nat => fun word : List Nat => returnWord p.1 word) :=
    (returnWord_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact Partrec.map raisedWord_partrec hr

theorem raisedReplacement_returns (head factor : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true) :
    ∃ out, out ∈ raisedReplacement head factor := by
  obtain ⟨word, hw⟩ := raisedWord_returns head factor hh hf
  exact ⟨_, Part.mem_map _ hw⟩

/-- The literal executed original return has the complete genuine raised
M value word and every derived original Normal LOW/last-factor bound. -/
theorem raisedReplacement_spec (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ raisedReplacement head factor) :
    ∃ word, word ∈ raisedWord head factor ∧ out = returnWord head word ∧
      NativeContext.SourceTrackingSequences.trackingCheck (raisedBaseCode head) word = true ∧
      out.map (interpretation 0) = word.map (NativeContext.interpretation (raisedBaseCode head)) ∧
      out.length = word.length ∧
      ∀ d ∈ out, Theta.acceptedLowCode 0 d = true ∧ interpretation 0 d ≤ interpretation 0 factor := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := raisedWord_spec head factor word hh hf hm hlt hw
  have hc (c : Nat) (he : c ∈ word) := (hs.2.2 c he).1
  have hb (c : Nat) (he : c ∈ word) := (hs.2.2 c he).2.2
  refine ⟨word, hw, rfl, hs.1, returnWord_values head word hc hb, ?_, ?_⟩
  · simp only [returnWord, List.length_map]
  · intro d hd
    obtain ⟨c, he, rfl⟩ := List.mem_map.mp hd
    have hr := SkSourcePathSupport.entryCode_spec _ c (hc c he) (hb c he)
    exact ⟨hr.1, hr.2.le.trans (hs.2.2 c he).2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Replacement
