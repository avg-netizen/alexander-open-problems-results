import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingSource

/-!
# Actual complete assignment words returned to canonical public syntax

Every emitted original word entry is genuinely LOW, as a consequence of
the independently computed RAW tracking condition. Real original public
returns canonicalize every entry while preserving the entire chronological
value word. The exact original full assignment execution is retained.
This neither assumes nor defines an evaluation function. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Return

open Source
open NativeContext.SourceTrackingSequences (lastCode)
open Hereditary.FinePredecessor (stripLast stripLast_split)

theorem source_one_word_low (word : List Nat)
    (hw : SourceOneIota.SourceTrackingRaw.trackingCheck word = true) :
    ∀ c ∈ word, lowCheckCode 0 c = true := by
  have ht := (SourceOneIota.SourceTrackingRaw.trackingCheck_exact word).mp hw
  obtain ⟨last, he, hh⟩ := stripLast_split word ht.1
  have hlast : lastCode word = last := by simp only [lastCode, hh, Option.getD_some]
  intro c hc
  rw [he] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact c).mp (ht.2.1.nodes c hc)).1
  · simpa only [hlast, List.mem_singleton.mp hc] using ht.2.2.1

theorem native_word_low (q : Nat) (word : List Nat)
    (hw : NativeContext.SourceTrackingRaw.trackingCheck q word = true) :
    ∀ c ∈ word, NativeContext.lowCheckCode q c = true := by
  have ht := (NativeContext.SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  obtain ⟨last, he, hh⟩ := stripLast_split word ht.1
  have hlast : lastCode word = last := by simp only [lastCode, hh, Option.getD_some]
  intro c hc
  rw [he] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact q c).mp (ht.2.1.nodes c hc)).1
  · simpa only [hlast, List.mem_singleton.mp hc] using ht.2.2.1

def sourceOneWord (word : List Nat) : List Nat :=
  word.map SourceOneIota.SourceTrackingRaw.Support.publicCode

theorem sourceOneWord_primrec : Primrec sourceOneWord := Primrec.list_map Primrec.id
  (SourceOneIota.SourceTrackingRaw.Support.publicCode_primrec.comp Primrec.snd).to₂

theorem sourceOneWord_spec (word : List Nat)
    (hw : SourceOneIota.SourceTrackingRaw.trackingCheck word = true) :
    (∀ c ∈ sourceOneWord word, Canonical.check c = true) ∧
      (sourceOneWord word).map unionInterpretation = word.map (interpretation 0) := by
  have hl := source_one_word_low word hw
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d (hl d hd)).1
  · rw [sourceOneWord, List.map_map]
    exact List.map_congr_left (fun d hd =>
      (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d (hl d hd)).2)

def nativeWord (alpha : Nat) (word : List Nat) : List Nat :=
  word.map (NativeContext.UniformPublicReturn.publicCode (contextCode alpha))

theorem nativeWord_primrec : Primrec₂ nativeWord :=
  (Primrec.list_map Primrec.snd
    (NativeContext.UniformPublicReturn.publicCode_primrec.comp
      (contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂

theorem nativeWord_spec (alpha : Nat) (word : List Nat)
    (hw : NativeContext.SourceTrackingRaw.trackingCheck (contextCode alpha) word = true) :
    (∀ c ∈ nativeWord alpha word, Canonical.check c = true) ∧
      (nativeWord alpha word).map unionInterpretation = word.map (NativeContext.interpretation (contextCode alpha)) := by
  have hl := native_word_low (contextCode alpha) word hw
  have hs : ∀ d ∈ word, Canonical.check (NativeContext.UniformPublicReturn.publicCode (contextCode alpha) d) = true ∧
      unionInterpretation (NativeContext.UniformPublicReturn.publicCode (contextCode alpha) d) =
        NativeContext.interpretation (contextCode alpha) d := fun d hd =>
    NativeContext.UniformPublicReturn.publicCode_spec _ d
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr (hl d hd))
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (hs d hd).1
  · rw [nativeWord, List.map_map]
    exact List.map_congr_left (fun d hd => (hs d hd).2)

def sourceOneExecute (alpha : Nat) : Part (List Nat) :=
  (SourceOneIota.SourceAdditiveTracking.Assignment.execute (sourceOneCode alpha)).map sourceOneWord

theorem sourceOneExecute_partrec : Partrec sourceOneExecute := Partrec.map
  (SourceOneIota.SourceAdditiveTracking.Assignment.execute_partrec.comp sourceOneCode_primrec.to_comp)
  (sourceOneWord_primrec.comp Primrec.snd).to_comp.to₂

theorem sourceOneExecute_returns (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha = 0) :
    ∃ codes, codes ∈ sourceOneExecute alpha := by
  obtain ⟨word, hw⟩ := SourceOneIota.SourceAdditiveTracking.Assignment.execute_returns _ (sourceOne_caller alpha hi hl)
  exact ⟨sourceOneWord word, Part.mem_map _ hw⟩

theorem sourceOneExecute_spec (alpha : Nat) (codes : List Nat) (ho : codes ∈ sourceOneExecute alpha) :
    (∀ c ∈ codes, Canonical.check c = true) ∧ ∃ word,
      word ∈ SourceOneIota.SourceAdditiveTracking.Assignment.execute (sourceOneCode alpha) ∧
        codes = sourceOneWord word ∧ codes.map unionInterpretation = word.map (interpretation 0) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff sourceOneWord).mp ho
  have hs := sourceOneWord_spec word (SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking _ word hw)
  exact ⟨hs.1, word, hw, rfl, hs.2⟩

def nativeExecute (alpha : Nat) : Part (List Nat) :=
  (NativeContext.SourceAdditiveTracking.Assignment.execute (contextCode alpha) (nativeCode alpha)).map (nativeWord alpha)

theorem nativeExecute_partrec : Partrec nativeExecute := Partrec.map
  (Partrec.comp NativeContext.SourceAdditiveTracking.Assignment.execute_partrec
    (contextCode_primrec.pair nativeCode_primrec).to_comp)
  (nativeWord_primrec.comp Primrec.fst Primrec.snd).to_comp.to₂

theorem nativeExecute_returns (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0) :
    ∃ codes, codes ∈ nativeExecute alpha := by
  obtain ⟨word, hw⟩ := NativeContext.SourceAdditiveTracking.Assignment.execute_returns _ _ (native_caller alpha hi hl)
  exact ⟨nativeWord alpha word, Part.mem_map _ hw⟩

theorem nativeExecute_spec (alpha : Nat) (codes : List Nat) (ho : codes ∈ nativeExecute alpha) :
    (∀ c ∈ codes, Canonical.check c = true) ∧ ∃ word,
      word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (contextCode alpha) (nativeCode alpha) ∧
        codes = nativeWord alpha word ∧
          codes.map unionInterpretation = word.map (NativeContext.interpretation (contextCode alpha)) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := nativeWord_spec alpha word (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)
  exact ⟨hs.1, word, hw, rfl, hs.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Return
