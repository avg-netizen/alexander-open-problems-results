import Alexander313.Wilken.SourceOneNativeSkSourcePathSupport

/-!
# Genuine source-one initial sk eligibility and chronological lowering

The original public cutoff is compared with actual source-one mu before
the first truncation. Every subsequent native entry has a derived original
finiteBase1 bound, so real canonical public return followed by source-zero
lowering gives a checked Normal LOW chronological word. No Native base-one
parser or assumed original representation. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceWord.Support

open SkSourcePathSupport

abbrev Query := SkNextSearch.Query
abbrev Word := NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.Word

def eligible (root cutoff : Nat) : Bool := SkNextSearch.inputCheck root cutoff &&
  !(Canonical.less (SourceTrackingSupport.muPublicCode root) (Canonical.canonicalize cutoff))

theorem eligible_primrec : Primrec₂ eligible :=
  (Primrec.and.comp SkNextSearch.inputCheck_primrec
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp
      (SourceTrackingSupport.muPublicCode_primrec.comp Primrec.fst)
      (Canonical.Effective.canonicalize_primrec.comp Primrec.snd)))).to₂

theorem eligible_exact (root cutoff : Nat) : eligible root cutoff = true ↔
    Mu.inputCheck root = true ∧ unionCheck cutoff = true ∧
      unionInterpretation cutoff ≤ Mu.sourceValue root := by
  constructor
  · intro he
    obtain ⟨hi, hl⟩ := Bool.and_eq_true.mp he
    obtain ⟨ha, hc⟩ := (SkNextSearch.inputCheck_exact root cutoff).mp hi
    have hm := SourceTrackingSupport.muPublicCode_spec root ha
    have hb := NativeContext.SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1
      (Canonical.canonicalize_check cutoff hc)
    exact ⟨ha, hc, by simpa only [hm.2, Canonical.canonicalize_value cutoff hc] using hb.mp hl⟩
  · rintro ⟨ha, hc, hle⟩
    have hm := SourceTrackingSupport.muPublicCode_spec root ha
    refine Bool.and_eq_true.mpr ⟨(SkNextSearch.inputCheck_exact root cutoff).mpr ⟨ha, hc⟩, ?_⟩
    apply (NativeContext.SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1
      (Canonical.canonicalize_check cutoff hc)).mpr
    simpa only [hm.2, Canonical.canonicalize_value cutoff hc] using hle

theorem ineligible_exact (root cutoff : Nat) (ha : Mu.inputCheck root = true)
    (hc : unionCheck cutoff = true) : eligible root cutoff = false ↔
      Mu.sourceValue root < unionInterpretation cutoff := by
  constructor
  · intro he
    apply lt_of_not_ge
    intro hle
    have ht := (eligible_exact root cutoff).mpr ⟨ha, hc, hle⟩
    rw [he] at ht
    cases ht
  · intro hlt
    apply Bool.eq_false_of_not_eq_true
    intro he
    exact hlt.not_ge ((eligible_exact root cutoff).mp he).2.2

def flatWord (word : Word) : List Nat := word.map fun entry => entryCode entry.1 entry.2

theorem flatWord_primrec : Primrec flatWord := by
  have he : Primrec₂ (fun word : Word => fun entry : NativeContext.PublicEpsilonUnboundedIota.Context =>
      entryCode entry.1 entry.2) :=
    (entryCode_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_map Primrec.id he

theorem flatWord_spec (word : Word)
    (hc : ∀ entry ∈ word, NativeContext.lowCheckCode entry.1 entry.2 = true)
    (hb : ∀ entry ∈ word, NativeContext.interpretation entry.1 entry.2 < finiteBase 1) :
    (∀ d ∈ flatWord word, Theta.acceptedLowCode 0 d = true) ∧
      (flatWord word).map (interpretation 0) =
        word.map (fun entry => NativeContext.interpretation entry.1 entry.2) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hd
    exact (entryCode_spec entry.1 entry.2 (hc entry he) (hb entry he)).1
  · rw [flatWord, List.map_map]
    apply List.map_congr_left
    intro entry he
    exact (entryCode_spec entry.1 entry.2 (hc entry he) (hb entry he)).2

theorem first_flatWord_spec (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true)
    (word : Word) (hw : word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
      ((alphaCode root, out.2), cutoff)) :
    (∀ d ∈ flatWord word, Theta.acceptedLowCode 0 d = true) ∧
      (flatWord word).map (interpretation 0) =
        word.map (fun entry => NativeContext.interpretation entry.1 entry.2) := by
  have hs := NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_spec _ _ _ word hw
  exact flatWord_spec word (fun entry he => (hs.2.2.2 entry he).1)
    (first_loop_entry_bound root cutoff out ho hh word hw)

theorem first_stopCode_spec (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) :
    Theta.acceptedLowCode 0 (entryCode (alphaCode root) out.2) = true ∧
      interpretation 0 (entryCode (alphaCode root) out.2) =
        NativeContext.interpretation (alphaCode root) out.2 := by
  have hs := SkNextSearch.execute_spec root cutoff out ho
  have ha := ((SkNextSearch.inputCheck_exact root cutoff).mp hs.1).1
  exact entryCode_spec _ out.2 hs.2.1
    ((hs.2.2.2.1.le.trans (SkNextStepSupport.nextValue_le_mu root (unionInterpretation cutoff))).trans_lt
      (mu_lt_public_boundary root ha))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceWord.Support
