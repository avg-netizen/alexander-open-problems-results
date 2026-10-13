import Alexander313.Wilken.SourceOneNativeSkRawSupport
import Alexander313.Wilken.PublicEpsilonNativeSkPublicValueInvariance

/-!
# Executing source-one sk from arbitrary original RAW epsilon spellings

The actual RAW checker constructs its genuine source-zero HIGH root and
invokes the complete original-source initialized producer. Only the first
code is restored to the unchanged original RAW spelling. Actual raw mu
invariance derives the whole recurrence, both maximal stops, and the real
RAW tracker. Later entries remain computed original Normal LOW syntax.
Canonical public outputs depend only on original root and cutoff values.
No Native base-one, input Normality, representative, endpoint, global
dictionary assignment, Par or evaluation oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw

open Support

def execute (p : Query) : Part (List Nat) := cond (inputCheck p.1 p.2)
  ((SkSourceWord.execute (rootQuery p)).map (restore p.1)) Part.none

theorem execute_partrec : Partrec execute := by
  have he := SkSourceWord.execute_partrec.comp rootQuery_primrec.to_comp
  have hm : Computable₂ (fun p : Query => fun codes : List Nat => restore p.1 codes) :=
    (restore_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact Partrec.cond inputCheck_primrec.to_comp (Partrec.map he hm) Partrec.none

theorem execute_domain (raw cutoff : Nat) : (execute (raw, cutoff)).Dom ↔
    inputCheck raw cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck raw cutoff with
    | true => rfl
    | false =>
      have hx : (Part.none : Part (List Nat)).Dom := by
        simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
  · intro hi
    have hd := (SkSourceWord.execute_domain _ _).mpr (root_caller raw cutoff hi)
    simpa only [execute, hi, Bool.cond_true, rootQuery] using hd

theorem execute_returns (raw cutoff : Nat) (hi : inputCheck raw cutoff = true) :
    ∃ codes, codes ∈ execute (raw, cutoff) :=
  Part.dom_iff_mem.mp ((execute_domain raw cutoff).mpr hi)

theorem execute_member (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) :
    inputCheck raw cutoff = true ∧ ∃ original,
      original ∈ SkSourceWord.execute (SourceTrackingRaw.Support.rootCode raw, cutoff) ∧
        codes = restore raw original := by
  have hi := (execute_domain raw cutoff).mp (Part.dom_iff_mem.mpr ⟨codes, ho⟩)
  rw [execute, hi, Bool.cond_true] at ho
  obtain ⟨original, hm, he⟩ := (Part.mem_map_iff _).mp ho
  exact ⟨hi, original, hm, he.symm⟩

/-- The literal original raw initial entry is retained; every later code
is an actual original-source Normal LOW return, with no supplied witness. -/
theorem execute_spec (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) :
    inputCheck raw cutoff = true ∧ ∃ tail, codes = raw :: tail ∧
      (∀ d ∈ tail, Theta.acceptedLowCode 0 d = true) ∧
      lowCheckCode 0 raw = true ∧ 1 < interpretation 0 raw := by
  obtain ⟨hi, original, hm, rfl⟩ := execute_member raw cutoff codes ho
  have hs := SkSourceWord.execute_spec _ cutoff original hm
  obtain ⟨tail, he⟩ := hs.2.2.1
  have hr := (inputCheck_exact raw cutoff).mp hi
  refine ⟨hi, tail, by rw [he, restore_cons], ?_, hr.1, hr.2.1⟩
  intro d hd
  exact hs.2.2.2 d (by rw [he]; exact List.mem_cons_of_mem _ hd)

theorem execute_low (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) : ∀ d ∈ codes, lowCheckCode 0 d = true := by
  obtain ⟨hi, tail, he, ht, hl, hp⟩ := execute_spec raw cutoff codes ho
  intro d hd
  rw [he] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hl
  · exact ((Theta.acceptedLowCode_iff 0 d).mp (ht d hd)).1

/-- Restoring the raw first code preserves the genuine maximal recurrence
through actual original raw mu invariance, including both stopping cases. -/
theorem execute_source (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) : SkSourceRecurrence.SourcePath cutoff codes := by
  obtain ⟨hi, original, hm, he⟩ := execute_member raw cutoff codes ho
  have hr := Bool.and_eq_true.mp hi
  have hv := (SourceTrackingRaw.Support.rootCode_spec raw hr.1).2.2
  have hp := SkSourceRecurrence.execute_source _ cutoff original hm
  obtain ⟨tail, hhead⟩ := (SkSourceWord.execute_spec _ cutoff original hm).2.2.1
  rw [hhead] at hp
  rw [he, hhead, restore_cons]
  exact sourcePath_replace_head cutoff raw _ tail hp hr.1 hv.symm

theorem execute_terminal (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) :
    ∃ before final, codes = before ++ [final] ∧ SkSourceRecurrence.Terminal cutoff final :=
  (execute_source raw cutoff codes ho).terminal

theorem execute_tracking (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (raw, cutoff))
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) : SourceTrackingRaw.trackingCheck codes = true := by
  obtain ⟨hi, original, hm, he⟩ := execute_member raw cutoff codes ho
  have hr := Bool.and_eq_true.mp hi
  have hv := (SourceTrackingRaw.Support.rootCode_spec raw hr.1).2.2
  have ht := SkTracking.execute_tracking _ cutoff original hm hmul hcut
  have ha := (SkTracking.Support.original_root _
    (SourceTrackingRaw.Support.rootCode_spec raw hr.1).2.1).1
  obtain ⟨tail, hhead⟩ := (SkSourceWord.execute_spec _ cutoff original hm).2.2.1
  rw [hhead] at ht
  rw [he, hhead, restore_cons]
  exact tracking_replace_head raw _ tail ht hr.1 ha hv.symm

/-- Equal original raw epsilon and cutoff values determine the entire
executing chronological value word; written source identity is not used. -/
theorem execute_values_eq (raw other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) (ht : otherCodes ∈ execute (other, otherCutoff))
    (hv : interpretation 0 raw = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.map (interpretation 0) = otherCodes.map (interpretation 0) := by
  have hp := execute_source raw cutoff codes ho
  have hq := execute_source other otherCutoff otherCodes ht
  obtain ⟨hi, xs, he, hx, hl, hr⟩ := execute_spec raw cutoff codes ho
  obtain ⟨hj, ys, hf, hy, hk, hs⟩ := execute_spec other otherCutoff otherCodes ht
  rw [he] at hp ⊢
  rw [hf] at hq ⊢
  exact hp.values_eq hq hcut hv

theorem execute_length_eq (raw other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ execute (raw, cutoff)) (ht : otherCodes ∈ execute (other, otherCutoff))
    (hv : interpretation 0 raw = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.length = otherCodes.length := by
  simpa only [List.length_map] using congrArg List.length
    (execute_values_eq raw other cutoff otherCutoff codes otherCodes ho ht hv hcut)

def publicWord (codes : List Nat) : List Nat := codes.map SourceTrackingRaw.Support.publicCode

theorem publicWord_primrec : Primrec publicWord :=
  Primrec.list_map Primrec.id (SourceTrackingRaw.Support.publicCode_primrec.comp Primrec.snd).to₂

def executePublic (p : Query) : Part (List Nat) := (execute p).map publicWord

theorem executePublic_partrec : Partrec executePublic :=
  Partrec.map execute_partrec (publicWord_primrec.comp Primrec.snd).to_comp.to₂

theorem executePublic_domain (raw cutoff : Nat) : (executePublic (raw, cutoff)).Dom ↔
    inputCheck raw cutoff = true := execute_domain raw cutoff

theorem executePublic_returns (raw cutoff : Nat) (hi : inputCheck raw cutoff = true) :
    ∃ codes, codes ∈ executePublic (raw, cutoff) :=
  Part.dom_iff_mem.mp ((executePublic_domain raw cutoff).mpr hi)

theorem executePublic_spec (raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executePublic (raw, cutoff)) :
    inputCheck raw cutoff = true ∧ (∀ d ∈ codes, Canonical.check d = true) ∧
      ∃ source, source ∈ execute (raw, cutoff) ∧
        codes.map unionInterpretation = source.map (interpretation 0) := by
  obtain ⟨source, hs, rfl⟩ := (Part.mem_map_iff publicWord).mp ho
  have hp (d : Nat) (hd : d ∈ source) := SourceTrackingRaw.Support.publicCode_spec d
    (execute_low raw cutoff source hs d hd)
  refine ⟨(execute_spec raw cutoff source hs).1, ?_, source, hs, ?_⟩
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact (hp c hc).1
  · rw [publicWord, List.map_map]
    apply List.map_congr_left
    intro d hd
    exact (hp d hd).2

/-- Actual canonical public value injection turns the independently
proved SAME-source recurrence equality into literal whole-word equality. -/
theorem executePublic_eq (raw other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ executePublic (raw, cutoff)) (ht : otherCodes ∈ executePublic (other, otherCutoff))
    (hv : interpretation 0 raw = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : codes = otherCodes := by
  obtain ⟨hi, hc, source, hs, hvalues⟩ := executePublic_spec raw cutoff codes ho
  obtain ⟨hj, hd, target, hr, htarget⟩ := executePublic_spec other otherCutoff otherCodes ht
  exact NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
    codes otherCodes hc hd (hvalues.trans
      ((execute_values_eq raw other cutoff otherCutoff source target hs hr hv hcut).trans htarget.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw
