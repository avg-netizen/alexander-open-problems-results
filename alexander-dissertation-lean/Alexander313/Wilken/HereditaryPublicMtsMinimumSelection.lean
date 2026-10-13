import Alexander313.Wilken.HereditaryPublicMtsMinimumSelectionSupport

/-!
# An independent numerical shortest covering selector

The actual mts computes the already proved minimum length. A separate
finite primitive recursive scan checks every localization subsequence of
that length, keeping the greatest lexical value word. The genuine arbitrary
covering subsequence theorem supplies completeness. Its actual partial
producer terminates exactly when the true grammar caller has any covering.
The scan never consumes a minimum, lexical or covering certificate oracle.
Equality of this numerical selector with mts, and lexical maximality among
coverings of different lengths, are explicitly separate. Uncompiled draft.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSelection

open NativeContext NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)
open MinimumSelectionSupport

theorem covering_base_word (gamma : Nat) (codes : List Nat)
    (hc : Covering gamma gamma codes) : codes = [gamma] := by
  cases hc with
  | root hg => rfl
  | append previous current before hp hedge =>
    have he := (Support.eligible_exact previous gamma).mp hedge
    have hfloor : unionInterpretation gamma ≤ unionInterpretation previous := by
      rcases ReachBound.covering_root_or_lt hp with rfl | hlt
      · exact le_rfl
      · exact hlt.le
    exact False.elim (lt_irrefl _ (hfloor.trans_lt he.2.2.1))

/-- The reflexive covering is also a literal localization subsequence. -/
theorem covering_sublist (gamma beta d : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) : codes.Sublist (localization gamma d) := by
  rcases ReachBound.covering_root_or_lt hc with rfl | hlt
  · simpa only [covering_base_word gamma codes hc,
      MinimumSupport.localization_base gamma d hi hd] using (List.Sublist.refl [gamma])
  · exact CoveringLocalization.covering_sublist gamma beta d codes hc hi hd hlt

def choice (gamma beta d : Nat) : Option (List Nat) :=
  select ((gamma, beta), (Support.word gamma (localization gamma d).tail).length)
    (enumerate (localization gamma d))

theorem choice_primrec : Primrec (fun p : (Nat × Nat) × Nat => choice p.1.1 p.1.2 p.2) := by
  have hg := Primrec.fst.comp Primrec.fst
  have hb := Primrec.snd.comp Primrec.fst
  have hl := localization_primrec.comp hg Primrec.snd
  have hk := Primrec.list_length.comp
    (Support.word_primrec.comp hg (Primrec.list_tail.comp hl))
  exact select_primrec.comp ((hg.pair hb).pair hk) (enumerate_primrec.comp hl)

/-- Actual mts minimum length supplies one checked enumerated candidate;
completeness for all competitors comes from genuine covering localization. -/
theorem choice_exists (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hr : ∃ codes, Covering gamma beta codes) : ∃ out, choice gamma beta d = some out := by
  have hw : Support.word gamma (localization gamma d).tail ∈ Infinity.execute gamma beta := by
    rw [Infinity.execute_eq_own gamma beta hi]
    simpa only [PublicMts.execute, hi, Bool.cond_true] using
      Part.mem_map (fun e => Support.word gamma (localization gamma e).tail) hd
  have hs := Minimum.infinity_execute_shortest gamma beta _ hw hr
  apply select_exists
  refine ⟨_, (enumerate_mem _ _).mpr (covering_sublist gamma beta d _ hs.1 hi hd), ?_⟩
  exact (passes_exact _ _).mpr ⟨hs.1, rfl⟩

/-- Every real selected output is a genuine shortest covering, and is
lexically greatest among all coverings of that genuine minimum length. -/
theorem choice_optimal (gamma beta d : Nat) (out : List Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : choice gamma beta d = some out) :
    Covering gamma beta out ∧
      (∀ codes, Covering gamma beta codes → out.length ≤ codes.length) ∧
      (∀ codes, Covering gamma beta codes → codes.length = out.length →
        codes.map unionInterpretation = out.map unionInterpretation ∨
          List.Lex (· < ·) (codes.map unionInterpretation) (out.map unionInterpretation)) := by
  have hpass := (select_first _ _ _ ho).1
  have hs := (passes_exact _ out).mp hpass
  have hw : Support.word gamma (localization gamma d).tail ∈ PublicMts.execute gamma beta := by
    simpa only [PublicMts.execute, hi, Bool.cond_true] using
      Part.mem_map (fun e => Support.word gamma (localization gamma e).tail) hd
  refine ⟨hs.1, ?_, ?_⟩
  · intro codes hc
    rw [hs.2]
    exact Minimum.execute_length_le_covering gamma beta _ codes hw hc
  · intro codes hc hlength
    apply select_lex_maximal _ _ out codes (MinimumSupport.localization_strict gamma beta d hi hd) ho
      (covering_sublist gamma beta d codes hc hi hd)
    exact (passes_exact _ codes).mpr ⟨hc, hlength.trans hs.2⟩

def execute (gamma beta : Nat) : Part (List Nat) := cond (Infinity.inputCheck gamma beta)
  ((SkNextSearch.Support.search gamma beta).bind fun d => Part.ofOption (choice gamma beta d)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hc : Partrec₂ (fun p : Nat × Nat => fun d : Nat => Part.ofOption (choice p.1 p.2 d)) :=
    choice_primrec.to_comp.ofOption.to₂
  exact (Partrec.cond Infinity.inputCheck_primrec.to_comp
    (Partrec.bind SkNextSearch.Support.search_partrec hc) Partrec.none).to₂

theorem execute_spec (gamma beta : Nat) (out : List Nat) (ho : out ∈ execute gamma beta) :
    Infinity.inputCheck gamma beta = true ∧ ∃ d, d ∈ SkNextSearch.Support.search gamma beta ∧
      choice gamma beta d = some out := by
  have hi : Infinity.inputCheck gamma beta = true := by
    cases h : Infinity.inputCheck gamma beta with
    | true => rfl
    | false => exact False.elim (by
        simpa only [execute, h, Bool.cond_false, Part.notMem_none] using ho)
  have hb : out ∈ (SkNextSearch.Support.search gamma beta).bind
      (fun d => Part.ofOption (choice gamma beta d)) := by
    simpa only [execute, hi, Bool.cond_true] using ho
  obtain ⟨d, hd, hs⟩ := Part.mem_bind_iff.mp hb
  have he : choice gamma beta d = some out := by
    have hm := Part.mem_ofOption.mp hs
    exact Option.mem_def.mp hm
  exact ⟨hi, d, hd, he⟩

/-- Every actual execution derives its independent covering before the
OWN caller and lexical/minimum conclusions are used. -/
theorem execute_optimal (gamma beta : Nat) (out : List Nat) (ho : out ∈ execute gamma beta) :
    Covering gamma beta out ∧
      (∀ codes, Covering gamma beta codes → out.length ≤ codes.length) ∧
      (∀ codes, Covering gamma beta codes → codes.length = out.length →
        codes.map unionInterpretation = out.map unionInterpretation ∨
          List.Lex (· < ·) (codes.map unionInterpretation) (out.map unionInterpretation)) := by
  obtain ⟨hi, d, hd, hs⟩ := execute_spec gamma beta out ho
  have hc := ((passes_exact _ out).mp (select_first _ _ _ hs).1).1
  have hj := InfinityHat.own_input_of_cut gamma beta hi (ReachBound.covering_lt_own hc)
  exact choice_optimal gamma beta d out hj hd hs

/-- An independent shortest covering with the same lexical maximum
property is the literal canonical output. No selected word is supplied. -/
theorem execute_optimal_unique (gamma beta : Nat) (out other : List Nat)
    (ho : out ∈ execute gamma beta) (hc : Covering gamma beta other)
    (hshort : ∀ codes, Covering gamma beta codes → other.length ≤ codes.length)
    (hmax : ∀ codes, Covering gamma beta codes → codes.length = other.length →
      codes.map unionInterpretation = other.map unionInterpretation ∨
        List.Lex (· < ·) (codes.map unionInterpretation) (other.map unionInterpretation)) :
    out = other := by
  have hs := execute_optimal gamma beta out ho
  have hl : out.length = other.length := Nat.le_antisymm (hs.2.1 other hc) (hshort out hs.1)
  apply SkPublicValueInvariance.canonical_words_eq out other
    (CoveringLocalization.covering_checked hs.1) (CoveringLocalization.covering_checked hc)
  rcases hs.2.2 other hc hl.symm with he | hlex
  · exact he.symm
  · rcases hmax out hs.1 hl with he | hother
    · exact he
    · exact False.elim (asymm hlex hother)

theorem execute_returns (gamma beta : Nat) (hi : Infinity.inputCheck gamma beta = true)
    (hr : ∃ codes, Covering gamma beta codes) : ∃ out, out ∈ execute gamma beta := by
  obtain ⟨codes, hc⟩ := hr
  have hj := InfinityHat.own_input_of_cut gamma beta hi (ReachBound.covering_lt_own hc)
  obtain ⟨d, hd⟩ := search_returns gamma beta hj
  obtain ⟨out, hs⟩ := choice_exists gamma beta d hj hd ⟨codes, hc⟩
  refine ⟨out, ?_⟩
  simp only [execute, hi, Bool.cond_true]
  exact Part.mem_bind hd (Part.mem_ofOption.mpr (Option.mem_def.mpr hs))

theorem execute_domain (gamma beta : Nat) : (execute gamma beta).Dom ↔
    Infinity.inputCheck gamma beta = true ∧ ∃ codes, Covering gamma beta codes := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    exact ⟨(execute_spec gamma beta out ho).1, out, (execute_optimal gamma beta out ho).1⟩
  · rintro ⟨hi, hr⟩
    exact Part.dom_iff_mem.mpr (execute_returns gamma beta hi hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSelection
