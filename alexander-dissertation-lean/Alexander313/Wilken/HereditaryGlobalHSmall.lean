import Alexander313.Wilken.HereditaryGlobalHSmallSupport
import Alexander313.Wilken.HereditaryGlobalTrackingSequences

/-!
# Actual small-cutoff h on genuine segmented global references

The entire original global reference prefix, including its literal upsilon
chain, is retained. The genuine proper last epsilon supplies every public
mu/sk caller. Actual mu cover selects the independently executing sk splice
or leaves the original reference unchanged. Both beta-at-most-gamma clauses
of Definition3.34 have exact partial recursive execution and independently
derived global tracking recognition on the multiplicative cutoff domain.
The large-cutoff mts branch and gamma-hat construction remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHSmall

open GlobalTrackingSequences
open PublicTrackingSequences (coverCheck coverCheck_primrec coverCheck_exact)
open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

abbrev Query := List Nat × (Nat × Nat)

def inputCheck (p : Query) : Bool := referenceCheck (p.1 ++ [p.2.1]) &&
  (MuPublicDictionary.Support.inputCheck p.2.1 &&
    (Canonical.check p.2.2 && !(Canonical.less p.2.1 p.2.2)))

theorem inputCheck_primrec : Primrec inputCheck := by
  have hgamma := Primrec.fst.comp Primrec.snd
  have hcut := Primrec.snd.comp Primrec.snd
  have hword := Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp hgamma (Primrec.const []))
  exact Primrec.and.comp (referenceCheck_primrec.comp hword)
    (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp hgamma)
      (Primrec.and.comp (Canonical.Effective.check_primrec.comp hcut)
        (Primrec.not.comp (Canonical.Effective.less_primrec.comp hgamma hcut))))

theorem inputCheck_exact (p : Query) : inputCheck p = true ↔
    Reference (p.1 ++ [p.2.1]) ∧ MuPublicDictionary.Support.inputCheck p.2.1 = true ∧
      Canonical.check p.2.2 = true ∧ unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 := by
  rw [inputCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, referenceCheck_exact]
  constructor
  · rintro ⟨hr, ha, hc, hb⟩
    have hg := ((MuPublicDictionary.Support.inputCheck_image _).mp ha).1
    exact ⟨hr, ha, hc, (canonical_not_less_exact _ _ hg hc).mp hb⟩
  · rintro ⟨hr, ha, hc, hb⟩
    have hg := ((MuPublicDictionary.Support.inputCheck_image _).mp ha).1
    exact ⟨hr, ha, hc, (canonical_not_less_exact _ _ hg hc).mpr hb⟩

theorem sk_caller (p : Query) (hi : inputCheck p = true) :
    SkPublicDictionary.Support.inputCheck p.2.1 p.2.2 = true := by
  have hs := (inputCheck_exact p).mp hi
  have hg := (MuPublicDictionary.Support.inputCheck_image _).mp hs.2.1
  exact (SkPublicDictionary.UpsilonDomain.inputCheck_exact _ _).mpr
    ⟨hg.1, hg.2.1, hg.2.2, Canonical.check_original hs.2.2.1⟩

def execute (p : Query) : Part (List Nat) := cond (inputCheck p)
  (cond (coverCheck p.2.1 p.2.2)
    ((SkPublicDictionary.execute p.2).map fun codes => p.1 ++ codes)
    (Part.some (p.1 ++ [p.2.1]))) Part.none

theorem execute_partrec : Partrec execute := by
  have hgamma := Primrec.fst.comp Primrec.snd
  have hcut := Primrec.snd.comp Primrec.snd
  have hc := coverCheck_primrec.comp hgamma hcut
  have hs := Partrec.map (SkPublicDictionary.execute_partrec.comp Computable.snd)
    ((Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂)
  have hw := Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp hgamma (Primrec.const []))
  exact Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond hc.to_comp hs hw.to_comp.partrec) Partrec.none

theorem execute_returns (p : Query) (hi : inputCheck p = true) :
    ∃ codes, codes ∈ execute p := by
  cases hc : coverCheck p.2.1 p.2.2 with
  | false =>
    refine ⟨p.1 ++ [p.2.1], ?_⟩
    simp only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff]
  | true =>
    obtain ⟨codes, ho⟩ := SkPublicDictionary.execute_returns _ _ (sk_caller p hi)
    refine ⟨p.1 ++ codes, ?_⟩
    simpa only [execute, hi, hc, Bool.cond_true] using Part.mem_map (fun codes => p.1 ++ codes) ho

theorem execute_domain (p : Query) : (execute p).Dom ↔ inputCheck p = true := by
  constructor
  · intro hd
    cases hi : inputCheck p with
    | true => rfl
    | false =>
      have hn : (Part.none : Part (List Nat)).Dom := by
        simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    exact Part.dom_iff_mem.mpr (execute_returns p hi)

/-- Exact actual beta-at-most-gamma clauses retain the entire global
prefix. The numerical covering decision uses the independent proper mu. -/
theorem execute_clauses (p : Query) (out : List Nat) : out ∈ execute p ↔ inputCheck p = true ∧
    ((unionInterpretation p.2.2 ≤ SkPublicRecurrence.muValue p.2.1 ∧
        ∃ codes, codes ∈ SkPublicDictionary.execute p.2 ∧ out = p.1 ++ codes) ∨
      (SkPublicRecurrence.muValue p.2.1 < unionInterpretation p.2.2 ∧
        out = p.1 ++ [p.2.1])) := by
  constructor
  · intro ho
    have hi := (execute_domain p).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
    refine ⟨hi, ?_⟩
    cases hc : coverCheck p.2.1 p.2.2 with
    | true =>
      have hw : out ∈ (SkPublicDictionary.execute p.2).map (fun codes => p.1 ++ codes) := by
        simpa only [execute, hi, hc, Bool.cond_true] using ho
      obtain ⟨codes, hm, he⟩ := (Part.mem_map_iff _).mp hw
      exact Or.inl ⟨((coverCheck_exact _ _).mp hc).2.2, codes, hm, he.symm⟩
    | false =>
      have hs := (inputCheck_exact p).mp hi
      have hb : ¬ unionInterpretation p.2.2 ≤ SkPublicRecurrence.muValue p.2.1 := by
        intro hb
        have ht := (coverCheck_exact _ _).mpr ⟨hs.2.1, hs.2.2.1, hb⟩
        rw [hc] at ht
        cases ht
      have he : out = p.1 ++ [p.2.1] := by
        simpa only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using ho
      exact Or.inr ⟨lt_of_not_ge hb, he⟩
  · rintro ⟨hi, ⟨hcover, codes, hm, rfl⟩ | ⟨hfail, rfl⟩⟩
    · have hs := (inputCheck_exact p).mp hi
      have hc := (coverCheck_exact _ _).mpr ⟨hs.2.1, hs.2.2.1, hcover⟩
      simpa only [execute, hi, hc, Bool.cond_true] using Part.mem_map (fun codes => p.1 ++ codes) hm
    · have hc : coverCheck p.2.1 p.2.2 = false := Bool.eq_false_of_not_eq_true (by
        intro ht
        exact hfail.not_ge ((coverCheck_exact _ _).mp ht).2.2)
      simp only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff]

theorem execute_tracking (p : Query) (out : List Nat) (ho : out ∈ execute p)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hone : 1 < unionInterpretation p.2.2) : Tracking out := by
  have hs := (execute_clauses p out).mp ho
  have hi := (inputCheck_exact p).mp hs.1
  rcases hs.2 with ⟨hc, codes, hcodes, rfl⟩ | ⟨hc, rfl⟩
  · obtain ⟨tail, he, _⟩ := SkPublicRecurrence.execute_initial _ _ codes hcodes
    have ht := SkPublicRecurrence.execute_tracking _ _ codes hcodes hm hone
    rw [he] at ht ⊢
    exact SmallHSupport.global_tracking_splice _ _ _ hi.1 hi.2.1 ht
  · have he := (MuPublicDictionary.Support.inputCheck_image _).mp hi.2.1
    have hp := EpsilonOffsets.epsilon_pos_principal he.2.1
    have hgt := EpsilonOffsets.epsilon_one_lt he.2.1
    have ht := PublicTrackingSequences.singleton_tracking _ he.1 hp.1 hp.2 hgt.le
    exact SmallHSupport.global_tracking_splice _ _ [] hi.1 hi.2.1 ht

theorem execute_trackingCheck (p : Query) (out : List Nat) (ho : out ∈ execute p)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hone : 1 < unionInterpretation p.2.2) : trackingCheck out = true :=
  (trackingCheck_exact out).mpr (execute_tracking p out ho hm hone)

theorem execute_spec (p : Query) (out : List Nat) (ho : out ∈ execute p) :
    inputCheck p = true ∧ out ≠ [] ∧ (∀ c ∈ out, Canonical.check c = true) := by
  have hs := (execute_clauses p out).mp ho
  have hi := (inputCheck_exact p).mp hs.1
  refine ⟨hs.1, ?_⟩
  have hp : ∀ c ∈ p.1, Canonical.check c = true := fun c hc =>
    (hi.1.epsilons c (List.mem_append.mpr (Or.inl hc))).1
  rcases hs.2 with ⟨hc, codes, hcodes, rfl⟩ | ⟨hc, rfl⟩
  · have hn := SkPublicRecurrence.execute_initial _ _ codes hcodes
    have hs := SkPublicRecurrence.execute_spec _ _ codes hcodes
    refine ⟨?_, ?_⟩
    · intro he
      have hz := (List.append_eq_nil_iff.mp he).2
      obtain ⟨tail, ht, _⟩ := hn
      rw [ht] at hz
      exact List.cons_ne_nil _ _ hz
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hp c hc
      · exact hs.2.2.1 c hc
  · refine ⟨?_, ?_⟩
    · intro he
      exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp he).2
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hp c hc
      · simpa only [List.mem_singleton.mp hc] using
          ((MuPublicDictionary.Support.inputCheck_image _).mp hi.2.1).1

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHSmall
