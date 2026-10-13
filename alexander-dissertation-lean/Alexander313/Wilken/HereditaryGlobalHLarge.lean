import Alexander313.Wilken.HereditaryGlobalHLargeSupport
import Alexander313.Wilken.HereditaryGlobalTrackingSequences
import Alexander313.Wilken.HereditaryMultiplicativeClassification

/-!
# Genuine executing large-cutoff h from mts and independent sk

The actual full-domain mts word is tested by the independently proved
finite covering recognizer. Its real penultimate epsilon licenses the
independent sk call, and the literal original global prefix plus mts prefix
is retained. For strict multiplicative targets the executable branch test
has precisely the genuine semantic hat cut, without producing a numerical
minimum. Every emitted word has an independently derived global tracker.
Arbitrary-reach sufficiency is separate. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHLarge

open GlobalTrackingSequences (Reference Tracking referenceCheck referenceCheck_primrec
  referenceCheck_exact trackingCheck trackingCheck_exact)
open GlobalHLargeSupport
open PublicMts
open PublicMts.CoveringSupport (Covering)
open PublicMts.CoveringRecognition (coveringCheck coveringCheck_primrec coveringCheck_exact)
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_append_singleton
  stripLast_append_singleton)

abbrev Query := List Nat × (Nat × Nat)

def inputCheck (p : Query) : Bool :=
  (referenceCheck (p.1 ++ [p.2.1]) && Infinity.inputCheck p.2.1 p.2.2) &&
    (Canonical.less p.2.1 p.2.2 && Multiplicative.canonicalCheck p.2.2)

theorem inputCheck_computable : Computable inputCheck := by
  have hg := Primrec.fst.comp Primrec.snd
  have hb := Primrec.snd.comp Primrec.snd
  have hw := Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp hg (Primrec.const []))
  have ha := Primrec.and.comp (referenceCheck_primrec.comp hw)
    (Infinity.inputCheck_primrec.comp hg hb)
  have ht := Primrec.and.to_comp.comp
    (Canonical.Effective.less_primrec.comp hg hb).to_comp
    (Multiplicative.canonicalCheck_computable.comp hb.to_comp)
  exact Primrec.and.to_comp.comp ha.to_comp ht

theorem inputCheck_exact (p : Query) : inputCheck p = true ↔
    Reference (p.1 ++ [p.2.1]) ∧ Infinity.inputCheck p.2.1 p.2.2 = true ∧
      unionInterpretation p.2.1 < unionInterpretation p.2.2 ∧
        MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2) := by
  rw [inputCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    referenceCheck_exact, Multiplicative.canonicalCheck_exact]
  constructor
  · rintro ⟨⟨hr, hi⟩, hlt, hc, hm⟩
    exact ⟨hr, hi, ((Canonical.less_exact _ _).mp hlt).2.2, hm⟩
  · rintro ⟨hr, hi, hlt, hm⟩
    have hs := (Infinity.inputCheck_exact _ _).mp hi
    have hg := ((MuPublicDictionary.Support.inputCheck_image _).mp hs.1).1
    exact ⟨⟨hr, hi⟩, (Canonical.less_exact _ _).mpr ⟨hg, hs.2.1, hlt⟩,
      hs.2.1, hm⟩

def epsilon (codes : List Nat) : Nat := lastCode (stripLast codes)
def retained (p : Query) (codes : List Nat) : List Nat := p.1 ++ stripLast (stripLast codes)

theorem epsilon_primrec : Primrec epsilon := lastCode_primrec.comp stripLast_primrec

theorem retained_primrec : Primrec₂ retained :=
  (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
    (stripLast_primrec.comp (stripLast_primrec.comp Primrec.snd))).to₂

def after (p : Query) (codes : List Nat) : Part (List Nat) :=
  cond (coveringCheck p.2.1 p.2.2 codes)
    ((SkPublicDictionary.execute (epsilon codes, p.2.2)).map
      (fun word => retained p codes ++ word)) Part.none

theorem after_partrec : Partrec₂ after := by
  have hg := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hc := coveringCheck_primrec.comp (hg.pair (hb.pair Primrec.snd))
  have hs := SkPublicDictionary.execute_partrec.comp
    ((epsilon_primrec.comp Primrec.snd).pair hb).to_comp
  have he : Computable₂ (fun p : Query × List Nat => fun word : List Nat =>
      retained p.1 p.2 ++ word) :=
    (Primrec.list_append.comp
      (retained_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp.to₂
  exact Partrec.cond hc.to_comp (Partrec.map hs he) Partrec.none

def execute (p : Query) : Part (List Nat) := cond (inputCheck p)
  ((Infinity.execute p.2.1 p.2.2).bind (after p)) Part.none

theorem execute_partrec : Partrec execute := by
  have hm := Infinity.execute_partrec.comp
    (Primrec.fst.comp Primrec.snd).to_comp (Primrec.snd.comp Primrec.snd).to_comp
  exact Partrec.cond inputCheck_computable (Partrec.bind hm after_partrec) Partrec.none

/-- A real strict covering supplies the actual sk caller at its numerical
penultimate epsilon; the target is already canonical by the full mts guard. -/
theorem sk_caller (p : Query) (codes : List Nat) (hi : inputCheck p = true)
    (hc : Covering p.2.1 p.2.2 codes) :
    SkPublicDictionary.Support.inputCheck (epsilon codes) p.2.2 = true := by
  have hs := (inputCheck_exact p).mp hi
  obtain ⟨eta, e, he, hp, hadj⟩ := covering_penultimate hc hs.2.2.1
  have ha := (PublicMts.Support.eligible_exact e p.2.2).mp hadj
  have hsplit : codes = (eta ++ [e]) ++ [p.2.2] :=
    he.trans (List.append_assoc eta [e] [p.2.2]).symm
  have hv : epsilon codes = e := by
    rw [epsilon, hsplit, stripLast_append_singleton, lastCode_append_singleton]
  have hg := (MuPublicDictionary.Support.inputCheck_image e).mp ha.1
  rw [hv]
  exact (SkPublicDictionary.UpsilonDomain.inputCheck_exact _ _).mpr
    ⟨hg.1, hg.2.1, hg.2.2,
      Canonical.check_original ((Infinity.inputCheck_exact _ _).mp hs.2.1).2.1⟩

/-- Exact literal execution retains the original prefix and actual mts
prefix, then invokes the independently executing sk at the real epsilon. -/
theorem execute_spec (p : Query) (out : List Nat) : out ∈ execute p ↔
    inputCheck p = true ∧ ∃ codes, codes ∈ Infinity.execute p.2.1 p.2.2 ∧
      Covering p.2.1 p.2.2 codes ∧ ∃ word,
        word ∈ SkPublicDictionary.execute (epsilon codes, p.2.2) ∧
          out = retained p codes ++ word := by
  constructor
  · intro ho
    have hi : inputCheck p = true := by
      cases h : inputCheck p with
      | true => rfl
      | false =>
        have hn : out ∈ (Part.none : Part (List Nat)) := by
          simpa only [execute, h, Bool.cond_false] using ho
        exact False.elim (Part.notMem_none _ hn)
    have hm : out ∈ (Infinity.execute p.2.1 p.2.2).bind (after p) := by
      simpa only [execute, hi, Bool.cond_true] using ho
    obtain ⟨codes, hc, ht⟩ := Part.mem_bind_iff.mp hm
    have hb : coveringCheck p.2.1 p.2.2 codes = true := by
      cases h : coveringCheck p.2.1 p.2.2 codes with
      | true => rfl
      | false =>
        have hn : out ∈ (Part.none : Part (List Nat)) := by
          simpa only [after, h, Bool.cond_false] using ht
        exact False.elim (Part.notMem_none _ hn)
    have hs : out ∈ (SkPublicDictionary.execute (epsilon codes, p.2.2)).map
        (fun word => retained p codes ++ word) := by
      simpa only [after, hb, Bool.cond_true] using ht
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hs
    exact ⟨hi, codes, hc, (coveringCheck_exact _ _ _).mp hb, word, hw, he.symm⟩
  · rintro ⟨hi, codes, hc, ht, word, hw, rfl⟩
    have hb := (coveringCheck_exact _ _ _).mpr ht
    have hs : retained p codes ++ word ∈ after p codes := by
      simpa only [after, hb, Bool.cond_true] using
        Part.mem_map (fun word => retained p codes ++ word) hw
    simpa only [execute, hi, Bool.cond_true] using Part.mem_bind hc hs

/-- On the independently checked strict M input, the exact executable
large-h domain is the true semantic singleton-boundary cut. -/
theorem execute_domain_cut (p : Query) (hi : inputCheck p = true) :
    (execute p).Dom ↔ unionInterpretation p.2.2 < InfinityHat.value p.2.1
      ((Infinity.inputCheck_exact _ _).mp ((inputCheck_exact p).mp hi).2.1).1 := by
  have hs := (inputCheck_exact p).mp hi
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨_, codes, hc, ht, word, hw, he⟩ := (execute_spec p out).mp ho
    exact (InfinityHat.execute_covering_iff_lt_value _ _ codes hc hs.2.2.2 hs.2.2.1).mp ht
  · intro hcut
    obtain ⟨codes, hc⟩ := Infinity.execute_returns _ _ hs.2.1
    have ht := (InfinityHat.execute_covering_iff_lt_value _ _ codes hc hs.2.2.2 hs.2.2.1).mpr hcut
    obtain ⟨word, hw⟩ := SkPublicDictionary.execute_returns _ _ (sk_caller p codes hi ht)
    exact Part.dom_iff_mem.mpr ⟨retained p codes ++ word,
      (execute_spec p _).mpr ⟨hi, codes, hc, ht, word, hw, rfl⟩⟩

/-- The genuine semantic cut derives the full grammar input internally;
Definition3.34 has no independently supplied infinity-bound premise. -/
theorem input_of_cut (p : Query)
    (hg : MuPublicDictionary.Support.inputCheck p.2.1 = true)
    (hr : Reference (p.1 ++ [p.2.1])) (hb : Canonical.check p.2.2 = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hlt : unionInterpretation p.2.1 < unionInterpretation p.2.2)
    (hcut : unionInterpretation p.2.2 < InfinityHat.value p.2.1 hg) :
    inputCheck p = true := by
  have hown := hcut.trans_le (InfinityHat.value_le_own _ hg)
  have hinfinity := hown.trans (ContextSupport.ownCeiling_boundary _ hg)
  exact (inputCheck_exact p).mpr ⟨hr, (Infinity.inputCheck_exact _ _).mpr
    ⟨hg, hb, hm.1, hm.2.1, hlt.le, hinfinity⟩, hlt, hm⟩

/-- The complete numerical large-h domain is exactly the printed proper
reference/strict multiplicative semantic-cut domain. -/
theorem execute_domain_exact (p : Query) : (execute p).Dom ↔
    ∃ hg : MuPublicDictionary.Support.inputCheck p.2.1 = true,
      Reference (p.1 ++ [p.2.1]) ∧ Canonical.check p.2.2 = true ∧
        MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2) ∧
          unionInterpretation p.2.1 < unionInterpretation p.2.2 ∧
            unionInterpretation p.2.2 < InfinityHat.value p.2.1 hg := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    have hi := ((execute_spec p out).mp ho).1
    have hs := (inputCheck_exact p).mp hi
    have hg := (Infinity.inputCheck_exact _ _).mp hs.2.1
    exact ⟨hg.1, hs.1, hg.2.1, hs.2.2.2, hs.2.2.1,
      (execute_domain_cut p hi).mp hd⟩
  · rintro ⟨hg, hr, hb, hm, hlt, hcut⟩
    have hi := input_of_cut p hg hr hb hm hlt hcut
    exact (execute_domain_cut p hi).mpr hcut

/-- Actual execution exhibits the literal mts suffix (epsilon,beta)
and the independently executing sk word in the printed large-h form. -/
theorem execute_form (p : Query) (out : List Nat) (ho : out ∈ execute p) :
    ∃ eta : List Nat, ∃ e : Nat, ∃ word : List Nat,
      eta ++ [e, p.2.2] ∈ Infinity.execute p.2.1 p.2.2 ∧
        word ∈ SkPublicDictionary.execute (e, p.2.2) ∧ out = (p.1 ++ eta) ++ word := by
  obtain ⟨hi, codes, hc, ht, word, hw, heout⟩ := (execute_spec p out).mp ho
  obtain ⟨eta, e, he, hp, hadj⟩ := covering_penultimate ht ((inputCheck_exact p).mp hi).2.2.1
  have hsplit : codes = (eta ++ [e]) ++ [p.2.2] :=
    he.trans (List.append_assoc eta [e] [p.2.2]).symm
  have hepsilon : epsilon codes = e := by
    rw [epsilon, hsplit, stripLast_append_singleton, lastCode_append_singleton]
  have hretained : retained p codes = p.1 ++ eta := by
    rw [retained, hsplit, stripLast_append_singleton, stripLast_append_singleton]
  exact ⟨eta, e, word, by rw [← he]; exact hc,
    by simpa only [hepsilon] using hw, heout.trans (congrArg (fun xs => xs ++ word) hretained)⟩

/-- Every actual large-h execution has the full literal Definition3.34
form and an independent segmented global tracking certificate. -/
theorem execute_tracking (p : Query) (out : List Nat) (ho : out ∈ execute p) : Tracking out := by
  obtain ⟨hi, codes, hc, ht, word, hw, rfl⟩ := (execute_spec p out).mp ho
  have hs := (inputCheck_exact p).mp hi
  obtain ⟨eta, e, he, hp, hadj⟩ := covering_penultimate ht hs.2.2.1
  have hg := (PublicMts.Support.eligible_exact e p.2.2).mp hadj
  have hreference := covering_global_reference p.1 p.2.1 e (eta ++ [e]) hs.1 hp hg.1
  have hsplit : codes = (eta ++ [e]) ++ [p.2.2] :=
    he.trans (List.append_assoc eta [e] [p.2.2]).symm
  have hepsilon : epsilon codes = e := by
    rw [epsilon, hsplit, stripLast_append_singleton, lastCode_append_singleton]
  have hretained : retained p codes = p.1 ++ eta := by
    rw [retained, hsplit, stripLast_append_singleton, stripLast_append_singleton]
  rw [hepsilon] at hw
  obtain ⟨tail, hword, hone⟩ := SkPublicRecurrence.execute_initial e p.2.2 word hw
  have hbeta : 1 < unionInterpretation p.2.2 :=
    (EpsilonOffsets.epsilon_one_lt
      ((MuPublicDictionary.Support.inputCheck_image _).mp
        ((Infinity.inputCheck_exact _ _).mp hs.2.1).1).2.1).trans hs.2.2.1
  have htracked := SkPublicRecurrence.execute_tracking e p.2.2 word hw hs.2.2.2 hbeta
  rw [hword] at htracked
  have hr : Reference ((p.1 ++ eta) ++ [e]) := by
    simpa only [List.append_assoc] using hreference
  have hglobal := GlobalTrackingSequences.SmallHSupport.global_tracking_splice
    (p.1 ++ eta) e tail hr hg.1 htracked
  simpa only [hretained, hword] using hglobal

theorem execute_trackingCheck (p : Query) (out : List Nat) (ho : out ∈ execute p) :
    trackingCheck out = true := (trackingCheck_exact out).mpr (execute_tracking p out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHLarge
