import Alexander313.Wilken.HereditaryPublicTrackingErasure

/-!
# Actual public small-cutoff branches of the auxiliary h sequence

The genuine reference prefix and its last proper epsilon derive every
independent public mu/sk caller. The computed mu-cover flag selects the
actual prefix plus sk word, or leaves the original reference unchanged.
Both printed beta-at-most-gamma branches3.34 have real partial recursive
execution and independent tracking certificates for the printed M cutoff.
The beta-above-gamma branch needs the genuine mts producer and is separate.
No tracking assignment, output certificate or evaluation is supplied.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicHSmall

open PublicTrackingSequences
open SkPublicRecurrence (muValue mu_input_canonical mu_input_epsilon)
open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

/-- A genuine nonempty reference is itself a tracking sequence, using
its last epsilon as the real final principal entry. -/
theorem reference_tracking_or_empty {xs : List Nat} (hr : Reference xs) :
    xs = [] ∨ Tracking xs := by
  induction hr with
  | nil => exact Or.inl rfl
  | one a ha =>
    have he := mu_input_epsilon a ha
    have hb := EpsilonOffsets.epsilon_one_lt he
    have hp : Ordinal.IsPrincipal (· + ·) (unionInterpretation a) := by
      rw [← he]
      exact Ordinal.isPrincipal_add_omega0_opow _
    exact Or.inr (singleton_tracking a (mu_input_canonical a ha)
      (zero_lt_one.trans hb) hp hb.le)
  | cons a b xs ha hab hcover ht ih =>
    rcases ih with he | hs
    · cases he
    · exact Or.inr (tracking_prepend a b xs ha hab hcover
        (EpsilonOffsets.epsilon_one_lt (mu_input_epsilon b (ht.nodes b List.mem_cons_self))) hs)

theorem reference_tracking {xs : List Nat} (hr : Reference xs) (hne : xs ≠ []) : Tracking xs :=
  (reference_tracking_or_empty hr).resolve_left hne

/-- The original reference prefix already supplies the actual covering
edges needed to attach an independently executing sk tracker at its last epsilon. -/
theorem reference_tracking_splice (prefix : List Nat) (gamma : Nat) (tail : List Nat)
    (hr : Reference (prefix ++ [gamma])) (ht : Tracking (gamma :: tail)) :
    Tracking (prefix ++ gamma :: tail) := by
  induction prefix generalizing gamma tail with
  | nil => simpa only [List.nil_append] using ht
  | cons a rest ih =>
    cases rest with
    | nil =>
      change Reference [a, gamma] at hr
      cases hr with
      | cons a b xs ha hab hcover href =>
        exact tracking_prepend a gamma tail ha hab hcover
          (EpsilonOffsets.epsilon_one_lt (mu_input_epsilon gamma (href.nodes gamma List.mem_cons_self))) ht
    | cons b rest =>
      change Reference (a :: b :: (rest ++ [gamma])) at hr
      cases hr with
      | cons a b xs ha hab hcover href =>
        have htracked := ih gamma tail href ht
        exact tracking_prepend a b (rest ++ gamma :: tail) ha hab hcover
          (EpsilonOffsets.epsilon_one_lt (mu_input_epsilon b (href.nodes b List.mem_cons_self))) htracked

abbrev Query := List Nat × (Nat × Nat)

def inputCheck (p : Query) : Bool := referenceCheck (p.1 ++ [p.2.1]) &&
  (Canonical.check p.2.2 && !(Canonical.less p.2.1 p.2.2))

theorem inputCheck_primrec : Primrec inputCheck := by
  have hgamma := Primrec.fst.comp Primrec.snd
  have hcut := Primrec.snd.comp Primrec.snd
  have hword := Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp hgamma (Primrec.const []))
  exact Primrec.and.comp (referenceCheck_primrec.comp hword)
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp hcut)
      (Primrec.not.comp (Canonical.Effective.less_primrec.comp hgamma hcut)))

theorem inputCheck_exact (p : Query) : inputCheck p = true ↔
    Reference (p.1 ++ [p.2.1]) ∧ Canonical.check p.2.2 = true ∧
      unionInterpretation p.2.2 ≤ unionInterpretation p.2.1 := by
  rw [inputCheck, Bool.and_eq_true, Bool.and_eq_true, referenceCheck_exact]
  constructor
  · rintro ⟨hr, hc, hb⟩
    have hg := mu_input_canonical _ (hr.nodes _ (List.mem_append.mpr (Or.inr List.mem_cons_self)))
    exact ⟨hr, hc, (canonical_not_less_exact _ _ hg hc).mp hb⟩
  · rintro ⟨hr, hc, hb⟩
    have hg := mu_input_canonical _ (hr.nodes _ (List.mem_append.mpr (Or.inr List.mem_cons_self)))
    exact ⟨hr, hc, (canonical_not_less_exact _ _ hg hc).mpr hb⟩

theorem sk_caller (p : Query) (hi : inputCheck p = true) :
    SkPublicDictionary.Support.inputCheck p.2.1 p.2.2 = true := by
  have hs := (inputCheck_exact p).mp hi
  have ha := hs.1.nodes _ (List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hg := (MuPublicDictionary.Support.inputCheck_image _).mp ha
  exact (SkPublicDictionary.UpsilonDomain.inputCheck_exact _ _).mpr
    ⟨hg.1, hg.2.1, hg.2.2, Canonical.check_original hs.2.1⟩

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
  exact Partrec.cond inputCheck_primrec.to_comp (Partrec.cond hc.to_comp hs hw.to_comp.partrec) Partrec.none

/-- Every genuine small-cutoff caller has an actual terminating output;
the covering branch invokes the independently terminating sk producer. -/
theorem execute_returns (p : Query) (hi : inputCheck p = true) : ∃ codes, codes ∈ execute p := by
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

/-- Exact executing source3.34 beta-at-most-gamma clauses: computed public
mu cover selects the real prefix-plus-sk output; failure leaves the genuine
original reference literally unchanged. -/
theorem execute_clauses (p : Query) (out : List Nat) : out ∈ execute p ↔ inputCheck p = true ∧
    ((unionInterpretation p.2.2 ≤ muValue p.2.1 ∧
        ∃ codes, codes ∈ SkPublicDictionary.execute p.2 ∧ out = p.1 ++ codes) ∨
      (muValue p.2.1 < unionInterpretation p.2.2 ∧ out = p.1 ++ [p.2.1])) := by
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
      have ha := hs.1.nodes _ (List.mem_append.mpr (Or.inr List.mem_cons_self))
      have hb : ¬ unionInterpretation p.2.2 ≤ muValue p.2.1 := by
        intro hb
        have ht := (coverCheck_exact _ _).mpr ⟨ha, hs.2.1, hb⟩
        rw [hc] at ht
        cases ht
      have he : out = p.1 ++ [p.2.1] := by
        simpa only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using ho
      exact Or.inr ⟨lt_of_not_ge hb, he⟩
  · rintro ⟨hi, ⟨hcover, codes, hm, rfl⟩ | ⟨hfail, rfl⟩⟩
    · have hs := (inputCheck_exact p).mp hi
      have ha := hs.1.nodes _ (List.mem_append.mpr (Or.inr List.mem_cons_self))
      have hc := (coverCheck_exact _ _).mpr ⟨ha, hs.2.1, hcover⟩
      simpa only [execute, hi, hc, Bool.cond_true] using Part.mem_map (fun codes => p.1 ++ codes) hm
    · have hc : coverCheck p.2.1 p.2.2 = false := Bool.eq_false_of_not_eq_true (by
        intro ht
        exact hfail.not_ge ((coverCheck_exact _ _).mp ht).2.2)
      simp only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff]

/-- The computed small h sequence has a genuine independent relative
tracking certificate on precisely the printed multiplicative cutoff domain. -/
theorem execute_tracking (p : Query) (out : List Nat) (ho : out ∈ execute p)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hone : 1 < unionInterpretation p.2.2) : trackingCheck out = true := by
  have hs := (execute_clauses p out).mp ho
  have hr := (inputCheck_exact p).mp hs.1
  apply (trackingCheck_exact _).mpr
  rcases hs.2 with ⟨hc, codes, hcodes, rfl⟩ | ⟨hc, rfl⟩
  · obtain ⟨tail, he, _⟩ := SkPublicRecurrence.execute_initial _ _ codes hcodes
    have ht := SkPublicRecurrence.execute_tracking _ _ codes hcodes hm hone
    rw [he] at ht ⊢
    exact reference_tracking_splice _ _ _ hr.1 ht
  · exact reference_tracking hr.1 (by simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, not_false_eq_true])

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicHSmall
