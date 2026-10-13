import Alexander313.Wilken.PublicEpsilonNativeSkPublicValueInvariance

/-!
# Executing sk from original RAW epsilon spellings

The actual original RAW LOW epsilon checker constructs its genuine HIGH
root atom. The terminating native loop and original-source return then
produce the entire finite original-source recurrence and canonical public
word. The unchanged original raw initial value and both maximal stops are
derived. Equal SAME-source raw root and public cutoff values yield literally
equal canonical public words. No input Normality, representative, endpoint,
cross-source/global dictionary assignment, Par or evaluation is supplied.
The tracking conclusion retains the printed multiplicative cutoff M>1.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkRaw

abbrev Query := SkNextSearch.Support.Query

def inputCheck (q raw cutoff : Nat) : Bool :=
  SourceTrackingRaw.Support.inputCheck q raw && unionCheck cutoff

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Primrec.comp SourceTrackingRaw.Support.inputCheck_primrec Primrec.fst)
    (Canonical.Effective.unionCheck_primrec.comp Primrec.snd)

/-- The actual finite domain is every original RAW LOW epsilon strictly
above the literal source base and every admitted public cutoff spelling. -/
theorem inputCheck_exact (q raw cutoff : Nat) : inputCheck q raw cutoff = true ↔
    lowCheckCode q raw = true ∧ base q < interpretation q raw ∧
      Ordinal.omega0 ^ interpretation q raw = interpretation q raw ∧ unionCheck cutoff = true := by
  rw [inputCheck, Bool.and_eq_true, SourceTrackingRaw.Support.inputCheck_exact]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
    fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def rootQuery (p : Query) : Query :=
  ((p.1.1, SourceTrackingRaw.Support.rootCode p.1.1 p.1.2), p.2)

theorem rootQuery_primrec : Primrec rootQuery :=
  ((Primrec.fst.comp Primrec.fst).pair
    (Primrec.comp SourceTrackingRaw.Support.rootCode_primrec Primrec.fst)).pair Primrec.snd

theorem root_caller (q raw cutoff : Nat) (hi : inputCheck q raw cutoff = true) :
    SkIteration.inputCheck q (SourceTrackingRaw.Support.rootCode q raw) cutoff = true := by
  obtain ⟨hr, hc⟩ := Bool.and_eq_true.mp hi
  exact (SkIteration.inputCheck_exact _ _ _).mpr
    ⟨(SourceTrackingRaw.Support.rootCode_spec q raw hr).2.1, hc⟩

def executeSource (p : Query) : Part (List Nat) := cond (inputCheck p.1.1 p.1.2 p.2)
  (SkSourceWord.execute (rootQuery p)) Part.none

theorem executeSource_partrec : Partrec executeSource :=
  Partrec.cond inputCheck_primrec.to_comp
    (SkSourceWord.execute_partrec.comp rootQuery_primrec.to_comp) Partrec.none

theorem executeSource_domain (q raw cutoff : Nat) : (executeSource ((q, raw), cutoff)).Dom ↔
    inputCheck q raw cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck q raw cutoff with
    | true => rfl
    | false =>
      have hx : (Part.none : Part (List Nat)).Dom := by
        simpa only [executeSource, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
  · intro hi
    have hd := (SkSourceWord.execute_domain _ _ _).mpr (root_caller q raw cutoff hi)
    simpa only [executeSource, hi, Bool.cond_true, rootQuery] using hd

theorem executeSource_returns (q raw cutoff : Nat) (hi : inputCheck q raw cutoff = true) :
    ∃ codes, codes ∈ executeSource ((q, raw), cutoff) :=
  Part.dom_iff_mem.mp ((executeSource_domain q raw cutoff).mpr hi)

theorem executeSource_member (q raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executeSource ((q, raw), cutoff)) :
    inputCheck q raw cutoff = true ∧
      codes ∈ SkSourceWord.execute ((q, SourceTrackingRaw.Support.rootCode q raw), cutoff) := by
  have hi := (executeSource_domain q raw cutoff).mp (Part.dom_iff_mem.mpr ⟨codes, ho⟩)
  exact ⟨hi, by simpa only [executeSource, hi, Bool.cond_true, rootQuery] using ho⟩

/-- Actual execution constructs the complete original-source recurrence,
original raw initial value and literal maximal final position. -/
theorem executeSource_spec (q raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executeSource ((q, raw), cutoff)) :
    inputCheck q raw cutoff = true ∧
      (∀ d ∈ codes, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) ∧
      SkSourceRecurrence.SourcePath q cutoff codes ∧ ∃ a xs, codes = a :: xs ∧
        interpretation q a = interpretation q raw ∧ 1 < interpretation q a ∧
        ∃ before final, codes = before ++ [final] ∧ SkSourceRecurrence.Terminal q cutoff final := by
  obtain ⟨hi, hm⟩ := executeSource_member q raw cutoff codes ho
  have hs := SkSourceRecurrence.execute_spec q _ cutoff codes hm
  have hv := (SourceTrackingRaw.Support.rootCode_spec q raw (Bool.and_eq_true.mp hi).1).2.2
  obtain ⟨a, xs, hcodes, hvalue, hpos, hterminal⟩ := hs.2
  exact ⟨hi, (SkSourceWord.execute_spec q _ cutoff codes hm).2.1, hs.1,
    a, xs, hcodes, hvalue.trans hv, hpos, hterminal⟩

theorem executeSource_tracking (q raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executeSource ((q, raw), cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hp : 1 < unionInterpretation cutoff) : SourceTrackingRaw.trackingCheck q codes = true :=
  SkTracking.execute_tracking q _ cutoff codes (executeSource_member q raw cutoff codes ho).2 hm hp

def executePublic (p : Query) : Part (List Nat) := cond (inputCheck p.1.1 p.1.2 p.2)
  (SkSourceWord.executePublic (rootQuery p)) Part.none

theorem executePublic_partrec : Partrec executePublic :=
  Partrec.cond inputCheck_primrec.to_comp
    (SkSourceWord.executePublic_partrec.comp rootQuery_primrec.to_comp) Partrec.none

theorem executePublic_domain (q raw cutoff : Nat) : (executePublic ((q, raw), cutoff)).Dom ↔
    inputCheck q raw cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck q raw cutoff with
    | true => rfl
    | false =>
      have hx : (Part.none : Part (List Nat)).Dom := by
        simpa only [executePublic, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
  · intro hi
    have hd := (SkSourceWord.executePublic_domain _ _ _).mpr (root_caller q raw cutoff hi)
    simpa only [executePublic, hi, Bool.cond_true, rootQuery] using hd

theorem executePublic_member (q raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executePublic ((q, raw), cutoff)) :
    inputCheck q raw cutoff = true ∧
      codes ∈ SkSourceWord.executePublic ((q, SourceTrackingRaw.Support.rootCode q raw), cutoff) := by
  have hi := (executePublic_domain q raw cutoff).mp (Part.dom_iff_mem.mpr ⟨codes, ho⟩)
  exact ⟨hi, by simpa only [executePublic, hi, Bool.cond_true, rootQuery] using ho⟩

theorem executePublic_returns (q raw cutoff : Nat) (hi : inputCheck q raw cutoff = true) :
    ∃ codes, codes ∈ executePublic ((q, raw), cutoff) :=
  Part.dom_iff_mem.mp ((executePublic_domain q raw cutoff).mpr hi)

theorem public_source_values (q raw cutoff : Nat) (public source : List Nat)
    (hp : public ∈ executePublic ((q, raw), cutoff))
    (hs : source ∈ executeSource ((q, raw), cutoff)) :
    public.map unionInterpretation = source.map (interpretation q) :=
  SkPublicValueInvariance.public_source_values q _ cutoff public source
    (executePublic_member q raw cutoff public hp).2 (executeSource_member q raw cutoff source hs).2

theorem executePublic_canonical (q raw cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ executePublic ((q, raw), cutoff)) :
    ∀ d ∈ codes, Canonical.check d = true :=
  (SkSourceWord.executePublic_spec q _ cutoff codes (executePublic_member q raw cutoff codes ho).2).2.1

/-- Equal original RAW root and cutoff values at the SAME literal source
give literally identical entire executing canonical public words. -/
theorem executePublic_eq (q raw other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ executePublic ((q, raw), cutoff))
    (ht : otherCodes ∈ executePublic ((q, other), otherCutoff))
    (hv : interpretation q raw = interpretation q other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : codes = otherCodes := by
  obtain ⟨hi, hm⟩ := executePublic_member q raw cutoff codes ho
  obtain ⟨hj, hn⟩ := executePublic_member q other otherCutoff otherCodes ht
  have hr := (SourceTrackingRaw.Support.rootCode_spec q raw (Bool.and_eq_true.mp hi).1).2.2
  have hs := (SourceTrackingRaw.Support.rootCode_spec q other (Bool.and_eq_true.mp hj).1).2.2
  exact SkPublicValueInvariance.executePublic_eq q _ _ cutoff otherCutoff codes otherCodes hm hn
    (hr.trans (hv.trans hs.symm)) hcut

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkRaw
