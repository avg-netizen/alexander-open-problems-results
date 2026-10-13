import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignment
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRawRecurrence

/-!
# Genuine original source-one assignment value fidelity

Original raw principal spellings need not give equal public input tags.
Their actually executed principal logarithms are canonical, so genuine
omega-power injectivity identifies those outputs literally. The real
prefix/factor return codes then agree literally. Thus nonmultiplicative
inputs execute the same child and printed branch; multiplicative leaves
use the genuine original localization word VALUE invariance. The selected
multiplicative endpoint recurrence uses this SAME full assignment procedure.
No raw spelling identity, recursive-word or canonical-input oracle is used.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.ValueInvariance

open AssignmentSupport
open SourceMultiplicativeTracking (rawWord)

theorem multiplicative_transport (c d : Nat)
    (hd : inputCheck d = true) (hv : interpretation 0 c = interpretation 0 d)
    (hm : SourceMultiplicativePrincipal.inputCheck c = true) :
    SourceMultiplicativePrincipal.inputCheck d = true := by
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact c).mp hm
  have ht := (inputCheck_exact d).mp hd
  apply (SourceMultiplicativePrincipal.inputCheck_exact d).mpr
  exact ⟨ht.1, ht.2.1, by simpa only [hv] using hc.2.2⟩

/-- Equal original values identify the actually returned canonical
logarithm, not the two different literal input tags. -/
theorem factor_outputs_eq (c d : Nat) (pair other : Factor.Output)
    (hp : pair ∈ Factor.execute c) (ht : other ∈ Factor.execute d)
    (hv : interpretation 0 c = interpretation 0 d) : pair = other := by
  have hc := (Factor.execute_domain c).mp (Part.dom_iff_mem.mpr ⟨pair, hp⟩)
  have hd := (Factor.execute_domain d).mp (Part.dom_iff_mem.mpr ⟨other, ht⟩)
  rw [Factor.execute, hc, Bool.cond_true] at hp
  rw [Factor.execute, hd, Bool.cond_true] at ht
  obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).mp hp
  obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp ht
  have hsa := PrincipalLogarithm.logarithm_value (Factor.publicCode c) a ha
  have hsb := PrincipalLogarithm.logarithm_value (Factor.publicCode d) b hb
  have htags : unionInterpretation (Factor.publicCode c) =
      unionInterpretation (Factor.publicCode d) := by
    simpa only [Factor.publicCode, unionInterpretation_pair] using hv
  have he : a = b := Canonical.check_value_injective a b hsa.2.2.2.1 hsb.2.2.2.1
    (omegaPower_strictMono.injective (hsa.2.2.2.2.trans (htags.trans hsb.2.2.2.2.symm)))
  subst b
  rfl

/-- A nonmultiplicative equal-valued pair uses literally the same real
factor codes, hence the same executing child and branch output. -/
theorem nonmultiplicative_outputs_eq (c d : Nat) (word other : List Nat)
    (hc : word ∈ execute c) (hd : other ∈ execute d)
    (hv : interpretation 0 c = interpretation 0 d)
    (hm : SourceMultiplicativePrincipal.inputCheck c = false) : word = other := by
  rcases execute_clauses c word hc with ⟨hmc, he⟩ |
    ⟨hmc, prefix, factor, heads, hf, hh, ho⟩
  · rw [hm] at hmc; cases hmc
  · rcases execute_clauses d other hd with ⟨hmd, he⟩ |
      ⟨hmd, prefix', factor', heads', hf', hh', ho'⟩
    · have htrue := multiplicative_transport d c (execute_spec c word hc).1 hv.symm hmd
      rw [hm] at htrue
      cases htrue
    · have heq : (prefix, factor) = (prefix', factor') :=
        factor_outputs_eq c d (prefix, factor) (prefix', factor') hf hf' hv
      have hp : prefix = prefix' := congrArg Prod.fst heq
      have ht : factor = factor' := congrArg Prod.snd heq
      subst prefix'; subst factor'
      have hw : heads = heads' := Part.mem_unique hh hh'
      subst heads'
      exact Part.mem_unique ho ho'

/-- Whole executing words depend on the genuine original ordinal value,
with code spelling retained only where the real source clauses retain it. -/
theorem execute_values_eq (c d : Nat) (word other : List Nat)
    (hc : word ∈ execute c) (hd : other ∈ execute d)
    (hv : interpretation 0 c = interpretation 0 d) :
    word.map (interpretation 0) = other.map (interpretation 0) := by
  cases hm : SourceMultiplicativePrincipal.inputCheck c with
  | false => exact congrArg (List.map (interpretation 0))
      (nonmultiplicative_outputs_eq c d word other hc hd hv hm)
  | true =>
    have hmd := multiplicative_transport c d (execute_spec d other hd).1 hv hm
    have hw : word = rawWord c := Part.mem_unique hc (execute_multiplicative c hm)
    have ht : other = rawWord d := Part.mem_unique hd (execute_multiplicative d hmd)
    rw [hw, ht]
    exact SourceMultiplicativeTracking.Spelling.rawWord_values_eq c d
      (execute_spec c word hc).1 (execute_spec d other hd).1 hv

theorem execute_length_eq (c d : Nat) (word other : List Nat)
    (hc : word ∈ execute c) (hd : other ∈ execute d)
    (hv : interpretation 0 c = interpretation 0 d) : word.length = other.length := by
  simpa only [List.length_map] using congrArg List.length (execute_values_eq c d word other hc hd hv)

/-- The genuine selected endpoint is an original multiplicative caller,
and the complete assignment executes the independent word at that endpoint. -/
theorem multiplicative_selected_recurrence (current : Nat)
    (entry : SourceMultiplicativeTracking.Support.Entry) (word child : List Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true)
    (hs : SourceMultiplicativeTracking.Support.select current
      (SourceMultiplicativeTracking.Support.table
        (SourceMultiplicativeTracking.Prefix.properPrefix (SourceLocalization.RootAdapter.rootCode current))) =
          some entry)
    (ho : word ∈ execute current) (hc : child ∈ execute entry.1) :
    word.map (interpretation 0) = child.map (interpretation 0) ++ [interpretation 0 current] := by
  have hp := SourceMultiplicativeTracking.Recurrence.rawWord_some_spec current entry hm hs
  have hi := (inputCheck_exact entry.1).mp (execute_spec entry.1 child hc).1
  have hmchild : SourceMultiplicativePrincipal.inputCheck entry.1 = true :=
    (SourceMultiplicativePrincipal.inputCheck_exact entry.1).mpr
      ⟨hi.1, hi.2.1, hp.2.1⟩
  have hw : word = rawWord current := Part.mem_unique ho (execute_multiplicative current hm)
  have hcword : child = rawWord entry.1 := Part.mem_unique hc (execute_multiplicative entry.1 hmchild)
  simpa only [hw, hcword] using
    SourceMultiplicativeTracking.RawRecurrence.rawWord_some_values current entry hm hs

/-- The actual selected endpoint supplies its own original multiplicative
guard, so the same full assignment really terminates there. -/
theorem multiplicative_selected_returns (current : Nat)
    (entry : SourceMultiplicativeTracking.Support.Entry)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true)
    (hs : SourceMultiplicativeTracking.Support.select current
      (SourceMultiplicativeTracking.Support.table
        (SourceMultiplicativeTracking.Prefix.properPrefix (SourceLocalization.RootAdapter.rootCode current))) =
          some entry) :
    ∃ child, child ∈ execute entry.1 ∧
      (rawWord current).map (interpretation 0) =
        child.map (interpretation 0) ++ [interpretation 0 current] := by
  have hp := SourceMultiplicativeTracking.Recurrence.rawWord_some_spec current entry hm hs
  obtain ⟨a, he, ht, hn, _⟩ := (rootCheck_exact entry.1).mp hp.1
  have hi : Localization.inputCheck 0 entry.1 = true :=
    (Localization.inputCheck_exact 0 entry.1).mpr ⟨a, he, ht, hn⟩
  have hc := SourceMultiplicativeTracking.node_principal_spec entry.1
    ((Localization.inputCheck_exact 0 entry.1).mp hi)
  have hmul : SourceMultiplicativePrincipal.inputCheck entry.1 = true :=
    (SourceMultiplicativePrincipal.inputCheck_exact entry.1).mpr ⟨hc.1, hc.2.2.2, hp.2.1⟩
  exact ⟨rawWord entry.1, execute_multiplicative entry.1 hmul,
    SourceMultiplicativeTracking.RawRecurrence.rawWord_some_values current entry hm hs⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.ValueInvariance
