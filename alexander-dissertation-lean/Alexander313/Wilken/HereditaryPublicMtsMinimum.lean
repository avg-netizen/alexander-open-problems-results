import Alexander313.Wilken.HereditaryPublicMtsMinimumSupport

/-!
# Actual least-predecessor mts has minimum covering length

Induction over an independent covering bounds the actual mts word at every
target no larger than that covering's final value. When the target passes
the previous final value, that previous row genuinely covers it. The first
passing row is no later, and its independently executing subquery satisfies
the induction bound. Thus the emitted covering is shortest among all genuine
coverings, without an assigned cost table. Lexicographic maximality and
uniqueness among all shortest coverings remain separate. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Minimum

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)
open MinimumSupport

/-- The strengthened induction compares every real executing target below
the current covering value, rather than assuming monotonic minimum costs. -/
theorem execute_length_le_covering_bound {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) (beta : Nat) (out : List Nat)
    (ho : out ∈ execute gamma beta)
    (hbound : unionInterpretation beta ≤ unionInterpretation current) : out.length ≤ codes.length := by
  revert beta out
  induction hc with
  | root hg =>
    intro beta out ho hbound
    have hs := (inputCheck_exact gamma beta).mp (execute_spec gamma beta out ho).1
    have he : beta = gamma := Canonical.check_value_injective beta gamma hs.2.1
      ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
      (le_antisymm hbound hs.2.2.2.2.1)
    subst beta
    simpa only [execute_base gamma out ho] using
      (le_rfl : [gamma].length ≤ [gamma].length)
  | append previous current codes hp hedge ih =>
    intro beta out ho hbound
    by_cases hprevious : unionInterpretation beta ≤ unionInterpretation previous
    · have hh := ih beta out ho hprevious
      simp only [List.length_append, List.length_singleton]
      omega
    · have hgt : unionInterpretation previous < unionInterpretation beta := lt_of_not_ge hprevious
      have hfloor : unionInterpretation gamma ≤ unionInterpretation previous := by
        rcases ReachBound.covering_root_or_lt hp with rfl | hlt
        · exact le_rfl
        · exact hlt.le
      have hstrict := hfloor.trans_lt hgt
      obtain ⟨hi, d, hd, hout⟩ := execute_spec gamma beta out ho
      have he := (Support.eligible_exact previous current).mp hedge
      have hpass : PublicTrackingSequences.adjacencyCheck previous beta = true :=
        (Support.eligible_exact previous beta).mpr
          ⟨he.1, ((inputCheck_exact gamma beta).mp hi).2.1, hgt, hbound.trans he.2.2.2⟩
      have hcover := Covering.append previous beta codes hp hpass
      have hsub := CoveringLocalization.covering_sublist gamma beta d (codes ++ [beta])
        hcover hi hd hstrict
      have hpreviousMem : previous ∈ codes := by
        simpa only [hp.last] using SourceTrackingSequences.lastCode_mem codes hp.nonempty
      have hmember : previous ∈ localization gamma d :=
        hsub.subset (List.mem_append.mpr (Or.inl hpreviousMem))
      obtain ⟨before, hlocal, htail⟩ := localization_split gamma beta d hi hd hstrict
      have hbefore : previous ∈ gamma :: before := by
        rw [hlocal] at hmember
        rcases List.mem_append.mp hmember with hm | hm
        · exact hm
        · exact False.elim (hgt.ne (congrArg unionInterpretation (List.mem_singleton.mp hm)))
      have htableMem : previous ∈ (Support.table gamma before).map Prod.fst := by
        rw [Support.table_codes]
        exact hbefore
      obtain ⟨candidate, hcandidate, hcode⟩ := List.mem_map.mp htableMem
      have hcandidatePass : PublicTrackingSequences.adjacencyCheck candidate.1 beta = true := by
        simpa only [hcode] using hpass
      obtain ⟨selected, hs⟩ := CoveringSupport.select_exists beta (Support.table gamma before)
        ⟨previous, htableMem, hpass⟩
      have hselected := Support.select_mem beta _ selected hs
      have htableStrict : (((Support.table gamma before).map Prod.fst).map
          unionInterpretation).Pairwise (· < ·) := by
        have ht := localization_strict gamma beta d hi hd
        rw [hlocal, List.map_append] at ht
        rw [Support.table_codes]
        exact (List.pairwise_append.mp ht).1
      have hselectedBound : unionInterpretation selected.1 ≤ unionInterpretation previous := by
        simpa only [hcode] using select_le_passing beta _ selected candidate
          hs hcandidate hcandidatePass htableStrict
      have hentry : selected ∈ Support.table gamma (localization gamma d).tail := by
        rw [htail, Support.table_append_singleton]
        exact List.mem_append.mpr (Or.inl hselected)
      have hchild := entry_execution gamma beta d selected hi hd hentry
      have hlength := ih selected.1 selected.2 hchild hselectedBound
      have hw : out = selected.2 ++ [beta] := by
        rw [htail, Support.word_append, Support.extend_some gamma beta _ selected hs] at hout
        exact hout
      simp only [hw, List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hlength 1

theorem execute_length_le_covering (gamma beta : Nat) (out codes : List Nat)
    (ho : out ∈ execute gamma beta) (hc : Covering gamma beta codes) :
    out.length ≤ codes.length := execute_length_le_covering_bound hc beta out ho le_rfl

/-- Any independently executing full-domain word is no longer than any
genuine covering of its target; existence derives the needed OWN guard. -/
theorem infinity_execute_length_le_covering (gamma beta : Nat) (out codes : List Nat)
    (ho : out ∈ Infinity.execute gamma beta) (hc : Covering gamma beta codes) :
    out.length ≤ codes.length := by
  have hi := (Infinity.execute_spec gamma beta out ho).1
  have hj := InfinityHat.own_input_of_cut gamma beta hi (ReachBound.covering_lt_own hc)
  have hs : out ∈ execute gamma beta := by
    rw [← Infinity.execute_eq_own gamma beta hj]
    exact ho
  exact execute_length_le_covering gamma beta out codes hs hc

theorem infinity_execute_base (gamma : Nat) (out : List Nat)
    (ho : out ∈ Infinity.execute gamma gamma) : out = [gamma] := by
  have hg := ((Infinity.inputCheck_exact gamma gamma).mp
    (Infinity.execute_spec gamma gamma out ho).1).1
  have hi := (execute_spec gamma gamma [gamma] (base_execution gamma hg)).1
  have hs : out ∈ execute gamma gamma := by
    rw [← Infinity.execute_eq_own gamma gamma hi]
    exact ho
  exact execute_base gamma out hs

/-- Source3.27 minimum length is attained by the independently executing
mts covering whenever any covering reaches the represented target,
including the genuine reflexive root singleton. -/
theorem infinity_execute_shortest (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ Infinity.execute gamma beta)
    (hr : ∃ codes, Covering gamma beta codes) :
    Covering gamma beta out ∧ ∀ codes, Covering gamma beta codes → out.length ≤ codes.length := by
  have hs := (Infinity.inputCheck_exact gamma beta).mp (Infinity.execute_spec gamma beta out ho).1
  have hc : Covering gamma beta out := by
    by_cases he : unionInterpretation gamma = unionInterpretation beta
    · have hcode : beta = gamma := Canonical.check_value_injective beta gamma hs.2.1
        ((MuPublicDictionary.Support.inputCheck_image gamma).mp hs.1).1 he.symm
      subst beta
      simpa only [infinity_execute_base gamma out ho] using Covering.root hs.1
    · have hlt := lt_of_le_of_ne hs.2.2.2.2.1 he
      exact (Reach.infinity_execute_covering_iff_reachable gamma beta out ho hlt).mpr hr
  exact ⟨hc, fun codes hcodes => infinity_execute_length_le_covering gamma beta out codes ho hcodes⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Minimum
