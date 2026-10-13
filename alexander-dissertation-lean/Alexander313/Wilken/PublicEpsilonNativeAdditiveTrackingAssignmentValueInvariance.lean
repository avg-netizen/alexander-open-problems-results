import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueSupport
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingSpelling

/-!
# Genuine native assignment is invariant in original input value

Native factoring may retain different written exponent spellings. Its
actual finite ANF prefix has the canonical MNF-prefix value, and the last
factor has the canonical last-factor value. Real conditional replacements
and the rightmost cover scan agree in values at paired actual headwords.
The finite source derivation then identifies the entire independently
executing assignment. No raw or Normal spelling identity, recursive word,
tracker, factorization or cross-source mu is assumed. Uncompiled sources.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.ValueInvariance

open AssignmentSupport AssignmentValueSupport SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open Alexander313.Wilken.MultiplicativeNormalForm

theorem stripLast_values_eq (q : Nat) (xs ys : List Nat)
    (hv : xs.map (interpretation q) = ys.map (interpretation q)) :
    (stripLast xs).map (interpretation q) = (stripLast ys).map (interpretation q) := by
  have he := congrArg (fun vs : List Ordinal.{0} => vs.reverse.tail.reverse) hv
  simpa only [stripLast, List.map_reverse, List.map_tail] using he

theorem lastEligibleCheck_eq (q : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q)) :
    BranchesSupport.lastEligibleCheck q heads = BranchesSupport.lastEligibleCheck q otherHeads := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hh
  have hu := (SourceTrackingRaw.trackingCheck_conditions q otherHeads).mp ht
  have hl := SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation q) heads otherHeads hs.1 hv
  have hr := rawInput_eq q (lastCode heads) (lastCode otherHeads) hs.2.2.1 hu.2.2.1 hl
  have hp := stripLast_values_eq q heads otherHeads hv
  apply Bool.eq_iff_iff.mpr
  change (BranchesSupport.lastEligibleCheck q heads = true) ↔
    BranchesSupport.lastEligibleCheck q otherHeads = true
  rw [BranchesSupport.lastEligibleCheck_exact q heads hh,
    BranchesSupport.lastEligibleCheck_exact q otherHeads ht]
  by_cases hn : stripLast heads = []
  · have hm : stripLast otherHeads = [] := List.map_eq_nil_iff.mp
      (by simpa only [hn, List.map_nil] using hp.symm)
    simp only [hr, if_pos hn, if_pos hm, hl]
  · have hm : stripLast otherHeads ≠ [] := by
      intro he
      exact hn (List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hp))
    have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq
      (interpretation q) (interpretation q) (stripLast heads) (stripLast otherHeads) hn hp
    simp only [hr, if_neg hn, if_neg hm, hl, hlast]

theorem appendCheck_eq (q factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (he : interpretation q factor = interpretation q otherFactor)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q)) :
    BranchesSupport.appendCheck q factor heads = BranchesSupport.appendCheck q otherFactor otherHeads := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hh
  have hu := (SourceTrackingRaw.trackingCheck_conditions q otherHeads).mp ht
  have hl := SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation q) heads otherHeads hs.1 hv
  have hr := coverCheck_eq q (lastCode heads) (lastCode otherHeads) factor otherFactor
    hs.2.2.1 hu.2.2.1 hf hg hl he
  simp only [BranchesSupport.appendCheck, lastEligibleCheck_eq q heads otherHeads hh ht hv, hr]

/-- The computed append flag and the genuine fallback insertion agree
at two actual recursive headwords with equal chronological values. -/
theorem branches_values_eq (q factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode otherHeads))
    (he : interpretation q factor = interpretation q otherFactor)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q))
    (word otherWord : List Nat)
    (hw : word ∈ Branches.execute ((q, factor), heads))
    (ho : otherWord ∈ Branches.execute ((q, otherFactor), otherHeads)) :
    word.map (interpretation q) = otherWord.map (interpretation q) := by
  have hflag := appendCheck_eq q factor otherFactor heads otherHeads hh ht hf hg he hv
  cases ha : BranchesSupport.appendCheck q factor heads with
  | true =>
    have hotherFlag : BranchesSupport.appendCheck q otherFactor otherHeads = true := hflag.symm.trans ha
    have hw : word = heads ++ [factor] := by
      simpa only [Branches.execute, ha, Bool.cond_true, Part.mem_some_iff] using hw
    have ho : otherWord = otherHeads ++ [otherFactor] := by
      simpa only [Branches.execute, hotherFlag, Bool.cond_true, Part.mem_some_iff] using ho
    simp only [hw, ho, List.map_append, List.map_cons, List.map_nil, hv, he]
  | false =>
    have hotherFlag : BranchesSupport.appendCheck q otherFactor otherHeads = false := hflag.symm.trans ha
    have hw : word ∈ Insertion.execute ((q, factor), heads) := by
      simpa only [Branches.execute, ha, Bool.cond_false] using hw
    have ho : otherWord ∈ Insertion.execute ((q, otherFactor), otherHeads) := by
      simpa only [Branches.execute, hotherFlag, Bool.cond_false] using ho
    exact insertion_values_eq q factor otherFactor heads otherHeads hh ht hf hg hm hb hc he hv word otherWord hw ho

theorem multiplicative_transport (q c d : Nat)
    (hd : inputCheck q d = true) (hv : interpretation q c = interpretation q d)
    (hm : SourceMultiplicativePrincipal.inputCheck q c = true) :
    SourceMultiplicativePrincipal.inputCheck q d = true := by
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact q c).mp hm
  have ht := (inputCheck_exact q d).mp hd
  exact (SourceMultiplicativePrincipal.inputCheck_exact q d).mpr
    ⟨ht.1, ht.2.1, by simpa only [hv] using hc.2.2⟩

theorem singleton_transport (q c d : Nat)
    (hd : inputCheck q d = true) (hv : interpretation q c = interpretation q d)
    (hs : Factor.singletonCheck q c = true) : Factor.singletonCheck q d = true := by
  have hc := (Factor.singletonCheck_exact q c).mp hs
  have ht := (inputCheck_exact q d).mp hd
  apply (Factor.singletonCheck_exact q d).mpr
  exact ⟨ht.1, ht.2.1, ht.2.2, by simpa only [hv] using hc.2.2.2.1,
    by simpa only [hv] using hc.2.2.2.2⟩

/-- The actual finite ANF prefix has its genuine canonical MNF-prefix
value; different native logarithm spellings are not identified. -/
theorem factor_prefix_value (q c : Nat) (pair : Factor.Output) (hp : pair ∈ Factor.execute q c) :
    interpretation q pair.1 = factorProduct (factorPrefix (canonicalMNF (interpretation q c))) := by
  have hc := (Factor.execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨pair, hp⟩)
  have hi := (Factor.splitCheck_exact q c).mp hc
  have hq := (HeightBoundary.input_spec q c hi.1).2.1
  have hpos := (base_pos q hq).trans_le hi.2.1
  rw [Factor.execute, hc, Bool.cond_true] at hp
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hp
  have hs := LogEnd.execute_spec q c d hd
  have hlog : Ordinal.omega0 ^ interpretation q d = interpretation q c := by
    have he : Ordinal.omega0 ^ interpretation q d = Hereditary.LogEnd.endValue (interpretation q c) := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hpos), Hereditary.LogEnd.endValue]
        using hs.2.2.2
    exact he.trans (SourceChi.Powers.endValue_principal _ hpos hi.2.2.1)
  have hword : omegaFactors (interpretation q d) = canonicalMNF (interpretation q c) := by
    rw [← hlog, canonicalMNF_omegaPower]
  have hp := FactorSupport.prefixCode_spec q d hs.2.1 hs.2.2.1
  simpa only [hword] using hp.2.2

theorem factor_values_eq (q c d : Nat) (pair other : Factor.Output)
    (hp : pair ∈ Factor.execute q c) (ht : other ∈ Factor.execute q d)
    (hv : interpretation q c = interpretation q d) :
    interpretation q pair.1 = interpretation q other.1 ∧
      interpretation q pair.2 = interpretation q other.2 := by
  constructor
  · rw [factor_prefix_value q c pair hp, factor_prefix_value q d other ht, hv]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlast, _⟩ := Factor.execute_spec q c pair hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hother, _⟩ := Factor.execute_spec q d other ht
    rw [hlast, hother, hv]

/-- Real finite source-clause induction compares the independently
executing child and its actual branch. Every tracker and factor-to-final
caller follows from the proved child and factor invariants. -/
theorem derivation_values_eq (q c : Nat) (word : List Nat)
    (hd : Derivation q c word) (d : Nat) (other : List Nat)
    (ho : other ∈ execute q d) (hv : interpretation q c = interpretation q d) :
    word.map (interpretation q) = other.map (interpretation q) := by
  induction hd generalizing d other with
  | multiplicative c hm =>
    have hi := (execute_spec q d other ho).1
    have hm' := multiplicative_transport q c d hi hv hm
    have hout : other = SourceMultiplicativeTracking.rawWord q d :=
      Part.mem_unique ho (execute_multiplicative q d hm')
    rw [hout]
    have hc := (SourceMultiplicativePrincipal.inputCheck_exact q c).mp hm
    have hinput : inputCheck q c = true :=
      (inputCheck_exact q c).mpr ⟨hc.1, hc.2.1, hc.2.2.2.1⟩
    exact SourceMultiplicativeTracking.Spelling.rawWord_values_eq q c d hinput hi hv
  | singleton c hm hs =>
    have hi := (execute_spec q d other ho).1
    have hm' : SourceMultiplicativePrincipal.inputCheck q d = false := Bool.eq_false_of_not_eq_true (by
      intro ht
      have hc := derivation_input q c [c] (.singleton c hm hs)
      have hf := multiplicative_transport q d c hc hv.symm ht
      rw [hm] at hf
      cases hf)
    have hs' := singleton_transport q c d hi hv hs
    have hout : other = [d] := Part.mem_unique ho (execute_singleton q d hm' hs')
    simp only [hout, List.map_cons, List.map_nil, hv]
  | split c prefix factor heads word hf hd hw ih =>
    have hi := derivation_input q c word (.split c prefix factor heads word hf hd hw)
    have ht := (execute_spec q d other ho).1
    have flags := split_flags q c prefix factor hf
    rcases execute_clauses q d other ho with ⟨hm, hout⟩ |
      ⟨hm, hs, hout⟩ | ⟨hm, hs, prefix', factor', heads', hf', hh', hw'⟩
    · have he := multiplicative_transport q d c hi hv.symm hm
      rw [flags.1] at he
      cases he
    · have he := singleton_transport q d c hi hv.symm hs
      rw [flags.2] at he
      cases he
    · have values := factor_values_eq q c d (prefix, factor) (prefix', factor') hf hf' hv
      have child : heads ∈ execute q prefix := (execute_iff_derivation q prefix heads).mpr hd
      have hwords := ih prefix' heads' hh' values.1
      have hleft := execute_spec q prefix heads child
      have hright := execute_spec q prefix' heads' hh'
      obtain ⟨_, _, _, hl, _, _, _, _, hmFactor, _, _, _, _⟩ := Factor.execute_spec q c (prefix, factor) hf
      obtain ⟨_, _, _, hl', _, _, _, _, _, _, _, _, _⟩ := Factor.execute_spec q d (prefix', factor') hf'
      have hb : interpretation q factor ≤ interpretation q (lastCode heads) :=
        (Factor.Bounds.execute_last_le_prefix_last q c (prefix, factor) hf).trans hleft.2.1.2.2.1
      have hb' : interpretation q factor' ≤ interpretation q (lastCode heads') :=
        (Factor.Bounds.execute_last_le_prefix_last q d (prefix', factor') hf').trans hright.2.1.2.2.1
      exact branches_values_eq q factor factor' heads heads' hleft.2.1.1 hright.2.1.1
        hl hl' hmFactor hb hb' values.2 hwords word other hw hw'

theorem execute_values_eq (q c d : Nat) (word other : List Nat)
    (hc : word ∈ execute q c) (hd : other ∈ execute q d)
    (hv : interpretation q c = interpretation q d) :
    word.map (interpretation q) = other.map (interpretation q) :=
  derivation_values_eq q c word ((execute_iff_derivation q c word).mp hc) d other hd hv

theorem execute_length_eq (q c d : Nat) (word other : List Nat)
    (hc : word ∈ execute q c) (hd : other ∈ execute q d)
    (hv : interpretation q c = interpretation q d) : word.length = other.length := by
  simpa only [List.length_map] using congrArg List.length (execute_values_eq q c d word other hc hd hv)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.ValueInvariance
