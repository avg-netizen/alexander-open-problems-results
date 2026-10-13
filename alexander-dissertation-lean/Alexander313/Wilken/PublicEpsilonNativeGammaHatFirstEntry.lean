import Alexander313.Wilken.PublicEpsilonNativeGammaHat
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance

/-!
# The genuine first-entry criterion below the singleton boundary

Every FIRST of an actually executing multiplicative word is itself a real
singleton execution of the same assignment. A FIRST above the original mu
therefore supplies an actual candidate for the least singleton boundary.
Conversely the independently executing singleton at that boundary and the
actual strict M-word order force every word at or above it to start above
mu. This proves the first-entry comparison in Lemma3.32 on the original
finite native domain. No mts construction, executing minimum, global mu
identification, large h or evaluation is claimed. Source-only uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHat.FirstEntry

open SourceTrackingSequences

/-- Actual M execution retains its literal final input, so a singleton
VALUE word is already a literal singleton at that input. -/
theorem execute_singleton_of_values (q c : Nat) (out : List Nat)
    (hc : SourceMultiplicativePrincipal.inputCheck q c = true)
    (ho : out ∈ SourceAdditiveTracking.Assignment.execute q c)
    (hv : out.map (interpretation q) = [interpretation q c]) : out = [c] := by
  have hlast := (SourceAdditiveTracking.MultiplicativePrefix.execute_multiplicative_prefix
    q c out hc ho).1
  obtain ⟨d, hd, hvalue⟩ := List.map_eq_singleton_iff.mp hv
  have he : d = c := by simpa only [hd, lastCode_singleton] using hlast
  simpa only [he] using hd

/-- The actual prefix theorem supplies an independent execution at FIRST;
its singleton VALUES and literal final input give a genuine singleton. -/
theorem execute_first_singleton (q c first : Nat) (tail : List Nat)
    (hc : SourceMultiplicativePrincipal.inputCheck q c = true)
    (ho : first :: tail ∈ SourceAdditiveTracking.Assignment.execute q c) :
    SourceMultiplicativePrincipal.inputCheck q first = true ∧
      [first] ∈ SourceAdditiveTracking.Assignment.execute q first := by
  have hp := (SourceAdditiveTracking.MultiplicativePrefix.execute_multiplicative_prefix
    q c (first :: tail) hc ho).2 [] first tail (by simp only [List.nil_append])
  obtain ⟨hf, out, hout, hv⟩ := hp
  have hv : out.map (interpretation q) = [interpretation q first] := by
    simpa only [List.nil_append, List.map_singleton] using hv
  have he := execute_singleton_of_values q first out hf hout hv
  exact ⟨hf, by simpa only [he] using hout⟩

/-- At an input strictly above the original root, FIRST is strictly above
that root: it is either the unchanged final input or a genuine HIGH node. -/
theorem execute_first_gt_root (q root c first : Nat) (tail : List Nat)
    (ha : rootCheck q root = true)
    (hc : SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true)
    (ho : first :: tail ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c)
    (hlt : interpretation q root < interpretation (betaCode q root) c) :
    interpretation q root < interpretation (betaCode q root) first := by
  have he : first :: tail = SourceMultiplicativeTracking.rawWord (betaCode q root) c :=
    Part.mem_unique ho (SourceAdditiveTracking.Assignment.execute_multiplicative _ c hc)
  have hm : first ∈ SourceMultiplicativeTracking.rawWord (betaCode q root) c := by
    rw [← he]
    exact List.mem_cons_self
  rcases SourceAdditiveTracking.ReplacementSupport.rawWord_member _ c first hm with hlast | hp
  · simpa only [hlast] using hlt
  · have hhigh := SourceMultiplicativeTracking.properPrefix_roots _ _
      (SourceMultiplicativePrincipal.rootInput _ c hc) first hp
    simpa only [beta_base q root ha] using Mu.root_base_lt _ first hhigh

/-- A real FIRST above mu is a candidate, hence bounds the genuine least
singleton boundary from above. Its value also lies below the actual input. -/
theorem first_above_mu_candidate (q root c first : Nat) (tail : List Nat)
    (ha : rootCheck q root = true)
    (hc : SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true)
    (ho : first :: tail ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c)
    (hlt : interpretation q root < interpretation (betaCode q root) c)
    (hmu : Mu.sourceValue q root < interpretation (betaCode q root) first) :
    interpretation (betaCode q root) first ∈ CandidateValues q root ∧
      value q root ha ≤ interpretation (betaCode q root) first ∧
        interpretation (betaCode q root) first ≤ interpretation (betaCode q root) c := by
  have hs := execute_first_singleton _ c first tail hc ho
  have hcandidate : interpretation (betaCode q root) first ∈ CandidateValues q root :=
    ⟨first, hs.1, rfl, execute_first_gt_root q root c first tail ha hc ho hlt, hmu, hs.2⟩
  have hb := (SourceAdditiveTracking.Assignment.execute_spec _ c (first :: tail) ho).2.1.2.1
    first List.mem_cons_self
  exact ⟨hcandidate, value_le_candidate q root ha _ hcandidate, hb⟩

/-- The independent M-word execution starts mu-covered exactly below the
least represented singleton boundary. Both comparisons are derived from
actual executions; no mts or boundary test is supplied. -/
theorem execute_lt_value_iff_first_le_mu (q root c first : Nat) (tail : List Nat)
    (ha : rootCheck q root = true)
    (hc : SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true)
    (ho : first :: tail ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c)
    (hlt : interpretation q root < interpretation (betaCode q root) c) :
    interpretation (betaCode q root) c < value q root ha ↔
      interpretation (betaCode q root) first ≤ Mu.sourceValue q root := by
  constructor
  · intro hbelow
    apply le_of_not_gt
    intro habove
    have hs := first_above_mu_candidate q root c first tail ha hc ho hlt habove
    exact hbelow.not_ge (hs.2.1.trans hs.2.2)
  · intro hcovered
    apply lt_of_not_ge
    intro hatle
    obtain ⟨d, hd, hv, hsingleton, hroot, hmu, hupper⟩ := value_spec q root ha
    rcases lt_or_eq_of_le hatle with hatlt | hateq
    · have hlex := SourceMultiplicativeTracking.Order.execute_multiplicative_lex
        (betaCode q root) d c [d] (first :: tail) hd hc
        (by simpa only [hv] using hatlt) hsingleton ho
      have hfirst : value q root ha ≤ interpretation (betaCode q root) first := by
        have h : interpretation (betaCode q root) d ≤ interpretation (betaCode q root) first :=
          List.head_le_of_lt (by simpa only [List.map_cons, List.map_nil] using hlex)
        simpa only [hv] using h
      exact hmu.not_ge (hfirst.trans hcovered)
    · have hvalues := SourceAdditiveTracking.Assignment.ValueInvariance.execute_values_eq
        (betaCode q root) d c [d] (first :: tail) hsingleton ho (hv.trans hateq)
      have hfirst : value q root ha = interpretation (betaCode q root) first := by
        have hcons := List.cons.inj (by
          simpa only [List.map_cons, List.map_nil] using hvalues)
        exact hv.symm.trans hcons.1
      exact hmu.not_ge (by simpa only [← hfirst] using hcovered)

/-- The criterion refers to the actual computed FIRST of every complete
M execution and does not require a supplied decomposition of its word. -/
theorem execute_lt_value_iff_firstCode_le_mu (q root c : Nat) (out : List Nat)
    (ha : rootCheck q root = true)
    (hc : SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true)
    (ho : out ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c)
    (hlt : interpretation q root < interpretation (betaCode q root) c) :
    interpretation (betaCode q root) c < value q root ha ↔
      interpretation (betaCode q root) (SourceAdditiveTracking.Insertion.firstCode out) ≤
        Mu.sourceValue q root := by
  cases out with
  | nil => exact False.elim (SourceAdditiveTracking.Assignment.execute_nonempty _ c [] ho rfl)
  | cons first tail =>
    simpa only [SourceAdditiveTracking.Insertion.firstCode, List.head?_cons, Option.getD_some]
      using execute_lt_value_iff_first_le_mu q root c first tail ha hc ho hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHat.FirstEntry
