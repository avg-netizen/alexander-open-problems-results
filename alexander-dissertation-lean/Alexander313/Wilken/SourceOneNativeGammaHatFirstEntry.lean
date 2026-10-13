import Alexander313.Wilken.SourceOneNativeGammaHat
import Alexander313.Wilken.PublicEpsilonNativeGammaHatFirstEntry

/-!
# The original-source-one FIRST and singleton-boundary criterion

Every actual alpha-context M word has an independently executing singleton
at its FIRST. Original check-zero root fidelity identifies its alpha base,
so a FIRST above original mu gives a genuine source-one candidate. Actual
M-word strict order and equal-value full-assignment fidelity prove the
converse at the least represented singleton. Original source-one mu is
retained throughout, never replaced by a Native-base-one computation.
Semantic boundary only; mts/public transport and numerical minimum remain
separate. Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHat.FirstEntry

open NativeContext.SourceTrackingSequences

/-- FIRST is the unchanged final input or a genuine HIGH alpha-context
prefix node, hence is strictly above the actual original source-zero root. -/
theorem execute_first_gt_root (a c first : Nat) (tail : List Nat)
    (ha : rootCheck a = true)
    (hc : NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true)
    (ho : first :: tail ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c)
    (hlt : interpretation 0 a < NativeContext.interpretation (alphaCode a) c) :
    interpretation 0 a < NativeContext.interpretation (alphaCode a) first := by
  have he : first :: tail = NativeContext.SourceMultiplicativeTracking.rawWord (alphaCode a) c :=
    Part.mem_unique ho (NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ c hc)
  have hm : first ∈ NativeContext.SourceMultiplicativeTracking.rawWord (alphaCode a) c := by
    rw [← he]
    exact List.mem_cons_self
  rcases NativeContext.SourceAdditiveTracking.ReplacementSupport.rawWord_member _ c first hm
    with hlast | hp
  · simpa only [hlast] using hlt
  · have hhigh := NativeContext.SourceMultiplicativeTracking.properPrefix_roots _ _
      (NativeContext.SourceMultiplicativePrincipal.rootInput _ c hc) first hp
    simpa only [OrderSupport.alpha_base a ha] using
      NativeContext.PublicEpsilonUnboundedIota.Mu.root_base_lt _ first hhigh

/-- A FIRST above ORIGINAL source-one mu is a real singleton candidate;
the actual complete assignment also bounds FIRST by its input value. -/
theorem first_above_mu_candidate (a c first : Nat) (tail : List Nat)
    (ha : rootCheck a = true)
    (hc : NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true)
    (ho : first :: tail ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c)
    (hlt : interpretation 0 a < NativeContext.interpretation (alphaCode a) c)
    (hmu : Mu.sourceValue a < NativeContext.interpretation (alphaCode a) first) :
    NativeContext.interpretation (alphaCode a) first ∈ CandidateValues a ∧
      value a ha ≤ NativeContext.interpretation (alphaCode a) first ∧
        NativeContext.interpretation (alphaCode a) first ≤
          NativeContext.interpretation (alphaCode a) c := by
  have hs := NativeContext.PublicEpsilonUnboundedIota.GammaHat.FirstEntry.execute_first_singleton
    (alphaCode a) c first tail hc ho
  have hcandidate : NativeContext.interpretation (alphaCode a) first ∈ CandidateValues a :=
    ⟨first, hs.1, rfl, execute_first_gt_root a c first tail ha hc ho hlt, hmu, hs.2⟩
  have hb := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ c (first :: tail) ho).2.1.2.1
    first List.mem_cons_self
  exact ⟨hcandidate, value_le_candidate a ha _ hcandidate, hb⟩

/-- The actual alpha-context M execution is FIRST-covered by original
source-one mu exactly below the original semantic singleton boundary. -/
theorem execute_lt_value_iff_first_le_mu (a c first : Nat) (tail : List Nat)
    (ha : rootCheck a = true)
    (hc : NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true)
    (ho : first :: tail ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c)
    (hlt : interpretation 0 a < NativeContext.interpretation (alphaCode a) c) :
    NativeContext.interpretation (alphaCode a) c < value a ha ↔
      NativeContext.interpretation (alphaCode a) first ≤ Mu.sourceValue a := by
  constructor
  · intro hbelow
    apply le_of_not_gt
    intro habove
    have hs := first_above_mu_candidate a c first tail ha hc ho hlt habove
    exact hbelow.not_ge (hs.2.1.trans hs.2.2)
  · intro hcovered
    apply lt_of_not_ge
    intro hatle
    obtain ⟨d, hd, hv, hsingleton, hroot, hmu, hupper⟩ := value_spec a ha
    rcases lt_or_eq_of_le hatle with hatlt | hateq
    · have hlex := NativeContext.SourceMultiplicativeTracking.Order.execute_multiplicative_lex
        (alphaCode a) d c [d] (first :: tail) hd hc
        (by simpa only [hv] using hatlt) hsingleton ho
      have hfirst : value a ha ≤ NativeContext.interpretation (alphaCode a) first := by
        have h : NativeContext.interpretation (alphaCode a) d ≤
            NativeContext.interpretation (alphaCode a) first :=
          List.head_le_of_lt (by simpa only [List.map_cons, List.map_nil] using hlex)
        simpa only [hv] using h
      exact hmu.not_ge (hfirst.trans hcovered)
    · have hvalues := NativeContext.SourceAdditiveTracking.Assignment.ValueInvariance.execute_values_eq
        (alphaCode a) d c [d] (first :: tail) hsingleton ho (hv.trans hateq)
      have hfirst : value a ha = NativeContext.interpretation (alphaCode a) first := by
        have hcons := List.cons.inj (by simpa only [List.map_cons, List.map_nil] using hvalues)
        exact hv.symm.trans hcons.1
      exact hmu.not_ge (by simpa only [← hfirst] using hcovered)

/-- Every actual full M execution uses its computed numerical FIRST;
the decomposition is obtained from genuine nonempty execution. -/
theorem execute_lt_value_iff_firstCode_le_mu (a c : Nat) (out : List Nat)
    (ha : rootCheck a = true)
    (hc : NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true)
    (ho : out ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c)
    (hlt : interpretation 0 a < NativeContext.interpretation (alphaCode a) c) :
    NativeContext.interpretation (alphaCode a) c < value a ha ↔
      NativeContext.interpretation (alphaCode a)
        (NativeContext.SourceAdditiveTracking.Insertion.firstCode out) ≤ Mu.sourceValue a := by
  cases out with
  | nil => exact False.elim (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ c [] ho rfl)
  | cons first tail =>
    simpa only [NativeContext.SourceAdditiveTracking.Insertion.firstCode, List.head?_cons,
      Option.getD_some] using execute_lt_value_iff_first_le_mu a c first tail ha hc ho hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHat.FirstEntry
