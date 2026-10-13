import Alexander313.Wilken.DirectLimitNotations
import Alexander313.Wilken.SourceStarComparison

/-!
# Canonical support in the actual direct limit

The finite support sets are independent of their fragment, by iterating the
proved adjacent source agreement. A least finite witness therefore defines
support on the actual global grammar. Every other finite witness gives the
same support and star, including the old duplicated terminal convention.

These are semantic constructions, not executable normalization or comparison
algorithms. No support agreement or global-star contract is an input.
-/

namespace Alexander313.Wilken

theorem sourceP_fragment_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m n' : Nat) (hm : m < n) (hnn' : n ≤ n')
    (ξ : SourceNotationOrdinal τ n (m + 1))
    (ξ' : SourceNotationOrdinal τ n' (m + 1)) (heq : ξ.val = ξ'.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ n' m (hm.trans_le hnn') ξ' := by
  have steps : ∀ d (η : SourceNotationOrdinal τ (n + d) (m + 1)),
      ξ.val = η.val →
      sourceP τ hτ n m hm ξ = sourceP τ hτ (n + d) m (by omega) η := by
    intro d
    induction d with
    | zero =>
      intro η hη
      have hsame : ξ = η := Subtype.ext hη
      subst η
      rfl
    | succ d ih =>
      intro η hη
      let γ : SourceNotationOrdinal τ (n + d) (m + 1) :=
        ⟨ξ.val, sourceNotation_fragment_mono τ hτ n (m + 1) (n + d)
          (Nat.succ_le_of_lt hm) (by omega) ξ.property⟩
      calc
        sourceP τ hτ n m hm ξ = sourceP τ hτ (n + d) m (by omega) γ := ih γ rfl
        _ = sourceP τ hτ (n + Nat.succ d) m (by omega) η := by
          simpa only [Nat.add_succ] using
            sourceP_finite_end_extension τ hτ (n + d) m (by omega) γ η hη
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  exact steps d ξ' heq

/-- The actual inclusion T_m ⊆ T_(m+1) survives the direct limit. -/
theorem globalNotation_embeds_next (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) {ξ : Ordinal.{0}} (hξ : GlobalNotation τ m ξ) :
    GlobalNotation τ (m + 1) ξ := by
  obtain ⟨n, hmn, hξn⟩ := globalNotation_finite_witness τ hτ m hξ
  have hnext := sourceNotation_embeds_next τ n m hmn hξn
  have hnew : m + 1 < n + 1 := by omega
  exact sourceNotation_to_globalNotation τ hτ (n + 1) (m + 1) hnew
    (sourceNotation_fragment_mono τ hτ n (m + 1) (n + 1)
      (Nat.succ_le_of_lt hmn) (Nat.le_succ n) hnext)

abbrev GlobalNotationOrdinal (τ : Ordinal.{0}) (m : Nat) :=
  {ξ : Ordinal.{0} // GlobalNotation τ m ξ}

theorem globalNotation_common_fragment (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α γ : GlobalNotationOrdinal τ m) :
    ∃ n, m < n ∧ sourceNotation τ n m α.val ∧ sourceNotation τ n m γ.val := by
  obtain ⟨n, hmn, hα⟩ := globalNotation_finite_witness τ hτ m α.property
  obtain ⟨n', hmn', hγ⟩ := globalNotation_finite_witness τ hτ m γ.property
  refine ⟨max n n', hmn.trans_le (le_max_left n n'), ?_, ?_⟩
  · exact sourceNotation_fragment_mono τ hτ n m (max n n') hmn.le
      (le_max_left n n') hα
  · exact sourceNotation_fragment_mono τ hτ n' m (max n n') hmn'.le
      (le_max_right n n') hγ

noncomputable def globalSupportFragment (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) : Nat := by
  classical
  exact Nat.find (globalNotation_finite_witness τ hτ (m + 1) ξ.property)

theorem globalSupportFragment_spec (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) :
    m + 1 < globalSupportFragment τ hτ m ξ ∧
      sourceNotation τ (globalSupportFragment τ hτ m ξ) (m + 1) ξ.val := by
  classical
  exact Nat.find_spec (globalNotation_finite_witness τ hτ (m + 1) ξ.property)

noncomputable def globalP (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) : Finset Ordinal.{0} :=
  sourceP τ hτ (globalSupportFragment τ hτ m ξ) m
    (by have h := (globalSupportFragment_spec τ hτ m ξ).1; omega)
    ⟨ξ.val, (globalSupportFragment_spec τ hτ m ξ).2⟩

/-- All actual finite witnesses give literally the same canonical support.
The witness need only contain level m, so its next level may be terminal. -/
theorem globalP_finite_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1))
    (n : Nat) (hm : m < n) (ξn : SourceNotationOrdinal τ n (m + 1))
    (heq : ξ.val = ξn.val) :
    globalP τ hτ m ξ = sourceP τ hτ n m hm ξn := by
  let q := globalSupportFragment τ hτ m ξ
  have hq : m < q := by
    have h := (globalSupportFragment_spec τ hτ m ξ).1
    omega
  let ξq : SourceNotationOrdinal τ q (m + 1) :=
    ⟨ξ.val, (globalSupportFragment_spec τ hτ m ξ).2⟩
  let p := max q n
  let ξp : SourceNotationOrdinal τ p (m + 1) :=
    ⟨ξ.val, sourceNotation_fragment_mono τ hτ q (m + 1) p
      (by have h := (globalSupportFragment_spec τ hτ m ξ).1; omega)
      (le_max_left q n) ξq.property⟩
  change sourceP τ hτ q m hq ξq = sourceP τ hτ n m hm ξn
  exact (sourceP_fragment_agreement τ hτ q m p hq (le_max_left q n) ξq ξp rfl).trans
    (sourceP_fragment_agreement τ hτ n m p hm (le_max_right q n) ξn ξp heq.symm).symm

theorem globalP_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1))
    (hlow : ξ.val < omegaSequence τ (m + 1)) :
    globalP τ hτ m ξ = (canonicalANF ξ.val).toFinset :=
  sourceP_low τ hτ (globalSupportFragment τ hτ m ξ) m
    (by have h := (globalSupportFragment_spec τ hτ m ξ).1; omega)
    ⟨ξ.val, (globalSupportFragment_spec τ hτ m ξ).2⟩ hlow

theorem globalP_below (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1))
    (p : Ordinal.{0}) (hp : p ∈ globalP τ hτ m ξ) :
    p < omegaSequence τ (m + 1) :=
  sourceP_below τ hτ (globalSupportFragment τ hτ m ξ) m
    (by have h := (globalSupportFragment_spec τ hτ m ξ).1; omega)
    ⟨ξ.val, (globalSupportFragment_spec τ hτ m ξ).2⟩ p hp

theorem globalP_theta (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ γ : GlobalNotationOrdinal τ (m + 1)) (k : Nat)
    (hmk : m < k) (hsort : γ.val < omegaSequence τ (k + 2))
    (heq : ξ.val = globalCollapse τ k γ.val) :
    globalP τ hτ m ξ = globalP τ hτ m γ := by
  obtain ⟨n, hmn, hξ, hγ⟩ := globalNotation_common_fragment τ hτ (m + 1) ξ γ
  let p := max n (k + 1)
  have hkp : k < p := (Nat.lt_succ_self k).trans_le (le_max_right n (k + 1))
  have hmp : m < p := hmk.trans hkp
  let ξp : SourceNotationOrdinal τ p (m + 1) :=
    ⟨ξ.val, sourceNotation_fragment_mono τ hτ n (m + 1) p hmn.le
      (le_max_left n (k + 1)) hξ⟩
  let γp : SourceNotationOrdinal τ p (m + 1) :=
    ⟨γ.val, sourceNotation_fragment_mono τ hτ n (m + 1) p hmn.le
      (le_max_left n (k + 1)) hγ⟩
  have hb := source_finite_collapse_argument_lt_boundary τ hτ p (m + 1) k
    (Nat.succ_le_of_lt hmk) hkp γp.property hsort
  have hfinite : ξp.val = sourceFiniteCollapse τ p k γp.val :=
    heq.trans (globalCollapse_finite_agreement τ hτ p k hkp γ.val hb)
  rw [globalP_finite_agreement τ hτ m ξ p hmp ξp rfl,
    globalP_finite_agreement τ hτ m γ p hmp γp rfl]
  exact sourceP_theta τ hτ p m hmp ξp γp k hmk hkp hsort hfinite

theorem globalP_source_normal_add (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ α β : GlobalNotationOrdinal τ (m + 1))
    (hnormal : SourceNormalSum ξ.val α.val β.val) :
    globalP τ hτ m ξ = globalP τ hτ m α ∪ globalP τ hτ m β := by
  obtain ⟨n, hmn, hα, hβ⟩ := globalNotation_common_fragment τ hτ (m + 1) α β
  have hm : m < n := by omega
  let αn : SourceNotationOrdinal τ n (m + 1) := ⟨α.val, hα⟩
  let βn : SourceNotationOrdinal τ n (m + 1) := ⟨β.val, hβ⟩
  have hsum : sourceNotation τ n (m + 1) (α.val + β.val) := by
    rw [sourceNotation, if_pos hmn] at hα hβ ⊢
    exact .add hα hβ
  let ξn : SourceNotationOrdinal τ n (m + 1) :=
    ⟨ξ.val, by rw [sourceNormalSum_eq_add hnormal]; exact hsum⟩
  rw [globalP_finite_agreement τ hτ m ξ n hm ξn rfl,
    globalP_finite_agreement τ hτ m α n hm αn rfl,
    globalP_finite_agreement τ hτ m β n hm βn rfl]
  exact sourceP_source_normal_add τ hτ n m hm ξn αn βn hnormal

noncomputable def globalStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) : Ordinal.{0} := by
  classical
  exact ((globalP τ hτ m ξ).filter (fun p => omegaSequence τ m ≤ p)).sup id

theorem globalStar_finite_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1))
    (n : Nat) (hm : m < n) (ξn : SourceNotationOrdinal τ n (m + 1))
    (heq : ξ.val = ξn.val) :
    globalStar τ hτ m ξ = sourceStar τ hτ n m hm ξn := by
  classical
  unfold globalStar sourceStar
  rw [globalP_finite_agreement τ hτ m ξ n hm ξn heq]

theorem globalStar_eq_lowStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1))
    (hlow : ξ.val < omegaSequence τ (m + 1)) :
    globalStar τ hτ m ξ = lowStar τ m ξ.val := by
  classical
  rw [globalStar, globalP_low τ hτ m ξ hlow, lowStar]

theorem globalStar_lt_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) (β : Ordinal.{0})
    (hβ : 0 < β) (hbase : omegaSequence τ m ≤ β) :
    globalStar τ hτ m ξ < β ↔ ∀ p ∈ globalP τ hτ m ξ, p < β := by
  let n := globalSupportFragment τ hτ m ξ
  have hm : m < n := by
    have h := (globalSupportFragment_spec τ hτ m ξ).1
    omega
  let ξn : SourceNotationOrdinal τ n (m + 1) :=
    ⟨ξ.val, (globalSupportFragment_spec τ hτ m ξ).2⟩
  rw [globalStar_finite_agreement τ hτ m ξ n hm ξn rfl,
    globalP_finite_agreement τ hτ m ξ n hm ξn rfl]
  exact sourceStar_lt_iff τ hτ n m hm ξn β hβ hbase

theorem globalStar_lt_cardinal (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : GlobalNotationOrdinal τ (m + 1)) :
    globalStar τ hτ m ξ < omegaSequence τ (m + 1) :=
  (globalStar_lt_iff τ hτ m ξ (omegaSequence τ (m + 1))
    (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1))))
    (omegaSequence_step τ m).le).mpr (globalP_below τ hτ m ξ)

end Alexander313.Wilken
