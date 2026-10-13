import Alexander313.Wilken.SourceStarComparison
import Alexander313.Wilken.RelativeTermAdmissibility

/-!
# Normal literal terms and actual finite source support

`NormalSums` uses the paper's final-principal-summand convention at every
written sum. `SourceNormal` additionally excludes a zero left summand and
requires sums above the atomic parameter base, as in Definition 2.23.
These predicates are semantic normal-form conditions, not an executable
normalization/comparison procedure or a supplied fidelity theorem.

The exposed theta-m nodes at cutoff m+1 recover exactly the part of the
constructed finite P at or above Ω_m, and hence its star. Arbitrary atomic
parameters are not mistaken for their principal parts. For full P on the
next-base grammar, the actual canonical ANF of each parameter is retained.
All source collapse, admission, ANF and support facts are the existing ones.
-/

namespace Alexander313.Wilken

namespace RelativeTerm

variable {Parameter : Type}

def NormalSums (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat) :
    RelativeTerm Parameter → Prop
  | .parameter _ => True
  | .sum a b => NormalSums τ parameters n a ∧ NormalSums τ parameters n b ∧
      SourceNormalSum ((.sum a b : RelativeTerm Parameter).eval parameters (sourceFiniteCollapse τ n))
        (a.eval parameters (sourceFiniteCollapse τ n)) (b.eval parameters (sourceFiniteCollapse τ n))
  | .theta _ a => NormalSums τ parameters n a

def SourceNormal (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0})
    (n : Nat) (base : Ordinal.{0}) : RelativeTerm Parameter → Prop
  | .parameter _ => True
  | .sum a b => SourceNormal τ parameters n base a ∧ SourceNormal τ parameters n base b ∧
      0 < a.eval parameters (sourceFiniteCollapse τ n) ∧
      base < (.sum a b : RelativeTerm Parameter).eval parameters (sourceFiniteCollapse τ n) ∧
      SourceNormalSum ((.sum a b : RelativeTerm Parameter).eval parameters (sourceFiniteCollapse τ n))
        (a.eval parameters (sourceFiniteCollapse τ n)) (b.eval parameters (sourceFiniteCollapse τ n))
  | .theta _ a => SourceNormal τ parameters n base a

theorem SourceNormal.normalSums {τ : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}}
    {n : Nat} {base : Ordinal.{0}} {t : RelativeTerm Parameter}
    (h : SourceNormal τ parameters n base t) : NormalSums τ parameters n t := by
  revert h
  induction t with
  | parameter _ => intro _; trivial
  | sum a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2.1, h.2.2.2.2⟩
  | theta k a ih => intro h; exact ih h

theorem NormalSums.sum_concat {τ : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}}
    {n : Nat} {a b : RelativeTerm Parameter} (h : NormalSums τ parameters n (.sum a b)) :
    IsAdditiveNormalForm
      (canonicalANF (a.eval parameters (sourceFiniteCollapse τ n)) ++
        canonicalANF (b.eval parameters (sourceFiniteCollapse τ n))) :=
  sourceNormalSum_canonical_concat h.2.2

theorem NormalSums.sum_anf {τ : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}}
    {n : Nat} {a b : RelativeTerm Parameter} (h : NormalSums τ parameters n (.sum a b)) :
    canonicalANF ((.sum a b : RelativeTerm Parameter).eval parameters (sourceFiniteCollapse τ n)) =
      canonicalANF (a.eval parameters (sourceFiniteCollapse τ n)) ++
        canonicalANF (b.eval parameters (sourceFiniteCollapse τ n)) := by
  apply canonicalANF_eq_of_normal h.sum_concat
  rw [principalSum_append, principalSum_canonicalANF, principalSum_canonicalANF]
  rfl

def isThetaAt (m : Nat) : RelativeTerm Parameter → Prop
  | .theta k _ => k = m
  | _ => False

instance isThetaAt_decidable (m : Nat) (t : RelativeTerm Parameter) : Decidable (isThetaAt m t) := by
  cases t with
  | parameter _ => exact isFalse (fun h => h)
  | sum _ _ => exact isFalse (fun h => h)
  | theta k _ => exact inferInstanceAs (Decidable (k = m))

def exposedTheta [DecidableEq Parameter] (m : Nat) :
    RelativeTerm Parameter → Finset (RelativeTerm Parameter)
  | .parameter _ => ∅
  | .sum a b => exposedTheta m a ∪ exposedTheta m b
  | .theta k a => if k = m then {.theta k a} else
      if m < k then exposedTheta m a else ∅

theorem exposedTheta_eq_subterms [DecidableEq Parameter] (m : Nat) (t : RelativeTerm Parameter) :
    exposedTheta m t = (t.subtermsAt (m + 1)).filter (isThetaAt m) := by
  induction t with
  | parameter p => simp [exposedTheta, subtermsAt, Finset.filter_singleton, isThetaAt]
  | sum a b iha ihb =>
    simp [exposedTheta, subtermsAt, Finset.filter_insert, isThetaAt, iha, ihb, Finset.filter_union]
  | theta k a ih =>
    by_cases hkm : k = m
    · subst k
      simp [exposedTheta, subtermsAt, Finset.filter_singleton, isThetaAt]
    · by_cases hmk : m < k
      · have hle : m + 1 ≤ k := by omega
        simp [exposedTheta, subtermsAt, Finset.filter_insert, isThetaAt, hkm, hmk, hle, ih]
      · have hle : ¬m + 1 ≤ k := by omega
        simp [exposedTheta, subtermsAt, Finset.filter_singleton, isThetaAt, hkm, hmk, hle]

theorem exposedTheta_isThetaAt [DecidableEq Parameter] (m : Nat)
    (t s : RelativeTerm Parameter) (hs : s ∈ exposedTheta m t) : isThetaAt m s := by
  rw [exposedTheta_eq_subterms] at hs
  exact (Finset.mem_filter.mp hs).2

theorem exposedTheta_size_le [DecidableEq Parameter] (m : Nat)
    (t s : RelativeTerm Parameter) (hs : s ∈ exposedTheta m t) : s.size ≤ t.size := by
  revert hs
  induction t with
  | parameter p => intro hs; exact False.elim (Finset.notMem_empty s hs)
  | sum a b iha ihb =>
    intro hs
    rcases Finset.mem_union.mp hs with ha | hb
    · exact (iha ha).trans (sum_left_size_lt a b).le
    · exact (ihb hb).trans (sum_right_size_lt a b).le
  | theta k a ih =>
    intro hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by simpa only [exposedTheta, if_pos hkm,
        Finset.mem_singleton] using hs
      subst s
      exact le_rfl
    · by_cases hmk : m < k
      · have ha : s ∈ exposedTheta m a := by
          simpa only [exposedTheta, if_neg hkm, if_pos hmk] using hs
        exact (ih ha).trans (theta_arg_size_lt k a).le
      · have hf : s ∈ (∅ : Finset (RelativeTerm Parameter)) := by
          simpa only [exposedTheta, if_neg hkm, if_neg hmk] using hs
        exact False.elim (Finset.notMem_empty s hf)

theorem exposedTheta_argument_size_lt [DecidableEq Parameter] (m k : Nat)
    (a s : RelativeTerm Parameter) (hs : s ∈ exposedTheta m a) :
    s.size < (.theta k a : RelativeTerm Parameter).size :=
  (exposedTheta_size_le m a s hs).trans_lt (theta_arg_size_lt k a)

/-- This packages the actual base-zero admission in the precise next-base
    semantic domain required by the unchanged source P function. -/
noncomputable def sourceAdmittedOrdinal (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t) :
    SourceNotationOrdinal τ n (m + 1) := by
  refine ⟨t.eval parameters (sourceFiniteCollapse τ n), ?_⟩
  apply sourceNotation_upward τ n 0 (m + 1) (Nat.zero_le _) (Nat.succ_le_of_lt hm)
  rw [sourceNotation, if_pos (show 0 < n by omega)]
  exact ht.denote

@[simp] theorem sourceAdmittedOrdinal_val (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t) :
    (sourceAdmittedOrdinal τ parameters n m hm t ht).val =
      t.eval parameters (sourceFiniteCollapse τ n) := rfl

theorem sourceP_filter_eq_exposedTheta [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hnormal : NormalSums τ parameters n t) :
    (sourceP τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht)).filter
        (fun p => omegaSequence τ m ≤ p) =
      (exposedTheta m t).image (fun s => s.eval parameters (sourceFiniteCollapse τ n)) := by
  classical
  revert hnormal
  induction ht with
  | @parameter p hp =>
    intro _
    have hlow : parameters p < omegaSequence τ (m + 1) :=
      hp.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le _))
    rw [sourceP_low τ hτ n m hm _ hlow]
    simp only [exposedTheta, Finset.image_empty]
    ext q
    constructor
    · intro hq
      obtain ⟨hq, hlarge⟩ := Finset.mem_filter.mp hq
      have hsmall : q < omegaSequence τ 0 :=
        (canonicalANF_mem_le (List.mem_toFinset.mp hq)).trans_lt hp
      exact False.elim (hsmall.not_ge
        (((omegaSequence_strictMono τ).monotone (Nat.zero_le m)).trans hlarge))
    · intro hq
      exact False.elim (Finset.notMem_empty q hq)
  | @sum a b ha hb iha ihb =>
    intro hnormal
    rw [sourceP_source_normal_add τ hτ n m hm _
      (sourceAdmittedOrdinal τ parameters n m hm a ha)
      (sourceAdmittedOrdinal τ parameters n m hm b hb) hnormal.2.2,
      Finset.filter_union, iha hnormal.1, ihb hnormal.2.1]
    simp only [exposedTheta, Finset.image_union]
  | @theta k a h0k hkn hsort ha ih =>
    intro hnormal
    by_cases hmk : m < k
    · have hkm : k ≠ m := by omega
      rw [sourceP_theta τ hτ n m hm _
        (sourceAdmittedOrdinal τ parameters n m hm a ha) k hmk hkn hsort rfl, ih hnormal]
      simp only [exposedTheta, if_neg hkm, if_pos hmk]
    · have hrange := source_theta_range τ parameters n k a hkn ha hsort
      have hkm : k ≤ m := by omega
      have hlow : sourceFiniteCollapse τ n k (a.eval parameters (sourceFiniteCollapse τ n)) <
          omegaSequence τ (m + 1) :=
        hrange.2.trans_le ((omegaSequence_strictMono τ).monotone (Nat.add_le_add_right hkm 1))
      rw [sourceP_low τ hτ n m hm _ hlow]
      simp only [sourceAdmittedOrdinal_val, eval]
      rw [canonicalANF_principal (sourceFiniteCollapse_pos τ hτ n k hkn _)
          (sourceFiniteCollapse_add_closed τ n k hkn _)]
      by_cases hkm' : k = m
      · subst k
        simp [exposedTheta, eval, Finset.filter_singleton, hrange.1]
      · have hlt : k < m := by omega
        have hsmall : sourceFiniteCollapse τ n k (a.eval parameters (sourceFiniteCollapse τ n)) <
            omegaSequence τ m :=
          hrange.2.trans_le ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hlt))
        simp [exposedTheta, eval, Finset.filter_singleton, hkm', hmk, not_le_of_gt hsmall]

theorem sourceP_filter_eq_subterms [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hnormal : NormalSums τ parameters n t) :
    (sourceP τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht)).filter
        (fun p => omegaSequence τ m ≤ p) =
      ((t.subtermsAt (m + 1)).filter (isThetaAt m)).image
        (fun s => s.eval parameters (sourceFiniteCollapse τ n)) := by
  rw [← exposedTheta_eq_subterms]
  exact sourceP_filter_eq_exposedTheta τ hτ parameters n m hm t ht hnormal

theorem sourceStar_eq_exposedTheta [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hnormal : NormalSums τ parameters n t) :
    sourceStar τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht) =
      ((exposedTheta m t).image (fun s => s.eval parameters (sourceFiniteCollapse τ n))).sup id := by
  classical
  rw [sourceStar, sourceP_filter_eq_exposedTheta τ hτ parameters n m hm t ht hnormal]

theorem sourceStar_eq_subterms [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hnormal : SourceNormal τ parameters n τ t) :
    sourceStar τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht) =
      (((t.subtermsAt (m + 1)).filter (isThetaAt m)).image
        (fun s => s.eval parameters (sourceFiniteCollapse τ n))).sup id := by
  rw [← exposedTheta_eq_subterms]
  exact sourceStar_eq_exposedTheta τ hτ parameters n m hm t ht hnormal.normalSums

/-- Full low support expands an atomic parameter into its actual canonical
    ANF. It is deliberately distinct from raw literal parameter collection. -/
noncomputable def parameterANFSupport (parameters : Parameter → Ordinal.{0})
    (t : RelativeTerm Parameter) : Finset Ordinal.{0} := by
  classical
  exact match t with
    | .parameter p => (canonicalANF (parameters p)).toFinset
    | .sum a b => parameterANFSupport parameters a ∪ parameterANFSupport parameters b
    | .theta _ a => parameterANFSupport parameters a

theorem sourceP_eq_parameterANFSupport (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (t : SourceRelativeTerm τ (m + 1))
    (ht : Admissible (sourceParameters τ (m + 1)) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n (m + 1) t)
    (hnormal : NormalSums τ (sourceParameters τ (m + 1)) n t) :
    sourceP τ hτ n m hm
        ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m)
          (Nat.succ_le_of_lt hm) t ht⟩ = parameterANFSupport (sourceParameters τ (m + 1)) t := by
  classical
  revert hnormal
  induction ht with
  | parameter hp =>
    intro _
    rw [sourceP_low τ hτ n m hm _ hp]
    rfl
  | @sum a b ha hb iha ihb =>
    intro hnormal
    rw [sourceP_source_normal_add τ hτ n m hm _
      ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m)
        (Nat.succ_le_of_lt hm) a ha⟩
      ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m)
        (Nat.succ_le_of_lt hm) b hb⟩ hnormal.2.2,
      iha hnormal.1, ihb hnormal.2.1]
    rfl
  | @theta k a hmk hkn hsort ha ih =>
    intro hnormal
    rw [sourceP_theta τ hτ n m hm _
      ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m)
        (Nat.succ_le_of_lt hm) a ha⟩ k (by omega) hkn hsort rfl, ih hnormal]
    rfl

end RelativeTerm

end Alexander313.Wilken
