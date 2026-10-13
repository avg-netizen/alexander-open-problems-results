import Alexander313.Wilken.RelativeTermExposedCodes
import Alexander313.Wilken.RelativeTermPublicCodes

/-!
# Literal constituents for the base-one comparison recursion

At base one every admitted parameter is zero. A normal literal tree therefore
has an actual additive normal form consisting of its outer theta atoms. The
same-level source star law is expressed using the actual exposed node list.
The smaller constituents preserve source admission and normal sums; no order
algorithm or support theorem is supplied as an assumption.
-/

namespace Alexander313.Wilken.RelativeTerm

def thetaAtoms {Parameter : Type} : RelativeTerm Parameter → List (RelativeTerm Parameter)
  | .parameter _ => []
  | .sum a b => thetaAtoms a ++ thetaAtoms b
  | .theta k a => [.theta k a]

theorem thetaAtoms_size_le {Parameter : Type} (t s : RelativeTerm Parameter)
    (hs : s ∈ thetaAtoms t) : s.size ≤ t.size := by
  revert hs
  induction t with
  | parameter p => intro hs; simp [RelativeTerm.thetaAtoms] at hs
  | sum a b iha ihb =>
    intro hs
    rcases List.mem_append.mp hs with ha | hb
    · exact (iha ha).trans (sum_left_size_lt a b).le
    · exact (ihb hb).trans (sum_right_size_lt a b).le
  | theta k a => intro hs; have he : s = .theta k a := List.mem_singleton.mp hs; subst s; exact le_rfl

theorem thetaAtoms_sum_size_lt {Parameter : Type} (a b s : RelativeTerm Parameter)
    (hs : s ∈ thetaAtoms (.sum a b)) : s.size < (.sum a b : RelativeTerm Parameter).size := by
  rcases List.mem_append.mp hs with ha | hb
  · exact (thetaAtoms_size_le a s ha).trans_lt (sum_left_size_lt a b)
  · exact (thetaAtoms_size_le b s hb).trans_lt (sum_right_size_lt a b)

theorem Admissible.thetaAtoms {Parameter : Type} {parameters : Parameter → Ordinal}
    {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal} {n r : Nat}
    {t s : RelativeTerm Parameter} (ht : Admissible parameters omega theta n r t)
    (hs : s ∈ thetaAtoms t) : Admissible parameters omega theta n r s := by
  revert hs
  induction ht with
  | parameter hp => intro hs; simp [RelativeTerm.thetaAtoms] at hs
  | sum ha hb iha ihb =>
    intro hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha hs
    · exact ihb hs
  | theta h0k hkn hsort ha ih =>
    intro hs
    have he := List.mem_singleton.mp hs
    subst s
    exact .theta h0k hkn hsort ha

theorem NormalSums.thetaAtoms {Parameter : Type} {τ : Ordinal.{0}}
    {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : NormalSums τ parameters n t) (hs : s ∈ thetaAtoms t) :
    NormalSums τ parameters n s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [RelativeTerm.thetaAtoms] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    have he := List.mem_singleton.mp hs
    subst s
    exact ht

theorem Admissible.exposedThetaList {Parameter : Type} {parameters : Parameter → Ordinal}
    {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal} {n r : Nat}
    {t s : RelativeTerm Parameter} (ht : Admissible parameters omega theta n r t)
    (m : Nat) (hs : s ∈ exposedThetaList m t) : Admissible parameters omega theta n r s := by
  revert hs
  induction ht with
  | parameter hp => intro hs; simp [RelativeTerm.exposedThetaList] at hs
  | sum ha hb iha ihb =>
    intro hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha hs
    · exact ihb hs
  | @theta k a h0k hkn hsort ha ih =>
    intro hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by simpa only [RelativeTerm.exposedThetaList, if_pos hkm,
        List.mem_singleton] using hs
      subst s
      exact .theta h0k hkn hsort ha
    · by_cases hmk : m < k
      · apply ih
        simpa only [RelativeTerm.exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [RelativeTerm.exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem NormalSums.exposedThetaList {Parameter : Type} {τ : Ordinal.{0}}
    {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : NormalSums τ parameters n t) (m : Nat) (hs : s ∈ exposedThetaList m t) :
    NormalSums τ parameters n s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [RelativeTerm.exposedThetaList] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by simpa only [RelativeTerm.exposedThetaList, if_pos hkm,
        List.mem_singleton] using hs
      subst s
      exact ht
    · by_cases hmk : m < k
      · apply ih ht
        simpa only [RelativeTerm.exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [RelativeTerm.exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem exposedThetaList_size_le {Parameter : Type} [DecidableEq Parameter]
    (m : Nat) (t s : RelativeTerm Parameter) (hs : s ∈ exposedThetaList m t) :
    s.size ≤ t.size :=
  exposedTheta_size_le m t s ((mem_exposedThetaList_iff m t s).mp hs)

namespace SourceOne

def Normal (n : Nat) (t : RelativeTerm Nat) : Prop := NormalSums 1 parameters n t

private theorem base_pos : (0 : Ordinal.{0}) < 1 := by simp

theorem thetaAtoms_denote_anf (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (hnormal : Normal n t) :
    (thetaAtoms t).map (denote n) = canonicalANF (denote n t) := by
  revert hnormal
  induction ht with
  | @parameter p hp =>
    intro _
    have hp0 := (parameter_lt_base_iff p).mp hp
    subst p
    simp [thetaAtoms, denote, eval, parameters, canonicalANF_zero]
  | @sum a b ha hb iha ihb =>
    intro hnormal
    rw [thetaAtoms, List.map_append, iha hnormal.1, ihb hnormal.2.1]
    exact (NormalSums.sum_anf hnormal).symm
  | @theta k a h0k hkn hsort ha ih =>
    intro _
    simp only [RelativeTerm.thetaAtoms, List.map_singleton, denote, eval]
    exact (canonicalANF_principal (sourceFiniteCollapse_pos 1 base_pos n k hkn _)
      (sourceFiniteCollapse_add_closed 1 n k hkn _)).symm

theorem thetaAtoms_denote_normal (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (hnormal : Normal n t) :
    IsAdditiveNormalForm ((thetaAtoms t).map (denote n)) := by
  rw [thetaAtoms_denote_anf n t ht hnormal]
  exact canonicalANF_normal _

theorem thetaAtoms_denote_sum (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (hnormal : Normal n t) :
    principalSum ((thetaAtoms t).map (denote n)) = denote n t := by
  rw [thetaAtoms_denote_anf n t ht hnormal, principalSum_canonicalANF]

theorem theta_lt_of_level_lt (n k l : Nat) (a b : RelativeTerm Nat)
    (ha : admissible n (.theta k a)) (hb : admissible n (.theta l b)) (hkl : k < l) :
    denote n (.theta k a) < denote n (.theta l b) := by
  cases ha with
  | theta h0k hkn hsorta ha =>
    cases hb with
    | theta h0l hln hsortb hb =>
      exact (source_theta_range 1 parameters n k a hkn ha hsorta).2.trans_le
        (((omegaSequence_strictMono 1).monotone (Nat.succ_le_of_lt hkl)).trans
          (source_theta_range 1 parameters n l b hln hb hsortb).1)

theorem theta_lt_iff_exposed (n k : Nat) (a b : RelativeTerm Nat)
    (ha : admissible n (.theta k a)) (hb : admissible n (.theta k b))
    (hna : Normal n a) (hnb : Normal n b) :
    denote n (.theta k a) < denote n (.theta k b) ↔
      (denote n a < denote n b ∧
        ∀ q ∈ exposedThetaList k a, denote n q < denote n (.theta k b)) ∨
      ∃ q ∈ exposedThetaList k b, denote n (.theta k a) ≤ denote n q := by
  classical
  cases ha with
  | theta h0k hkn hsorta ha =>
    cases hb with
    | theta h0k' hkn' hsortb hb =>
      let α := sourceAdmittedOrdinal 1 parameters n k hkn a ha
      let β := sourceAdmittedOrdinal 1 parameters n k hkn b hb
      have star_lt (t : RelativeTerm Nat) (ht : admissible n t) (hnt : Normal n t)
          (c : Ordinal.{0}) (hc : 0 < c) :
          sourceStar 1 base_pos n k hkn (sourceAdmittedOrdinal 1 parameters n k hkn t ht) < c ↔
            ∀ q ∈ exposedThetaList k t, denote n q < c := by
        rw [sourceStar_eq_exposedTheta 1 base_pos parameters n k hkn t ht hnt]
        rw [Finset.sup_lt_iff hc]
        constructor
        · intro h q hq
          exact h _ (Finset.mem_image.mpr ⟨q, (mem_exposedThetaList_iff k t q).mp hq, rfl⟩)
        · intro h p hp
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact h q ((mem_exposedThetaList_iff k t q).mpr hq)
      have star_le : denote n (.theta k a) ≤ sourceStar 1 base_pos n k hkn β ↔
          ∃ q ∈ exposedThetaList k b, denote n (.theta k a) ≤ denote n q := by
        change denote n (.theta k a) ≤
          sourceStar 1 base_pos n k hkn (sourceAdmittedOrdinal 1 parameters n k hkn b hb) ↔ _
        rw [← not_lt, star_lt b hb hnb (denote n (.theta k a))
          (sourceFiniteCollapse_pos 1 base_pos n k hkn _)]
        simp only [not_forall, _root_.not_imp, not_lt, exists_prop]
      have hs := sourceFiniteCollapse_lt_iff_sourceStar 1 base_pos n k hkn α β hsorta hsortb
      exact hs.trans (or_congr
        (and_congr Iff.rfl (star_lt a ha hna _
          (sourceFiniteCollapse_pos 1 base_pos n k hkn _))) star_le)

end SourceOne

end Alexander313.Wilken.RelativeTerm
