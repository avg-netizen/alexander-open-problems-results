import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Common

/-!
# Canonical finite additive principal decompositions

The principal summands in Wilken Lemma 2.3(c) and Definition 2.9 are those
of additive normal form. An arbitrary raw sum tree does not determine
these summands: ordinal addition can absorb an earlier smaller summand.

This module constructs the decomposition from the actual ordinal CNF,
expands its finite coefficients, and proves uniqueness using additive
principal closure and cancellation. The normalization algorithm retains
only summands not absorbed by the already normalized suffix. Its semantic
construction is noncomputable and is not a public ordinal-code algorithm.
All proof terms are candidates awaiting external compilation.
-/

namespace Alexander313.Wilken

universe u

/-- Evaluate a finite ordered list using ordinal addition. -/
def principalSum : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | a :: xs => a + principalSum xs

/-- Positive additive principal summands in nonincreasing order. Repeated
summands are retained; the CNF coefficient is their multiplicity. -/
def IsAdditiveNormalForm (xs : List Ordinal.{u}) : Prop :=
  (∀ a ∈ xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a) ∧
    xs.Pairwise (fun a b => b ≤ a)

theorem additiveNormalForm_nil : IsAdditiveNormalForm ([] : List Ordinal.{u}) := by
  simp [IsAdditiveNormalForm]

theorem additiveNormalForm_singleton {a : Ordinal.{u}}
    (ha : 0 < a) (hp : Ordinal.IsPrincipal (· + ·) a) :
    IsAdditiveNormalForm [a] := by
  simp [IsAdditiveNormalForm, ha, hp]

theorem additiveNormalForm_tail {a : Ordinal.{u}} {xs : List Ordinal.{u}}
    (h : IsAdditiveNormalForm (a :: xs)) : IsAdditiveNormalForm xs :=
  ⟨fun b hb => h.1 b (List.mem_cons_of_mem _ hb),
    (List.pairwise_cons.1 h.2).2⟩

theorem additiveNormalForm_head_ge {a b : Ordinal.{u}} {xs : List Ordinal.{u}}
    (h : IsAdditiveNormalForm (a :: xs)) (hb : b ∈ xs) : b ≤ a :=
  (List.pairwise_cons.1 h.2).1 b hb

theorem principalSum_append (xs ys : List Ordinal.{u}) :
    principalSum (xs ++ ys) = principalSum xs + principalSum ys := by
  induction xs with
  | nil => simp [principalSum]
  | cons a xs ih => simp [principalSum, ih, add_assoc]

theorem principalSum_mem_le {a : Ordinal.{u}} {xs : List Ordinal.{u}}
    (ha : a ∈ xs) : a ≤ principalSum xs := by
  revert ha
  induction xs with
  | nil => simp
  | cons b xs ih =>
    intro ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact le_self_add
    · exact (ih ha).trans le_add_self

/-- A finite sum of ordinals below a positive principal bound stays below
that bound. This includes the empty sum. -/
theorem principalSum_lt {q : Ordinal.{u}} (hq : 0 < q)
    (hp : Ordinal.IsPrincipal (· + ·) q) (xs : List Ordinal.{u})
    (hxs : ∀ a ∈ xs, a < q) : principalSum xs < q := by
  revert hxs
  induction xs with
  | nil => intro _; exact hq
  | cons a xs ih =>
    intro hxs
    exact hp (hxs a (List.mem_cons_self))
      (ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb)))

/-- Ordered positive principal lists denoting the same ordinal are equal.
The comparison of first summands follows from principal closure, rather
than from any assumed uniqueness of raw relative terms. -/
theorem additiveNormalForm_unique {xs ys : List Ordinal.{u}}
    (hxs : IsAdditiveNormalForm xs) (hys : IsAdditiveNormalForm ys)
    (heq : principalSum xs = principalSum ys) : xs = ys := by
  revert hxs hys heq
  induction xs generalizing ys with
  | nil =>
    intro hxs hys heq
    cases ys with
    | nil => rfl
    | cons q qs =>
      have hq := (hys.1 q (List.mem_cons_self)).1
      have hsum : 0 < principalSum (q :: qs) := hq.trans_le le_self_add
      exact False.elim ((ne_of_gt hsum) heq.symm)
  | cons p ps ih =>
    intro hxs hys heq
    cases ys with
    | nil =>
      have hp := (hxs.1 p (List.mem_cons_self)).1
      have hsum : 0 < principalSum (p :: ps) := hp.trans_le le_self_add
      exact False.elim ((ne_of_gt hsum) heq)
    | cons q qs =>
      have hp := hxs.1 p (List.mem_cons_self)
      have hq := hys.1 q (List.mem_cons_self)
      have hpq : p = q := by
        rcases lt_trichotomy p q with hpq | hpq | hqp
        · have hx : principalSum (p :: ps) < q :=
            principalSum_lt hq.1 hq.2 _ (by
              intro a ha
              rcases List.mem_cons.1 ha with rfl | ha
              · exact hpq
              · exact (additiveNormalForm_head_ge hxs ha).trans_lt hpq)
          have hy : q ≤ principalSum (q :: qs) := le_self_add
          exact False.elim ((ne_of_lt (hx.trans_le hy)) heq)
        · exact hpq
        · have hy : principalSum (q :: qs) < p :=
            principalSum_lt hp.1 hp.2 _ (by
              intro a ha
              rcases List.mem_cons.1 ha with rfl | ha
              · exact hqp
              · exact (additiveNormalForm_head_ge hys ha).trans_lt hqp)
          have hx : p ≤ principalSum (p :: ps) := le_self_add
          exact False.elim ((ne_of_lt (hy.trans_le hx)) heq.symm)
      subst q
      have htail : principalSum ps = principalSum qs := by
        apply add_left_cancel (a := p)
        simpa only [principalSum] using heq
      exact congrArg (List.cons p)
        (ih (ys := qs) (additiveNormalForm_tail hxs) (additiveNormalForm_tail hys) htail)

/-- Prepend an atom to a normalized suffix. A smaller atom is absorbed by
the suffix's leading principal summand. -/
noncomputable def prependPrincipal (a : Ordinal.{u}) (xs : List Ordinal.{u}) :
    List Ordinal.{u} := by
  classical
  exact match xs with
    | [] => [a]
    | b :: bs => if a < b then b :: bs else a :: b :: bs

/-- Structural recursion over a finite list; no semantic minimum oracle is
used by this normalization once comparison of its atoms is available. -/
noncomputable def normalizePrincipal : List Ordinal.{u} → List Ordinal.{u}
  | [] => []
  | a :: xs => prependPrincipal a (normalizePrincipal xs)

theorem prependPrincipal_mem {a p : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hp : p ∈ prependPrincipal a xs) : p = a ∨ p ∈ xs := by
  classical
  cases xs with
  | nil => simpa [prependPrincipal] using hp
  | cons b bs =>
    by_cases h : a < b
    · exact Or.inr (by simpa [prependPrincipal, h] using hp)
    · simpa [prependPrincipal, h, List.mem_cons] using hp

theorem normalizePrincipal_mem {p : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hp : p ∈ normalizePrincipal xs) : p ∈ xs := by
  revert hp
  induction xs with
  | nil => simp [normalizePrincipal]
  | cons a xs ih =>
    intro hp
    rcases prependPrincipal_mem hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

theorem normalizePrincipal_atoms (xs : List Ordinal.{u})
    (hxs : ∀ a ∈ xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a) :
    ∀ a ∈ normalizePrincipal xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a :=
  fun a ha => hxs a (normalizePrincipal_mem ha)

theorem prependPrincipal_normal {a : Ordinal.{u}} {xs : List Ordinal.{u}}
    (ha : 0 < a ∧ Ordinal.IsPrincipal (· + ·) a)
    (hxs : IsAdditiveNormalForm xs) :
    IsAdditiveNormalForm (prependPrincipal a xs) := by
  classical
  cases xs with
  | nil => simpa [prependPrincipal] using additiveNormalForm_singleton ha.1 ha.2
  | cons b bs =>
    by_cases hab : a < b
    · simpa [prependPrincipal, hab] using hxs
    · rw [prependPrincipal, if_neg hab]
      refine ⟨?_, List.pairwise_cons.2 ⟨?_, hxs.2⟩⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ha
        · exact hxs.1 p hp
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact le_of_not_gt hab
        · exact (additiveNormalForm_head_ge hxs hp).trans (le_of_not_gt hab)

theorem normalizePrincipal_normal (xs : List Ordinal.{u})
    (hxs : ∀ a ∈ xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a) :
    IsAdditiveNormalForm (normalizePrincipal xs) := by
  revert hxs
  induction xs with
  | nil => intro _; exact additiveNormalForm_nil
  | cons a xs ih =>
    intro hxs
    exact prependPrincipal_normal (hxs a (List.mem_cons_self))
      (ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb)))

theorem principalSum_prependPrincipal (a : Ordinal.{u}) (xs : List Ordinal.{u})
    (hxs : ∀ b ∈ xs, Ordinal.IsPrincipal (· + ·) b) :
    principalSum (prependPrincipal a xs) = a + principalSum xs := by
  classical
  cases xs with
  | nil => simp [prependPrincipal, principalSum]
  | cons b bs =>
    by_cases hab : a < b
    · have hb := hxs b (List.mem_cons_self)
      simp only [prependPrincipal, if_pos hab, principalSum]
      rw [← add_assoc, hb.add_eq_right hab]
    · simp [prependPrincipal, hab, principalSum]

theorem principalSum_normalizePrincipal (xs : List Ordinal.{u})
    (hxs : ∀ a ∈ xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a) :
    principalSum (normalizePrincipal xs) = principalSum xs := by
  revert hxs
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro hxs
    have htail := fun b hb => hxs b (List.mem_cons_of_mem _ hb)
    rw [normalizePrincipal, principalSum_prependPrincipal _ _
      (fun b hb => (normalizePrincipal_atoms xs htail b hb).2), ih htail]
    rfl

theorem principalSum_replicate (a : Ordinal.{u}) (n : Nat) :
    principalSum (List.replicate n a) = a * (n : Ordinal) := by
  induction n with
  | zero => simp [principalSum]
  | succ n ih =>
    rw [List.replicate_succ', principalSum_append, ih]
    simp [principalSum, Nat.cast_add_one, mul_add_one]

/-- The finite multiplicity of a coefficient below ω. The outside value
zero is auxiliary and never used for an actual ω-CNF coefficient. -/
noncomputable def cnfMultiplicity (c : Ordinal.{u}) : Nat := by
  classical
  exact if hc : c < Ordinal.omega0 then Classical.choose (Ordinal.lt_omega0.1 hc) else 0

theorem cnfMultiplicity_spec {c : Ordinal.{u}} (hc : c < Ordinal.omega0) :
    c = (cnfMultiplicity c : Ordinal) := by
  classical
  unfold cnfMultiplicity
  rw [dif_pos hc]
  exact Classical.choose_spec (Ordinal.lt_omega0.1 hc)

noncomputable def expandPrincipalCNF : List (Ordinal.{u} × Ordinal.{u}) → List Ordinal.{u}
  | [] => []
  | p :: xs => List.replicate (cnfMultiplicity p.2) (Ordinal.omega0 ^ p.1) ++
      expandPrincipalCNF xs

theorem expandPrincipalCNF_atoms (xs : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ a ∈ expandPrincipalCNF xs, 0 < a ∧ Ordinal.IsPrincipal (· + ·) a := by
  induction xs with
  | nil => simp [expandPrincipalCNF]
  | cons p xs ih =>
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · have hae := List.eq_of_mem_replicate ha
      subst a
      exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos,
        Ordinal.isPrincipal_add_omega0_opow _⟩
    · exact ih a ha

theorem principalSum_expandPrincipalCNF (xs : List (Ordinal.{u} × Ordinal.{u}))
    (hxs : ∀ p ∈ xs, p.2 < Ordinal.omega0) :
    principalSum (expandPrincipalCNF xs) =
      xs.foldr (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0 := by
  revert hxs
  induction xs with
  | nil => intro _; rfl
  | cons p xs ih =>
    intro hxs
    rw [expandPrincipalCNF, principalSum_append, principalSum_replicate,
      ← cnfMultiplicity_spec (hxs p (List.mem_cons_self)),
      ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))]
    rfl

/-- The actual canonical ANF of an ordinal, including the empty ANF at 0. -/
noncomputable def canonicalANF (ξ : Ordinal.{u}) : List Ordinal.{u} :=
  normalizePrincipal (expandPrincipalCNF (Ordinal.CNF Ordinal.omega0 ξ))

theorem canonicalANF_normal (ξ : Ordinal.{u}) :
    IsAdditiveNormalForm (canonicalANF ξ) :=
  normalizePrincipal_normal _ (expandPrincipalCNF_atoms _)

theorem principalSum_canonicalANF (ξ : Ordinal.{u}) :
    principalSum (canonicalANF ξ) = ξ := by
  rw [canonicalANF, principalSum_normalizePrincipal _ (expandPrincipalCNF_atoms _),
    principalSum_expandPrincipalCNF _
      (fun p hp => Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hp)]
  exact Ordinal.CNF.foldr _ _

theorem canonicalANF_eq_of_normal {ξ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hxs : IsAdditiveNormalForm xs) (heq : principalSum xs = ξ) :
    canonicalANF ξ = xs :=
  additiveNormalForm_unique (canonicalANF_normal ξ) hxs
    ((principalSum_canonicalANF ξ).trans heq.symm)

theorem canonicalANF_zero : canonicalANF (0 : Ordinal.{u}) = [] := by
  apply canonicalANF_eq_of_normal additiveNormalForm_nil
  rfl

theorem canonicalANF_principal {ξ : Ordinal.{u}} (hξ : 0 < ξ)
    (hp : Ordinal.IsPrincipal (· + ·) ξ) : canonicalANF ξ = [ξ] := by
  apply canonicalANF_eq_of_normal (additiveNormalForm_singleton hξ hp)
  simp [principalSum]

theorem canonicalANF_mem_le {a ξ : Ordinal.{u}} (ha : a ∈ canonicalANF ξ) : a ≤ ξ :=
  (principalSum_mem_le ha).trans_eq (principalSum_canonicalANF ξ)

/-- Addition is concatenation followed by actual ordinal absorption. -/
theorem canonicalANF_add (ξ η : Ordinal.{u}) :
    canonicalANF (ξ + η) = normalizePrincipal (canonicalANF ξ ++ canonicalANF η) := by
  have hxs : ∀ a ∈ canonicalANF ξ ++ canonicalANF η,
      0 < a ∧ Ordinal.IsPrincipal (· + ·) a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact (canonicalANF_normal ξ).1 a ha
    · exact (canonicalANF_normal η).1 a ha
  apply canonicalANF_eq_of_normal (normalizePrincipal_normal _ hxs)
  rw [principalSum_normalizePrincipal _ hxs, principalSum_append,
    principalSum_canonicalANF, principalSum_canonicalANF]

theorem canonicalANF_add_mem {ξ η a : Ordinal.{u}}
    (ha : a ∈ canonicalANF (ξ + η)) :
    a ∈ canonicalANF ξ ∨ a ∈ canonicalANF η := by
  rw [canonicalANF_add] at ha
  exact List.mem_append.1 (normalizePrincipal_mem ha)

/-- A concrete absorption law that rules out raw-leaf collection as ANF. -/
theorem canonicalANF_add_of_lt_principal {ξ η : Ordinal.{u}}
    (hη : 0 < η) (hp : Ordinal.IsPrincipal (· + ·) η) (hξη : ξ < η) :
    canonicalANF (ξ + η) = [η] := by
  rw [hp.add_eq_right hξη]
  exact canonicalANF_principal hη hp

end Alexander313.Wilken
