import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeightSupport
import Alexander313.Wilken.SourceFixedPointLimits

/-!
# Actual relative-collapse bounds from the two hull minima

The low tail shift is strictly increasing, and shifts an argument below an
Omega-divisible ceiling to another argument below that SAME ceiling. An
ordinal induction proves the bound for the actual relative collapse, using
the actual source minimum as a candidate. No relative-collapse, translation,
successor or enclosure premise is supplied. Uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus

open SourceFixedPointLimits

theorem omega_succ (τ α : Ordinal.{0}) (hle : τ ≤ α)
    (hlt : α < omegaSequence τ 1) (k : Nat) :
    omegaSequence τ (k + 1) = omegaSequence α (k + 1) := by
  exact congrArg Cardinal.ord (HeightSupport.levelCardinal_eq_of_zero_eq τ α
    (HeightSupport.levelCardinal_zero_eq_of_interval τ α hle hlt) (k + 1))

theorem positive_collapse (τ α : Ordinal.{0}) (hle : τ ≤ α)
    (hlt : α < omegaSequence τ 1) (n k : Nat) (hk : 0 < k) (hkn : k < n)
    (ξ : Ordinal.{0}) :
    sourceFiniteCollapse τ n k ξ = sourceFiniteCollapse α n k ξ := by
  apply HeightSupport.finiteCollapse_suffix_congr _ _ n 1 k _ (by omega) hkn ξ
  intro j hj
  cases j with
  | zero => omega
  | succ j => exact omega_succ τ α hle hlt j

theorem next_notation_iff (τ α : Ordinal.{0}) (hle : τ ≤ α)
    (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n) (ξ : Ordinal.{0}) :
    sourceNotation τ n 1 ξ ↔ sourceNotation α n 1 ξ := by
  rw [sourceNotation_iff_hull τ n 1 hn ξ, sourceNotation_iff_hull α n 1 hn ξ,
    ← omega_succ τ α hle hlt 2]
  apply HeightSupport.hull_suffix_congr
  · intro k hk
    cases k with
    | zero => omega
    | succ k => exact omega_succ τ α hle hlt k
  · intro k hk hkn η
    exact positive_collapse τ α hle hlt n k (by omega) hkn η
  · intro η _
    exact positive_collapse τ α hle hlt n 1 (by omega) hn η

noncomputable def tailShift (Ω α δ : Ordinal.{0}) : Ordinal.{0} :=
  Ω * (δ / Ω) + (α + δ % Ω)

theorem tailShift_strictMono (Ω α : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) (hα : α < Ω) :
    StrictMono (tailShift Ω α) := by
  intro δ ε hδε
  have hρδ := Ordinal.mod_lt δ hΩ.ne'
  have hρε := Ordinal.mod_lt ε hΩ.ne'
  have hq : δ / Ω ≤ ε / Ω := Ordinal.div_le_left hδε.le Ω
  rcases hq.eq_or_lt with hq | hq
  · have hρ : δ % Ω < ε % Ω := by
      have he : Ω * (ε / Ω) + δ % Ω < Ω * (ε / Ω) + ε % Ω := by
        calc
          Ω * (ε / Ω) + δ % Ω = δ := by rw [← hq, Ordinal.div_add_mod]
          _ < ε := hδε
          _ = Ω * (ε / Ω) + ε % Ω := (Ordinal.div_add_mod ε Ω).symm
      exact (Ordinal.isNormal_add_right _).strictMono.lt_iff_lt.mp he
    change Ω * (δ / Ω) + (α + δ % Ω) < Ω * (ε / Ω) + (α + ε % Ω)
    rw [hq]
    exact (Ordinal.isNormal_add_right _).strictMono
      ((Ordinal.isNormal_add_right α).strictMono hρ)
  · have hh : Ω * (δ / Ω) < Ω * (ε / Ω) :=
      (Ordinal.isNormal_mul_right hΩ).strictMono hq
    exact (multiple_add_low_lt_of_lt Ω _ _ _ hΩ ⟨δ / Ω, rfl⟩ ⟨ε / Ω, rfl⟩
      hh (hp hα hρδ)).trans_le le_self_add

theorem tailShift_lt_multiple (Ω α δ Δ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) (hα : α < Ω) (hΔ : Ω ∣ Δ)
    (hδ : δ < Δ) : tailShift Ω α δ < Δ := by
  obtain ⟨d, rfl⟩ := hΔ
  have hq : δ / Ω < d := (Ordinal.lt_mul_iff_div_lt hΩ.ne').mp hδ
  have hh : Ω * (δ / Ω) < Ω * d := (Ordinal.isNormal_mul_right hΩ).strictMono hq
  exact multiple_add_low_lt_of_lt Ω _ _ _ hΩ ⟨δ / Ω, rfl⟩ ⟨d, rfl⟩ hh
    (hp hα (Ordinal.mod_lt δ hΩ.ne'))

theorem tailShift_notation_sort (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hα : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (δ : Ordinal.{0}) (hd : sourceNotation τ n 1 δ)
    (hs : δ < omegaSequence τ 2) :
    sourceNotation τ n 1 (tailShift (omegaSequence τ 1) α δ) ∧
      tailShift (omegaSequence τ 1) α δ < omegaSequence τ 2 := by
  let Ω := omegaSequence τ 1
  let head : SourceNotationOrdinal τ n 1 :=
    ⟨Ω * (δ / Ω), high_part_notation τ hτ n 0 (by omega) ⟨δ, hd⟩ hs⟩
  have htail : α + δ % Ω < Ω :=
    (omegaSequence_add_closed τ 0) hα (Ordinal.mod_lt δ (next_cardinal_pos τ hτ 0).ne')
  have hh : head.val < omegaSequence τ 2 := (Ordinal.mul_div_le δ Ω).trans_lt hs
  exact ⟨(shiftArgument τ n 0 (by omega) head _ htail).property,
    shiftArgument_sort τ n 0 (by omega) head hh _ htail⟩

/-- Every zero-index call in the source's OWN minimum hull is below that
minimum, so it becomes an actual parameter in the target hull. Higher calls
agree by the actual finite recursion. The target local ceiling is arbitrary. -/
theorem source_minimum_hull_to_target (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (γ : Ordinal.{0}) (hg : sourceNotation τ n 1 γ)
    (hgs : γ < omegaSequence τ 2) (δ ξ : Ordinal.{0})
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ
      (sourceFiniteCollapse τ n 0 γ) ξ) :
    Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ
      (sourceFiniteCollapse τ n 0 γ) ξ := by
  have hp := sourceFiniteCollapse_proper_notation τ n 0 (by omega) γ hgs hg
  induction hξ with
  | below_base h => exact .below_base (h.trans_le hle)
  | below_parameter h => exact .below_parameter h
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | @higher k η hk hkn hs hη ih =>
    rw [positive_collapse τ α hle hlt n k hk hkn η]
    exact .higher hk hkn (by simpa only [← omega_succ τ α hle hlt (k + 1)] using hs) ih
  | @«local» η hs hη ih =>
    have hηs : η < omegaSequence τ 2 := hs.trans hgs
    have hηn := source_hull_next_notation τ n 0 (by omega) hgs.le hp.le hη
    have hηp := sourceFiniteCollapse_proper_notation τ n 0 (by omega) η hηs hηn
    exact .below_parameter ((finiteCollapse_hull_initial (by omega) γ _).mp
      ⟨.local hs hη, hηp⟩)

/-- Actual relative collapse is bounded by the actual low-tail-shifted source
collapse. Both the target argument membership and candidate are DERIVED. -/
theorem relative_collapse_le_tailShift (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (δ : Ordinal.{0}) (hd : sourceNotation α n 1 δ)
    (hs : δ < omegaSequence τ 2) :
    sourceFiniteCollapse α n 0 δ ≤
      sourceFiniteCollapse τ n 0 (tailShift (omegaSequence τ 1) α δ) := by
  classical
  revert hd hs
  refine Ordinal.induction δ ?_
  intro δ ih hd hs
  let Ω := omegaSequence τ 1
  let f := tailShift Ω α
  let γ := f δ
  let β := sourceFiniteCollapse τ n 0 γ
  have hΩ := next_cardinal_pos τ hτ 0
  have hn0 : 0 < n := by omega
  have hdτ := (next_notation_iff τ α hle hlt n hn δ).mpr hd
  have hγ := tailShift_notation_sort τ α hτ hlt n hn δ hdτ hs
  have hβs : β < Ω := sourceFiniteCollapse_proper_notation τ n 0 hn0 γ hγ.2 hγ.1
  let head : SourceNotationOrdinal τ n 1 :=
    ⟨Ω * (δ / Ω), high_part_notation τ hτ n 0 hn0 ⟨δ, hdτ⟩ hs⟩
  have hhead : head.val < omegaSequence τ 2 := (Ordinal.mul_div_le δ Ω).trans_lt hs
  have htail : α + δ % Ω < Ω := (omegaSequence_add_closed τ 0) hlt (Ordinal.mod_lt δ hΩ.ne')
  have hαβ : α < β := le_self_add.trans_lt
    (tail_lt_collapse τ hτ n 0 hn0 head hhead ⟨δ / Ω, rfl⟩ _ htail)
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β γ :=
    sourceFiniteCollapse_argument_notation τ n 0 hn0 γ hγ.2 hγ.1
  have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 γ β
    head.val (α + δ % Ω) ⟨δ / Ω, rfl⟩ htail).mp hown
  have hρ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β (δ % Ω) := by
    rcases (le_add_self : δ % Ω ≤ α + δ % Ω).eq_or_lt with he | he
    · simpa only [← he] using hsplit.2
    · exact source_hull_initial_segment τ hτ n 0 hn0 γ β hγ.2.le hβs
        hsplit.2 htail he
  have hδ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β δ := by
    simpa only [Ordinal.div_add_mod] using Hull.add hsplit.1 hρ
  have harg := source_minimum_hull_to_target τ α hτ hle hlt n hn γ hγ.1 hγ.2 δ δ hδ
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ξ) :
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β ξ := by
    induction hx with
    | below_base h => exact .below_parameter (h.trans hαβ)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | @higher k η hk hkn hηs hη ihη =>
      rw [← positive_collapse τ α hle hlt n k hk hkn η]
      exact .higher hk hkn (by simpa only [omega_succ τ α hle hlt (k + 1)] using hηs) ihη
    | @«local» η hηδ hη ihη =>
      have hηs : η < omegaSequence τ 2 := hηδ.trans hs
      have hηn := source_hull_next_notation α n 0 hn0
        (by simpa only [← omega_succ τ α hle hlt 1] using hs.le)
        (by simpa only [← omega_succ τ α hle hlt 0] using hβs.le) hη
      have hηbound := ih η hηδ hηn hηs
      have hηmod := Ordinal.mod_lt η hΩ.ne'
      have hηsplit : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β
          (Ω * (η / Ω)) ∧
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β (η % Ω) :=
        (source_hull_multiple_add_low_iff τ hτ n 0 hn0 γ β _ _
          ⟨η / Ω, rfl⟩ hηmod).mp (by simpa only [Ordinal.div_add_mod] using ihη)
      have hfη : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β (f η) :=
        .add hηsplit.1 (.add (.below_parameter hαβ) hηsplit.2)
      have hfηlt : f η < γ := tailShift_strictMono Ω α hΩ
        (omegaSequence_add_closed τ 0) hlt hηδ
      have hfηn := source_hull_next_notation τ n 0 hn0 hγ.2.le hβs.le hfη
      have hfηp := sourceFiniteCollapse_proper_notation τ n 0 hn0 (f η)
        (hfηlt.trans hγ.2) hfηn
      have hcall : sourceFiniteCollapse τ n 0 (f η) < β :=
        (finiteCollapse_hull_initial hn0 γ _).mp ⟨.local hfηlt hfη, hfηp⟩
      exact .below_parameter (hηbound.trans_lt hcall)
  apply finiteCollapse_minimal hn0
  refine ⟨?_, ?_, harg⟩
  · simpa only [← omega_succ τ α hle hlt 0] using hβs
  · intro ξ hx hξs
    apply (finiteCollapse_hull_initial hn0 γ ξ).mp
    exact ⟨forward hx, by simpa only [omega_succ τ α hle hlt 0] using hξs⟩

/-- The original successor hull is a candidate for the actual relative
collapse of the original divided high part. This is the needed alpha-plus
upper bridge; no equality or term-translation theorem is assumed. -/
theorem relative_highPart_le_source_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 1 < n) (A Δ η : Ordinal.{0})
    (hA : sourceNotation τ n 1 A) (hAs : A < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hη : η < omegaSequence τ 1)
    (he : A = Δ + η) :
    sourceFiniteCollapse (sourceFiniteCollapse τ n 0 A) n 0 Δ ≤
      sourceFiniteCollapse τ n 0 (A + 1) := by
  let α := sourceFiniteCollapse τ n 0 A
  let C := sourceFiniteCollapse τ n 0 (A + 1)
  let Ω := omegaSequence τ 1
  have hn0 : 0 < n := by omega
  have hle : τ ≤ α := by simpa only [omegaSequence_zero] using
    (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hαs : α < Ω := sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hA
  have hηs : η + 1 < Ω := (omegaSequence_isSuccLimit τ 0).add_one_lt hη
  have hS : sourceNotation τ n 1 (A + 1) :=
    (SourceCollapseSuccessors.succArgument τ hτ n 0 hn0 ⟨A, hA⟩).property
  have hSs : A + 1 < omegaSequence τ 2 := (omegaSequence_isSuccLimit τ 1).add_one_lt hAs
  have hCs : C < Ω := sourceFiniteCollapse_proper_notation τ n 0 hn0 (A + 1) hSs hS
  have hαC : α < C := SourceCollapseSuccessors.collapse_lt_successor τ hτ n 0 hn0 ⟨A, hA⟩ hAs
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΔs : Δ < omegaSequence τ 2 := hΔA.trans_lt hAs
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (A + 1) C (A + 1) :=
    sourceFiniteCollapse_argument_notation τ n 0 hn0 (A + 1) hSs hS
  have hownSplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 (A + 1) C
    Δ (η + 1) hΔ hηs).mp (by simpa only [he, add_assoc] using hown)
  have harg := source_minimum_hull_to_target τ α hτ hle hαs n hn
    (A + 1) hS hSs Δ Δ hownSplit.1
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 Δ C ξ) :
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (A + 1) C ξ := by
    induction hx with
    | below_base h => exact .below_parameter (h.trans hαC)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | @higher k δ hk hkn hs hδ ih =>
      rw [← positive_collapse τ α hle hαs n k hk hkn δ]
      exact .higher hk hkn (by simpa only [omega_succ τ α hle hαs (k + 1)] using hs) ih
    | @«local» δ hδΔ hδ ih =>
      have hδs : δ < omegaSequence τ 2 := hδΔ.trans hΔs
      have hδn := source_hull_next_notation α n 0 hn0
        (by simpa only [← omega_succ τ α hle hαs 1] using hΔs.le)
        (by simpa only [← omega_succ τ α hle hαs 0] using hCs.le) hδ
      have hb := relative_collapse_le_tailShift τ α hτ hle hαs n hn δ hδn hδs
      have hρ := Ordinal.mod_lt δ (next_cardinal_pos τ hτ 0).ne'
      have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 (A + 1) C
        (Ω * (δ / Ω)) (δ % Ω) ⟨δ / Ω, rfl⟩ hρ).mp
        (by simpa only [Ordinal.div_add_mod] using ih)
      have hf : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (A + 1) C
          (tailShift Ω α δ) := .add hsplit.1 (.add (.below_parameter hαC) hsplit.2)
      have hfl : tailShift Ω α δ < Δ := tailShift_lt_multiple Ω α δ Δ
        (next_cardinal_pos τ hτ 0) (omegaSequence_add_closed τ 0) hαs hΔ hδΔ
      have hfA : tailShift Ω α δ < A + 1 := hfl.trans_le (hΔA.trans (lt_add_one A).le)
      have hfn := source_hull_next_notation τ n 0 hn0 hSs.le hCs.le hf
      have hfp := sourceFiniteCollapse_proper_notation τ n 0 hn0 _ (hfA.trans hSs) hfn
      have hcall : sourceFiniteCollapse τ n 0 (tailShift Ω α δ) < C :=
        (finiteCollapse_hull_initial hn0 (A + 1) _).mp ⟨.local hfA hf, hfp⟩
      exact .below_parameter (hb.trans_lt hcall)
  apply finiteCollapse_minimal hn0
  refine ⟨?_, ?_, harg⟩
  · simpa only [← omega_succ τ α hle hαs 0] using hCs
  · intro ξ hx hξs
    exact (finiteCollapse_hull_initial hn0 (A + 1) ξ).mp
      ⟨forward hx, by simpa only [omega_succ τ α hle hαs 0] using hξs⟩

/-- The same actual inequality in the unbounded source family. One real
finite fragment is obtained from the ORIGINAL source argument. The target
high-part admission and both agreement bounds are derived in that fragment. -/
theorem global_relative_highPart_le_source_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η : Ordinal.{0}) (hA : GlobalNotation τ 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η) :
    globalCollapse (globalCollapse τ 0 A) 0 Δ ≤ globalCollapse τ 0 (A + 1) := by
  obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness τ hτ 1 hA
  have hn0 : 0 < n := by omega
  have hAb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hAn hAs
  let α := globalCollapse τ 0 A
  have hα : α = sourceFiniteCollapse τ n 0 A :=
    globalCollapse_finite_agreement τ hτ n 0 hn0 A hAb
  have hle : τ ≤ α := by rw [hα]; simpa only [omegaSequence_zero] using
    (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hlt : α < omegaSequence τ 1 := by rw [hα]; exact
    sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hAn
  have hαp : 0 < α := hτ.trans_le hle
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α A := by
    rw [hα]; exact sourceFiniteCollapse_argument_notation τ n 0 hn0 A hAs hAn
  have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 A α Δ η hΔ hη).mp
    (by simpa only [he] using hown)
  have hΔn := source_hull_next_notation τ n 0 hn0 hAs.le hlt.le hsplit.1
  have hΔa := (next_notation_iff τ α hle hlt n hn Δ).mp hΔn
  have hΔs : Δ < omegaSequence τ 2 := (by rw [he]; exact le_self_add).trans_lt hAs
  have hΔsa : Δ < omegaSequence α 2 := by simpa only [← omega_succ τ α hle hlt 1] using hΔs
  have hΔb := source_finite_notation_sorted_lt_boundary α hαp n 1 1 le_rfl hn hΔa hΔsa
  have hSn := (SourceCollapseSuccessors.succArgument τ hτ n 0 hn0 ⟨A, hAn⟩).property
  have hSs := (omegaSequence_isSuccLimit τ 1).add_one_lt hAs
  have hSb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hSn hSs
  rw [globalCollapse_finite_agreement α hαp n 0 hn0 Δ hΔb,
    globalCollapse_finite_agreement τ hτ n 0 hn0 (A + 1) hSb, hα]
  exact relative_highPart_le_source_successor τ hτ n hn A Δ η hAn hAs hΔ hη he

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus
