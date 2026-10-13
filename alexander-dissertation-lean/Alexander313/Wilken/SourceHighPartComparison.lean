import Alexander313.Wilken.SourceCollapseSuccessors
import Alexander313.Wilken.SourceFixedPointLimits
import Alexander313.Wilken.HereditaryLocalizationRefinements

/-!
# Actual source high parts and residual comparison

The high part is the genuine ordinal left-division multiple
Omega * (argument / Omega), with remainder argument % Omega. A finite
canonical-ANF cut derives its source admission; no admitted partition or
high-part projection is supplied as a hypothesis. Actual argument-star and
low-tail bounds prove strict comparison inside each divisible high part.
This strengthens the adjacent-interval barrier to source Lemma 2.31 and
proves the selected localization levels strictly descend, as in 2.33(b).
The initial base is excluded from that descending list. The full corrected
fixed-point iff and fine localization are separate. All proof terms remain
uncompiled source candidates.
-/

namespace Alexander313.Wilken.SourceHighPartComparison

noncomputable def highPart (Omega a : Ordinal.{0}) : Ordinal.{0} := Omega * (a / Omega)

noncomputable def tailPart (Omega a : Ordinal.{0}) : Ordinal.{0} := a % Omega

theorem highPart_add_tailPart (Omega a : Ordinal.{0}) : highPart Omega a + tailPart Omega a = a :=
  Ordinal.div_add_mod a Omega

theorem highPart_le (Omega a : Ordinal.{0}) : highPart Omega a ≤ a := Ordinal.mul_div_le a Omega

theorem tailPart_lt (Omega a : Ordinal.{0}) (hOmega : 0 < Omega) : tailPart Omega a < Omega :=
  Ordinal.mod_lt a hOmega.ne'

theorem highPart_dvd (Omega a : Ordinal.{0}) : Omega ∣ highPart Omega a := ⟨a / Omega, rfl⟩

theorem highPart_mono (Omega : Ordinal.{0}) : Monotone (highPart Omega) := by
  intro a b hab
  exact mul_le_mul' le_rfl (Ordinal.div_le_left hab Omega)

/-- A principal atom above a positive cut has zero remainder at that cut.
This follows from principal closure and the actual division equation. -/
theorem principal_dvd_of_le (Omega p : Ordinal.{0}) (hOmega : 0 < Omega)
    (hp : Ordinal.IsPrincipal (· + ·) p) (hOp : Omega ≤ p) : Omega ∣ p := by
  apply Ordinal.dvd_of_mod_eq_zero
  by_contra hr
  have hrem : 0 < p % Omega := lt_of_le_of_ne (zero_le) (Ne.symm hr)
  have hprefix : Omega * (p / Omega) < p := by
    calc
      Omega * (p / Omega) = Omega * (p / Omega) + 0 := (add_zero _).symm
      _ < Omega * (p / Omega) + p % Omega := add_lt_add_right hrem _
      _ = p := Ordinal.div_add_mod p Omega
  have hsmall : p % Omega < p := (Ordinal.mod_lt p hOmega.ne').trans_le hOp
  have hbad : Omega * (p / Omega) + p % Omega < p := hp hprefix hsmall
  rw [Ordinal.div_add_mod] at hbad
  exact lt_irrefl _ hbad

private theorem principalSum_dvd (Omega : Ordinal.{0}) (xs : List Ordinal.{0})
    (hx : ∀ p ∈ xs, Omega ∣ p) : Omega ∣ principalSum xs := by
  revert hx
  induction xs with
  | nil => intro hx; exact ⟨0, by simp only [principalSum, mul_zero]⟩
  | cons p xs ih =>
    intro hx
    exact (Ordinal.dvd_add_iff (hx p List.mem_cons_self)).mpr
      (ih (fun q hq => hx q (List.mem_cons_of_mem _ hq)))

private theorem descending_cut (Omega : Ordinal.{0}) (xs : List Ordinal.{0})
    (hx : xs.Pairwise (fun a b => b ≤ a)) :
    ∃ high low : List Ordinal.{0}, xs = high ++ low ∧
      (∀ p ∈ high, Omega ≤ p) ∧ (∀ p ∈ low, p < Omega) := by
  classical
  revert hx
  induction xs with
  | nil => exact fun hx => ⟨[], [], rfl, by simp, by simp⟩
  | cons p xs ih =>
    intro hx
    by_cases hp : Omega ≤ p
    · obtain ⟨high, low, he, hh, hl⟩ := ih (List.pairwise_cons.mp hx).2
      refine ⟨p :: high, low, ?_, ?_, hl⟩
      · simp only [List.cons_append, he]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hh q hq
    · refine ⟨[], p :: xs, rfl, by simp, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact lt_of_not_ge hp
      · exact ((List.pairwise_cons.mp hx).1 q hq).trans_lt (lt_of_not_ge hp)

private theorem normal_append_parts (high low : List Ordinal.{0})
    (hn : IsAdditiveNormalForm (high ++ low)) :
    IsAdditiveNormalForm high ∧ IsAdditiveNormalForm low := by
  have hp := List.pairwise_append.mp hn.2
  exact ⟨⟨fun p h => hn.1 p (List.mem_append.mpr (Or.inl h)), hp.1⟩,
    ⟨fun p h => hn.1 p (List.mem_append.mpr (Or.inr h)), hp.2.1⟩⟩

/-- The actual division split is a prefix/suffix split of canonical ANF.
It includes high=empty and low=empty without a special-case oracle. -/
theorem canonicalANF_divmod_split (Omega a : Ordinal.{0}) (hOmega : 0 < Omega)
    (hprincipal : Ordinal.IsPrincipal (· + ·) Omega) :
    ∃ high low : List Ordinal.{0}, canonicalANF a = high ++ low ∧
      IsAdditiveNormalForm high ∧ IsAdditiveNormalForm low ∧
      (∀ p ∈ high, Omega ≤ p) ∧ (∀ p ∈ low, p < Omega) ∧
      highPart Omega a = principalSum high ∧ tailPart Omega a = principalSum low := by
  obtain ⟨high, low, he, hh, hl⟩ := descending_cut Omega (canonicalANF a) (canonicalANF_normal a).2
  have hn : IsAdditiveNormalForm (high ++ low) := by rw [← he]; exact canonicalANF_normal a
  have hparts := normal_append_parts high low hn
  have hlow : principalSum low < Omega := principalSum_lt hOmega hprincipal low hl
  have hhighDvd : Omega ∣ principalSum high := principalSum_dvd Omega high (by
    intro p hp
    exact principal_dvd_of_le Omega p hOmega (hparts.1.1 p hp).2 (hh p hp))
  obtain ⟨q, hq⟩ := hhighDvd
  have hvalue : a = principalSum high + principalSum low := by
    rw [← principalSum_canonicalANF a, he, principalSum_append]
  have hdiv : a / Omega = q := by
    rw [hvalue, hq, Ordinal.mul_add_div _ hOmega.ne', Ordinal.div_eq_zero_of_lt hlow, add_zero]
  have hhi : highPart Omega a = principalSum high := by rw [highPart, hdiv, ← hq]
  have hlo : tailPart Omega a = principalSum low := by
    rw [tailPart, hvalue, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlow]
  exact ⟨high, low, he, hparts.1, hparts.2, hh, hl, hhi, hlo⟩

theorem source_principalSum_notation (tau : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (xs : List Ordinal.{0}) (hx : ∀ p ∈ xs, sourceNotation tau n (m + 1) p) :
    sourceNotation tau n (m + 1) (principalSum xs) := by
  revert hx
  induction xs with
  | nil =>
    intro hx
    exact (source_nextNotation_iff_hull tau n m hm 0).mpr
      (.below_parameter (omegaSequence_isSuccLimit tau m).bot_lt)
  | cons p xs ih =>
    intro hx
    apply (source_nextNotation_iff_hull tau n m hm _).mpr
    exact .add ((source_nextNotation_iff_hull tau n m hm p).mp (hx p List.mem_cons_self))
      ((source_nextNotation_iff_hull tau n m hm _).mp
        (ih (fun q hq => hx q (List.mem_cons_of_mem _ hq))))

/-- The high part is proved admitted from the original argument's actual
canonical principal components. Division itself is not a source closure rule. -/
theorem highPart_notation (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal tau n (m + 1)) :
    sourceNotation tau n (m + 1) (highPart (omegaSequence tau (m + 1)) a.val) := by
  obtain ⟨high, low, he, hhN, hlN, hh, hl, hhi, hlo⟩ :=
    canonicalANF_divmod_split (omegaSequence tau (m + 1)) a.val
      (omegaSequence_isSuccLimit tau m).bot_lt (omegaSequence_add_closed tau m)
  rw [hhi]
  apply source_principalSum_notation tau n m hm high
  intro p hp
  exact (sourceComponent tau htau n m hm a p
    (by rw [he]; exact List.mem_append.mpr (Or.inl hp))).property

noncomputable def highArgument (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal tau n (m + 1)) :
    SourceNotationOrdinal tau n (m + 1) :=
  ⟨highPart (omegaSequence tau (m + 1)) a.val, highPart_notation tau htau n m hm a⟩

def lowArgument (tau : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (eta : Ordinal.{0}) (heta : eta < omegaSequence tau (m + 1)) :
    SourceNotationOrdinal tau n (m + 1) :=
  ⟨eta, sourceNotation_next_of_low tau n m hm heta⟩

def residualArgument (tau : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (delta : SourceNotationOrdinal tau n (m + 1))
    (eta : Ordinal.{0}) (heta : eta < omegaSequence tau (m + 1)) :
    SourceNotationOrdinal tau n (m + 1) :=
  SourceCollapseSuccessors.addArgument tau n m hm delta (lowArgument tau n m hm eta heta)

@[simp] theorem residualArgument_val (tau : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (delta : SourceNotationOrdinal tau n (m + 1))
    (eta : Ordinal.{0}) (heta : eta < omegaSequence tau (m + 1)) :
    (residualArgument tau n m hm delta eta heta).val = delta.val + eta := rfl

/-- The full actual collapse is strictly increasing in the low residual
within a fixed divisible high part. The earlier high star survives in the
later argument; the earlier tail is below the genuine later collapse. -/
theorem same_high_part_strict (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (delta : SourceNotationOrdinal tau n (m + 1))
    (hdeltaSort : delta.val < omegaSequence tau (m + 2))
    (hdeltaDvd : omegaSequence tau (m + 1) ∣ delta.val)
    (eta rho : Ordinal.{0}) (hetarho : eta < rho) (hrho : rho < omegaSequence tau (m + 1)) :
    sourceFiniteCollapse tau n m (delta.val + eta) <
      sourceFiniteCollapse tau n m (delta.val + rho) := by
  have heta := hetarho.trans hrho
  let a := SourceFixedPointLimits.shiftArgument tau n m hm delta eta heta
  let b := SourceFixedPointLimits.shiftArgument tau n m hm delta rho hrho
  have ha := SourceFixedPointLimits.shiftArgument_sort tau n m hm delta hdeltaSort eta heta
  have hb := SourceFixedPointLimits.shiftArgument_sort tau n m hm delta hdeltaSort rho hrho
  apply (sourceFiniteCollapse_lt_iff_sourceStar tau htau n m hm a b ha hb).mpr
  refine Or.inl ⟨add_lt_add_right hetarho _, ?_⟩
  change sourceStar tau htau n m hm a < sourceFiniteCollapse tau n m b.val
  rw [SourceFixedPointLimits.star_shift_eq_max tau htau n m hm delta hdeltaDvd eta heta]
  apply max_lt
  · have hhigh : sourceStar tau htau n m hm delta ≤ sourceStar tau htau n m hm b := by
      rw [SourceFixedPointLimits.star_shift_eq_max tau htau n m hm delta hdeltaDvd rho hrho]
      exact le_max_left _ _
    exact hhigh.trans_lt (sourceStar_lt_sourceFiniteCollapse tau htau n m hm b hb)
  · exact (SourceCollapseSuccessors.star_le_argument_of_low tau htau n m hm
      (SourceFixedPointLimits.lowArgument tau n m hm eta heta) heta).trans_lt
      (hetarho.trans (SourceFixedPointLimits.tail_lt_collapse tau htau n m hm delta
        hdeltaSort hdeltaDvd rho hrho))

theorem residual_strictMonoOn (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (delta : SourceNotationOrdinal tau n (m + 1))
    (hdeltaSort : delta.val < omegaSequence tau (m + 2))
    (hdeltaDvd : omegaSequence tau (m + 1) ∣ delta.val) :
    StrictMonoOn (fun eta : Ordinal.{0} => sourceFiniteCollapse tau n m (delta.val + eta))
      (Set.Iio (omegaSequence tau (m + 1))) :=
  fun eta heta rho hrho hlt => same_high_part_strict tau htau n m hm delta hdeltaSort hdeltaDvd
    eta rho hlt hrho

/-- Increasing actual theta values with reversed argument order force
strict high-part descent. Equality of high parts is ruled out by the genuine
same-block residual comparison, rather than by an assumed partition law. -/
theorem highPart_lt_of_argument_le (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal tau n (m + 1))
    (ha : a.val < omegaSequence tau (m + 2)) (hb : b.val < omegaSequence tau (m + 2))
    (hab : sourceFiniteCollapse tau n m a.val < sourceFiniteCollapse tau n m b.val)
    (hba : b.val ≤ a.val) :
    highPart (omegaSequence tau (m + 1)) b.val < highPart (omegaSequence tau (m + 1)) a.val := by
  let Omega := omegaSequence tau (m + 1)
  have hOmega : 0 < Omega := (omegaSequence_isSuccLimit tau m).bot_lt
  have hle := highPart_mono Omega hba
  apply lt_of_le_of_ne hle
  intro he
  let delta := highArgument tau htau n m hm a
  let eta := tailPart Omega a.val
  let rho := tailPart Omega b.val
  have hdeltaSort : delta.val < omegaSequence tau (m + 2) := (highPart_le Omega a.val).trans_lt ha
  have hdeltaDvd : Omega ∣ delta.val := highPart_dvd Omega a.val
  have heta : eta < Omega := tailPart_lt Omega a.val hOmega
  have hrho : rho < Omega := tailPart_lt Omega b.val hOmega
  have hav : a.val = delta.val + eta := (highPart_add_tailPart Omega a.val).symm
  have hbv : b.val = delta.val + rho := by
    rw [← highPart_add_tailPart Omega b.val, he]
    rfl
  have hresidual : rho ≤ eta := (add_le_add_iff_left delta.val).mp (by rw [← hbv, ← hav]; exact hba)
  by_cases hresidualEq : rho = eta
  · have hargs : b.val = a.val := by rw [hbv, hresidualEq, ← hav]
    exact (ne_of_lt hab) (congrArg (sourceFiniteCollapse tau n m) hargs).symm
  · have hresidualLt := lt_of_le_of_ne hresidual hresidualEq
    have hreverse := same_high_part_strict tau htau n m hm delta hdeltaSort hdeltaDvd rho eta
      hresidualLt heta
    rw [← hbv, ← hav] at hreverse
    exact lt_asymm hab hreverse

/-- Source Lemma 2.31 for the actual finite family: the argument of every
genuine theta value in the adjacent interval has strictly lower Omega part. -/
theorem adjacent_highPart_lt (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal tau n (m + 1))
    (ha : a.val < omegaSequence tau (m + 2)) (hb : b.val < omegaSequence tau (m + 2))
    (hab : sourceFiniteCollapse tau n m a.val < sourceFiniteCollapse tau n m b.val)
    (hbs : sourceFiniteCollapse tau n m b.val < sourceFiniteCollapse tau n m (a.val + 1)) :
    highPart (omegaSequence tau (m + 1)) b.val < highPart (omegaSequence tau (m + 1)) a.val :=
  highPart_lt_of_argument_le tau htau n m hm a b ha hb hab
    (SourceCollapseSuccessors.adjacent_argument_lt tau htau n m hm a b ha hb hab hbs).le

theorem global_highPart_lt_of_argument_le (tau : Ordinal.{0}) (htau : 0 < tau)
    (m : Nat) (a b : GlobalNotationOrdinal tau (m + 1))
    (ha : a.val < omegaSequence tau (m + 2)) (hb : b.val < omegaSequence tau (m + 2))
    (hab : globalCollapse tau m a.val < globalCollapse tau m b.val) (hba : b.val ≤ a.val) :
    highPart (omegaSequence tau (m + 1)) b.val < highPart (omegaSequence tau (m + 1)) a.val := by
  obtain ⟨n, hmn, han, hbn⟩ := globalNotation_common_fragment tau htau (m + 1) a b
  have hm : m < n := by omega
  let an : SourceNotationOrdinal tau n (m + 1) := ⟨a.val, han⟩
  let bn : SourceNotationOrdinal tau n (m + 1) := ⟨b.val, hbn⟩
  have habound := source_finite_notation_sorted_lt_boundary tau htau n (m + 1) (m + 1)
    le_rfl hmn han ha
  have hbbound := source_finite_notation_sorted_lt_boundary tau htau n (m + 1) (m + 1)
    le_rfl hmn hbn hb
  rw [globalCollapse_finite_agreement tau htau n m hm a.val habound,
    globalCollapse_finite_agreement tau htau n m hm b.val hbbound] at hab
  exact highPart_lt_of_argument_le tau htau n m hm an bn ha hb hab hba

/-- The same exact high-part exclusion in the genuine direct-limit family. -/
theorem global_adjacent_highPart_lt (tau : Ordinal.{0}) (htau : 0 < tau)
    (m : Nat) (a b : GlobalNotationOrdinal tau (m + 1))
    (ha : a.val < omegaSequence tau (m + 2)) (hb : b.val < omegaSequence tau (m + 2))
    (hab : globalCollapse tau m a.val < globalCollapse tau m b.val)
    (hbs : globalCollapse tau m b.val < globalCollapse tau m (a.val + 1)) :
    highPart (omegaSequence tau (m + 1)) b.val < highPart (omegaSequence tau (m + 1)) a.val :=
  global_highPart_lt_of_argument_le tau htau m a b ha hb hab
    (SourceCollapseSuccessors.global_adjacent_argument_lt tau htau m a b ha hb hab hbs).le

noncomputable def localizationLevel (r c : Nat) : Ordinal.{0} :=
  highPart (omegaSequence (RelativeTerm.Hereditary.finiteBase r) 1)
    (RelativeTerm.Hereditary.Localization.argumentValue r c)

open RelativeTerm.Hereditary

/-- Transport the genuine finite high-part comparison to original hereditary
theta-zero nodes, keeping their actual source admission. -/
theorem node_level_lt (r c d : Nat)
    (hc : RelativeTerm.Hereditary.Localization.Node r c)
    (hd : RelativeTerm.Hereditary.Localization.Node r d)
    (hv : RelativeTerm.Hereditary.Localization.value r c < RelativeTerm.Hereditary.Localization.value r d)
    (harg : RelativeTerm.Hereditary.Localization.argumentValue r d ≤
      RelativeTerm.Hereditary.Localization.argumentValue r c) : localizationLevel r d < localizationLevel r c := by
    obtain ⟨a, rfl, hca, hna⟩ := hc
    obtain ⟨b, rfl, hdb, hnb⟩ := hd
    let n := max (.theta 0 a : RelativeTerm Nat).height (.theta 0 b : RelativeTerm Nat).height
    have hat := Theta.checked_admissible r n (.theta 0 a) hca (Nat.le_max_left _ _)
    have hbt := Theta.checked_admissible r n (.theta 0 b) hdb (Nat.le_max_right _ _)
    have hn : 0 < n := by
      cases hat.2 with
      | theta h0k hkn hsort ha => exact hkn
    have haa := Theta.admitted_theta_argument hat
    have hbb := Theta.admitted_theta_argument hbt
    let an := RelativeTerm.sourceAdmittedOrdinal (finiteBase r) (parameters r) n 0 hn a haa.2
    let bn := RelativeTerm.sourceAdmittedOrdinal (finiteBase r) (parameters r) n 0 hn b hbb.2
    have hasort : an.val < omegaSequence (finiteBase r) 2 := by
      cases hat.2 with
      | theta h0k hkn hsort ha => exact hsort
    have hbsort : bn.val < omegaSequence (finiteBase r) 2 := by
      cases hbt.2 with
      | theta h0k hkn hsort hb => exact hsort
    have hav : an.val = denote r a := (denote_eq_finite r n a haa.2).symm
    have hbv : bn.val = denote r b := (denote_eq_finite r n b hbb.2).symm
    have hvalues : sourceFiniteCollapse (finiteBase r) n 0 an.val <
        sourceFiniteCollapse (finiteBase r) n 0 bn.val := by
      change finiteDenote r n (.theta 0 a) < finiteDenote r n (.theta 0 b)
      rw [← denote_eq_finite r n (.theta 0 a) hat.2, ← denote_eq_finite r n (.theta 0 b) hbt.2]
      simpa only [Localization.value, interpretation_code] using hv
    have harguments : bn.val ≤ an.val := by
      rw [hav, hbv]
      simpa only [Localization.argumentValue, Localization.argumentCode_theta, interpretation_code] using harg
    have hlevel := highPart_lt_of_argument_le (finiteBase r) (finiteBase_pos r) n 0 hn an bn
      hasort hbsort hvalues harguments
    rw [hav, hbv] at hlevel
    simpa only [localizationLevel, Localization.argumentValue, Localization.argumentCode_theta,
      interpretation_code] using hlevel

/-- Source Lemma 2.33(b): after the initial base, every selected fixed-point
level is a genuine Omega-one multiple and the levels strictly descend. -/
theorem sourcePath_levels_descending {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : RelativeTerm.Hereditary.Localization.SourcePath r source (c :: tail)) :
    (tail.map (localizationLevel r)).Pairwise (fun a b => b < a) := by
  have hall : ∀ {path : List Nat},
      RelativeTerm.Hereditary.Localization.SourcePath r source path →
      (path.tail.map (localizationLevel r)).Pairwise (fun a b => b < a) := by
    intro path hp
    induction hp with
    | stop c hc hmax => simp
    | next c d tail hc hcd hd harg hp ih =>
      change (localizationLevel r d :: tail.map (localizationLevel r)).Pairwise (fun a b => b < a)
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have hde := RelativeTerm.Hereditary.Localization.Refinements.sourcePath_head_lt_tail hp e he
      have hdn := hp.nodes d List.mem_cons_self
      have hen := hp.nodes e (List.mem_cons_of_mem _ he)
      have hle := harg e (RelativeTerm.Hereditary.Localization.Refinements.sourcePath_tail_mem hp e he)
        (hcd.trans hde)
      exact node_level_lt r d e hdn hen hde hle
  exact hall hp

theorem nativePath_levels_descending (r c : Nat)
    (hc : RelativeTerm.Hereditary.Localization.inputCheck r c = true) :
    ((RelativeTerm.Hereditary.Localization.nativePath r c).tail.map (localizationLevel r)).Pairwise
      (fun a b => b < a) := by
  obtain ⟨tail, he⟩ := RelativeTerm.Hereditary.Localization.nativePath_head r c
  have hp := RelativeTerm.Hereditary.Localization.nativePath_source r c hc
  rw [he] at hp ⊢
  simpa only [List.tail_cons] using sourcePath_levels_descending hp

theorem localizationLevel_multiple (r c : Nat) :
    omegaSequence (RelativeTerm.Hereditary.finiteBase r) 1 ∣ localizationLevel r c :=
  highPart_dvd _ _

end Alexander313.Wilken.SourceHighPartComparison
