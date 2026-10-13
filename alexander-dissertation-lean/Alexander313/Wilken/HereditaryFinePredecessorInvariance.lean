import Alexander313.Wilken.HereditaryLocalizationOrder
import Alexander313.Wilken.HereditarySourceZetaTransport

/-!
# Actual same-public-base fine-predecessor determinacy

Equal originally admitted theta-zero root values give equal argument values
by genuine collapse injection. The true ANF remainder then determines the
last principal value and its shortened prefix. Both literal first-branch
tests agree. The remaining branch uses the already derived equality of
ordinary localization VALUE paths, not literal support or spelling equality.

The chosen native predecessors need not have equal codes. Their ordinal
values, and their actual canonical emissions, agree. Original raw adapters
use the genuine normalizer and retain all original guards. This is a derived
same-base invariance theorem, not fine lex order or a cross-base translation.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FinePredecessor.Invariance

open Localization

private theorem map_tail {alpha beta : Type} (f : alpha → beta) (xs : List alpha) :
    xs.tail.map f = (xs.map f).tail := by
  cases xs <;> rfl

private theorem map_stripLast {alpha beta : Type} (f : alpha → beta) (xs : List alpha) :
    (stripLast xs).map f = stripLast (xs.map f) := by
  simp only [stripLast, List.map_reverse, map_tail]

private theorem map_head_getD {alpha beta : Type} (f : alpha → beta)
    (xs : List alpha) (z : alpha) :
    f (xs.head?.getD z) = (xs.map f).head?.getD (f z) := by
  cases xs <;> rfl

private theorem map_second_getD {alpha beta : Type} (f : alpha → beta)
    (xs : List alpha) (z : alpha) :
    f (xs[1]?.getD z) = (xs.map f)[1]?.getD (f z) := by
  cases xs with
  | nil => rfl
  | cons a xs => cases xs <;> rfl

private theorem nil_iff_of_map_eq {alpha beta gamma : Type}
    (f : alpha → gamma) (g : beta → gamma) (xs : List alpha) (ys : List beta)
    (he : xs.map f = ys.map g) : xs = [] ↔ ys = [] := by
  cases xs <;> cases ys <;> simp_all

/-- Original weak-normal nodes supply the actual injective collapse callers. -/
theorem argument_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : argumentValue r c = argumentValue r d := by
  exact SourceZeta.Transport.argument_value_injective r c d
    (SourceZeta.Transport.normal_raw_input r c ((Localization.inputCheck_exact r c).mpr hc))
    (SourceZeta.Transport.normal_raw_input r d ((Localization.inputCheck_exact r d).mpr hd)) he

theorem parts_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : delta r c = delta r d ∧ residual r c = residual r d := by
  have ha := argument_value_eq r c d hc hd he
  have hp := SourceDecomposition.parts_code_value r 0 _ (argument_accepted r c hc)
  have hq := SourceDecomposition.parts_code_value r 0 _ (argument_accepted r d hd)
  exact ⟨hp.1.trans ((congrArg (fun x => omegaSequence (finiteBase r) 1 *
    (x / omegaSequence (finiteBase r) 1)) ha).trans hq.1.symm),
    hp.2.trans ((congrArg (fun x => x % omegaSequence (finiteBase r) 1) ha).trans hq.2.symm)⟩

theorem lowWord_values_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) :
    (lowWord r c).map (denote r) = (lowWord r d).map (denote r) := by
  have hp := (SourceDecomposition.parts_anf r 0 _ (argument_accepted r c hc)).2
  have hq := (SourceDecomposition.parts_anf r 0 _ (argument_accepted r d hd)).2
  exact hp.trans ((congrArg canonicalANF (parts_value_eq r c d hc hd he).2).trans hq.symm)

theorem lowWord_empty_iff (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : lowWord r c = [] ↔ lowWord r d = [] :=
  nil_iff_of_map_eq (denote r) (denote r) _ _ (lowWord_values_eq r c d hc hd he)

theorem prefixResidual_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : prefixResidual r c = prefixResidual r d := by
  unfold prefixResidual
  rw [map_stripLast, map_stripLast, lowWord_values_eq r c d hc hd he]

theorem lastAtom_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : denote r (lastAtom r c) = denote r (lastAtom r d) := by
  simp only [lastAtom, map_head_getD, List.map_reverse,
    Theta.Normalization.zeroTree_denote, lowWord_values_eq r c d hc hd he]

theorem prefixCode_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : interpretation r (prefixCode r c) = interpretation r (prefixCode r d) := by
  rw [prefixCode_value, prefixCode_value, (parts_value_eq r c d hc hd he).1,
    prefixResidual_value_eq r c d hc hd he]

theorem prefixNode_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : value r (prefixNode r c) = value r (prefixNode r d) := by
  simpa only [value, prefixNode, interpretation_code, denote, eval,
    prefixCode] using congrArg (globalCollapse (finiteBase r) 0)
      (prefixCode_value_eq r c d hc hd he)

/-- Both the unit condition and the ordinary STRICT supremum condition are
determined by actual ANF values, including the empty-remainder boundary. -/
theorem firstBranch_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : firstBranch r c = firstBranch r d := by
  have hn := not_congr (lowWord_empty_iff r c d hc hd he)
  have hp := parts_value_eq r c d hc hd he
  have hs : firstBranch r c = true ↔ firstBranch r d = true := by
    rw [firstBranch_exact r c hc, firstBranch_exact r d hd]
    simp only [FirstCase, hn, lastAtom_value_eq r c d hc hd he,
      prefixResidual_value_eq r c d hc hd he, hp.1]
  cases hleft : firstBranch r c <;> cases hright : firstBranch r d <;> simp_all

theorem inputCheck_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : inputCheck r c = inputCheck r d := by
  have hs : inputCheck r c = true ↔ inputCheck r d = true := by
    simp only [inputCheck_exact, hc, hd, true_and, he]
  cases hleft : inputCheck r c <;> cases hright : inputCheck r d <;> simp_all

/-- The literal penultimate spellings may differ; the actual penultimate
ordinal is determined by the derived ordinary value-path equality. -/
theorem fallback_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : value r (fallback r c) = value r (fallback r d) := by
  have hp := Localization.Order.values_eq_of_value_eq r c d hc hd he
  simp only [Localization.Order.values] at hp
  simp only [fallback, penultimate, map_second_getD, List.map_reverse, hp]

theorem predecessorCode_value_eq (r c d : Nat) (hc : inputCheck r c = true)
    (hd : inputCheck r d = true) (he : value r c = value r d) :
    value r (predecessorCode r c) = value r (predecessorCode r d) := by
  have hcn := ((inputCheck_exact r c).mp hc).1
  have hdn := ((inputCheck_exact r d).mp hd).1
  have hbranch := firstBranch_eq r c d hcn hdn he
  simp only [predecessorCode, hc, hd, Bool.cond_true, nativeCode, ← hbranch]
  cases hb : firstBranch r c with
  | false => simpa only [hb, Bool.cond_false] using fallback_value_eq r c d hcn hdn he
  | true => simpa only [hb, Bool.cond_true] using prefixNode_value_eq r c d hcn hdn he

theorem predecessor_value_eq (r c d a b : Nat) (ha : a ∈ predecessor r c)
    (hb : b ∈ predecessor r d) (he : value r c = value r d) : value r a = value r b := by
  obtain ⟨hc, rfl⟩ := (predecessor_graph r c a).mp ha
  obtain ⟨hd, rfl⟩ := (predecessor_graph r d b).mp hb
  exact predecessorCode_value_eq r c d hc hd he

theorem canonicalCode_eq (r c d : Nat) (hc : inputCheck r c = true)
    (hd : inputCheck r d = true) (he : value r c = value r d) : canonicalCode r c = canonicalCode r d := by
  have hp := canonicalCode_spec r c hc
  have hq := canonicalCode_spec r d hd
  exact Canonical.check_value_injective _ _ hp.1 hq.1
    (hp.2.trans ((predecessorCode_value_eq r c d hc hd he).trans hq.2.symm))

theorem rawPredecessorCode_value_eq (r c d : Nat) (hc : rawInputCheck r c = true)
    (hd : rawInputCheck r d = true) (he : interpretation r c = interpretation r d) :
    value r (rawPredecessorCode r c) = value r (rawPredecessorCode r d) := by
  have hcn := raw_normalized_input r c hc
  have hdn := raw_normalized_input r d hd
  have hcc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  have hdd := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hd).1).1
  have hp := (Theta.Normalization.normalizeCode_checked r c hcc).2.2
  have hq := (Theta.Normalization.normalizeCode_checked r d hdd).2.2
  have hv := predecessorCode_value_eq r _ _ hcn hdn (hp.trans (he.trans hq.symm))
  simpa only [rawPredecessorCode, hc, hd, Bool.cond_true] using hv

/-- Actual canonical emission of the executing original raw predecessor. -/
def rawCanonicalCode (r c : Nat) : Nat := cond (rawInputCheck r c)
  (Localization.emit r (rawPredecessorCode r c)) 0

theorem rawCanonicalCode_primrec : Primrec₂ rawCanonicalCode :=
  (rawInputCheck_primrec.cond (Localization.emit_primrec.comp Primrec.fst rawPredecessorCode_primrec)
    (Primrec.const 0)).to₂

theorem rawCanonicalCode_spec (r c : Nat) (hc : rawInputCheck r c = true) :
    Canonical.check (rawCanonicalCode r c) = true ∧
      unionInterpretation (rawCanonicalCode r c) = value r (rawPredecessorCode r c) := by
  simpa only [rawCanonicalCode, hc, Bool.cond_true] using
    Localization.emit_spec r _ (rawPredecessor_spec r c hc).1

theorem rawCanonicalCode_eq (r c d : Nat) (hc : rawInputCheck r c = true)
    (hd : rawInputCheck r d = true) (he : interpretation r c = interpretation r d) :
    rawCanonicalCode r c = rawCanonicalCode r d := by
  have hp := rawCanonicalCode_spec r c hc
  have hq := rawCanonicalCode_spec r d hd
  exact Canonical.check_value_injective _ _ hp.1 hq.1
    (hp.2.trans ((rawPredecessorCode_value_eq r c d hc hd he).trans hq.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.FinePredecessor.Invariance
