import Alexander313.Wilken.HereditaryThetaNormal
import Alexander313.Wilken.HereditaryThetaNormalization
import Alexander313.Wilken.HereditaryThetaEmbeddings

/-! # Genuine uniform effectivity of full hereditary normalization

The actual suffix absorber and zero-based source reconstruction are finite
list folds. A literal all-level code course evaluates the actual normalizer,
including earlier payload decoding and its zero-tree fallback. The equality
holds on every raw tree; the raw code operation keeps whole decoder failure
at zero. Original admission/value preservation is proved in the semantic
normalization module and is not supplied as an effectivity hypothesis.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization.Effective

open ThetaCourse
open Theta.Effective

theorem zeroTree_primrec : Primrec zeroTree := by
  have h := rawTree_primrec.comp BaseArithmetic.zeroCode_primrec
  simpa only [BaseArithmetic.zeroCode_eq, rawTree_code] using h

private def prependNumeric (r : Nat) (a : RelativeTerm Nat)
    (as : List (RelativeTerm Nat)) : List (RelativeTerm Nat) :=
  cond (as.length == 0) [a]
    (cond (less r a (as[0]?.getD (.parameter 0))) as (a :: as))

theorem prependAtom_primrec : Primrec
    (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) =>
      prependAtom p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.1) :=
    Primrec.fst
  have ha : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have has : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hhead := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp has (Primrec.const 0)) (Primrec.const (RelativeTerm.parameter 0))
  have h := (Primrec.beq.comp (Primrec.list_length.comp has) (Primrec.const 0)).cond
    (Primrec.list_cons.comp ha (Primrec.const []))
    ((less_primrec.comp (hr.pair (ha.pair hhead))).cond has (Primrec.list_cons.comp ha has))
  have heq : (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) =>
      prependNumeric p.1 p.2.1 p.2.2) =
      (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) =>
        prependAtom p.1 p.2.1 p.2.2) := by
    funext p
    cases p.2.2 <;> simp [prependNumeric, prependAtom]
  change Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) =>
    prependNumeric p.1 p.2.1 p.2.2) at h
  rw [heq] at h
  exact h

theorem normalizeAtoms_primrec : Primrec₂ normalizeAtoms := by
  have hs : Primrec₂ (fun p : Nat × List (RelativeTerm Nat) =>
      fun q : RelativeTerm Nat × List (RelativeTerm Nat) => prependAtom p.1 q.1 q.2) :=
    (prependAtom_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have heq : (fun p : Nat × List (RelativeTerm Nat) => p.2.foldr (prependAtom p.1) []) =
      (fun p : Nat × List (RelativeTerm Nat) => normalizeAtoms p.1 p.2) := by
    funext p
    induction p.2 <;> simp_all [normalizeAtoms]
  change Primrec (fun p : Nat × List (RelativeTerm Nat) => p.2.foldr (prependAtom p.1) []) at h
  rw [heq] at h
  exact h.to₂

private theorem buildRev_fold (r : Nat) (as : List (RelativeTerm Nat)) :
    buildRev r as = as.foldr (fun a t => .sum t a) (zeroTree r) := by
  induction as <;> simp_all [buildRev]

theorem buildAtoms_primrec : Primrec₂ buildAtoms := by
  have hs : Primrec₂ (fun (_ : Nat × List (RelativeTerm Nat)) =>
      fun p : RelativeTerm Nat × RelativeTerm Nat => RelativeTerm.sum p.1 p.2) :=
    (sum_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldl Primrec.snd (zeroTree_primrec.comp Primrec.fst) hs
  have heq : (fun p : Nat × List (RelativeTerm Nat) =>
      p.2.foldl RelativeTerm.sum (zeroTree p.1)) =
      (fun p : Nat × List (RelativeTerm Nat) => buildAtoms p.1 p.2) := by
    funext p
    rw [buildAtoms, buildRev_fold, List.foldr_reverse]
  change Primrec (fun p : Nat × List (RelativeTerm Nat) =>
    p.2.foldl RelativeTerm.sum (zeroTree p.1)) at h
  rw [heq] at h
  exact h.to₂

@[simp] theorem normalize_default (r : Nat) : normalize r (.parameter 0) = zeroTree r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa [normalize_parameter_succ, rawTree, decode, zeroTree] using
      congrArg (fun t : RelativeTerm Nat => RelativeTerm.parameter t.code) ih

private def parameterOp (q : Nat × Nat) (p : Nat) (previous : RelativeTerm Nat) :
    RelativeTerm Nat :=
  .parameter (cond (isCode p) previous (zeroTree (q.1 - 1))).code

private def sumOp (q : Nat × Nat) (a b : RelativeTerm Nat) : RelativeTerm Nat :=
  buildAtoms q.1 (normalizeAtoms q.1 (atoms q.1 a ++ atoms q.1 b))

private def thetaOp (_ : Nat × Nat) (k : Nat) (a : RelativeTerm Nat) :
    RelativeTerm Nat := .theta k a

private def fold : Nat → Nat → RelativeTerm Nat :=
  run zeroTree (fun _ _ => .parameter 0) parameterOp sumOp thetaOp

private theorem fold_primrec : Primrec₂ fold := by
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × RelativeTerm Nat) =>
      parameterOp p.1 p.2.1 p.2.2) := by
    have hvalue : Primrec (fun p : (Nat × Nat) × (Nat × RelativeTerm Nat) =>
        cond (isCode p.2.1) p.2.2 (zeroTree (p.1.1 - 1))) :=
      (isCode_primrec.comp (Primrec.fst.comp Primrec.snd)).cond
      (Primrec.snd.comp Primrec.snd)
      (zeroTree_primrec.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)))
    exact parameter_primrec.comp (code_primrec.comp hvalue)
  have hs : Primrec (fun p : (Nat × Nat) × (RelativeTerm Nat × RelativeTerm Nat) =>
      sumOp p.1 p.2.1 p.2.2) := by
    have hr : Primrec (fun p : (Nat × Nat) × (RelativeTerm Nat × RelativeTerm Nat) => p.1.1) :=
      Primrec.fst.comp Primrec.fst
    have ha := atoms_primrec.comp hr (Primrec.fst.comp Primrec.snd)
    have hb := atoms_primrec.comp hr (Primrec.snd.comp Primrec.snd)
    exact buildAtoms_primrec.comp hr
      (normalizeAtoms_primrec.comp hr (Primrec.list_append.comp ha hb))
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × RelativeTerm Nat) =>
      thetaOp p.1 p.2.1 p.2.2) :=
    theta_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact run_primrec _ _ _ _ _ zeroTree_primrec
    (Primrec.const (RelativeTerm.parameter 0)).to₂ hp hs ht

private theorem fold_code (r : Nat) (t : RelativeTerm Nat) : fold r t.code = normalize r t := by
  induction r generalizing t with
  | zero =>
    induction t <;>
      simp_all [fold, run, code, Nat.unpair_pair, normalize_parameter_zero,
        normalize_sum, normalize_theta, sumOp, thetaOp]
  | succ r ihr =>
    induction t with
    | parameter p =>
      cases hd : decode p with
      | none =>
        have hs := (decode_eq_none_iff p).mp hd
        simp [fold, run, code, Nat.unpair_pair, parameterOp, hs,
          normalize_parameter_succ, rawTree, hd]
      | some u =>
        have hu := decode_sound p u hd
        have hprevious := ihr u
        simp only [fold] at hprevious
        rw [← hu]
        simp [fold, run, code, Nat.unpair_pair, parameterOp,
          normalize_parameter_succ_code, hprevious]
    | sum a b iha ihb =>
      simp only [fold] at iha ihb
      simp [fold, run, code, Nat.unpair_pair, iha, ihb, normalize_sum, sumOp]
    | theta k a ih =>
      simp only [fold] at ih
      simp [fold, run, code, Nat.unpair_pair, ih, normalize_theta, thetaOp]

theorem normalize_primrec : Primrec₂ normalize := by
  have h := fold_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)
  simpa only [fold_code] using h.to₂

theorem normalizeCode_primrec : Primrec₂ normalizeCode := by
  have h := (Primrec.option_isSome.comp (decode_primrec.comp Primrec.snd)).cond
    (code_primrec.comp (normalize_primrec.comp Primrec.fst (rawTree_primrec.comp Primrec.snd)))
    (Primrec.const 0)
  have heq : (fun p : Nat × Nat => cond (decode p.2).isSome
      (normalize p.1 (rawTree p.2)).code 0) =
      (fun p : Nat × Nat => normalizeCode p.1 p.2) := by
    funext p
    cases hd : decode p.2 <;> simp [normalizeCode, rawTree, hd]
  rw [heq] at h
  exact h.to₂

theorem lessRawCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => lessRawCode p.1 p.2.1 p.2.2) :=
  lessCode_primrec.comp (Primrec.fst.pair
    ((normalizeCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))

theorem equalRawCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => equalRawCode p.1 p.2.1 p.2.2) :=
  equalCode_primrec.comp (Primrec.fst.pair
    ((normalizeCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))

theorem normalize_computable : Computable₂ normalize := normalize_primrec.to_comp

theorem normalizeCode_computable : Computable₂ normalizeCode := normalizeCode_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization.Effective
