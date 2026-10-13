import Alexander313.Wilken.SourceOneNormalPrimitive
import Alexander313.Wilken.SourceOneNormalization

/-! # Primitive recursion for the actual base-one normalizer

The existing atom absorption uses the now-proved primitive recursive literal
comparison. Two finite list folds and the actual raw-syntax value fold implement
the existing normalizer, with an exact equality proof on every tree. Decoder
failure still gives the literal raw result zero. No semantic normalization
contract or canonical uniqueness hypothesis is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Normalization.Effective

open Comparison.Effective

private def prependNumeric (a : RelativeTerm Nat) (as : List (RelativeTerm Nat)) :
    List (RelativeTerm Nat) :=
  cond (as.length == 0) [a]
    (cond (Comparison.less a (as[0]?.getD (.parameter 0))) as (a :: as))

private theorem prependNumeric_eq (a : RelativeTerm Nat) (as : List (RelativeTerm Nat)) :
    prependNumeric a as = prependAtom a as := by
  cases as <;> simp [prependNumeric, prependAtom]

theorem prependAtom_primrec : Primrec₂ prependAtom := by
  have hhead : Primrec (fun p : RelativeTerm Nat × List (RelativeTerm Nat) =>
      p.2[0]?.getD (.parameter 0)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const (RelativeTerm.parameter 0))
  have h := (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)).cond
    (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
    ((less_primrec.comp Primrec.fst hhead).cond Primrec.snd
      (Primrec.list_cons.comp Primrec.fst Primrec.snd))
  have heq : (fun p : RelativeTerm Nat × List (RelativeTerm Nat) => prependNumeric p.1 p.2) =
      (fun p : RelativeTerm Nat × List (RelativeTerm Nat) => prependAtom p.1 p.2) := by
    funext p
    exact prependNumeric_eq _ _
  change Primrec (fun p : RelativeTerm Nat × List (RelativeTerm Nat) => prependNumeric p.1 p.2) at h
  rw [heq] at h
  exact h.to₂

theorem normalizeAtoms_primrec : Primrec normalizeAtoms := by
  have hs : Primrec₂ (fun (_ : List (RelativeTerm Nat)) =>
      fun p : RelativeTerm Nat × List (RelativeTerm Nat) => prependAtom p.1 p.2) :=
    (prependAtom_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const []) hs
  have heq : (fun as : List (RelativeTerm Nat) => as.foldr prependAtom []) = normalizeAtoms := by
    funext as
    induction as <;> simp_all [normalizeAtoms]
  change Primrec (fun as : List (RelativeTerm Nat) => as.foldr prependAtom []) at h
  rw [heq] at h
  exact h

private theorem buildRev_fold (as : List (RelativeTerm Nat)) :
    buildRev as = as.foldr (fun a t => .sum t a) (.parameter 0) := by
  induction as <;> simp_all [buildRev]

theorem buildAtoms_primrec : Primrec buildAtoms := by
  have hs : Primrec₂ (fun (_ : List (RelativeTerm Nat)) =>
      fun p : RelativeTerm Nat × RelativeTerm Nat => RelativeTerm.sum p.1 p.2) :=
    (sum_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldl Primrec.id (Primrec.const (RelativeTerm.parameter 0)) hs
  have heq : (fun as : List (RelativeTerm Nat) =>
      as.foldl RelativeTerm.sum (.parameter 0)) = buildAtoms := by
    funext as
    rw [buildAtoms, buildRev_fold, List.foldr_reverse]
  change Primrec (fun as : List (RelativeTerm Nat) =>
    as.foldl RelativeTerm.sum (.parameter 0)) at h
  rw [heq] at h
  exact h

private def parameterOp (_ : Unit) (_ : Nat) : RelativeTerm Nat := .parameter 0

private def sumOp (a b : RelativeTerm Nat) : RelativeTerm Nat :=
  buildAtoms (normalizeAtoms (thetaAtoms a ++ thetaAtoms b))

private def thetaOp (_ : Unit) (k : Nat) (a : RelativeTerm Nat) : RelativeTerm Nat := .theta k a

theorem normalize_primrec : Primrec normalize := by
  have hp : Primrec₂ parameterOp := (Primrec.const (RelativeTerm.parameter 0)).to₂
  have hs : Primrec₂ sumOp :=
    (buildAtoms_primrec.comp (normalizeAtoms_primrec.comp
      (Primrec.list_append.comp (thetaAtoms_primrec.comp Primrec.fst)
        (thetaAtoms_primrec.comp Primrec.snd)))).to₂
  have ht : Primrec (fun p : Unit × (Nat × RelativeTerm Nat) => thetaOp p.1 p.2.1 p.2.2) :=
    theta_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  let fold := ValueFold.term parameterOp sumOp thetaOp ()
  have h : Primrec fold := (ValueFold.term_primrec parameterOp sumOp thetaOp
    (.parameter 0) hp hs ht).comp (Primrec.const ()) Primrec.id
  have heq : fold = normalize := by
    funext t
    induction t <;> simp_all [fold, ValueFold.term, parameterOp, sumOp, thetaOp, normalize]
  rw [heq] at h
  exact h

theorem normalizeCode_primrec : Primrec normalizeCode := by
  have ht := Primrec.option_getD.comp decode_primrec (Primrec.const (RelativeTerm.parameter 0))
  have h := (Primrec.option_isSome.comp decode_primrec).cond
    (code_primrec.comp (normalize_primrec.comp ht)) (Primrec.const 0)
  have heq : (fun c => cond (decode c).isSome
      (normalize ((decode c).getD (.parameter 0))).code 0) = normalizeCode := by
    funext c
    cases hc : decode c <;> simp [normalizeCode, hc]
  rw [heq] at h
  exact h

theorem acceptedLowCode_primrec : Primrec acceptedLowCode :=
  Primrec.and.comp Comparison.Effective.acceptedCode_primrec
    (Primrec.nat_le.comp PublicCodes.outerSortCode_primrec (Primrec.const 1)).decide

theorem lessRawCode_primrec : Primrec₂ lessRawCode :=
  (Comparison.Effective.lessCode_primrec.comp (normalizeCode_primrec.comp Primrec.fst)
    (normalizeCode_primrec.comp Primrec.snd)).to₂

theorem equalRawCode_primrec : Primrec₂ equalRawCode :=
  (Comparison.Effective.equalCode_primrec.comp (normalizeCode_primrec.comp Primrec.fst)
    (normalizeCode_primrec.comp Primrec.snd)).to₂

theorem normalize_computable : Computable normalize := normalize_primrec.to_comp

theorem normalizeCode_computable : Computable normalizeCode := normalizeCode_primrec.to_comp

theorem lessRawCode_computable : Computable₂ lessRawCode := lessRawCode_primrec.to_comp

theorem equalRawCode_computable : Computable₂ equalRawCode := equalRawCode_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.SourceOne.Normalization.Effective
