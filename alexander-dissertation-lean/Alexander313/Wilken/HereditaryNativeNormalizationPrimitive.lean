import Alexander313.Wilken.HereditaryNativeNormalization

/-!
# Genuine PR native normalization

The real suffix absorber and source reconstruction are finite list folds.
A literal native value fold carries the epsilon-context code into each sum
operation and computes the defined normalizer on every tree. Atomic public
payloads are not opened by this fold. The original native admission checker
guards whole-code execution and its positive graph. No normalization or
termination interface is supplied. Uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Normalization.Effective

open Comparison (atoms)
open ThetaCourse (rawTree rawTree_primrec rawTree_code)

private def prependNumeric (q : Nat) (a : RelativeTerm Nat)
    (as : List (RelativeTerm Nat)) : List (RelativeTerm Nat) :=
  cond (as.length == 0) [a]
    (cond (Comparison.less q a (as[0]?.getD zeroTree)) as (a :: as))

theorem prependAtom_primrec : Primrec
    (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => prependAtom p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.1) := Primrec.fst
  have ha : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have has : Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hhead := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp has (Primrec.const 0)) (Primrec.const zeroTree)
  have h := (Primrec.beq.comp (Primrec.list_length.comp has) (Primrec.const 0)).cond
    (Primrec.list_cons.comp ha (Primrec.const []))
    ((Comparison.Effective.less_primrec.comp (hq.pair (ha.pair hhead))).cond has (Primrec.list_cons.comp ha has))
  have he : (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => prependNumeric p.1 p.2.1 p.2.2) =
      (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => prependAtom p.1 p.2.1 p.2.2) := by
    funext p
    cases p.2.2 <;> simp [prependNumeric, prependAtom]
  change Primrec (fun p : Nat × (RelativeTerm Nat × List (RelativeTerm Nat)) => prependNumeric p.1 p.2.1 p.2.2) at h
  rw [he] at h
  exact h

theorem normalizeAtoms_primrec : Primrec₂ normalizeAtoms := by
  have hs : Primrec₂ (fun p : Nat × List (RelativeTerm Nat) =>
      fun a : RelativeTerm Nat × List (RelativeTerm Nat) => prependAtom p.1 a.1 a.2) :=
    (prependAtom_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have he : (fun p : Nat × List (RelativeTerm Nat) => p.2.foldr (prependAtom p.1) []) =
      (fun p : Nat × List (RelativeTerm Nat) => normalizeAtoms p.1 p.2) := by
    funext p
    induction p.2 <;> simp_all [normalizeAtoms]
  rw [he] at h
  exact h.to₂

private theorem buildRev_fold (as : List (RelativeTerm Nat)) :
    buildRev as = as.foldr (fun a t => .sum t a) zeroTree := by
  induction as <;> simp_all [buildRev]

theorem buildAtoms_primrec : Primrec buildAtoms := by
  have hs : Primrec₂ (fun (_ : List (RelativeTerm Nat)) =>
      fun p : RelativeTerm Nat × RelativeTerm Nat => RelativeTerm.sum p.1 p.2) :=
    (sum_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldl Primrec.id (Primrec.const zeroTree) hs
  have he : (fun as : List (RelativeTerm Nat) => as.foldl RelativeTerm.sum zeroTree) = buildAtoms := by
    funext as
    rw [buildAtoms, buildRev_fold, List.foldr_reverse]
  change Primrec (fun as : List (RelativeTerm Nat) => as.foldl RelativeTerm.sum zeroTree) at h
  rw [he] at h
  exact h

abbrev State := Nat × RelativeTerm Nat

private def parameterOp (q p : Nat) : State := (q, .parameter p)

private def sumOp (a b : State) : State :=
  (a.1, buildAtoms (normalizeAtoms a.1 (atoms a.2 ++ atoms b.2)))

private def thetaOp (q k : Nat) (a : State) : State := (q, .theta k a.2)

def normalizeStateCode (q c : Nat) : State := ValueFold.code parameterOp sumOp thetaOp (0, zeroTree) q c

theorem normalizeStateCode_primrec : Primrec₂ normalizeStateCode := by
  have hp : Primrec₂ parameterOp := (Primrec.fst.pair (parameter_primrec.comp Primrec.snd)).to₂
  have hs : Primrec₂ sumOp := by
    have hq : Primrec (fun p : State × State => p.1.1) := Primrec.fst.comp Primrec.fst
    have ha : Primrec (fun p : State × State => atoms p.1.2) := Comparison.atoms_primrec.comp (Primrec.snd.comp Primrec.fst)
    have hb : Primrec (fun p : State × State => atoms p.2.2) := Comparison.atoms_primrec.comp (Primrec.snd.comp Primrec.snd)
    exact (hq.pair (buildAtoms_primrec.comp (normalizeAtoms_primrec.comp hq
      (Primrec.list_append.comp ha hb)))).to₂
  have ht : Primrec (fun p : Nat × (Nat × State) => thetaOp p.1 p.2.1 p.2.2) :=
    Primrec.fst.pair (theta_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact ValueFold.code_primrec parameterOp sumOp thetaOp (0, zeroTree) hp hs ht

theorem normalizeStateCode_code (q : Nat) (t : RelativeTerm Nat) :
    normalizeStateCode q t.code = (q, normalize q t) := by
  rw [normalizeStateCode, ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, parameterOp, sumOp, thetaOp, normalize]

theorem normalize_primrec : Primrec₂ normalize := by
  have h := Primrec.snd.comp (normalizeStateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd))
  simpa only [normalizeStateCode_code] using h.to₂

theorem normalizeCode_primrec : Primrec₂ normalizeCode :=
  (checkCode_primrec.cond (code_primrec.comp (normalize_primrec.comp Primrec.fst
    (rawTree_primrec.comp Primrec.snd))) (Primrec.const 0)).to₂

theorem graph_primrec : Primrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (checkCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.snd)
      (normalizeCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))

theorem normalizeCode_computable : Computable₂ normalizeCode := normalizeCode_primrec.to_comp

theorem lessRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => lessRawCode p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.1) :=
    checkCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.2) :=
    checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.and.comp hc hd) (Comparison.lessCode_primrec.comp (Primrec.fst.pair
    ((normalizeCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))

theorem equalRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => equalRawCode p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.1) :=
    checkCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.2) :=
    checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.and.comp hc hd) (Comparison.equalCode_primrec.comp (Primrec.fst.pair
    ((normalizeCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Normalization.Effective
