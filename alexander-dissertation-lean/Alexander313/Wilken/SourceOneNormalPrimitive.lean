import Alexander313.Wilken.SourceOneComparisonPrimitive

/-! # Primitive recursive admission of normal base-one codes

The actual normality checker retains the final-principal sum convention.
Its recursive tree fold reconstructs the input and calls the literal
primitive recursive comparison. Raw admission additionally retains the
existing source-admission and exact decoding checks. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective

private def appendNumeric (as bs : List (RelativeTerm Nat)) : Bool :=
  cond (bs.length == 0) (as.length == 0)
    (cond (bs.length == 1) (as.all (fun a => !less a (bs[0]?.getD (.parameter 0)))) false)

private theorem appendNumeric_eq (as bs : List (RelativeTerm Nat)) :
    appendNumeric as bs = normalAppend as bs := by
  cases bs with
  | nil => cases as <;> rfl
  | cons b bs => cases bs <;> simp [appendNumeric, normalAppend]

theorem normalAppend_primrec : Primrec₂ normalAppend := by
  have hlen : Primrec (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hhead : Primrec (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) =>
      p.2[0]?.getD (.parameter 0)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const (RelativeTerm.parameter 0))
  have hall : Primrec (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) =>
      p.1.all (fun a => !less a (p.2[0]?.getD (.parameter 0)))) := by
    have htest : Primrec₂ (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) =>
        fun a : RelativeTerm Nat => !less a (p.2[0]?.getD (.parameter 0))) :=
      (Primrec.not.comp (less_primrec.comp Primrec.snd (hhead.comp Primrec.fst))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id Primrec.fst
  have h := (Primrec.beq.comp hlen (Primrec.const 0)).cond
    (Primrec.beq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0))
    ((Primrec.beq.comp hlen (Primrec.const 1)).cond hall (Primrec.const false))
  have heq : (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) => appendNumeric p.1 p.2) =
      (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) => normalAppend p.1 p.2) := by
    funext p
    exact appendNumeric_eq _ _
  change Primrec (fun p : List (RelativeTerm Nat) × List (RelativeTerm Nat) => appendNumeric p.1 p.2) at h
  rw [heq] at h
  exact h.to₂

private abbrev State := RelativeTerm Nat × Bool

private def normalParameter (_ : Unit) (p : Nat) : State := (.parameter p, true)

private def normalSum (a b : State) : State :=
  (.sum a.1 b.1, (a.2 && b.2) && normalAppend (thetaAtoms a.1) (thetaAtoms b.1))

private def normalTheta (_ : Unit) (k : Nat) (a : State) : State := (.theta k a.1, a.2)

theorem normalCheck_primrec : Primrec normalCheck := by
  have hp : Primrec₂ normalParameter :=
    ((parameter_primrec.comp Primrec.snd).pair (Primrec.const true)).to₂
  have hs : Primrec₂ normalSum := by
    have ht : Primrec (fun p : State × State => RelativeTerm.sum p.1.1 p.2.1) :=
      sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    have hc : Primrec (fun p : State × State => p.1.2 && p.2.2) :=
      Primrec.and.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
    have ha : Primrec (fun p : State × State => normalAppend (thetaAtoms p.1.1) (thetaAtoms p.2.1)) :=
      normalAppend_primrec.comp
      (thetaAtoms_primrec.comp (Primrec.fst.comp Primrec.fst))
      (thetaAtoms_primrec.comp (Primrec.fst.comp Primrec.snd))
    exact (ht.pair (Primrec.and.comp hc ha)).to₂
  have ht : Primrec (fun p : Unit × (Nat × State) => normalTheta p.1 p.2.1 p.2.2) :=
    (theta_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let fold := ValueFold.term normalParameter normalSum normalTheta ()
  have hf : Primrec fold := (ValueFold.term_primrec normalParameter normalSum normalTheta
    (.parameter 0, false) hp hs ht).comp (Primrec.const ()) Primrec.id
  have heq : ∀ t : RelativeTerm Nat, fold t = (t, normalCheck t) := by
    intro t
    induction t <;> simp_all [fold, ValueFold.term, normalParameter, normalSum, normalTheta, normalCheck]
  have h := Primrec.snd.comp hf
  have hfun : (fun t => (fold t).2) = normalCheck := by
    funext t
    rw [heq]
  rw [hfun] at h
  exact h

theorem acceptedCode_primrec : Primrec acceptedCode :=
  Primrec.and.comp PublicCodes.checkCode_primrec
    (normalCheck_primrec.comp (Primrec.option_getD.comp decode_primrec
      (Primrec.const (RelativeTerm.parameter 0))))

theorem less_computable : Computable₂ less := less_primrec.to_comp

theorem equal_computable : Computable₂ equal := equal_primrec.to_comp

theorem lessCode_computable : Computable₂ lessCode := lessCode_primrec.to_comp

theorem equalCode_computable : Computable₂ equalCode := equalCode_primrec.to_comp

theorem normalCheck_computable : Computable normalCheck := normalCheck_primrec.to_comp

theorem acceptedCode_computable : Computable acceptedCode := acceptedCode_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective
