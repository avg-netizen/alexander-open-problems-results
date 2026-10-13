import Alexander313.Wilken.HereditaryCanonicalCodes

/-!
# Executing adjacent finite-base lowering on its actual caller domain

An originally checked tree at level r+1 whose true value is below that
level's base contains no current theta node. Opening each actual earlier
payload, and preserving sums, therefore produces an originally checked
low tree at level r with exactly the same source value. The executable
guard uses the genuine full normalizer and ordinal comparison with the
constructed current base code. It does not assume a translation contract.

This is the finite-endpoint conversion r+1 to r. It is not the arbitrary
temporary-epsilon-base conversion required by the later tracking routines.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Lowering

open ThetaCourse

def lowerTree : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => rawTree p
  | .sum a b => .sum (lowerTree a) (lowerTree b)
  | .theta _ _ => .parameter 0

theorem lowerTree_primrec : Primrec lowerTree := by
  have hp : Primrec₂ (fun (_ : Nat) p => rawTree p) :=
    (rawTree_primrec.comp Primrec.snd).to₂
  have ht : Primrec (fun (_ : Nat × (Nat × RelativeTerm Nat)) =>
      (.parameter 0 : RelativeTerm Nat)) := Primrec.const _
  have hf := (ValueFold.term_primrec (fun (_ : Nat) p => rawTree p) sum
    (fun _ _ _ => .parameter 0) (.parameter 0) hp sum_primrec ht).comp
      (Primrec.const 0) Primrec.id
  have he : ValueFold.term (fun (_ : Nat) p => rawTree p) sum
      (fun _ _ _ => .parameter 0) 0 = lowerTree := by
    funext t
    induction t <;> simp_all [ValueFold.term, lowerTree]
  simpa only [he, id_eq] using hf

theorem checked_theta_base_le (r k : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta k a) = true) :
    finiteBase r ≤ denote r (.theta k a) := by
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r (.theta k a)).mp ht
  rw [denote_eq_finite r n (.theta k a) ha.2]
  cases ha.2 with
  | theta h0k hkn hsort ha =>
    exact ((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le k)).trans
      (source_theta_range (finiteBase r) (parameters r) n k a hkn ha hsort).1

theorem lowerTree_spec (r : Nat) (t : RelativeTerm Nat)
    (ht : check (r + 1) t = true) (hb : denote (r + 1) t < finiteBase (r + 1)) :
    check r (lowerTree t) = true ∧ denote r (lowerTree t) = denote (r + 1) t := by
  revert ht hb
  induction t with
  | parameter p =>
    intro ht hb
    exact ⟨Theta.checked_parameter_payload r p ht,
      (Theta.denote_parameter_succ r p).symm⟩
  | sum a b iha ihb =>
    intro ht hb
    have hc := Bool.and_eq_true_iff.mp ((Uniform.check_sum (r + 1) a b).symm.trans ht)
    have hba : denote (r + 1) a < finiteBase (r + 1) :=
      (le_self_add : denote (r + 1) a ≤ denote (r + 1) a + denote (r + 1) b).trans_lt hb
    have hbb : denote (r + 1) b < finiteBase (r + 1) :=
      (le_add_self : denote (r + 1) b ≤ denote (r + 1) a + denote (r + 1) b).trans_lt hb
    have ha := iha hc.1 hba
    have hb' := ihb hc.2 hbb
    refine ⟨?_, ?_⟩
    · simp only [lowerTree, Uniform.check_sum, ha.1, hb'.1, Bool.true_and]
    · change denote r (lowerTree a) + denote r (lowerTree b) =
        denote (r + 1) a + denote (r + 1) b
      rw [ha.2, hb'.2]
  | theta k a ih =>
    intro ht hb
    exact False.elim ((not_lt_of_ge (checked_theta_base_le (r + 1) k a ht)) hb)

theorem lowerTree_low (r : Nat) (t : RelativeTerm Nat)
    (ht : check (r + 1) t = true) (hb : denote (r + 1) t < finiteBase (r + 1)) :
    lowCheck r (lowerTree t) = true := by
  have hs := lowerTree_spec r t ht hb
  have hsmall : denote r (lowerTree t) < omegaSequence (finiteBase r) 1 :=
    (hs.2.trans_lt hb).trans (finiteBase_lt_cardinal r)
  have hsort := (denote_lt_iff_outerSort_le r (lowerTree t) hs.1 1 (Nat.zero_lt_succ 0)).mp hsmall
  simp only [lowCheck, hs.1, hsort, decide_true, Bool.true_and]

def checkInput (r c : Nat) : Bool :=
  checkCode (r + 1) c &&
    Theta.Normalization.lessRawCode (r + 1) c (BaseArithmetic.freshCode (r + 1))

theorem checkInput_primrec : Primrec₂ checkInput := by
  have hr : Primrec (fun p : Nat × Nat => p.1 + 1) := Primrec.succ.comp Primrec.fst
  exact (Primrec.and.comp (Uniform.hereditaryCheckCode_primrec.comp hr Primrec.snd)
    (Theta.Normalization.Effective.lessRawCode_primrec.comp
      (hr.pair (Primrec.snd.pair (BaseArithmetic.freshCode_primrec.comp hr))))).to₂

theorem checkInput_exact (r c : Nat) : checkInput r c = true ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) := by
  simp only [checkInput, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨hc, ?_⟩
    have hf := BaseArithmetic.checkCode_old (r + 1) _ (BaseArithmetic.fresh_checked (r + 1))
    have hf' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hf)).1
    simpa only [BaseArithmetic.fresh_value] using
      (Theta.Normalization.lessRawCode_correct (r + 1) c _ hc hf').mp hb
  · rintro ⟨hc, hb⟩
    refine ⟨hc, ?_⟩
    have hf := BaseArithmetic.checkCode_old (r + 1) _ (BaseArithmetic.fresh_checked (r + 1))
    have hf' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hf)).1
    apply (Theta.Normalization.lessRawCode_correct (r + 1) c _ hc hf').mpr
    simpa only [BaseArithmetic.fresh_value] using hb

def lowerCode (r c : Nat) : Nat := cond (checkInput r c) (lowerTree (rawTree c)).code 0

theorem lowerCode_primrec : Primrec₂ lowerCode :=
  (checkInput_primrec.cond
    (code_primrec.comp (lowerTree_primrec.comp (rawTree_primrec.comp Primrec.snd)))
    (Primrec.const 0)).to₂

theorem lowerCode_spec (r c : Nat) (hc : checkInput r c = true) :
    lowCheckCode r (lowerCode r c) = true ∧
      interpretation r (lowerCode r c) = interpretation (r + 1) c := by
  obtain ⟨hcheck, hsmall⟩ := (checkInput_exact r c).mp hc
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff (r + 1) c).mp hcheck
  have hb : denote (r + 1) t < finiteBase (r + 1) := by
    simpa only [interpretation_code] using hsmall
  simp only [lowerCode, hc, Bool.cond_true, rawTree_code, lowCheckCode_code, interpretation_code]
  exact ⟨lowerTree_low r t ht hb, (lowerTree_spec r t ht hb).2⟩

theorem lowerCode_union (r c : Nat) (hc : checkInput r c = true) :
    unionCheck (Nat.pair r (lowerCode r c)) = true := by
  simpa only [unionCheck_pair] using (lowerCode_spec r c hc).1

def canonicalLower (r c : Nat) : Nat :=
  cond (checkInput r c) (Canonical.canonicalize (Nat.pair r (lowerCode r c))) 0

theorem canonicalLower_primrec : Primrec₂ canonicalLower :=
  (checkInput_primrec.cond
    (Canonical.Effective.canonicalize_primrec.comp
      (Primrec₂.natPair.comp Primrec.fst lowerCode_primrec)) (Primrec.const 0)).to₂

theorem canonicalLower_checked (r c : Nat) (hc : checkInput r c = true) :
    Canonical.check (canonicalLower r c) = true := by
  simp only [canonicalLower, hc, Bool.cond_true]
  exact Canonical.canonicalize_check _ (lowerCode_union r c hc)

theorem canonicalLower_original (r c : Nat) (hc : checkInput r c = true) :
    unionCheck (canonicalLower r c) = true := by
  simp only [canonicalLower, hc, Bool.cond_true]
  exact Canonical.canonicalize_original _ (lowerCode_union r c hc)

theorem canonicalLower_value (r c : Nat) (hc : checkInput r c = true) :
    unionInterpretation (canonicalLower r c) = interpretation (r + 1) c := by
  simp only [canonicalLower, hc, Bool.cond_true]
  exact (Canonical.canonicalize_value _ (lowerCode_union r c hc)).trans
    (by simpa only [unionInterpretation_pair] using (lowerCode_spec r c hc).2)

theorem lowerCode_lift_value (r c : Nat) (hc : lowCheckCode r c = true) :
    checkInput r (BaseArithmetic.liftCode c) = true ∧
      interpretation r (lowerCode r (BaseArithmetic.liftCode c)) = interpretation r c := by
  have he := Theta.lift_old_checked r c hc
  have hv := Theta.lift_original_value r c
  have hb := (lt_nextBase_iff_code r _).mpr ⟨c, hc, rfl⟩
  have hg := (checkInput_exact r _).mpr ⟨(Bool.and_eq_true_iff.mp
    (by simpa only [lowCheckCode_eq] using he)).1,
    hv.trans_lt hb⟩
  exact ⟨hg, ((lowerCode_spec r _ hg).2).trans hv⟩

def graph (r c q : Nat) : Bool :=
  checkInput r c && (Canonical.check q && (q == canonicalLower r c))

theorem graph_primrec : Primrec (fun p : (Nat × Nat) × Nat => graph p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (checkInput_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst))
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.beq.comp Primrec.snd (canonicalLower_primrec.comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))))

theorem graph_exact (r c q : Nat) : graph r c q = true ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation (r + 1) c := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hc, hq, he⟩
    have hs := (checkInput_exact r c).mp hc
    refine ⟨hs.1, hs.2, hq, ?_⟩
    rw [he]
    exact canonicalLower_value r c hc
  · rintro ⟨hc, hb, hq, hv⟩
    have hg := (checkInput_exact r c).mpr ⟨hc, hb⟩
    exact ⟨hg, hq, Canonical.check_value_injective _ _ hq (canonicalLower_checked r c hg)
      (hv.trans (canonicalLower_value r c hg).symm)⟩

theorem lowerCode_computable : Computable₂ lowerCode := lowerCode_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Lowering
