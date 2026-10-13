import Alexander313.Wilken.HereditaryMultiplication

/-!
# Executing exact left division on original ordinal codes

Wilken's preliminary (1/gamma)*beta is the least delta satisfying
gamma*delta=beta, when it exists. For positive gamma the actual product is
strictly increasing in delta, so the quotient is unique. A genuine PR verifier
checks a finite pair: a canonical quotient code and an actual multiplication
certificate. The certificate is checked by the newly constructed multiplier;
its real computed product is compared with beta by genuine source equality.

Positive left multiplication bounds delta by beta. Canonical interval coverage
and the actual multiplication witness therefore derive termination whenever
the literal source equation has a solution. Numerical search does not choose
an ordinal minimum or assume a division/arithmetic/effectivity oracle.
Every term remains uncompiled; pinned library signatures were read locally.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.ExactDivision

def callerCheck (q v : Nat) : Bool :=
  (unionCheck q && unionCheck v) && (OmegaPowers.zeroCheck q == false)

theorem callerCheck_primrec : Primrec₂ callerCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
      (Uniform.unionCheck_primrec.comp Primrec.snd))
    (Primrec.beq.comp (OmegaPowers.zeroCheck_primrec.comp Primrec.fst)
      (Primrec.const false))).to₂

theorem callerCheck_exact (q v : Nat) : callerCheck q v = true ↔
    unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q := by
  simp only [callerCheck, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨hq, hv⟩, hz⟩
    refine ⟨hq, hv, pos_iff_ne_zero.mpr ?_⟩
    intro he
    have ht := (OmegaPowers.zeroCheck_exact q).mpr ⟨hq, he⟩
    rw [hz] at ht
    contradiction
  · rintro ⟨hq, hv, hp⟩
    refine ⟨⟨hq, hv⟩, ?_⟩
    cases hz : OmegaPowers.zeroCheck q with
    | false => rfl
    | true => exact False.elim ((ne_of_gt hp) ((OmegaPowers.zeroCheck_exact q).mp hz).2)

/-- Witness.first is the canonical quotient; Witness.second is the actual
multiplier's finite certificate, not a supplied product equation. -/
def certificateCheck (input witness : Nat) : Bool :=
  let q := input.unpair.1
  let v := input.unpair.2
  let c := witness.unpair.1
  let w := witness.unpair.2
  (callerCheck q v && Canonical.check c) &&
    (Multiplication.certificateCheck (Nat.pair q c) w &&
      Canonical.graph v (Multiplication.candidate (Nat.pair q c) w))

theorem certificateCheck_primrec : Primrec₂ certificateCheck := by
  have hi := Primrec.unpair.comp Primrec.fst
  have hw := Primrec.unpair.comp Primrec.snd
  have hq := Primrec.fst.comp hi
  have hv := Primrec.snd.comp hi
  have hc := Primrec.fst.comp hw
  have hm := Primrec.snd.comp hw
  have hp := Primrec₂.natPair.comp hq hc
  exact (Primrec.and.comp
    (Primrec.and.comp (callerCheck_primrec.comp hq hv)
      (Canonical.Effective.check_primrec.comp hc))
    (Primrec.and.comp (Multiplication.certificateCheck_primrec.comp hp hm)
      (Canonical.Effective.graph_primrec.comp hv
        (Multiplication.candidate_primrec.comp hp hm)))).to₂

theorem certificateCheck_spec (input witness : Nat)
    (hw : certificateCheck input witness = true) :
    unionCheck input.unpair.1 = true ∧ unionCheck input.unpair.2 = true ∧
      0 < unionInterpretation input.unpair.1 ∧ Canonical.check witness.unpair.1 = true ∧
      unionInterpretation input.unpair.1 * unionInterpretation witness.unpair.1 =
        unionInterpretation input.unpair.2 := by
  have hs := Bool.and_eq_true.mp hw
  have hleft := Bool.and_eq_true.mp hs.1
  have hcaller := (callerCheck_exact _ _).mp hleft.1
  have hright := Bool.and_eq_true.mp hs.2
  have hproduct := Multiplication.candidate_value _ _ hright.1
  have he := (Canonical.graph_exact _ _).mp hright.2
  refine ⟨hcaller.1, hcaller.2.1, hcaller.2.2, hleft.2, ?_⟩
  have hp : unionInterpretation (Multiplication.candidate
      (Nat.pair input.unpair.1 witness.unpair.1) witness.unpair.2) =
      unionInterpretation input.unpair.1 * unionInterpretation witness.unpair.1 :=
    by simpa only [Nat.unpair_pair] using hproduct.2
  exact hp.symm.trans he.2.2.symm

theorem certificate_witness (q v c : Nat) (hq : unionCheck q = true)
    (hv : unionCheck v = true) (hp : 0 < unionInterpretation q)
    (hc : Canonical.check c = true)
    (he : unionInterpretation q * unionInterpretation c = unionInterpretation v) :
    ∃ w : Nat, certificateCheck (Nat.pair q v) (Nat.pair c w) = true := by
  obtain ⟨w, hw⟩ := Multiplication.certificateCheck_witness q c hq (Canonical.check_original hc)
  have hs := Multiplication.candidate_value (Nat.pair q c) w hw
  refine ⟨w, ?_⟩
  simp only [certificateCheck, Nat.unpair_pair, Bool.and_eq_true]
  refine ⟨⟨(callerCheck_exact q v).mpr ⟨hq, hv, hp⟩, hc⟩, hw, ?_⟩
  apply (Canonical.graph_exact v _).mpr
  refine ⟨hv, hs.1, ?_⟩
  exact he.symm.trans (by simpa only [Nat.unpair_pair] using hs.2.symm)

/-- Literal source existence, before any code or computation is chosen. -/
def SourceDomain (q v : Nat) : Prop :=
  unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q ∧
    ∃ δ : Ordinal.{0}, unionInterpretation q * δ = unionInterpretation v

theorem certificate_exists_iff (q v : Nat) :
    (∃ witness, certificateCheck (Nat.pair q v) witness = true) ↔ SourceDomain q v := by
  constructor
  · rintro ⟨w, hw⟩
    have hs := certificateCheck_spec (Nat.pair q v) w hw
    simp only [Nat.unpair_pair] at hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1, _, hs.2.2.2.2⟩
  · rintro ⟨hq, hv, hp, δ, hδ⟩
    have hbound : δ ≤ unionInterpretation v :=
      (MultiplicativePrincipalArithmetic.quotient_le_product hp δ).trans_eq hδ
    have hvsmall : unionInterpretation v < finiteBaseLimit :=
      (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨v, hv, rfl⟩
    obtain ⟨c, hc, he⟩ := (Canonical.lt_finiteBaseLimit_iff_code δ).mp (hbound.trans_lt hvsmall)
    obtain ⟨w, hw⟩ := certificate_witness q v c hq hv hp hc (by rw [he]; exact hδ)
    exact ⟨Nat.pair c w, hw⟩

def search (input : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (certificateCheck input witness))

theorem search_partrec : Partrec search :=
  Partrec.rfind certificateCheck_primrec.to_comp.partrec.to₂

theorem search_domain (q v : Nat) : (search (Nat.pair q v)).Dom ↔ SourceDomain q v := by
  simpa [search, Nat.rfind_dom, eq_comm] using certificate_exists_iff q v

theorem search_checked (input witness : Nat) (hw : witness ∈ search input) :
    certificateCheck input witness = true := by
  have ht : true ∈ Part.some (certificateCheck input witness) := Nat.rfind_spec hw
  simpa only [Part.mem_some_iff, eq_comm] using ht

def evaluation (input : Nat) : Part Nat := (search input).map (fun w => w.unpair.1)

theorem evaluation_partrec : Partrec evaluation :=
  search_partrec.map ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.to₂)

def divide (q v : Nat) : Part Nat := evaluation (Nat.pair q v)

theorem divide_partrec : Partrec₂ divide :=
  (evaluation_partrec.comp Primrec₂.natPair.to_comp).to₂

theorem divide_domain (q v : Nat) : (divide q v).Dom ↔ SourceDomain q v :=
  search_domain q v

theorem divide_value (q v c : Nat) (hc : c ∈ divide q v) :
    unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q ∧
      Canonical.check c = true ∧ unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  obtain ⟨w, hw, he⟩ := (Part.mem_map_iff _).mp hc
  have hs := certificateCheck_spec (Nat.pair q v) w (search_checked _ w hw)
  simpa only [Nat.unpair_pair, he] using hs

theorem divide_original (q v c : Nat) (hc : c ∈ divide q v) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := (divide_value q v c hc).2.2.2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem divide_bound (q v c : Nat) (hc : c ∈ divide q v) :
    unionInterpretation c ≤ unionInterpretation v := by
  have hs := divide_value q v c hc
  exact (MultiplicativePrincipalArithmetic.quotient_le_product hs.2.2.1 _).trans_eq hs.2.2.2.2

theorem divide_returns (q v : Nat) (h : SourceDomain q v) :
    ∃ c : Nat, c ∈ divide q v ∧ Canonical.check c = true ∧
      unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  have hd := (divide_domain q v).mpr h
  have hm : (divide q v).get hd ∈ divide q v := ⟨hd, rfl⟩
  have hs := divide_value q v _ hm
  exact ⟨_, hm, hs.2.2.2.1, hs.2.2.2.2⟩

theorem divide_output_invariant (q v q' v' c d : Nat)
    (hc : c ∈ divide q v) (hd : d ∈ divide q' v')
    (hq : unionInterpretation q = unionInterpretation q')
    (hv : unionInterpretation v = unionInterpretation v') : c = d := by
  have hs := divide_value q v c hc
  have ht := divide_value q' v' d hd
  apply Canonical.check_value_injective c d hs.2.2.2.1 ht.2.2.2.1
  apply MultiplicativePrincipalArithmetic.positive_mul_injective hs.2.2.1
  exact hs.2.2.2.2.trans (hv.trans (by rw [hq]; exact ht.2.2.2.2.symm))

theorem divide_output_unique (q v c d : Nat)
    (hc : c ∈ divide q v) (hd : d ∈ divide q v) : c = d :=
  divide_output_invariant q v q v c d hc hd rfl rfl

/-- Every solution equals the returned quotient: this also proves that the
returned quotient is the least solution in Wilken's displayed definition. -/
theorem divide_eq_every_solution (q v c : Nat) (hc : c ∈ divide q v)
    (δ : Ordinal.{0}) (hδ : unionInterpretation q * δ = unionInterpretation v) :
    unionInterpretation c = δ := by
  have hs := divide_value q v c hc
  exact MultiplicativePrincipalArithmetic.positive_mul_injective hs.2.2.1
    (hs.2.2.2.2.trans hδ.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.ExactDivision
