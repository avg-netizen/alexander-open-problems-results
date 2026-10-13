import Alexander313.Wilken.HereditaryCanonicalCoefficients
import Alexander313.Wilken.HereditaryPrincipalLogarithm
import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# Actual reduced multiplicative factor words and literal last factors

The actual principal logarithm supplies a canonical exponent. Its real
canonical additive word is mapped through the existing genuine omega-power
algorithm. This PR finite construction gives canonical source multiplicative
principals strictly above one, weakly decreasing and with ordered product
equal to the original value. The empty word represents one. Real reduced MNF
uniqueness and canonical value injection give uniqueness of the entire code
word; no uniqueness is asserted for words allowing inserted unit factors.

Both factorization and last-factor computation are actual partial recursive
maps of the proved logarithm search. Their exact domain is original positive
additive-principal admission. PR finite certificates test the real logarithm
graph and literal computed outputs for positive graph Programs. The last
factor uses canonical one at the empty word. No parser, arithmetic, graph,
effectivity or termination oracle is supplied. All terms are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MultiplicativeNormalForm

open Alexander313.Wilken.MultiplicativePrincipalArithmetic
open Alexander313.Wilken.MultiplicativeNormalForm (factorProduct omegaFactors IsReducedMNF)

def factorWord (d : Nat) : List Nat :=
  (CanonicalCoefficients.word d).map OmegaPowers.powerCode

theorem factorWord_primrec : Primrec factorWord :=
  Primrec.list_map CanonicalCoefficients.word_primrec
    (OmegaPowers.powerCode_primrec.comp Primrec.snd).to₂

theorem factorWord_head_spec (d : Nat) (hd : unionCheck d = true) (c : Nat) (hc : c ∈ factorWord d) :
    Canonical.check c = true ∧ 1 < unionInterpretation c ∧
      IsMultiplicativePrincipal (unionInterpretation c) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  have hs := CanonicalCoefficients.word_head_spec d hd a ha
  have hu := Canonical.check_original hs.1
  refine ⟨OmegaPowers.powerCode_checked a hu, ?_, ?_⟩
  · rw [OmegaPowers.powerCode_value a hu]
    exact Ordinal.one_lt_opow.mpr ⟨Ordinal.one_lt_omega0, ne_of_gt hs.2.1⟩
  · rw [OmegaPowers.powerCode_value a hu]
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _,
      (omegaPower_multiplicative_iff _).mpr (Or.inr ⟨hs.2.1, hs.2.2⟩)⟩

theorem factorWord_values (d : Nat) (hd : unionCheck d = true) :
    (factorWord d).map unionInterpretation = omegaFactors (unionInterpretation d) := by
  calc
    (factorWord d).map unionInterpretation =
        ((CanonicalCoefficients.word d).map unionInterpretation).map (fun a => Ordinal.omega0 ^ a) := by
      simp only [factorWord, List.map_map]
      apply List.map_congr_left
      intro a ha
      exact OmegaPowers.powerCode_value a
        (Canonical.check_original (CanonicalCoefficients.word_head_spec d hd a ha).1)
    _ = omegaFactors (unionInterpretation d) := by
      rw [CanonicalCoefficients.word_anf d hd]
      rfl

theorem factorWord_reduced (d : Nat) (hd : unionCheck d = true) :
    IsReducedMNF ((factorWord d).map unionInterpretation) := by
  rw [factorWord_values d hd]
  exact Alexander313.Wilken.MultiplicativeNormalForm.omegaFactors_reduced _

theorem factorWord_product (d : Nat) (hd : unionCheck d = true) :
    factorProduct ((factorWord d).map unionInterpretation) = Ordinal.omega0 ^ unionInterpretation d := by
  rw [factorWord_values d hd]
  exact Alexander313.Wilken.MultiplicativeNormalForm.factorProduct_omegaFactors _

theorem factorWord_invariant (d e : Nat) (hd : unionCheck d = true) (he : unionCheck e = true)
    (hv : unionInterpretation d = unionInterpretation e) : factorWord d = factorWord e := by
  rw [factorWord, factorWord, CanonicalCoefficients.word_invariant d e hd he hv]

def encodeWord (d : Nat) : Nat := Encodable.encode (factorWord d)

theorem encodeWord_primrec : Primrec encodeWord := Primrec.encode.comp factorWord_primrec

def oneCode : Nat := CanonicalArithmetic.oneLabel.1

theorem oneCode_checked : Canonical.check oneCode = true := CanonicalArithmetic.oneLabel.2

theorem oneCode_value : unionInterpretation oneCode = 1 := CanonicalArithmetic.oneLabel_value

def lastFactorCode (d : Nat) : Nat := (factorWord d).reverse[0]?.getD oneCode

theorem lastFactorCode_primrec : Primrec lastFactorCode :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.list_reverse.comp factorWord_primrec) (Primrec.const 0))
    (Primrec.const oneCode)

theorem lastFactorCode_checked (d : Nat) (hd : unionCheck d = true) :
    Canonical.check (lastFactorCode d) = true := by
  cases hw : (factorWord d).reverse with
  | nil => simp only [lastFactorCode, hw]; exact oneCode_checked
  | cons c cs =>
    have hc : c ∈ factorWord d := List.mem_reverse.mp (by rw [hw]; exact List.mem_cons_self)
    simp only [lastFactorCode, hw, List.getElem?_cons_zero, Option.getD_some]
    exact (factorWord_head_spec d hd c hc).1

private theorem last_map_value (xs : List Nat) :
    unionInterpretation (xs.reverse[0]?.getD oneCode) =
      (xs.map unionInterpretation).reverse[0]?.getD 1 := by
  rw [← List.map_reverse]
  cases xs.reverse with
  | nil => exact oneCode_value
  | cons c cs => rfl

theorem lastFactorCode_value (d : Nat) :
    unionInterpretation (lastFactorCode d) =
      Alexander313.Wilken.MultiplicativeNormalForm.lastFactor ((factorWord d).map unionInterpretation) :=
  last_map_value _

def FormSpec (q : Nat) (rs : List Nat) : Prop :=
  Principal.unionPrincipalCheck q = true ∧ (∀ c ∈ rs, Canonical.check c = true) ∧
    IsReducedMNF (rs.map unionInterpretation) ∧ factorProduct (rs.map unionInterpretation) = unionInterpretation q

theorem factorWord_spec (q d : Nat) (hd : PrincipalLogarithm.graph q d = true) : FormSpec q (factorWord d) := by
  have hs := (PrincipalLogarithm.graph_exact q d).mp hd
  have hu := Canonical.check_original hs.2.2.2.1
  exact ⟨(Principal.unionPrincipalCheck_exact q).mpr ⟨hs.1, hs.2.1, hs.2.2.1⟩,
    fun c hc => (factorWord_head_spec d hu c hc).1, factorWord_reduced d hu,
    (factorWord_product d hu).trans hs.2.2.2.2⟩

theorem formSpec_unique (q v : Nat) (xs ys : List Nat) (hx : FormSpec q xs) (hy : FormSpec v ys)
    (he : unionInterpretation q = unionInterpretation v) : xs = ys := by
  apply CanonicalCoefficients.checked_word_ext xs ys hx.2.1 hy.2.1
  exact Alexander313.Wilken.MultiplicativeNormalForm.reducedMNF_unique hx.2.2.1 hy.2.2.1
    (hx.2.2.2.trans (he.trans hy.2.2.2.symm))

theorem formSpec_values (q : Nat) (rs : List Nat) (hr : FormSpec q rs) :
    rs.map unionInterpretation = Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q) := by
  have hs := (Principal.unionPrincipalCheck_exact q).mp hr.1
  exact Alexander313.Wilken.MultiplicativeNormalForm.reducedMNF_unique hr.2.2.1
    (Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF_reduced _)
    (hr.2.2.2.trans (Alexander313.Wilken.MultiplicativeNormalForm.factorProduct_canonicalMNF hs.2.1 hs.2.2).symm)

def normalForm (q : Nat) : Part Nat := (PrincipalLogarithm.logarithm q).map encodeWord

theorem normalForm_partrec : Partrec normalForm :=
  Partrec.map PrincipalLogarithm.logarithm_partrec (encodeWord_primrec.comp Primrec.snd).to_comp.to₂

theorem normalForm_domain (q : Nat) : (normalForm q).Dom ↔ Principal.unionPrincipalCheck q = true :=
  PrincipalLogarithm.logarithm_domain q

theorem normalForm_spec (q : Nat) (rs : List Nat) (hc : Encodable.encode rs ∈ normalForm q) : FormSpec q rs := by
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff encodeWord).mp hc
  have hrs : factorWord d = rs := Encodable.encode_injective he
  rw [← hrs]
  exact factorWord_spec q d (PrincipalLogarithm.logarithm_graph q d hd)

theorem normalForm_returns (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃ rs : List Nat, Encodable.encode rs ∈ normalForm q ∧ FormSpec q rs := by
  obtain ⟨d, hd, _, _⟩ := PrincipalLogarithm.logarithm_returns q hq
  exact ⟨factorWord d, Part.mem_map encodeWord hd,
    factorWord_spec q d (PrincipalLogarithm.logarithm_graph q d hd)⟩

theorem normalForm_head_spec (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalForm q)
    (c : Nat) (hc : c ∈ rs) : Canonical.check c = true ∧ 1 < unionInterpretation c ∧
      IsMultiplicativePrincipal (unionInterpretation c) := by
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff encodeWord).mp hr
  have hrs : factorWord d = rs := Encodable.encode_injective he
  rw [← hrs] at hc
  exact factorWord_head_spec d
    (Canonical.check_original (PrincipalLogarithm.logarithm_value q d hd).2.2.2.1) c hc

theorem normalForm_product (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalForm q) :
    factorProduct (rs.map unionInterpretation) = unionInterpretation q :=
  (normalForm_spec q rs hr).2.2.2

theorem normalForm_values (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalForm q) :
    rs.map unionInterpretation = Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q) :=
  formSpec_values q rs (normalForm_spec q rs hr)

theorem normalForm_descending (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalForm q) :
    (rs.map unionInterpretation).Pairwise (fun a b => b ≤ a) :=
  (normalForm_spec q rs hr).2.2.1.1.2

theorem normalForm_graph_iff (q c : Nat) : c ∈ normalForm q ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ FormSpec q rs := by
  constructor
  · intro hc
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff encodeWord).mp hc
    exact ⟨factorWord d, he.symm, factorWord_spec q d (PrincipalLogarithm.logarithm_graph q d hd)⟩
  · rintro ⟨rs, rfl, hs⟩
    obtain ⟨ss, hc, hss⟩ := normalForm_returns q hs.1
    have he := formSpec_unique q q rs ss hs hss rfl
    rw [he]
    exact hc

theorem normalForm_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, c ∈ normalForm q := by
  obtain ⟨rs, hc, hs⟩ := normalForm_returns q hq
  refine ⟨Encodable.encode rs, hc, ?_⟩
  intro c hc
  obtain ⟨ss, he, hss⟩ := (normalForm_graph_iff q c).mp hc
  exact he.trans (congrArg Encodable.encode (formSpec_unique q q ss rs hss hs rfl))

theorem normalForm_invariant (q v c d : Nat) (hc : c ∈ normalForm q) (hd : d ∈ normalForm v)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  obtain ⟨xs, hcx, hx⟩ := (normalForm_graph_iff q c).mp hc
  obtain ⟨ys, hdy, hy⟩ := (normalForm_graph_iff v d).mp hd
  exact hcx.trans ((congrArg Encodable.encode (formSpec_unique q v xs ys hx hy he)).trans hdy.symm)

def lastFactor (q : Nat) : Part Nat := (PrincipalLogarithm.logarithm q).map lastFactorCode

theorem lastFactor_partrec : Partrec lastFactor :=
  Partrec.map PrincipalLogarithm.logarithm_partrec (lastFactorCode_primrec.comp Primrec.snd).to_comp.to₂

theorem lastFactor_domain (q : Nat) : (lastFactor q).Dom ↔ Principal.unionPrincipalCheck q = true :=
  PrincipalLogarithm.logarithm_domain q

def LastFactorSpec (q c : Nat) : Prop :=
  Canonical.check c = true ∧ ∃ rs : List Nat, FormSpec q rs ∧
    unionInterpretation c = Alexander313.Wilken.MultiplicativeNormalForm.lastFactor (rs.map unionInterpretation)

theorem lastFactor_value (q c : Nat) (hc : c ∈ lastFactor q) : LastFactorSpec q c := by
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff lastFactorCode).mp hc
  have hs := PrincipalLogarithm.logarithm_value q d hd
  rw [← he]
  exact ⟨lastFactorCode_checked d (Canonical.check_original hs.2.2.2.1), factorWord d,
    factorWord_spec q d (PrincipalLogarithm.logarithm_graph q d hd), lastFactorCode_value d⟩

theorem lastFactor_returns (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃ c, c ∈ lastFactor q ∧ LastFactorSpec q c := by
  have hd := (lastFactor_domain q).mpr hq
  have hm : (lastFactor q).get hd ∈ lastFactor q := ⟨hd, rfl⟩
  exact ⟨_, hm, lastFactor_value q _ hm⟩

theorem lastFactor_spec_unique (q v c d : Nat) (hc : LastFactorSpec q c) (hd : LastFactorSpec v d)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  obtain ⟨xs, hx, hcv⟩ := hc.2
  obtain ⟨ys, hy, hdv⟩ := hd.2
  apply Canonical.check_value_injective c d hc.1 hd.1
  rw [hcv, hdv, formSpec_unique q v xs ys hx hy he]

theorem lastFactor_graph_iff (q c : Nat) : c ∈ lastFactor q ↔ LastFactorSpec q c := by
  constructor
  · exact lastFactor_value q c
  · intro hs
    obtain ⟨rs, hrs, _⟩ := hs.2
    obtain ⟨d, hd, hds⟩ := lastFactor_returns q hrs.1
    rw [lastFactor_spec_unique q q c d hs hds rfl]
    exact hd

theorem lastFactor_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, c ∈ lastFactor q := by
  obtain ⟨c, hc, hs⟩ := lastFactor_returns q hq
  exact ⟨c, hc, fun d hd => lastFactor_spec_unique q q d c (lastFactor_value q d hd) hs rfl⟩

theorem lastFactor_invariant (q v c d : Nat) (hc : c ∈ lastFactor q) (hd : d ∈ lastFactor v)
    (he : unionInterpretation q = unionInterpretation v) : c = d :=
  lastFactor_spec_unique q v c d (lastFactor_value q c hc) (lastFactor_value v d hd) he

theorem lastFactor_literal (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalForm q)
    (c : Nat) (hc : c ∈ lastFactor q) : c = rs.reverse[0]?.getD oneCode := by
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff lastFactorCode).mp hc
  have hrs := formSpec_unique q q rs (factorWord d) (normalForm_spec q rs hr)
    (factorWord_spec q d (PrincipalLogarithm.logarithm_graph q d hd)) rfl
  rw [hrs, ← he]
  rfl

theorem lastFactor_original (q c : Nat) (hc : c ∈ lastFactor q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := lastFactor_value q c hc
  exact ⟨Canonical.check_original hs.1, Canonical.check_normal hs.1⟩

theorem lastFactor_source (q c : Nat) (hc : c ∈ lastFactor q) : unionInterpretation c =
    Alexander313.Wilken.MultiplicativeNormalForm.lastFactor
      (Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q)) := by
  obtain ⟨rs, hr, hv⟩ := (lastFactor_value q c hc).2
  rw [hv, formSpec_values q rs hr]

theorem lastFactor_lf (q c : Nat) (hc : c ∈ lastFactor q) :
    unionInterpretation c = Alexander313.Wilken.MultiplicativeNormalForm.lf (unionInterpretation q) :=
  lastFactor_source q c hc

theorem lastFactor_exponent (q c d : Nat) (hc : c ∈ lastFactor q)
    (hd : d ∈ PrincipalLogarithm.logarithm q) : unionInterpretation c =
      Ordinal.omega0 ^ Alexander313.Wilken.MultiplicativeNormalForm.endExponent (unionInterpretation d) := by
  rw [lastFactor_lf q c hc, ← (PrincipalLogarithm.logarithm_value q d hd).2.2.2.2,
    Alexander313.Wilken.MultiplicativeNormalForm.lf_omegaPower]

theorem lastFactor_class (q c : Nat) (hc : c ∈ lastFactor q) :
    IsMultiplicativePrincipal (unionInterpretation c) := by
  obtain ⟨rs, hr, hv⟩ := (lastFactor_value q c hc).2
  rw [hv]
  by_cases hz : rs = []
  · rw [hz]
    exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
  · have hm : rs.map unionInterpretation ≠ [] := fun h => hz (List.map_eq_nil_iff.mp h)
    exact (Alexander313.Wilken.MultiplicativeNormalForm.lastFactor_spec hr.2.2.1 hm).1

theorem lastFactor_multiplicative (q c : Nat) (hc : c ∈ lastFactor q)
    (hq : IsMultiplicativePrincipal (unionInterpretation q)) : unionInterpretation c = unionInterpretation q :=
  (lastFactor_lf q c hc).trans (Alexander313.Wilken.MultiplicativeNormalForm.lf_multiplicative hq)

theorem factorWord_empty_iff (d : Nat) (hd : unionCheck d = true) :
    factorWord d = [] ↔ unionInterpretation d = 0 := by
  have hm : factorWord d = [] ↔ CanonicalCoefficients.word d = [] := List.map_eq_nil_iff
  rw [hm]
  constructor
  · intro hw
    have hs := principalSum_canonicalANF (unionInterpretation d)
    rw [← CanonicalCoefficients.word_anf d hd, hw] at hs
    exact hs.symm
  · intro hz
    have ha := CanonicalCoefficients.word_anf d hd
    rw [hz, canonicalANF_zero] at ha
    exact List.map_eq_nil_iff.mp ha

theorem factorWord_last_unit (d : Nat) (hd : unionCheck d = true) (hz : unionInterpretation d = 0) :
    lastFactorCode d = oneCode := by
  rw [lastFactorCode, (factorWord_empty_iff d hd).mpr hz]
  rfl

theorem formSpec_empty_iff (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    FormSpec q [] ↔ unionInterpretation q = 1 := by
  constructor
  · intro hs
    exact hs.2.2.2.symm
  · intro hunit
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness q hq
    have hs := (PrincipalLogarithm.graph_exact q d).mp hd
    have hz : unionInterpretation d = 0 := omegaPower_strictMono.injective
      (hs.2.2.2.2.trans (hunit.trans (Ordinal.opow_zero _).symm))
    have hw := (factorWord_empty_iff d (Canonical.check_original hs.2.2.2.1)).mpr hz
    rw [← hw]
    exact factorWord_spec q d hd

theorem normalForm_unit (q : Nat) (hq : Principal.unionPrincipalCheck q = true)
    (hv : unionInterpretation q = 1) : normalForm q = Part.some (Encodable.encode ([] : List Nat)) := by
  apply Part.eq_some_iff.mpr
  exact (normalForm_graph_iff q _).mpr ⟨[], rfl, (formSpec_empty_iff q hq).mpr hv⟩

theorem lastFactor_unit (q : Nat) (hq : Principal.unionPrincipalCheck q = true)
    (hv : unionInterpretation q = 1) : lastFactor q = Part.some oneCode := by
  apply Part.eq_some_iff.mpr
  apply (lastFactor_graph_iff q oneCode).mpr
  exact ⟨oneCode_checked, [], (formSpec_empty_iff q hq).mpr hv, oneCode_value⟩

/-- False is the complete factor-word output; true is the literal last code. -/
def certificateOutput (last : Bool) (d : Nat) : Nat := cond last (lastFactorCode d) (encodeWord d)

theorem certificateOutput_primrec : Primrec₂ certificateOutput :=
  (Primrec.fst.cond (lastFactorCode_primrec.comp Primrec.snd) (encodeWord_primrec.comp Primrec.snd)).to₂

def certificateCheck (last : Bool) (query d : Nat) : Bool :=
  PrincipalLogarithm.graph query.unpair.1 d && (query.unpair.2 == certificateOutput last d)

theorem certificateCheck_primrec : Primrec (fun p : Bool × (Nat × Nat) => certificateCheck p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Bool × (Nat × Nat) => p.2.1.unpair) := Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun p : Bool × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (PrincipalLogarithm.graph_primrec.comp (Primrec.fst.comp hq) hd)
    (Primrec.beq.comp (Primrec.snd.comp hq) (certificateOutput_primrec.comp Primrec.fst hd))

theorem formCertificate_exists_iff (q c : Nat) :
    (∃ d, certificateCheck false (Nat.pair q c) d = true) ↔
      ∃ rs : List Nat, c = Encodable.encode rs ∧ FormSpec q rs := by
  constructor
  · rintro ⟨d, hd⟩
    have hs : PrincipalLogarithm.graph q d = true ∧ c = encodeWord d := by
      simpa only [certificateCheck, Nat.unpair_pair, certificateOutput, Bool.cond_false,
        Bool.and_eq_true, beq_iff_eq] using hd
    exact ⟨factorWord d, hs.2, factorWord_spec q d hs.1⟩
  · rintro ⟨rs, rfl, hs⟩
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness q hs.1
    have he := formSpec_unique q q rs (factorWord d) hs (factorWord_spec q d hd) rfl
    exact ⟨d, by simp only [certificateCheck, Nat.unpair_pair, hd, Bool.true_and,
      certificateOutput, Bool.cond_false, beq_iff_eq, encodeWord, he]⟩

theorem lastCertificate_exists_iff (q c : Nat) :
    (∃ d, certificateCheck true (Nat.pair q c) d = true) ↔ LastFactorSpec q c := by
  constructor
  · rintro ⟨d, hd⟩
    have hs : PrincipalLogarithm.graph q d = true ∧ c = lastFactorCode d := by
      simpa only [certificateCheck, Nat.unpair_pair, certificateOutput, Bool.cond_true,
        Bool.and_eq_true, beq_iff_eq] using hd
    have hdcanon := ((PrincipalLogarithm.graph_exact q d).mp hs.1).2.2.2.1
    rw [hs.2]
    exact ⟨lastFactorCode_checked d (Canonical.check_original hdcanon), factorWord d,
      factorWord_spec q d hs.1, lastFactorCode_value d⟩
  · intro hs
    obtain ⟨rs, hrs, hv⟩ := hs.2
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness q hrs.1
    have hds := (PrincipalLogarithm.graph_exact q d).mp hd
    have he := formSpec_unique q q rs (factorWord d) hrs (factorWord_spec q d hd) rfl
    have hlast : c = lastFactorCode d := Canonical.check_value_injective _ _ hs.1
      (lastFactorCode_checked d (Canonical.check_original hds.2.2.2.1))
      (hv.trans (by rw [he]; exact (lastFactorCode_value d).symm))
    exact ⟨d, by simp only [certificateCheck, Nat.unpair_pair, hd, Bool.true_and,
      certificateOutput, Bool.cond_true, beq_iff_eq]; exact hlast⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.MultiplicativeNormalForm
