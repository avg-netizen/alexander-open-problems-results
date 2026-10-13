import Alexander313.Wilken.OrdinalPowerArithmetic
import Alexander313.Wilken.HereditaryMultiplication

/-!
# Actual decomposition of every original exponent into omega*delta+n

A PR numerical certificate contains a canonical delta, a natural n and the
constructed multiplier's genuine certificate for omega*delta. Real source
addition/equality checks the equation with the original exponent. Ordinal
division and finite remainder prove existence with delta bounded by the input;
actual canonical interval coverage therefore derives search termination.

The result encodes (canonical delta, n, canonical omega*delta). Actual ordinal
division uniqueness and canonical value injection determine that entire triple
independently of the original spelling or multiplication witness. No ordinal
division/decomposition graph or effectivity oracle is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.ExponentDecomposition

def omegaCode : Nat := OmegaPowers.powerCode (CanonicalArithmetic.numeralCode 1)

theorem omegaCode_checked : Canonical.check omegaCode = true :=
  OmegaPowers.powerCode_checked _ (Canonical.check_original (CanonicalArithmetic.numeralCode_checked 1))

theorem omegaCode_value : unionInterpretation omegaCode = Ordinal.omega0 := by
  rw [omegaCode, OmegaPowers.powerCode_value _
    (Canonical.check_original (CanonicalArithmetic.numeralCode_checked 1)),
    CanonicalArithmetic.numeralCode_value, Nat.cast_one, Ordinal.opow_one]

def delta (data : Nat) : Nat := data.unpair.1
def offset (data : Nat) : Nat := data.unpair.2.unpair.1
def «prefix» (data : Nat) : Nat := data.unpair.2.unpair.2

theorem delta_primrec : Primrec delta := Primrec.fst.comp Primrec.unpair
theorem offset_primrec : Primrec offset :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
theorem prefix_primrec : Primrec «prefix» :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

def productCandidate (w : Nat) : Nat :=
  Multiplication.candidate (Nat.pair omegaCode (delta w)) («prefix» w)

theorem productCandidate_primrec : Primrec productCandidate :=
  Multiplication.candidate_primrec.comp
    (Primrec₂.natPair.comp (Primrec.const omegaCode) delta_primrec) prefix_primrec

def certificateCheck (v w : Nat) : Bool :=
  (unionCheck v && Canonical.check (delta w)) &&
    (Multiplication.certificateCheck (Nat.pair omegaCode (delta w)) («prefix» w) &&
      Canonical.graph v (CanonicalArithmetic.canonicalSum (productCandidate w)
        (CanonicalArithmetic.numeralCode (offset w))))

theorem certificateCheck_primrec : Primrec₂ certificateCheck := by
  have hd := delta_primrec.comp Primrec.snd
  have hn := offset_primrec.comp Primrec.snd
  have hw := prefix_primrec.comp Primrec.snd
  have hp := Primrec₂.natPair.comp (Primrec.const omegaCode) hd
  exact (Primrec.and.comp
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
      (Canonical.Effective.check_primrec.comp hd))
    (Primrec.and.comp (Multiplication.certificateCheck_primrec.comp hp hw)
      (Canonical.Effective.graph_primrec.comp Primrec.fst
        (CanonicalArithmetic.canonicalSum_primrec.comp (productCandidate_primrec.comp Primrec.snd)
          (CanonicalArithmetic.numeralCode_primrec.comp hn))))).to₂

def pack (w : Nat) : Nat := Nat.pair (delta w) (Nat.pair (offset w) (productCandidate w))

theorem pack_primrec : Primrec pack :=
  Primrec₂.natPair.comp delta_primrec (Primrec₂.natPair.comp offset_primrec productCandidate_primrec)

/-- The original exponent and every interpreted component retain their true
source meanings. The remainder is a raw Nat, not a coded ordinal oracle. -/
def DataSpec (v data : Nat) : Prop :=
  unionCheck v = true ∧ Canonical.check (delta data) = true ∧ Canonical.check («prefix» data) = true ∧
    unionInterpretation («prefix» data) = Ordinal.omega0 * unionInterpretation (delta data) ∧
    unionInterpretation v = unionInterpretation («prefix» data) + (offset data : Ordinal.{0})

theorem certificateCheck_spec (v w : Nat) (hw : certificateCheck v w = true) : DataSpec v (pack w) := by
  have hs := Bool.and_eq_true.mp hw
  have hl := Bool.and_eq_true.mp hs.1
  have hr := Bool.and_eq_true.mp hs.2
  have hp := Multiplication.candidate_value _ _ hr.1
  have hv := (Canonical.graph_exact _ _).mp hr.2
  have he : unionInterpretation (productCandidate w) = Ordinal.omega0 * unionInterpretation (delta w) := by
    simpa only [productCandidate, Nat.unpair_pair, omegaCode_value] using hp.2
  simp only [DataSpec, pack, delta, «prefix», offset, Nat.unpair_pair]
  refine ⟨hl.1, hl.2, hp.1, he, ?_⟩
  exact hv.2.2.trans (by
    rw [CanonicalArithmetic.canonicalSum_value _ _ (Canonical.check_original hp.1)
      (Canonical.check_original (CanonicalArithmetic.numeralCode_checked _)),
      CanonicalArithmetic.numeralCode_value])

theorem certificate_witness (v : Nat) (hv : unionCheck v = true) :
    ∃ w : Nat, certificateCheck v w = true := by
  obtain ⟨δ, n, he, hbound⟩ := OrdinalPowerArithmetic.omega_finite_decomposition (unionInterpretation v)
  have hsmall : unionInterpretation v < finiteBaseLimit :=
    (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨v, hv, rfl⟩
  obtain ⟨d, hd, hdv⟩ := (Canonical.lt_finiteBaseLimit_iff_code δ).mp (hbound.trans_lt hsmall)
  obtain ⟨w, hw⟩ := Multiplication.certificateCheck_witness omegaCode d (Canonical.check_original omegaCode_checked)
    (Canonical.check_original hd)
  have hp := Multiplication.candidate_value (Nat.pair omegaCode d) w hw
  refine ⟨Nat.pair d (Nat.pair n w), ?_⟩
  simp only [certificateCheck, delta, offset, «prefix», Nat.unpair_pair, hv, hd, Bool.true_and, hw]
  apply (Canonical.graph_exact v _).mpr
  refine ⟨hv, CanonicalArithmetic.canonicalSum_checked _ _ (Canonical.check_original hp.1)
    (Canonical.check_original (CanonicalArithmetic.numeralCode_checked n)), ?_⟩
  rw [CanonicalArithmetic.canonicalSum_value _ _ (Canonical.check_original hp.1)
    (Canonical.check_original (CanonicalArithmetic.numeralCode_checked n)),
    CanonicalArithmetic.numeralCode_value]
  have hproduct : unionInterpretation (Multiplication.candidate (Nat.pair omegaCode d) w) = Ordinal.omega0 * δ :=
    by simpa only [Nat.unpair_pair, omegaCode_value, hdv] using hp.2
  simpa only [productCandidate, delta, offset, «prefix», Nat.unpair_pair, hproduct] using he

def search (v : Nat) : Part Nat := Nat.rfind (fun w => Part.some (certificateCheck v w))

theorem search_partrec : Partrec search := Partrec.rfind certificateCheck_primrec.to_comp.partrec.to₂

theorem search_domain (v : Nat) : (search v).Dom ↔ unionCheck v = true := by
  have he : (∃ w, certificateCheck v w = true) ↔ unionCheck v = true := by
    constructor
    · rintro ⟨w, hw⟩; exact (certificateCheck_spec v w hw).1
    · exact certificate_witness v
  simpa [search, Nat.rfind_dom, eq_comm] using he

theorem search_checked (v w : Nat) (hw : w ∈ search v) : certificateCheck v w = true := by
  have ht : true ∈ Part.some (certificateCheck v w) := Nat.rfind_spec hw
  simpa only [Part.mem_some_iff, eq_comm] using ht

def decompose (v : Nat) : Part Nat := (search v).map pack

theorem decompose_partrec : Partrec decompose :=
  search_partrec.map (pack_primrec.comp Primrec.snd).to_comp.to₂

theorem decompose_domain (v : Nat) : (decompose v).Dom ↔ unionCheck v = true := search_domain v

theorem decompose_value (v data : Nat) (hd : data ∈ decompose v) : DataSpec v data := by
  obtain ⟨w, hw, he⟩ := (Part.mem_map_iff pack).mp hd
  rw [← he]
  exact certificateCheck_spec v w (search_checked v w hw)

theorem decompose_returns (v : Nat) (hv : unionCheck v = true) :
    ∃ data : Nat, data ∈ decompose v ∧ DataSpec v data := by
  have hd := (decompose_domain v).mpr hv
  have hm : (decompose v).get hd ∈ decompose v := ⟨hd, rfl⟩
  exact ⟨_, hm, decompose_value v _ hm⟩

theorem data_unique (v t s : Nat) (ht : DataSpec v t) (hs : DataSpec v s) : t = s := by
  have he := OrdinalPowerArithmetic.omega_finite_decomposition_unique
    (ht.2.2.2.2.trans (by rw [ht.2.2.2.1])) (hs.2.2.2.2.trans (by rw [hs.2.2.2.1]))
  have hd := Canonical.check_value_injective (delta t) (delta s) ht.2.1 hs.2.1 he.1
  have hp := Canonical.check_value_injective («prefix» t) («prefix» s) ht.2.2.1 hs.2.2.1
    (ht.2.2.2.1.trans (by rw [he.1]; exact hs.2.2.2.1.symm))
  have hunpair : t.unpair = s.unpair := by
    apply Prod.ext
    · exact hd
    · apply Nat.unpair_injective
      exact Prod.ext he.2 hp
  exact Nat.unpair_injective hunpair

theorem decompose_graph_iff (v data : Nat) : data ∈ decompose v ↔ DataSpec v data := by
  constructor
  · exact decompose_value v data
  · intro hs
    obtain ⟨t, ht, hts⟩ := decompose_returns v hs.1
    rw [data_unique v data t hs hts]
    exact ht

end Alexander313.Wilken.RelativeTerm.Hereditary.ExponentDecomposition
