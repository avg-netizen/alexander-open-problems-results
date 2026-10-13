import Alexander313.Wilken.HereditaryNativePublicReturn
import Alexander313.Wilken.HereditaryNativeHeight
import Alexander313.Wilken.HereditaryPowers

/-!
# Genuine low arithmetic at the same positive public epsilon

Original native low inputs at contextCode s return to the actual public
level s+1. Their real values are below finiteBase(s+2), not merely below the
next cardinal. The endpoint is an actual omega fixed point; real ordinal
multiplicative closure and the bound a^b <= omega^(a*b) keep arithmetic
outputs below it. Logarithms are bounded by their genuine input components.

Actual public multiplication, arbitrary-base powers and first/last/principal
logarithm searches execute. Their canonical results undergo the real finite
embedding/bounded lowering return and then mapParameters translation into
the SAME original native context. Every caller bound is derived. Only this
positive public-base LOW domain is constructed; arbitrary coded epsilons,
full-sort native multiplication, dotted right subtraction, ordinal syntax
uniqueness and input-height preservation are not asserted. Search producers
are Partrec; finite conversions and omega-power kernels are separately PR.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowArithmetic

open NativePublicBridge (contextCode contextCode_primrec)

def lowInput (s c : Nat) : Bool := lowCheckCode (contextCode s) c

theorem lowInput_primrec : Primrec₂ lowInput :=
  (lowCheckCode_primrec.comp (contextCode_primrec.comp Primrec.fst) Primrec.snd).to₂

def publicCode (s c : Nat) : Nat := Nat.pair (s + 1) (NativePublicReturn.rawReturnCode s c)

theorem publicCode_primrec : Primrec₂ publicCode :=
  (Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) NativePublicReturn.rawReturnCode_primrec).to₂

theorem publicCode_spec (s c : Nat) (hc : lowInput s c = true) :
    unionCheck (publicCode s c) = true ∧ unionInterpretation (publicCode s c) = interpretation (contextCode s) c :=
  NativePublicReturn.rawReturnCode_union s c hc

theorem lowInput_bound (s c : Nat) (hc : lowInput s c = true) :
    interpretation (contextCode s) c < finiteBase ((s + 1) + 1) := by
  have hs := NativePublicReturn.rawReturnCode_low_spec s c hc
  have hb := (lt_nextBase_iff_code (s + 1) _).mpr
    ⟨NativePublicReturn.rawReturnCode s c, ((Theta.acceptedLowCode_iff _ _).mp hs.1).1, rfl⟩
  exact hs.2 ▸ hb

theorem endpoint_mul_closed (s : Nat) : Ordinal.IsPrincipal (· * ·) (finiteBase ((s + 1) + 1)) := by
  have he := finiteBase_succ_omegaPower_eq_self (s + 1)
  simpa only [he] using Ordinal.isPrincipal_mul_omega0_opow_opow (finiteBase ((s + 1) + 1))

theorem endpoint_power_closed (s : Nat) (a b : Ordinal.{0})
    (ha : a < finiteBase ((s + 1) + 1)) (hb : b < finiteBase ((s + 1) + 1)) :
    a ^ b < finiteBase ((s + 1) + 1) := by
  have hm := endpoint_mul_closed s ha hb
  have hp := omegaPower_strictMono hm
  rw [finiteBase_succ_omegaPower_eq_self (s + 1)] at hp
  calc
    a ^ b ≤ (Ordinal.omega0 ^ a) ^ b := Ordinal.opow_le_opow_left b (omegaPower_self_le a)
    _ = Ordinal.omega0 ^ (a * b) := (Ordinal.opow_mul _ _ _).symm
    _ < finiteBase ((s + 1) + 1) := hp

theorem translateCode_low (s c : Nat) (hc : Hereditary.lowCheckCode (s + 1) c = true) :
    lowCheckCode (contextCode s) (NativePublicBridge.translateCode s c) = true := by
  obtain ⟨t, rfl, ht⟩ := (Hereditary.lowCheckCode_iff (s + 1) c).mp hc
  simpa only [NativePublicBridge.translateCode_code, lowCheckCode_code, lowCheck,
    NativePublicBridge.translate_check, NativePublicBridge.translate_outerSort, Hereditary.lowCheck] using ht

/-- A real finite return, licensed only by canonical original admission and
the actual endpoint bound. Every executing caller below derives this bound. -/
def returnCode (s w : Nat) : Nat := NativePublicBridge.translateCode s
  (SourceZeta.Transport.returnCode (s + 1) w)

theorem returnCode_primrec : Primrec₂ returnCode :=
  (NativePublicBridge.translateCode_primrec.comp Primrec.fst
    (SourceZeta.Transport.returnCode_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)).to₂

theorem returnCode_spec (s w : Nat) (hw : Canonical.check w = true)
    (hb : unionInterpretation w < finiteBase ((s + 1) + 1)) :
    lowInput s (returnCode s w) = true ∧ Comparison.acceptedCode (contextCode s) (returnCode s w) = true ∧
      interpretation (contextCode s) (returnCode s w) = unionInterpretation w := by
  have hr := SourceZeta.Transport.returnCode_spec (s + 1) w hw hb
  have hs := (Theta.acceptedLowCode_iff _ _).mp hr.1
  have hcheck : Hereditary.checkCode (s + 1) (SourceZeta.Transport.returnCode (s + 1) w) = true :=
    (Bool.and_eq_true.mp (by simpa only [Hereditary.lowCheckCode_eq] using hs.1)).1
  have hnormal : SourceDecomposition.inputCheck (s + 1) (SourceZeta.Transport.returnCode (s + 1) w) = true :=
    (SourceDecomposition.inputCheck_exact _ _).mpr ⟨hcheck, hs.2⟩
  exact ⟨translateCode_low s _ hs.1, NativePublicBridge.translateCode_accepted s _ hnormal,
    (NativePublicBridge.translateCode_value s _).trans hr.2⟩

def principalInput (s c : Nat) : Bool := lowInput s c && Principal.unionPrincipalCheck (publicCode s c)

theorem principalInput_primrec : Primrec₂ principalInput :=
  (Primrec.and.comp lowInput_primrec (Principal.unionPrincipalCheck_primrec.comp publicCode_primrec)).to₂

theorem principalInput_exact (s c : Nat) : principalInput s c = true ↔
    lowInput s c = true ∧ 0 < interpretation (contextCode s) c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation (contextCode s) c) := by
  constructor
  · intro h
    obtain ⟨hc, hp⟩ := Bool.and_eq_true.mp h
    have hv := publicCode_spec s c hc
    have hs := (Principal.unionPrincipalCheck_exact _).mp hp
    exact ⟨hc, hv.2 ▸ hs.2.1, hv.2 ▸ hs.2.2⟩
  · rintro ⟨hc, hp, hprincipal⟩
    have hv := publicCode_spec s c hc
    exact Bool.and_eq_true.mpr ⟨hc, (Principal.unionPrincipalCheck_exact _).mpr
      ⟨hv.1, hv.2.symm ▸ hp, hv.2.symm ▸ hprincipal⟩⟩

/-- Tags 0/1 are binary multiplication/power; 2/3/4/5 are unary
leading logarithm/last logarithm/positive principal logarithm/omega power. -/
def input (tag s c d : Nat) : Bool :=
  cond ((tag == 0) || (tag == 1)) (lowInput s c && lowInput s d)
    (cond ((tag == 2) || (tag == 3) || (tag == 5)) (lowInput s c)
      (cond (tag == 4) (principalInput s c) false))

theorem input_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hs := Primrec.snd.comp Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have he (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  exact (Primrec.or.comp (he 0) (he 1)).cond
    (Primrec.and.comp (lowInput_primrec.comp hs hc) (lowInput_primrec.comp hs hd))
    ((Primrec.or.comp (Primrec.or.comp (he 2) (he 3)) (he 5)).cond
      (lowInput_primrec.comp hs hc) ((he 4).cond (principalInput_primrec.comp hs hc) (Primrec.const false)))

theorem input_exact (tag s c d : Nat) : input tag s c d = true ↔
    ((tag = 0 ∨ tag = 1) ∧ lowInput s c = true ∧ lowInput s d = true) ∨
    ((tag = 2 ∨ tag = 3 ∨ tag = 5) ∧ lowInput s c = true) ∨
    (tag = 4 ∧ lowInput s c = true ∧ 0 < interpretation (contextCode s) c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation (contextCode s) c)) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3
        · subst tag; simp [input]
        · by_cases h4 : tag = 4
          · subst tag; simp [input, principalInput_exact]
          · by_cases h5 : tag = 5 <;> simp [input, h0, h1, h2, h3, h4, h5]

theorem input_left (tag s c d : Nat) (hi : input tag s c d = true) : lowInput s c = true := by
  rcases (input_exact tag s c d).mp hi with ⟨_, hc, _⟩ | ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> exact hc

def publicOperation (tag u v : Nat) : Part Nat :=
  cond (tag == 0) (Multiplication.multiply u v)
    (cond (tag == 1) (Powers.power u v)
      (cond (tag == 2) (LogEnd.leadingLog u)
        (cond (tag == 3) (LogEnd.logend u)
          (cond (tag == 4) (PrincipalLogarithm.logarithm u)
            (cond (tag == 5) (Part.some (OmegaPowers.powerCode u)) Part.none)))))

theorem publicOperation_partrec : Partrec
    (fun p : Nat × (Nat × Nat) => publicOperation p.1 p.2.1 p.2.2) := by
  have he (n : Nat) := (Primrec.beq.comp Primrec.fst (Primrec.const n)).to_comp
  have hu := Computable.fst.comp Computable.snd
  have hv := Computable.snd.comp Computable.snd
  exact Partrec.cond (he 0) (Multiplication.multiply_partrec.comp hu hv)
    (Partrec.cond (he 1) (Powers.power_partrec.comp hu hv)
      (Partrec.cond (he 2) (LogEnd.leadingLog_partrec.comp hu)
        (Partrec.cond (he 3) (LogEnd.logend_partrec.comp hu)
          (Partrec.cond (he 4) (PrincipalLogarithm.logarithm_partrec.comp hu)
            (Partrec.cond (he 5) (OmegaPowers.powerCode_primrec.to_comp.comp hu).partrec Partrec.none)))))

def operation (tag s c d : Nat) : Part Nat := cond (input tag s c d)
  ((publicOperation tag (publicCode s c) (publicCode s d)).map (returnCode s)) Part.none

theorem operation_partrec : Partrec
    (fun p : (Nat × Nat) × (Nat × Nat) => operation p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Computable.fst.comp Computable.fst
  have hs := Computable.snd.comp Computable.fst
  have hc := Computable.fst.comp Computable.snd
  have hd := Computable.snd.comp Computable.snd
  have hp := publicOperation_partrec.comp (ht.pair
    ((publicCode_primrec.to_comp.comp hs hc).pair (publicCode_primrec.to_comp.comp hs hd)))
  have hm := Partrec.map hp (returnCode_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd).to₂
  exact Partrec.cond input_primrec.to_comp hm Partrec.none

theorem operation_witness (tag s c d out : Nat) (ho : out ∈ operation tag s c d) :
    input tag s c d = true ∧ ∃ w, w ∈ publicOperation tag (publicCode s c) (publicCode s d) ∧ out = returnCode s w := by
  cases hi : input tag s c d with
  | false => simp only [operation, hi, Bool.cond_false, Part.notMem_none] at ho
  | true =>
    obtain ⟨w, hw, he⟩ := (Part.mem_map_iff (returnCode s)).mp
      (by simpa only [operation, hi, Bool.cond_true] using ho)
    exact ⟨hi, w, hw, he.symm⟩

/-- True ordinal results, with source first/last logarithms including log 0=0. -/
def ResultSpec (tag : Nat) (a b z : Ordinal.{0}) : Prop :=
  if tag = 0 then z = a * b else if tag = 1 then z = a ^ b else
  if tag = 2 then LogEnd.SourceLogSpec false a z else
  if tag = 3 then LogEnd.SourceLogSpec true a z else
  if tag = 4 then Ordinal.omega0 ^ z = a else
  if tag = 5 then z = Ordinal.omega0 ^ a else False

theorem publicOperation_terminates (tag s c d : Nat) (hi : input tag s c d = true) :
    (publicOperation tag (publicCode s c) (publicCode s d)).Dom := by
  rcases (input_exact tag s c d).mp hi with ⟨ht, hc, hd⟩ | ⟨ht, hc⟩ | ⟨ht, hc, hp, ha⟩
  · have hpc := (publicCode_spec s c hc).1
    have hpd := (publicCode_spec s d hd).1
    rcases ht with rfl | rfl
    · simpa [publicOperation] using (Multiplication.multiply_domain _ _).mpr ⟨hpc, hpd⟩
    · simpa [publicOperation] using (Powers.power_domain _ _).mpr ⟨hpc, hpd⟩
  · have hpc := (publicCode_spec s c hc).1
    rcases ht with rfl | rfl | rfl
    · simpa [publicOperation] using (LogEnd.leadingLog_domain _).mpr hpc
    · simpa [publicOperation] using (LogEnd.logend_domain _).mpr hpc
    · simp [publicOperation]
  · subst tag
    have hpc := publicCode_spec s c hc
    have hpr := (Principal.unionPrincipalCheck_exact _).mpr
      ⟨hpc.1, hpc.2.symm ▸ hp, hpc.2.symm ▸ ha⟩
    simpa [publicOperation] using (PrincipalLogarithm.logarithm_domain _).mpr hpr

theorem publicOperation_spec (tag s c d w : Nat) (hi : input tag s c d = true)
    (hw : w ∈ publicOperation tag (publicCode s c) (publicCode s d)) :
    Canonical.check w = true ∧ unionInterpretation w < finiteBase ((s + 1) + 1) ∧
      ResultSpec tag (interpretation (contextCode s) c) (interpretation (contextCode s) d) (unionInterpretation w) := by
  rcases (input_exact tag s c d).mp hi with ⟨ht, hc, hd⟩ | ⟨ht, hc⟩ | ⟨ht, hc, hp, ha⟩
  · have hpc := publicCode_spec s c hc
    have hpd := publicCode_spec s d hd
    rcases ht with rfl | rfl
    · have hm : w ∈ Multiplication.multiply (publicCode s c) (publicCode s d) := by simpa [publicOperation] using hw
      have hs := Multiplication.multiply_value _ _ w hm
      have he : unionInterpretation w = interpretation (contextCode s) c * interpretation (contextCode s) d := by
        simpa only [hpc.2, hpd.2] using hs.2.2.2
      exact ⟨hs.2.2.1, he.symm ▸ endpoint_mul_closed s (lowInput_bound s c hc) (lowInput_bound s d hd), by simpa [ResultSpec] using he⟩
    · have hm : w ∈ Powers.power (publicCode s c) (publicCode s d) := by simpa [publicOperation] using hw
      have hs := Powers.power_value _ _ w hm
      have he : unionInterpretation w = interpretation (contextCode s) c ^ interpretation (contextCode s) d := by
        simpa only [hpc.2, hpd.2] using hs.2.2.2
      exact ⟨hs.2.2.1, he.symm ▸ endpoint_power_closed s _ _ (lowInput_bound s c hc) (lowInput_bound s d hd), by simpa [ResultSpec] using he⟩
  · have hpc := publicCode_spec s c hc
    rcases ht with rfl | rfl | rfl
    · have hm : w ∈ LogEnd.componentLog false (publicCode s c) := by simpa [publicOperation, LogEnd.leadingLog] using hw
      have hs := LogEnd.componentLog_value false _ w hm
      have hb := (LogEnd.componentLog_bound false _ w hm).trans_lt (hpc.2.symm ▸ lowInput_bound s c hc)
      exact ⟨hs.2.1, hb, by simpa [ResultSpec, hpc.2] using hs.2.2⟩
    · have hm : w ∈ LogEnd.componentLog true (publicCode s c) := by simpa [publicOperation, LogEnd.logend] using hw
      have hs := LogEnd.componentLog_value true _ w hm
      have hb := (LogEnd.componentLog_bound true _ w hm).trans_lt (hpc.2.symm ▸ lowInput_bound s c hc)
      exact ⟨hs.2.1, hb, by simpa [ResultSpec, hpc.2] using hs.2.2⟩
    · have he : w = OmegaPowers.powerCode (publicCode s c) := by simpa [publicOperation, eq_comm] using hw
      subst w
      have hv := OmegaPowers.powerCode_value _ hpc.1
      have hb := omegaPower_strictMono (hpc.2.symm ▸ lowInput_bound s c hc)
      rw [finiteBase_succ_omegaPower_eq_self (s + 1)] at hb
      exact ⟨OmegaPowers.powerCode_checked _ hpc.1, hv.symm ▸ hb, by simpa [ResultSpec, hpc.2] using hv⟩
  · subst tag
    have hm : w ∈ PrincipalLogarithm.logarithm (publicCode s c) := by simpa [publicOperation] using hw
    have hs := PrincipalLogarithm.logarithm_value _ w hm
    have hpc := publicCode_spec s c hc
    have hb := (PrincipalLogarithm.logarithm_bound _ w hm).trans_lt (hpc.2.symm ▸ lowInput_bound s c hc)
    exact ⟨hs.2.2.2.1, hb, by simpa [ResultSpec, hpc.2] using hs.2.2.2.2⟩

theorem operation_domain (tag s c d : Nat) : (operation tag s c d).Dom ↔ input tag s c d = true := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    exact (operation_witness tag s c d out ho).1
  · intro hi
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (publicOperation_terminates tag s c d hi)
    have hm : returnCode s w ∈ operation tag s c d := by
      simp only [operation, hi, Bool.cond_true]
      exact (Part.mem_map_iff (returnCode s)).mpr ⟨w, hw, rfl⟩
    exact Part.dom_iff_mem.mpr ⟨_, hm⟩

theorem operation_spec (tag s c d out : Nat) (ho : out ∈ operation tag s c d) :
    input tag s c d = true ∧ lowInput s out = true ∧ Comparison.acceptedCode (contextCode s) out = true ∧
      interpretation (contextCode s) out < finiteBase ((s + 1) + 1) ∧
      ResultSpec tag (interpretation (contextCode s) c) (interpretation (contextCode s) d) (interpretation (contextCode s) out) := by
  obtain ⟨hi, w, hw, rfl⟩ := operation_witness tag s c d out ho
  have hs := publicOperation_spec tag s c d w hi hw
  have hr := returnCode_spec s w hs.1 hs.2.1
  exact ⟨hi, hr.1, hr.2.1, hr.2.2.symm ▸ hs.2.1, hr.2.2.symm ▸ hs.2.2⟩

theorem operation_returns (tag s c d : Nat) (hi : input tag s c d = true) :
    ∃ out, out ∈ operation tag s c d ∧ lowInput s out = true ∧ Comparison.acceptedCode (contextCode s) out = true := by
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((operation_domain tag s c d).mpr hi)
  have hs := operation_spec tag s c d out ho
  exact ⟨out, ho, hs.2.1, hs.2.2.1⟩

theorem operation_unique (tag s c d : Nat) (hi : input tag s c d = true) :
    ∃! out, out ∈ operation tag s c d := by
  obtain ⟨out, ho, _⟩ := operation_returns tag s c d hi
  exact ⟨out, ho, fun z hz => Part.mem_unique hz ho⟩

private theorem sourceLogSpec_unique (last : Bool) (a z v : Ordinal.{0})
    (hz : LogEnd.SourceLogSpec last a z) (hv : LogEnd.SourceLogSpec last a v) : z = v := by
  by_cases ha : a = 0
  · have h0z : z = 0 := by simpa only [LogEnd.SourceLogSpec, if_pos ha] using hz
    have h0v : v = 0 := by simpa only [LogEnd.SourceLogSpec, if_pos ha] using hv
    exact h0z.trans h0v.symm
  · have hpz : Ordinal.omega0 ^ z = LogEnd.componentValue last a := by simpa only [LogEnd.SourceLogSpec, if_neg ha] using hz
    have hpv : Ordinal.omega0 ^ v = LogEnd.componentValue last a := by simpa only [LogEnd.SourceLogSpec, if_neg ha] using hv
    exact omegaPower_strictMono.injective (hpz.trans hpv.symm)

theorem resultSpec_unique (tag : Nat) (a b z v : Ordinal.{0})
    (hz : ResultSpec tag a b z) (hv : ResultSpec tag a b v) : z = v := by
  by_cases h0 : tag = 0
  · subst tag; exact (by simpa [ResultSpec] using hz : z = a * b).trans (by simpa [ResultSpec] using hv : v = a * b).symm
  · by_cases h1 : tag = 1
    · subst tag; exact (by simpa [ResultSpec] using hz : z = a ^ b).trans (by simpa [ResultSpec] using hv : v = a ^ b).symm
    · by_cases h2 : tag = 2
      · subst tag; exact sourceLogSpec_unique false a z v (by simpa [ResultSpec] using hz) (by simpa [ResultSpec] using hv)
      · by_cases h3 : tag = 3
        · subst tag; exact sourceLogSpec_unique true a z v (by simpa [ResultSpec] using hz) (by simpa [ResultSpec] using hv)
        · by_cases h4 : tag = 4
          · subst tag; exact omegaPower_strictMono.injective ((by simpa [ResultSpec] using hz : Ordinal.omega0 ^ z = a).trans (by simpa [ResultSpec] using hv : Ordinal.omega0 ^ v = a).symm)
          · by_cases h5 : tag = 5
            · subst tag; exact (by simpa [ResultSpec] using hz : z = Ordinal.omega0 ^ a).trans (by simpa [ResultSpec] using hv : v = Ordinal.omega0 ^ a).symm
            · simp [ResultSpec, h0, h1, h2, h3, h4, h5] at hz

/-- Equal actual input values give the same literal selected return code;
the proof uses unique canonical intermediate results, not native syntax uniqueness. -/
theorem operation_invariant (tag s c d c' d' out out' : Nat)
    (ho : out ∈ operation tag s c d) (ho' : out' ∈ operation tag s c' d')
    (hc : interpretation (contextCode s) c = interpretation (contextCode s) c')
    (hd : interpretation (contextCode s) d = interpretation (contextCode s) d') : out = out' := by
  obtain ⟨hi, w, hw, he⟩ := operation_witness tag s c d out ho
  obtain ⟨hi', w', hw', he'⟩ := operation_witness tag s c' d' out' ho'
  have hs := publicOperation_spec tag s c d w hi hw
  have hs' := publicOperation_spec tag s c' d' w' hi' hw'
  have hv := resultSpec_unique tag _ _ _ _ hs.2.2 (by rw [hc, hd]; exact hs'.2.2)
  have hww := Canonical.check_value_injective w w' hs.1 hs'.1 hv
  exact he.trans ((congrArg (returnCode s) hww).trans he'.symm)

/-- The sixth producer uses only proved finite PR operations. -/
def omegaCode (s c : Nat) : Nat := returnCode s (OmegaPowers.powerCode (publicCode s c))

theorem omegaCode_primrec : Primrec₂ omegaCode :=
  (returnCode_primrec.comp Primrec.fst (OmegaPowers.powerCode_primrec.comp publicCode_primrec)).to₂

theorem omegaCode_spec (s c : Nat) (hc : lowInput s c = true) :
    lowInput s (omegaCode s c) = true ∧ Comparison.acceptedCode (contextCode s) (omegaCode s c) = true ∧
      interpretation (contextCode s) (omegaCode s c) = Ordinal.omega0 ^ interpretation (contextCode s) c := by
  have hu := publicCode_spec s c hc
  have hb := omegaPower_strictMono (hu.2.symm ▸ lowInput_bound s c hc)
  rw [finiteBase_succ_omegaPower_eq_self (s + 1)] at hb
  have hv := OmegaPowers.powerCode_value _ hu.1
  have hr := returnCode_spec s _ (OmegaPowers.powerCode_checked _ hu.1) (hv.symm ▸ hb)
  exact ⟨hr.1, hr.2.1, hr.2.2.trans (by simpa only [hu.2] using hv)⟩

theorem operation_omegaCode (s c d : Nat) : operation 5 s c d = cond (lowInput s c) (Part.some (omegaCode s c)) Part.none := by
  simp [operation, input, publicOperation, omegaCode]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowArithmetic
