import Alexander313.Wilken.HereditaryLogEnd
import Alexander313.Wilken.HereditaryFinePredecessor

/-!
# A finite full-public decision for zero last exponent

The source last CNF exponent is zero exactly at zero or when the actual last
ANF component is one. The real checked weak-normal public ANF supplies that
component even above the low union domain. Original admission is retained;
the unit comparison and all finite kernels are genuinely primitive recursive.
The raw adapter executes the actual value-preserving normalizer. Only the
low-union corollary refers to the previously constructed Partrec logarithm.
No log-search bound, supplied logend decision or higher-sort union encoding
is assumed. All source proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.LogEndZero

/-- The zero-last-exponent condition on the actual ordinal ANF. -/
noncomputable def SourceZero (xi : Ordinal.{0}) : Prop :=
  xi = 0 ∨ LogEnd.endValue xi = 1

theorem sourceLogSpec_zero_iff (xi eta : Ordinal.{0})
    (hs : LogEnd.SourceLogSpec true xi eta) : eta = 0 ↔ SourceZero xi := by
  by_cases hz : xi = 0
  · have he : eta = 0 := by simpa only [LogEnd.SourceLogSpec, if_pos hz] using hs
    exact ⟨fun _ => Or.inl hz, fun _ => he⟩
  · have he : Ordinal.omega0 ^ eta = LogEnd.endValue xi := by
      simpa only [LogEnd.SourceLogSpec, if_neg hz, LogEnd.endValue] using hs
    constructor
    · intro h
      right
      simpa only [h, Ordinal.opow_zero] using he.symm
    · intro h
      have hu : LogEnd.endValue xi = 1 := h.resolve_left hz
      apply omegaPower_strictMono.injective
      exact he.trans (hu.trans (Ordinal.opow_zero Ordinal.omega0).symm)

def publicEndAtom (r c : Nat) : RelativeTerm Nat :=
  ((SourceDecomposition.word r c).reverse[0]?).getD (zeroTree r)

theorem publicEndAtom_primrec : Primrec₂ publicEndAtom :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (Primrec.list_reverse.comp SourceDecomposition.word_primrec) (Primrec.const 0))
    (Theta.Normalization.Effective.zeroTree_primrec.comp Primrec.fst)).to₂

private theorem first_map {alpha : Type} (f : alpha → Ordinal.{0})
    (as : List alpha) (z : alpha) :
    f (as[0]?.getD z) = (as.map f)[0]?.getD (f z) := by
  cases as <;> rfl

theorem publicEndAtom_value (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    denote r (publicEndAtom r c) = LogEnd.endValue (interpretation r c) := by
  rw [publicEndAtom, first_map, zeroTree_denote, List.map_reverse,
    (SourceDecomposition.word_spec r c hc).2]
  rfl

theorem publicEndAtom_checked (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    check r (publicEndAtom r c) = true ∧ Theta.Normal r (publicEndAtom r c) := by
  cases hw : (SourceDecomposition.word r c).reverse with
  | nil =>
    have hz := Theta.Normalization.zeroTree_admissible r 0
    simpa only [publicEndAtom, hw, List.getElem?_nil, Option.getD_none] using
      And.intro (Theta.admitted_checked hz) (Theta.Normalization.zeroTree_normal r)
  | cons a as =>
    have ha : a ∈ SourceDecomposition.word r c := by
      have h : a ∈ (SourceDecomposition.word r c).reverse := by rw [hw]; exact List.mem_cons_self
      simpa only [List.mem_reverse] using h
    have hs := (SourceDecomposition.word_spec r c hc).1 a ha
    simpa only [publicEndAtom, hw, List.getElem?_cons_zero, Option.getD_some] using
      And.intro hs.1 hs.2.1

def publicEndCode (r c : Nat) : Nat := (publicEndAtom r c).code

theorem publicEndCode_primrec : Primrec₂ publicEndCode :=
  (code_primrec.comp publicEndAtom_primrec).to₂

theorem publicEndCode_accepted (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    SourceDecomposition.inputCheck r (publicEndCode r c) = true := by
  have hs := publicEndAtom_checked r c hc
  apply (SourceDecomposition.inputCheck_exact r _).mpr
  refine ⟨(checkCode_iff r _).mpr ⟨publicEndAtom r c, rfl, hs.1⟩, ?_⟩
  simpa only [publicEndCode, ThetaCourse.rawTree_code] using hs.2

theorem publicEndCode_value (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    interpretation r (publicEndCode r c) = LogEnd.endValue (interpretation r c) := by
  simpa only [publicEndCode, interpretation_code] using publicEndAtom_value r c hc

theorem publicEndCode_unit_iff (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    SourceFixedPoint.equalCode r (publicEndCode r c) (FinePredecessor.unitCode r) = true ↔
      LogEnd.endValue (interpretation r c) = 1 := by
  have he := SourceFixedPoint.equalCode_exact r (publicEndCode r c) (FinePredecessor.unitCode r)
  have hs := (SourceDecomposition.inputCheck_exact r _).mp (publicEndCode_accepted r c hc)
  have hu := (SourceDecomposition.inputCheck_exact r _).mp (FinePredecessor.unitCode_spec r).1
  simpa only [hs.1, hs.2, hu.1, hu.2, publicEndCode_value r c hc,
    (FinePredecessor.unitCode_spec r).2, true_and] using he

def publicZeroCheck (r c : Nat) : Bool := SourceDecomposition.inputCheck r c &&
  (SourceFixedPoint.zeroCheck r c ||
    SourceFixedPoint.equalCode r (publicEndCode r c) (FinePredecessor.unitCode r))

theorem publicZeroCheck_primrec : Primrec₂ publicZeroCheck :=
  (Primrec.and.comp SourceDecomposition.inputCheck_primrec
    (Primrec.or.comp SourceFixedPoint.zeroCheck_primrec
      (SourceFixedPoint.equalCode_primrec.comp (Primrec.fst.pair
        (publicEndCode_primrec.pair (FinePredecessor.unitCode_primrec.comp Primrec.fst)))))).to₂

theorem publicZeroCheck_exact (r c : Nat) : publicZeroCheck r c = true ↔
    SourceDecomposition.inputCheck r c = true ∧ SourceZero (interpretation r c) := by
  rw [publicZeroCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, by simpa only [Bool.or_eq_true, SourceFixedPoint.zeroCheck_exact r c hc,
      publicEndCode_unit_iff r c hc, SourceZero] using h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, by simpa only [Bool.or_eq_true, SourceFixedPoint.zeroCheck_exact r c hc,
      publicEndCode_unit_iff r c hc, SourceZero] using h⟩

theorem publicZeroCheck_source (r c : Nat) : publicZeroCheck r c = true ↔
    checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) ∧
      SourceZero (interpretation r c) := by
  rw [publicZeroCheck_exact, SourceDecomposition.inputCheck_exact, and_assoc]

theorem publicZeroCheck_correct (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    publicZeroCheck r c = true ↔ interpretation r c = 0 ∨ LogEnd.endValue (interpretation r c) = 1 := by
  simpa only [publicZeroCheck_exact, hc, true_and, SourceZero]

theorem publicZeroCheck_exponent (r c : Nat) (hc : SourceDecomposition.inputCheck r c = true)
    (eta : Ordinal.{0}) (hs : LogEnd.SourceLogSpec true (interpretation r c) eta) :
    publicZeroCheck r c = true ↔ eta = 0 := by
  rw [publicZeroCheck_exact]
  exact ⟨fun h => (sourceLogSpec_zero_iff _ _ hs).mpr h.2,
    fun h => ⟨hc, (sourceLogSpec_zero_iff _ _ hs).mp h⟩⟩

theorem publicZeroCheck_invariant (r c s d : Nat)
    (hc : SourceDecomposition.inputCheck r c = true)
    (hd : SourceDecomposition.inputCheck s d = true)
    (he : interpretation r c = interpretation s d) :
    publicZeroCheck r c = publicZeroCheck s d := by
  have h : publicZeroCheck r c = true ↔ publicZeroCheck s d = true := by
    simp only [publicZeroCheck_exact, hc, hd, true_and, he]
  cases hleft : publicZeroCheck r c <;> cases hright : publicZeroCheck s d <;> simp_all

def rawZeroCheck (r c : Nat) : Bool := checkCode r c &&
  publicZeroCheck r (Theta.Normalization.normalizeCode r c)

theorem rawZeroCheck_primrec : Primrec₂ rawZeroCheck :=
  (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (publicZeroCheck_primrec.comp Primrec.fst Theta.Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawZeroCheck_exact (r c : Nat) : rawZeroCheck r c = true ↔
    checkCode r c = true ∧ SourceZero (interpretation r c) := by
  rw [rawZeroCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, h⟩
    have hn := Theta.Normalization.normalizeCode_accepted r c hc
    have hs := (publicZeroCheck_exact r _).mp h
    exact ⟨hc, by simpa only [hn.2] using hs.2⟩
  · rintro ⟨hc, h⟩
    have hn := Theta.Normalization.normalizeCode_accepted r c hc
    exact ⟨hc, (publicZeroCheck_exact r _).mpr ⟨hn.1, by simpa only [hn.2] using h⟩⟩

theorem rawZeroCheck_invariant (r c s d : Nat)
    (hc : checkCode r c = true) (hd : checkCode s d = true)
    (he : interpretation r c = interpretation s d) : rawZeroCheck r c = rawZeroCheck s d := by
  have h : rawZeroCheck r c = true ↔ rawZeroCheck s d = true := by
    simp only [rawZeroCheck_exact, hc, hd, true_and, he]
  cases hleft : rawZeroCheck r c <;> cases hright : rawZeroCheck s d <;> simp_all

def unionZeroCheck (q : Nat) : Bool := unionCheck q && rawZeroCheck q.unpair.1 q.unpair.2

theorem unionZeroCheck_primrec : Primrec unionZeroCheck :=
  Primrec.and.comp Uniform.unionCheck_primrec
    (rawZeroCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

theorem unionZeroCheck_exact (q : Nat) : unionZeroCheck q = true ↔
    unionCheck q = true ∧ SourceZero (unionInterpretation q) := by
  rw [unionZeroCheck, Bool.and_eq_true, rawZeroCheck_exact]
  constructor
  · rintro ⟨hq, hc, hs⟩
    exact ⟨hq, hs⟩
  · rintro ⟨hq, hs⟩
    have hc : checkCode q.unpair.1 q.unpair.2 = true :=
      (Bool.and_eq_true.mp (by simpa only [unionCheck, lowCheckCode_eq] using hq)).1
    exact ⟨hq, hc, hs⟩

theorem unionZeroCheck_logend (q output : Nat) (ho : output ∈ LogEnd.logend q) :
    unionZeroCheck q = true ↔ unionInterpretation output = 0 := by
  have hs := LogEnd.logend_value q output ho
  rw [unionZeroCheck_exact]
  exact ⟨fun h => (sourceLogSpec_zero_iff _ _ hs.2.2).mpr h.2,
    fun h => ⟨hs.1, (sourceLogSpec_zero_iff _ _ hs.2.2).mp h⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.LogEndZero
