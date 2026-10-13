import Alexander313.Wilken.HereditaryNativePublicReturn

/-!
# Executing native zeta at the same positive public epsilon

Original native literal theta-zero inputs at contextCode s are returned by
the genuine parameter canonicalization/embedding/lowering kernel to public
level s+1. The real public zeta producer uses the STRICT residual supremum
of Definition 2.42. Its proved value below the original root, and that root's
actual low public bound, supply every output conversion caller. The low
public result is translated back into the SAME original native context.

Normal and raw inputs retain their original native admission guards. The raw
route publicly normalizes the actual returned term; no equality between
independently executed native/public normalizers is assumed. Actual argument
values identify the source div/mod and supremum formula. A genuine executed
native-to-public-to-canonical round trip proves a complete PR numerical graph.
No arbitrary-native-base conversion or supplied recoder/termination oracle
is claimed. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceZeta

open NativePublicBridge (contextCode contextCode_value contextCode_checked)
open scoped Classical

def inputCheck (s c : Nat) : Bool := Comparison.acceptedCode (contextCode s) c && Localization.rootShape c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (Comparison.acceptedCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd)
    (Localization.rootShape_primrec.comp Primrec.snd)).to₂

def rawInputCheck (s c : Nat) : Bool := checkCode (contextCode s) c && Localization.rootShape c

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck :=
  (Primrec.and.comp (checkCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd)
    (Localization.rootShape_primrec.comp Primrec.snd)).to₂

theorem rawInputCheck_exact (s c : Nat) : rawInputCheck s c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check (contextCode s) (.theta 0 a) = true := by
  constructor
  · intro hc
    obtain ⟨ht, hs⟩ := Bool.and_eq_true.mp hc
    obtain ⟨t, he, ha⟩ := (checkCode_exact _ c).mp ht
    obtain ⟨a, hta⟩ := (Localization.rootShape_code t).mp (by simpa only [← he] using hs)
    subst t
    exact ⟨a, he.symm, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact Bool.and_eq_true.mpr ⟨by simpa only [checkCode_code] using ha,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩

theorem inputCheck_exact (s c : Nat) : inputCheck s c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check (contextCode s) (.theta 0 a) = true ∧
      Comparison.Normal (contextCode s) (.theta 0 a) := by
  constructor
  · intro hc
    obtain ⟨ht, hs⟩ := Bool.and_eq_true.mp hc
    have hn := (Comparison.acceptedCode_exact _ c).mp ht
    obtain ⟨a, he, ha⟩ := (rawInputCheck_exact s c).mp (Bool.and_eq_true.mpr ⟨hn.1, hs⟩)
    exact ⟨a, he, ha, by simpa only [he, ThetaCourse.rawTree_code] using hn.2⟩
  · rintro ⟨a, rfl, ha, hn⟩
    exact Bool.and_eq_true.mpr ⟨(Comparison.acceptedCode_exact _ _).mpr
      ⟨by simpa only [checkCode_code] using ha, by simpa only [ThetaCourse.rawTree_code] using hn⟩,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩

theorem normal_raw_input (s c : Nat) (hc : inputCheck s c = true) : rawInputCheck s c = true := by
  obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact s c).mp hc
  exact (rawInputCheck_exact s _).mpr ⟨a, rfl, ha⟩

def publicCode (s c : Nat) : Nat := NativePublicReturn.returnedCode s c

theorem publicCode_primrec : Primrec₂ publicCode := NativePublicReturn.returnedCode_primrec

theorem publicCode_value (s c : Nat) (hc : rawInputCheck s c = true) :
    Hereditary.interpretation (s + 1) (publicCode s c) = interpretation (contextCode s) c :=
  (NativePublicReturn.returnedCode_checked_value s c (Bool.and_eq_true.mp hc).1).2

theorem public_raw_input (s c : Nat) (hc : rawInputCheck s c = true) :
    Hereditary.SourceZeta.rawInputCheck (s + 1) (publicCode s c) = true := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact s c).mp hc
  apply (Hereditary.SourceZeta.rawInputCheck_exact _ _).mpr
  exact ⟨NativePublicReturn.returnTerm s a, by
    simp only [publicCode, NativePublicReturn.returnedCode_code, NativePublicReturn.returnTerm_theta],
    NativePublicReturn.returnTerm_checked s (.theta 0 a) ha⟩

theorem public_normal_input (s c : Nat) (hc : inputCheck s c = true) :
    Hereditary.SourceZeta.inputCheck (s + 1) (publicCode s c) = true := by
  obtain ⟨a, rfl, ha, hn⟩ := (inputCheck_exact s c).mp hc
  apply (Hereditary.SourceZeta.inputCheck_exact _ _).mpr
  have hp := (NativeContext.checked_admissible _ (.theta 0 a) ha).1
  exact ⟨NativePublicReturn.returnTerm s a, by
    simp only [publicCode, NativePublicReturn.returnedCode_code, NativePublicReturn.returnTerm_theta],
    NativePublicReturn.returnTerm_checked s (.theta 0 a) ha,
    NativePublicReturn.returnTerm_normal s (.theta 0 a) hp hn⟩

def argumentCode (c : Nat) : Nat := Localization.argumentCode c

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem public_argument_value (s c : Nat) (hc : rawInputCheck s c = true) :
    Hereditary.interpretation (s + 1) (Hereditary.SourceZeta.argumentCode (publicCode s c)) =
      interpretation (contextCode s) (argumentCode c) := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact s c).mp hc
  have haa := FixedPoint.checked_theta_argument (contextCode s) 0 a ha
  have hv := (NativePublicReturn.returnedCode_checked_value s a.code
    (by simpa only [checkCode_code] using haa)).2
  simpa only [publicCode, NativePublicReturn.returnedCode_code, NativePublicReturn.returnTerm_theta,
    Hereditary.SourceZeta.argumentCode, argumentCode, Localization.argumentCode_theta] using hv

/-- Literal native Definition 2.42 at the original same epsilon base. -/
noncomputable def sourceValue (s c : Nat) : Ordinal.{0} :=
  if FixedPoint.SourceStrict (contextCode s) 0 (argumentCode c) then
    Hereditary.SourceZeta.lastExponent (FixedPoint.residual (contextCode s) 0 (argumentCode c)) else 0

theorem sourceValue_public (s c : Nat) (hc : rawInputCheck s c = true) :
    Hereditary.SourceZeta.sourceValue (s + 1) (publicCode s c) = sourceValue s c := by
  simp only [Hereditary.SourceZeta.sourceValue, sourceValue,
    Hereditary.SourceFixedPoint.SourceStrict, Hereditary.SourceFixedPoint.delta,
    Hereditary.SourceFixedPoint.residual, FixedPoint.SourceStrict, FixedPoint.delta,
    FixedPoint.residual, contextCode_value, public_argument_value s c hc]

/-- The original native fixed-point routine itself recognizes the same
STRICT source relation; the constructor supplies its real admission/sort. -/
def strictCheck (s c : Nat) : Bool := FixedPoint.strictCode (contextCode s) 0 (argumentCode c)

theorem strictCheck_primrec : Primrec₂ strictCheck :=
  (FixedPoint.strictCode_primrec.comp
    ((NativePublicBridge.contextCode_primrec.comp Primrec.fst).pair
      ((Primrec.const 0).pair (argumentCode_primrec.comp Primrec.snd)))).to₂

theorem strictCheck_exact (s c : Nat) (hc : inputCheck s c = true) :
    strictCheck s c = true ↔ FixedPoint.SourceStrict (contextCode s) 0 (argumentCode c) := by
  obtain ⟨a, rfl, ha, hn⟩ := (inputCheck_exact s c).mp hc
  have hi := SourceChi.theta_argument_input (contextCode s) 0 a ha hn
  simpa only [strictCheck, argumentCode, Localization.argumentCode_theta] using
    FixedPoint.strictCode_correct (contextCode s) 0 a.code hi

theorem strictCheck_public (s c : Nat) (hc : inputCheck s c = true) :
    strictCheck s c = Hereditary.SourceZeta.strictCheck (s + 1) (publicCode s c) := by
  apply Bool.eq_iff_iff.mpr
  rw [strictCheck_exact s c hc,
    Hereditary.SourceZeta.strictCheck_exact (s + 1) _ (public_normal_input s c hc)]
  simp only [FixedPoint.SourceStrict, FixedPoint.delta, FixedPoint.residual,
    Hereditary.SourceFixedPoint.SourceStrict, Hereditary.SourceFixedPoint.delta,
    Hereditary.SourceFixedPoint.residual, contextCode_value,
    public_argument_value s c (normal_raw_input s c hc)]

/-- The output conversion is a genuine total finite kernel. Correctness
uses an actual canonical low union code with a derived strict caller bound. -/
def emit (s q : Nat) : Nat := NativePublicBridge.translateCode s
  (Hereditary.SourceZeta.Transport.returnCode (s + 1) q)

theorem emit_primrec : Primrec₂ emit :=
  (NativePublicBridge.translateCode_primrec.comp Primrec.fst
    (Hereditary.SourceZeta.Transport.returnCode_primrec.comp
      (Primrec.succ.comp Primrec.fst) Primrec.snd)).to₂

theorem translate_low (s c : Nat) (hc : Hereditary.lowCheckCode (s + 1) c = true) :
    lowCheckCode (contextCode s) (NativePublicBridge.translateCode s c) = true := by
  have ht : Hereditary.checkCode (s + 1) c = true :=
    (Bool.and_eq_true.mp (by simpa only [Hereditary.lowCheckCode_eq] using hc)).1
  obtain ⟨t, rfl, ha⟩ := (Hereditary.checkCode_iff (s + 1) c).mp ht
  have hl : Hereditary.lowCheck (s + 1) t = true := by simpa only [Hereditary.lowCheckCode_code] using hc
  simpa only [NativePublicBridge.translateCode_code, lowCheckCode_code, lowCheck,
    Hereditary.lowCheck, NativePublicBridge.translate_check, NativePublicBridge.translate_outerSort] using hl

theorem emit_spec (s q : Nat) (hq : Canonical.check q = true)
    (hb : unionInterpretation q < finiteBase (s + 2)) :
    Comparison.acceptedCode (contextCode s) (emit s q) = true ∧
      lowCheckCode (contextCode s) (emit s q) = true ∧
      interpretation (contextCode s) (emit s q) = unionInterpretation q := by
  have hp := Hereditary.SourceZeta.Transport.returnCode_spec (s + 1) q hq (by simpa only [Nat.add_assoc] using hb)
  have hl := (Theta.acceptedLowCode_iff (s + 1) _).mp hp.1
  have hi : Hereditary.SourceDecomposition.inputCheck (s + 1)
      (Hereditary.SourceZeta.Transport.returnCode (s + 1) q) = true :=
    (Hereditary.SourceDecomposition.inputCheck_exact _ _).mpr
      ⟨(Bool.and_eq_true.mp (by simpa only [Hereditary.lowCheckCode_eq] using hl.1)).1, hl.2⟩
  exact ⟨NativePublicBridge.translateCode_accepted s _ hi, translate_low s _ hl.1,
    (NativePublicBridge.translateCode_value s _).trans hp.2⟩

def zeta (s c : Nat) : Part Nat := cond (inputCheck s c)
  ((Hereditary.SourceZeta.zeta (s + 1) (publicCode s c)).map (emit s)) Part.none

theorem zeta_partrec : Partrec₂ zeta := by
  have hp := Hereditary.SourceZeta.zeta_partrec.comp
    (Primrec.succ.comp Primrec.fst).to_comp publicCode_primrec.to_comp
  have he := (emit_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact (Partrec.cond inputCheck_primrec.to_comp (Partrec.map hp he) Partrec.none).to₂

theorem zeta_domain (s c : Nat) : (zeta s c).Dom ↔ inputCheck s c = true := by
  cases hc : inputCheck s c with
  | false => simp only [zeta, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [zeta, hc, Bool.cond_true, Part.map, Hereditary.SourceZeta.zeta_domain,
      public_normal_input s c hc]

def rawZeta (s c : Nat) : Part Nat := cond (rawInputCheck s c)
  ((Hereditary.SourceZeta.rawZeta (s + 1) (publicCode s c)).map (emit s)) Part.none

theorem rawZeta_partrec : Partrec₂ rawZeta := by
  have hp := Hereditary.SourceZeta.rawZeta_partrec.comp
    (Primrec.succ.comp Primrec.fst).to_comp publicCode_primrec.to_comp
  have he := (emit_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact (Partrec.cond rawInputCheck_primrec.to_comp (Partrec.map hp he) Partrec.none).to₂

theorem rawZeta_domain (s c : Nat) : (rawZeta s c).Dom ↔ rawInputCheck s c = true := by
  cases hc : rawInputCheck s c with
  | false => simp only [rawZeta, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [rawZeta, hc, Bool.cond_true, Part.map, Hereditary.SourceZeta.rawZeta_domain,
      public_raw_input s c hc]

theorem zeta_spec (s c d : Nat) (hd : d ∈ zeta s c) :
    inputCheck s c = true ∧ Comparison.acceptedCode (contextCode s) d = true ∧
      lowCheckCode (contextCode s) d = true ∧ interpretation (contextCode s) d = sourceValue s c ∧
      interpretation (contextCode s) d < interpretation (contextCode s) c := by
  have hc := (zeta_domain s c).mp (Part.dom_iff_mem.mpr ⟨d, hd⟩)
  have hm : d ∈ (Hereditary.SourceZeta.zeta (s + 1) (publicCode s c)).map (emit s) :=
    by simpa only [zeta, hc, Bool.cond_true] using hd
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hm
  have hp := Hereditary.SourceZeta.zeta_value (s + 1) _ q hq
  have hb := Hereditary.SourceZeta.Transport.zeta_return_bound (s + 1) _ q hq
  have he := emit_spec s q hp.2.1 (by simpa only [Nat.add_assoc] using hb)
  have hv := publicCode_value s c (normal_raw_input s c hc)
  exact ⟨hc, he.1, he.2.1, he.2.2.trans (hp.2.2.trans
    (sourceValue_public s c (normal_raw_input s c hc))),
    he.2.2.trans_lt ((Hereditary.SourceZeta.zeta_bound (s + 1) _ q hq).trans_eq hv)⟩

theorem rawZeta_spec (s c d : Nat) (hd : d ∈ rawZeta s c) :
    rawInputCheck s c = true ∧ Comparison.acceptedCode (contextCode s) d = true ∧
      lowCheckCode (contextCode s) d = true ∧ interpretation (contextCode s) d = sourceValue s c ∧
      interpretation (contextCode s) d < interpretation (contextCode s) c := by
  have hc := (rawZeta_domain s c).mp (Part.dom_iff_mem.mpr ⟨d, hd⟩)
  have hm : d ∈ (Hereditary.SourceZeta.rawZeta (s + 1) (publicCode s c)).map (emit s) :=
    by simpa only [rawZeta, hc, Bool.cond_true] using hd
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hm
  have hp := Hereditary.SourceZeta.rawZeta_value (s + 1) _ q hq
  have hb := Hereditary.SourceZeta.Transport.rawZeta_return_bound (s + 1) _ q hq
  have he := emit_spec s q hp.2.1 (by simpa only [Nat.add_assoc] using hb)
  exact ⟨hc, he.1, he.2.1, he.2.2.trans (hp.2.2.trans (sourceValue_public s c hc)),
    he.2.2.trans_lt ((Hereditary.SourceZeta.rawZeta_bound (s + 1) _ q hq).trans_eq (publicCode_value s c hc))⟩

theorem zeta_returns (s c : Nat) (hc : inputCheck s c = true) : ∃ d, d ∈ zeta s c :=
  Part.dom_iff_mem.mp ((zeta_domain s c).mpr hc)

theorem rawZeta_returns (s c : Nat) (hc : rawInputCheck s c = true) : ∃ d, d ∈ rawZeta s c :=
  Part.dom_iff_mem.mp ((rawZeta_domain s c).mpr hc)

/-- Zero residual uses the actual empty ordinary supremum, retaining the
base case instead of replacing the strict test by a higher-part negation. -/
theorem zeta_zero_residual (s c : Nat) (hc : inputCheck s c = true)
    (hz : FixedPoint.residual (contextCode s) 0 (argumentCode c) = 0) :
    zeta s c = Part.some (emit s LogEnd.zeroCode) := by
  have hp : Hereditary.SourceFixedPoint.residual (s + 1) 0
      (Hereditary.SourceZeta.argumentCode (publicCode s c)) = 0 := by
    simpa only [Hereditary.SourceFixedPoint.residual, FixedPoint.residual, contextCode_value,
      public_argument_value s c (normal_raw_input s c hc)] using hz
  simp only [zeta, hc, Bool.cond_true,
    Hereditary.SourceZeta.zeta_zero_residual (s + 1) _ (public_normal_input s c hc) hp, Part.map_some]

/-- A finite inverse certificate is computed from the ORIGINAL native low
output, using the actual proved native return and public canonicalization. -/
def canonicalOutput (s d : Nat) : Nat := Hereditary.SourceZeta.Transport.canonicalOutput (s + 1)
  (NativePublicReturn.returnedCode s d)

theorem canonicalOutput_primrec : Primrec₂ canonicalOutput :=
  (Hereditary.SourceZeta.Transport.canonicalOutput_primrec.comp
    (Primrec.succ.comp Primrec.fst) NativePublicReturn.returnedCode_primrec).to₂

theorem canonicalOutput_spec (s d : Nat)
    (hd : Comparison.acceptedCode (contextCode s) d = true)
    (hl : lowCheckCode (contextCode s) d = true) :
    Canonical.check (canonicalOutput s d) = true ∧
      unionInterpretation (canonicalOutput s d) = interpretation (contextCode s) d := by
  have hp := NativePublicReturn.returnedCode_normal_low_spec s d hd hl
  have hc := Hereditary.SourceZeta.Transport.canonicalOutput_spec (s + 1) _ hp.1
  exact ⟨hc.1, hc.2.trans hp.2⟩

theorem canonicalOutput_emit (s q : Nat) (hq : Canonical.check q = true)
    (hb : unionInterpretation q < finiteBase (s + 2)) : canonicalOutput s (emit s q) = q := by
  have he := emit_spec s q hq hb
  have hc := canonicalOutput_spec s _ he.1 he.2.1
  exact Canonical.check_value_injective _ _ hc.1 hq (hc.2.trans he.2.2)

def graph (s c d : Nat) : Bool := inputCheck s c &&
  (Comparison.acceptedCode (contextCode s) d && (lowCheckCode (contextCode s) d &&
    ((d == emit s (canonicalOutput s d)) &&
      Hereditary.SourceZeta.graph (s + 1) (publicCode s c) (canonicalOutput s d))))

theorem graph_primrec : Primrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) := by
  have hs := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have hb := NativePublicBridge.contextCode_primrec.comp hs
  have hq := canonicalOutput_primrec.comp hs hd
  exact Primrec.and.comp (inputCheck_primrec.comp hs hc)
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp hb hd)
      (Primrec.and.comp (lowCheckCode_primrec.comp hb hd)
        (Primrec.and.comp (Primrec.beq.comp hd (emit_primrec.comp hs hq))
          (Hereditary.SourceZeta.graph_primrec.comp
            ((Primrec.succ.comp hs).pair ((publicCode_primrec.comp hs hc).pair hq))))))

theorem zeta_graph_iff (s c d : Nat) : d ∈ zeta s c ↔ graph s c d = true := by
  constructor
  · intro hd
    have hs := zeta_spec s c d hd
    have hm : d ∈ (Hereditary.SourceZeta.zeta (s + 1) (publicCode s c)).map (emit s) :=
      by simpa only [zeta, hs.1, Bool.cond_true] using hd
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hm
    have hp := Hereditary.SourceZeta.zeta_value (s + 1) _ q hq
    have hb := Hereditary.SourceZeta.Transport.zeta_return_bound (s + 1) _ q hq
    have he := canonicalOutput_emit s q hp.2.1 (by simpa only [Nat.add_assoc] using hb)
    simp only [graph, hs.1, hs.2.1, hs.2.2.1, he, beq_self_eq_true, Bool.true_and]
    exact (Hereditary.SourceZeta.zeta_graph_iff (s + 1) _ q).mp hq
  · intro hg
    obtain ⟨hc, _, _, he, hq⟩ := (by
      simpa only [graph, Bool.and_eq_true, beq_iff_eq] using hg :
      inputCheck s c = true ∧ Comparison.acceptedCode (contextCode s) d = true ∧
        lowCheckCode (contextCode s) d = true ∧ d = emit s (canonicalOutput s d) ∧
        Hereditary.SourceZeta.graph (s + 1) (publicCode s c) (canonicalOutput s d) = true)
    simp only [zeta, hc, Bool.cond_true]
    exact (Part.mem_map_iff (emit s)).mpr
      ⟨canonicalOutput s d, (Hereditary.SourceZeta.zeta_graph_iff (s + 1) _ _).mpr hq, he.symm⟩

def rawGraph (s c d : Nat) : Bool := rawInputCheck s c &&
  (Comparison.acceptedCode (contextCode s) d && (lowCheckCode (contextCode s) d &&
    ((d == emit s (canonicalOutput s d)) &&
      Hereditary.SourceZeta.rawGraph (s + 1) (publicCode s c) (canonicalOutput s d))))

theorem rawGraph_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawGraph p.1 p.2.1 p.2.2) := by
  have hs := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have hb := NativePublicBridge.contextCode_primrec.comp hs
  have hq := canonicalOutput_primrec.comp hs hd
  exact Primrec.and.comp (rawInputCheck_primrec.comp hs hc)
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp hb hd)
      (Primrec.and.comp (lowCheckCode_primrec.comp hb hd)
        (Primrec.and.comp (Primrec.beq.comp hd (emit_primrec.comp hs hq))
          (Hereditary.SourceZeta.rawGraph_primrec.comp
            ((Primrec.succ.comp hs).pair ((publicCode_primrec.comp hs hc).pair hq))))))

theorem rawZeta_graph_iff (s c d : Nat) : d ∈ rawZeta s c ↔ rawGraph s c d = true := by
  constructor
  · intro hd
    have hs := rawZeta_spec s c d hd
    have hm : d ∈ (Hereditary.SourceZeta.rawZeta (s + 1) (publicCode s c)).map (emit s) :=
      by simpa only [rawZeta, hs.1, Bool.cond_true] using hd
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hm
    have hp := Hereditary.SourceZeta.rawZeta_value (s + 1) _ q hq
    have hb := Hereditary.SourceZeta.Transport.rawZeta_return_bound (s + 1) _ q hq
    have he := canonicalOutput_emit s q hp.2.1 (by simpa only [Nat.add_assoc] using hb)
    simp only [rawGraph, hs.1, hs.2.1, hs.2.2.1, he, beq_self_eq_true, Bool.true_and]
    exact (Hereditary.SourceZeta.rawZeta_graph_iff (s + 1) _ q).mp hq
  · intro hg
    obtain ⟨hc, _, _, he, hq⟩ := (by
      simpa only [rawGraph, Bool.and_eq_true, beq_iff_eq] using hg :
      rawInputCheck s c = true ∧ Comparison.acceptedCode (contextCode s) d = true ∧
        lowCheckCode (contextCode s) d = true ∧ d = emit s (canonicalOutput s d) ∧
        Hereditary.SourceZeta.rawGraph (s + 1) (publicCode s c) (canonicalOutput s d) = true)
    simp only [rawZeta, hc, Bool.cond_true]
    exact (Part.mem_map_iff (emit s)).mpr
      ⟨canonicalOutput s d, (Hereditary.SourceZeta.rawZeta_graph_iff (s + 1) _ _).mpr hq, he.symm⟩

theorem graph_unique (s c : Nat) (hc : inputCheck s c = true) : ∃! d, graph s c d = true := by
  obtain ⟨d, hd⟩ := zeta_returns s c hc
  exact ⟨d, (zeta_graph_iff s c d).mp hd, fun e he => Part.mem_unique ((zeta_graph_iff s c e).mpr he) hd⟩

theorem rawGraph_unique (s c : Nat) (hc : rawInputCheck s c = true) : ∃! d, rawGraph s c d = true := by
  obtain ⟨d, hd⟩ := rawZeta_returns s c hc
  exact ⟨d, (rawZeta_graph_iff s c d).mp hd, fun e he => Part.mem_unique ((rawZeta_graph_iff s c e).mpr he) hd⟩

theorem zeta_output_invariant (s c v d e : Nat) (hd : d ∈ zeta s c) (he : e ∈ zeta s v)
    (hv : interpretation (contextCode s) c = interpretation (contextCode s) v) : d = e := by
  have hc := (zeta_spec s c d hd).1
  have hvn := (zeta_spec s v e he).1
  have hdp : d ∈ (Hereditary.SourceZeta.zeta (s + 1) (publicCode s c)).map (emit s) :=
    by simpa only [zeta, hc, Bool.cond_true] using hd
  have hep : e ∈ (Hereditary.SourceZeta.zeta (s + 1) (publicCode s v)).map (emit s) :=
    by simpa only [zeta, hvn, Bool.cond_true] using he
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hdp
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff (emit s)).mp hep
  rw [Hereditary.SourceZeta.Transport.zeta_output_invariant (s + 1) _ _ q w hq hw
    ((publicCode_value s c (normal_raw_input s c hc)).trans
      (hv.trans (publicCode_value s v (normal_raw_input s v hvn)).symm))]

theorem rawZeta_output_invariant (s c v d e : Nat) (hd : d ∈ rawZeta s c) (he : e ∈ rawZeta s v)
    (hv : interpretation (contextCode s) c = interpretation (contextCode s) v) : d = e := by
  have hc := (rawZeta_spec s c d hd).1
  have hvn := (rawZeta_spec s v e he).1
  have hdp : d ∈ (Hereditary.SourceZeta.rawZeta (s + 1) (publicCode s c)).map (emit s) :=
    by simpa only [rawZeta, hc, Bool.cond_true] using hd
  have hep : e ∈ (Hereditary.SourceZeta.rawZeta (s + 1) (publicCode s v)).map (emit s) :=
    by simpa only [rawZeta, hvn, Bool.cond_true] using he
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (emit s)).mp hdp
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff (emit s)).mp hep
  rw [Hereditary.SourceZeta.Transport.rawZeta_output_invariant (s + 1) _ _ q w hq hw
    ((publicCode_value s c hc).trans (hv.trans (publicCode_value s v hvn).symm))]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceZeta
