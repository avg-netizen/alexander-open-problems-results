import Alexander313.Wilken.HereditaryNativeOmegaPowerHeightSupport

/-!
# Genuine native omega-power height and finite-tail power execution

The real existing omegaCode producer returns LOW Normal output. Its actual
omega-power value stays below the input's literal height endpoint, including
index zero because that endpoint is the original epsilon base. Therefore its
written output height is at most the canonical input height. Real finite-tail
addition followed by this real producer gives the same bound for omega^(xi+n).
These are the exact arithmetic height primitives for the future mu exponent;
mu's original coefficient/iota construction and its comparison with lambda
are separate. No height, output, representation or endpoint oracle is used.
Omega execution here retains its original positive public contextCode s scope;
finite-tail addition in the support works at every coded epsilon. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowerHeight

open NativePublicBridge (contextCode contextCode_checked)

theorem omegaCode_canonical_height (s c : Nat) (hc : LowArithmetic.lowInput s c = true) :
    CanonicalHeight.canonicalHeightCode (contextCode s) (LowArithmetic.omegaCode s c) ≤
      CanonicalHeight.canonicalHeightCode (contextCode s) c := by
  have hs := LowArithmetic.omegaCode_spec s c hc
  apply (HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s) _ _ hs.1).mpr
  rw [hs.2.2]
  exact (omegaPower_strictMono
    ((HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s) _ c hc).mp le_rfl)).trans_eq
      (endpoint_epsilon_all (contextCode s) _ (contextCode_checked s))

/-- No max-one correction is necessary: the genuine original epsilon
base proves the exact output bound even for canonical input height zero. -/
theorem omegaCode_height (s c : Nat) (hc : LowArithmetic.lowInput s c = true) :
    heightCode (LowArithmetic.omegaCode s c) ≤ CanonicalHeight.canonicalHeightCode (contextCode s) c := by
  rw [← CanonicalHeight.canonicalHeightCode_normal (contextCode s) _
    (LowArithmetic.omegaCode_spec s c hc).2.1]
  exact omegaCode_canonical_height s c hc

theorem omegaCode_normal_height (s c : Nat) (hc : LowArithmetic.lowInput s c = true)
    (hn : Comparison.Normal (contextCode s) (ThetaCourse.rawTree c)) :
    heightCode (LowArithmetic.omegaCode s c) ≤ heightCode c := by
  have hi := HeightBoundary.input_spec (contextCode s) c hc
  have ha := (Comparison.acceptedCode_exact _ _).mpr ⟨hi.1, hn⟩
  simpa only [CanonicalHeight.canonicalHeightCode_normal _ _ ha] using omegaCode_height s c hc

theorem omegaCode_raw_height (s c : Nat) (hc : LowArithmetic.lowInput s c = true) :
    heightCode (LowArithmetic.omegaCode s c) ≤ heightCode c :=
  (omegaCode_height s c hc).trans (CanonicalHeight.canonicalHeightCode_le_raw _ _
    (HeightBoundary.input_spec (contextCode s) c hc).1)

/-- The genuine sixth Partrec operation executes exactly this output,
so every ORIGINAL numerical graph row inherits the proved height bound. -/
theorem operation_omega_height (s c d out : Nat) (ho : out ∈ LowArithmetic.operation 5 s c d) :
    heightCode out ≤ CanonicalHeight.canonicalHeightCode (contextCode s) c := by
  have hc := LowArithmetic.input_left 5 s c d (LowArithmetic.operation_spec 5 s c d out ho).1
  have he : out = LowArithmetic.omegaCode s c := by
    simpa only [LowArithmetic.operation_omegaCode, hc, Bool.cond_true, Part.mem_some_iff] using ho
  rw [he]
  exact omegaCode_height s c hc

def finiteTailPowerCode (s c n : Nat) : Nat :=
  LowArithmetic.omegaCode s (finiteTailCode (contextCode s) c n)

theorem finiteTailPowerCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => finiteTailPowerCode p.1.1 p.1.2 p.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have ht := finiteTailCode_primrec.comp
    (((NativePublicBridge.contextCode_primrec.comp hs).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact LowArithmetic.omegaCode_primrec.comp hs ht

/-- The actual PR finite-tail/power producer returns its literal value
omega^(xi+n), LOW and Normal, within the ORIGINAL canonical input height. -/
theorem finiteTailPowerCode_spec (s c n : Nat) (hc : LowArithmetic.lowInput s c = true) :
    LowArithmetic.lowInput s (finiteTailPowerCode s c n) = true ∧
      Comparison.acceptedCode (contextCode s) (finiteTailPowerCode s c n) = true ∧
      interpretation (contextCode s) (finiteTailPowerCode s c n) =
        Ordinal.omega0 ^ (interpretation (contextCode s) c + (n : Ordinal.{0})) ∧
      heightCode (finiteTailPowerCode s c n) ≤ CanonicalHeight.canonicalHeightCode (contextCode s) c := by
  have ht := finiteTailCode_spec (contextCode s) c n hc
  have hs := LowArithmetic.omegaCode_spec s _ ht.1
  refine ⟨hs.1, hs.2.1, ?_, ?_⟩
  · simpa only [finiteTailPowerCode, ht.2.2.1] using hs.2.2
  · have hh := omegaCode_height s (finiteTailCode (contextCode s) c n) ht.1
    rw [CanonicalHeight.canonicalHeightCode_normal _ _ ht.2.1] at hh
    exact hh.trans ht.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowerHeight
