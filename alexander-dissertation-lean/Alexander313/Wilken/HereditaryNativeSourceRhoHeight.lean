import Alexander313.Wilken.HereditaryNativeSourceRhoHeightSupport

/-!
# The full source rho height inequality on every original LOW input

For N=max(1, canonical input height), the actual source height criterion puts
the input below its literal endpoint. The real logarithm is at most that input
and rho is at most the base times that logarithm. Both factors lie strictly
below the proved epsilon endpoint, so rho does too. Its actual returned LOW
admission then gives canonical height at most N. Actual weak normality of the
rho output identifies this with its literal written height.

The source domain and positive public context contextCode s are unchanged.
Raw inputs use genuine normalization; original weak-Normal inputs have the
literal source Lemma 3.12 height statement. No operator, endpoint, height,
logarithm or closure premise is supplied. All candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho

open NativePublicBridge (contextCode contextCode_checked)

/-- Rho stays below every positive height endpoint above its input.
The original input and returned output admissions are derived by execution. -/
theorem rho_below_endpoint (s c out n : Nat) (ho : out ∈ rho s c) (hn : 0 < n)
    (hh : CanonicalHeight.canonicalHeightCode (contextCode s) c ≤ n) :
    interpretation (contextCode s) out < HeightBoundary.endpoint (contextCode s) n := by
  have hc : lowCheckCode (contextCode s) c = true := (rho_spec s c out ho).1
  have hi := (HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s) n c hc).mp hh
  obtain ⟨p, hp, hb⟩ := source_lemma_3_12_bound s c out ho
  have hl := (prepared_log_bound s c p hp).trans_lt hi
  exact hb.trans_lt (HeightBoundary.endpoint_mul_closed (contextCode s) n
    (contextCode_checked s) hn
    (HeightBoundary.base_lt_endpoint (contextCode s) n (contextCode_checked s) hn) hl)

/-- Source Lemma 3.12 on EVERY original source rho input, including raw
spellings and height zero. Canonical heights use actual normalization. -/
theorem source_lemma_3_12_height (s c out : Nat) (ho : out ∈ rho s c) :
    CanonicalHeight.canonicalHeightCode (contextCode s) out ≤
      max 1 (CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  have hlo : lowCheckCode (contextCode s) out = true := (rho_spec s c out ho).2.1
  apply (HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s) _ out hlo).mpr
  exact rho_below_endpoint s c out _ ho (by omega) (le_max_right _ _)

/-- The executing rho output is actually weak Normal, so its written
height satisfies the same canonical input-height inequality. -/
theorem rho_output_height (s c out : Nat) (ho : out ∈ rho s c) :
    heightCode out ≤ max 1 (CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [← CanonicalHeight.canonicalHeightCode_normal (contextCode s) out (rho_spec s c out ho).2.2.1]
  exact source_lemma_3_12_height s c out ho

/-- The literal Normal-input version of source Lemma 3.12. No accepted
input is assumed separately from its original low guard and Normality. -/
theorem source_lemma_3_12_normal_height (s c out : Nat) (ho : out ∈ rho s c)
    (hn : Comparison.Normal (contextCode s) (ThetaCourse.rawTree c)) :
    heightCode out ≤ max 1 (heightCode c) := by
  have hc : checkCode (contextCode s) c = true :=
    (HeightBoundary.input_spec (contextCode s) c (rho_spec s c out ho).1).1
  have ha := (Comparison.acceptedCode_exact (contextCode s) c).mpr ⟨hc, hn⟩
  simpa only [CanonicalHeight.canonicalHeightCode_normal (contextCode s) c ha] using rho_output_height s c out ho

/-- Raw written input height also bounds the returned written height,
since the actual normalizer never increases input height. -/
theorem rho_raw_height (s c out : Nat) (ho : out ∈ rho s c) :
    heightCode out ≤ max 1 (heightCode c) := by
  have hc := (HeightBoundary.input_spec (contextCode s) c (rho_spec s c out ho).1).1
  exact (rho_output_height s c out ho).trans
    (max_le_max le_rfl (CanonicalHeight.canonicalHeightCode_le_raw (contextCode s) c hc))

/-- Both clauses of source Lemma 3.12 for the actual executing operator.
The logarithm in the bound is the actual prepared source logend. -/
theorem source_lemma_3_12 (s c out : Nat) (ho : out ∈ rho s c) :
    (∃ p, Prepared s c p ∧ interpretation (contextCode s) out ≤
      base (contextCode s) * unionInterpretation (logCode p)) ∧
    CanonicalHeight.canonicalHeightCode (contextCode s) out ≤
      max 1 (CanonicalHeight.canonicalHeightCode (contextCode s) c) :=
  ⟨source_lemma_3_12_bound s c out ho, source_lemma_3_12_height s c out ho⟩

/-- Every original LOW input has a real returned LOW Normal output with
the source height estimate; execution supplies all of these facts. -/
theorem rho_returns_height (s c : Nat) (hc : inputCheck s c = true) :
    ∃ out, out ∈ rho s c ∧ lowCheckCode (contextCode s) out = true ∧
      Comparison.acceptedCode (contextCode s) out = true ∧
      heightCode out ≤ max 1 (CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  obtain ⟨out, ho⟩ := rho_returns s c hc
  have hs := rho_spec s c out ho
  exact ⟨out, ho, hs.2.1, hs.2.2.1, rho_output_height s c out ho⟩

/-- Original weak-Normal term spelling of the same source height law. -/
theorem source_lemma_3_12_term (s : Nat) (t : RelativeTerm Nat) (out : Nat)
    (ho : out ∈ rho s t.code) (hn : Comparison.Normal (contextCode s) t) :
    heightCode out ≤ max 1 t.height := by
  simpa only [heightCode_code] using source_lemma_3_12_normal_height s t.code out ho
    (by simpa only [ThetaCourse.rawTree_code] using hn)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho
