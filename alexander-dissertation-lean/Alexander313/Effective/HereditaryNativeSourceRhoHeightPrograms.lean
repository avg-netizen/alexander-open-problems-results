import Alexander313.Wilken.HereditaryNativeSourceRhoHeight
import Alexander313.Effective.HereditaryNativeSourceRhoPrograms

/-!
# Source height bounds for the real rho Programs and complete output graph

These corollaries apply to the already constructed executing rho Program,
its source columns, and its positive literal output-graph Programs. The
original source LOW domains and all chosen outputs, including zero, remain
unchanged. Canonical input height is the actual native normalizer's height;
the returned output is genuinely admitted and weak Normal. No height or
execution oracle is assumed. All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceRhoProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm (heightCode)
open NativeContext (SourceRho)
open NativePublicBridge (contextCode)

theorem program_canonical_height (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) out ≤
      max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [program_eval] at ho
  exact SourceRho.source_lemma_3_12_height s c out ho

theorem program_height (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    heightCode out ≤ max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [program_eval] at ho
  exact SourceRho.rho_output_height s c out ho

theorem program_normal_height (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c))
    (hn : NativeContext.Comparison.Normal (contextCode s) (ThetaCourse.rawTree c)) :
    heightCode out ≤ max 1 (heightCode c) := by
  rw [program_eval] at ho
  exact SourceRho.source_lemma_3_12_normal_height s c out ho hn

theorem program_raw_height (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    heightCode out ≤ max 1 (heightCode c) := by
  rw [program_eval] at ho
  exact SourceRho.rho_raw_height s c out ho

theorem program_lemma_3_12 (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    (∃ p, SourceRho.Prepared s c p ∧ NativeContext.interpretation (contextCode s) out ≤
      NativeContext.base (contextCode s) * unionInterpretation (SourceRho.logCode p)) ∧
    NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) out ≤
      max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [program_eval] at ho
  exact SourceRho.source_lemma_3_12 s c out ho

theorem program_returns_height (s c : Nat) (hc : SourceRho.inputCheck s c = true) :
    ∃ out, out ∈ program.eval (Nat.pair s c) ∧ NativeContext.lowCheckCode (contextCode s) out = true ∧
      NativeContext.Comparison.acceptedCode (contextCode s) out = true ∧
      heightCode out ≤ max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  simpa only [program_eval] using SourceRho.rho_returns_height s c hc

theorem sourceColumn_canonical_height (s c out : Nat) (ho : out ∈ (sourceColumn s).eval c) :
    NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) out ≤
      max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [sourceColumn_eval] at ho
  exact SourceRho.source_lemma_3_12_height s c out ho

theorem sourceColumn_height (s c out : Nat) (ho : out ∈ (sourceColumn s).eval c) :
    heightCode out ≤ max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) := by
  rw [sourceColumn_eval] at ho
  exact SourceRho.rho_output_height s c out ho

theorem sourceColumn_normal_height (s c out : Nat) (ho : out ∈ (sourceColumn s).eval c)
    (hn : NativeContext.Comparison.Normal (contextCode s) (ThetaCourse.rawTree c)) :
    heightCode out ≤ max 1 (heightCode c) := by
  rw [sourceColumn_eval] at ho
  exact SourceRho.source_lemma_3_12_normal_height s c out ho hn

/-- Successful execution of the actual complete positive graph certifies
the same bound for its literal output argument, including output zero. -/
theorem graphProgram_height (s c out : Nat)
    (ho : graphProgram.domain (Nat.pair s (Nat.pair c out))) :
    heightCode out ≤ max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) :=
  SourceRho.rho_output_height s c out ((graphProgram_domain s c out).mp ho)

theorem graphColumn_height (s c out : Nat) (ho : (graphColumn s c).domain out) :
    heightCode out ≤ max 1 (NativeContext.CanonicalHeight.canonicalHeightCode (contextCode s) c) :=
  SourceRho.rho_output_height s c out ((graphColumn_domain s c out).mp ho)

end Alexander313.HereditaryNativeSourceRhoProgram
