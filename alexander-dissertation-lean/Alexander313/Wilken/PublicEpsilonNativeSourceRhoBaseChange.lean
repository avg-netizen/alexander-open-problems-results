import Alexander313.Wilken.HereditaryNativeSourceRhoUniform

/-!
# Actual source rho preserves the FULL chosen smaller-base domain

Both-context admission makes the original normalized ANF/unit decomposition,
source chi, dotted RIGHT subtraction and actual base-left multiplication
agree literally. Original RAW LOW admission and the original atomic-stop
Par cutoff derive every second-context caller. The genuine target output
checker then derives FULL hidden Payloads and original Par BEFORE invoking
the real pi map, including zero outputs. These are the executing source
Lemma3.13 rho equations on its printed epsilon-only domain. Source3.10's
inverse-mu relation and a claim about arbitrary old numerical spellings are
not inferred from value equality. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

/-- The real source dotted RIGHT subtraction agrees on original dual
admission, independently of the distinct left-removal operation. -/
theorem rightCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    RightSubtraction.rightCode q c d = RightSubtraction.rightCode v c d := by
  have he : Comparison.equal q = Comparison.equal v :=
    funext fun t => funext fun u => BaseTransformation.equal_context q v t u
  simp only [RightSubtraction.rightCode, RightSubtraction.inputCheck,
    Arithmetic.inputCheck, hcq, hdq, hcv, hdv, Bool.true_and, Bool.cond_true,
    RightSubtraction.rightTerm, RightSubtraction.word, Arithmetic.leCode,
    OmegaPowers.BaseChange.lessRawCode_context q v d c hdq hcq hdv hcv,
    RightSubtraction.rightMatch, he,
    OmegaPowers.BaseChange.normalizedWord_context q v c hcq hcv,
    OmegaPowers.BaseChange.normalizedWord_context q v d hdq hdv]

theorem chiNat_context (q v ell : Nat) (hq : lowCheckCode q ell = true)
    (hv : lowCheckCode v ell = true) : chiNat q ell = chiNat v ell := by
  have hl := FiniteTailDecomposition.lambdaCode_context q v ell
    (Bool.and_eq_true.mp hq).1 (Bool.and_eq_true.mp hv).1
  have haq := (FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hq).1).1
  have hav : Comparison.acceptedCode v (FiniteTailDecomposition.lambdaCode q ell) = true := by
    rw [hl]
    exact (FiniteTailDecomposition.lambdaCode_spec v ell (Bool.and_eq_true.mp hv).1).1
  have hcq := (Decomposition.inputCheck_exact q _).mpr ((Comparison.acceptedCode_exact q _).mp haq)
  have hcv := (Decomposition.inputCheck_exact v _).mpr ((Comparison.acceptedCode_exact v _).mp hav)
  have he := SourceChi.BaseChange.chiCode_context q v _ hcq hcv
  simp only [chiNat, he, hl]

theorem reducedCode_context (q v ell : Nat) (hq : lowCheckCode q ell = true)
    (hv : lowCheckCode v ell = true) : reducedCode q ell = reducedCode v ell := by
  have hchi : chiCode q ell = chiCode v ell := by
    simp only [chiCode, chiNat_context q v ell hq hv]
  have hqc := ((Comparison.acceptedCode_exact q _).mp (chiCode_spec q ell hq).2.1).1
  have hvc : checkCode v (chiCode q ell) = true := by
    rw [hchi]
    exact ((Comparison.acceptedCode_exact v _).mp (chiCode_spec v ell hv).2.1).1
  have he := rightCode_context q v ell (chiCode q ell)
    (Bool.and_eq_true.mp hq).1 hqc (Bool.and_eq_true.mp hv).1 hvc
  simp only [reducedCode, he, hchi]

theorem finish_context (q v ell : Nat) (hq : lowCheckCode q ell = true)
    (hv : lowCheckCode v ell = true) : finish q ell = finish v ell := by
  have hr := reducedCode_context q v ell hq hv
  have hloq := (reducedCode_spec q ell hq).1
  have hlov : lowCheckCode v (reducedCode q ell) = true := by
    rw [hr]
    exact (reducedCode_spec v ell hv).1
  simp only [finish, BaseLeftMultiplication.execute_context q v _ hloq hlov, hr]

theorem execute_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : execute q c = execute v c := by
  have he := LogEnd.BaseChange.execute_context q v c hcq hcv
  obtain ⟨ell, hlq⟩ := Part.dom_iff_mem.mp ((LogEnd.execute_domain q c).mpr hcq)
  have hlv : ell ∈ LogEnd.execute v c := by rw [← he]; exact hlq
  have hsq := (LogEnd.execute_spec q c ell hlq).2.1
  have hsv := (LogEnd.execute_spec v c ell hlv).2.1
  simp only [execute, Part.eq_some_iff.mpr hlq, Part.eq_some_iff.mpr hlv, Part.bind_some]
  exact finish_context q v ell hsq hsv

/-- Original chosen-presentation Par supplies the real second epsilon
context; no target admission, logarithm or output-cutoff premise is added. -/
theorem execute_change (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    execute q c = execute v c :=
  execute_context q v c hc (OmegaPowers.BaseChange.target_low q v c hc hv hp)

/-- FULL hidden payload preservation is derived from the actual target
rho checker, rather than from the value of a chosen representative. -/
theorem output_payloads (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    Payloads v (rawTree out) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have ht : out ∈ execute v c := by rw [← execute_change q v c hc hv hp]; exact ho
  have htarget := (Bool.and_eq_true.mp (source_definition_3_11 v c out ht).2.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v out htarget)).1

theorem output_parBounded (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree out) := by
  have hs := (Bool.and_eq_true.mp (source_definition_3_11 q c out ho).2.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q out hs) hv).mpr
    (output_payloads q v c out ho hv hp)

theorem input_pi_caller (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  OmegaPowers.BaseChange.input_pi_caller q v c hc hv hl hp

theorem output_pi_caller (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨(Bool.and_eq_true.mp (source_definition_3_11 q c out ho).2.1).1, hv, hl,
      output_parBounded q v c out ho hv hp⟩

/-- The actual executing source3.13 pi/rho identity preserves EVERY
original RAW LOW chosen-presentation input and every numerical output,
including zero, at genuine epsilon source and target bases. -/
theorem source_lemma_3_13_execute_pi (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    (execute q c).map (BaseTransformation.piCode q v) =
      execute v (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp)]
  have he := execute_change q v c hc hv hp
  apply Part.ext
  intro out
  constructor
  · intro hm
    obtain ⟨d, hd, hdo⟩ := (Part.mem_map_iff _).mp hm
    rw [BaseTransformation.piCode_eq q v d (output_pi_caller q v c d hd hv hl hp)] at hdo
    subst out
    rw [← he]
    exact hd
  · intro ht
    have ho : out ∈ execute q c := by rw [he]; exact ht
    exact (Part.mem_map_iff _).mpr ⟨out, ho,
      BaseTransformation.piCode_eq q v out (output_pi_caller q v c out ho hv hl hp)⟩

theorem pi_output_spec (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    lowCheckCode v (BaseTransformation.piCode q v out) = true ∧
      Comparison.acceptedCode v (BaseTransformation.piCode q v out) = true ∧
      heightCode (BaseTransformation.piCode q v out) ≤
        max 1 (CanonicalHeight.canonicalHeightCode v (BaseTransformation.piCode q v c)) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have ht : out ∈ execute v c := by rw [← execute_change q v c hc hv hp]; exact ho
  rw [BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp),
    BaseTransformation.piCode_eq q v out (output_pi_caller q v c out ho hv hl hp)]
  have hs := source_definition_3_11 v c out ht
  exact ⟨hs.2.1, hs.2.2.1, source_lemma_3_12_height v c out ht⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.BaseChange
