import Alexander313.Wilken.HereditaryNativeLambdaPrincipalLimits

/-!
# Executing the actual source principal-limit decision

The normal decision runs the genuine two-branch lambda producer and tests its
actual admitted output for zero. Source Lemma2.48(a), already constructed,
identifies this finite test with membership in the ORIGINAL source class L.
The original raw decision performs the actual root normalization and retains
the original raw proper-root guard. Both decisions reject invalid roots and
are total Computable; no primitive-recursive lambda execution is claimed.
These source candidates remain uncompiled and outside the checkpoint.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits

open NativePublicBridge (contextCode)

/-- The actual zero test on a genuinely executing normal lambda output
recognizes membership in the ORIGINAL source principal-limit class. -/
theorem output_test_exact (s a out : Nat) (ho : out ∈ Branches.execute s a) :
    (!FixedPoint.zeroCheck out) = true ↔ PrincipalLimit (interpretation (contextCode s) a) := by
  classical
  have hi : Decomposition.inputCheck (Branches.outputContext s a) out = true :=
    (Branches.execute_spec s a out ho).2.1
  rw [Bool.not_eq_true_eq_eq_false, ← Bool.eq_false_eq_not_eq_true,
    FixedPoint.zeroCheck_exact _ out hi, execute_zero_iff s a out ho]
  exact not_not

/-- Invalid original normal proper roots return false; valid roots run
actual lambda before the genuine finite zero test. -/
def decision (s a : Nat) : Part Bool := cond (Branches.inputCheck s a)
  ((Branches.execute s a).map (fun out => !FixedPoint.zeroCheck out)) (Part.some false)

theorem decision_partrec : Partrec₂ decision := by
  have hm := Branches.execute_partrec.map
    (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp Primrec.snd)).to_comp.to₂
  exact (Partrec.cond Branches.inputCheck_primrec.to_comp hm
    (Computable.const false).partrec).to₂

theorem decision_total (s a : Nat) : (decision s a).Dom := by
  cases ha : Branches.inputCheck s a with
  | false => simpa only [decision, ha, Bool.cond_false] using Part.some_dom false
  | true =>
    rw [decision, ha]
    change (Branches.execute s a).Dom
    exact (Branches.execute_domain s a).mpr ha

theorem decision_true_iff (s a : Nat) : true ∈ decision s a ↔
    Branches.inputCheck s a = true ∧ PrincipalLimit (interpretation (contextCode s) a) := by
  cases ha : Branches.inputCheck s a with
  | false => simp [decision, ha]
  | true =>
    constructor
    · intro ht
      have hm : true ∈ (Branches.execute s a).map (fun out => !FixedPoint.zeroCheck out) := by
        simpa only [decision, ha, Bool.cond_true] using ht
      obtain ⟨out, ho, he⟩ := (Part.mem_map_iff (fun out => !FixedPoint.zeroCheck out)).mp hm
      exact ⟨ha, (output_test_exact s a out ho).mp he⟩
    · rintro ⟨_, hL⟩
      obtain ⟨out, ho⟩ := Branches.execute_returns s a ha
      have he := (output_test_exact s a out ho).mpr hL
      have hm := Part.mem_map (fun out => !FixedPoint.zeroCheck out) ho
      rw [he] at hm
      simpa only [decision, ha, Bool.cond_true] using hm

def check (s a : Nat) : Bool := (decision s a).get (decision_total s a)

theorem check_mem (s a : Nat) : check s a ∈ decision s a := ⟨decision_total s a, rfl⟩

theorem decision_eq_some (s a : Nat) : decision s a = Part.some (check s a) :=
  Part.eq_some_iff.mpr (check_mem s a)

theorem check_computable : Computable₂ check :=
  (decision_partrec.of_eq_tot (fun p => check_mem p.1 p.2)).to₂

/-- Exact original normal proper-root guard plus the actual source class L. -/
theorem check_exact (s a : Nat) : check s a = true ↔
    Branches.inputCheck s a = true ∧ PrincipalLimit (interpretation (contextCode s) a) := by
  simpa only [decision_eq_some, Part.mem_some_iff, eq_comm] using decision_true_iff s a

/-- The actual raw path normalizes the original root, retaining its genuine
original raw proper-root guard; malformed raw trees return false. -/
def rawCheck (s a : Nat) : Bool := Branches.Raw.inputCheck s a &&
  check s (Branches.Raw.normalizedRoot s a)

theorem rawCheck_computable : Computable₂ rawCheck := by
  have hn := check_computable.comp Computable.fst Branches.Raw.normalizedRoot_primrec.to_comp
  exact (Primrec.and.to_comp.comp Branches.Raw.inputCheck_primrec.to_comp hn).to₂

/-- Exact original RAW guard and ORIGINAL root class; real normalization
value fidelity derives the normalized class instead of supplying it. -/
theorem rawCheck_exact (s a : Nat) : rawCheck s a = true ↔
    Branches.Raw.inputCheck s a = true ∧ PrincipalLimit (interpretation (contextCode s) a) := by
  cases ha : Branches.Raw.inputCheck s a with
  | false => simp only [rawCheck, ha, Bool.false_and, Bool.false_eq_true, false_and]
  | true =>
    have hc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1
    have hv := (Normalization.normalizeCode_accepted (contextCode s) a hc).2
    simp only [rawCheck, ha, Bool.true_and, check_exact, (Bool.and_eq_true.mp ha).2,
      true_and, Branches.Raw.normalizedRoot, hv]

theorem check_rejected (s a : Nat) (ha : Branches.inputCheck s a = false) : check s a = false := by
  cases ht : check s a with
  | false => rfl
  | true => have hg := ((check_exact s a).mp ht).1; rw [ha] at hg; cases hg

theorem rawCheck_rejected (s a : Nat) (ha : Branches.Raw.inputCheck s a = false) : rawCheck s a = false := by
  simp only [rawCheck, ha, Bool.false_and]

/-- On admitted original normal roots, the decision depends only on the
original ordinal value; no output-presentation or branch oracle is needed. -/
theorem check_invariant (s a v b : Nat)
    (ha : Branches.inputCheck s a = true) (hb : Branches.inputCheck v b = true)
    (he : interpretation (contextCode s) a = interpretation (contextCode v) b) :
    check s a = check v b := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_exact, ha, hb, true_and, he]

theorem rawCheck_invariant (s a v b : Nat)
    (ha : Branches.Raw.inputCheck s a = true) (hb : Branches.Raw.inputCheck v b = true)
    (he : interpretation (contextCode s) a = interpretation (contextCode v) b) :
    rawCheck s a = rawCheck v b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawCheck_exact, ha, hb, true_and, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits
