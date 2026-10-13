import Alexander313.Wilken.PublicEpsilonNativeFineLocalization
import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive

/-!
# Fine localization on the actual original raw theta-zero domain

The input guard retains ORIGINAL native admission and literal theta-zero
shape at the SAME coded epsilon q. The actual normalizer preserves that
shape and value and derives the genuine Node caller of the ordinally
terminating fine-localization kernel. The encoded path ends at the computed
normalized root, whose value is the ORIGINAL raw root value. Base inputs
are included. No spelling invariance, parameter transport or cross-base
localization is inferred from normalization. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.Raw

open ThetaCourse

def inputCheck (q c : Nat) : Bool := checkCode q c && SourceLocalization.rootShape c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp NativeContext.checkCode_primrec
    (SourceLocalization.rootShape_primrec.comp Primrec.snd)).to₂

/-- Exactly the original raw theta-zero roots are recognized. No Normal,
properness, hidden-height or public-return condition is added. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check q (.theta 0 a) = true := by
  constructor
  · intro hc
    obtain ⟨hcheck, hshape⟩ := Bool.and_eq_true.mp hc
    obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hcheck
    have hs : SourceLocalization.rootShape t.code = true := by rw [he]; exact hshape
    obtain ⟨a, rfl⟩ := (SourceLocalization.rootShape_code t).mp hs
    exact ⟨a, he.symm, ht⟩
  · rintro ⟨a, rfl, ha⟩
    exact Bool.and_eq_true.mpr ⟨by simpa only [checkCode_code] using ha,
      (SourceLocalization.rootShape_code _).mpr ⟨a, rfl⟩⟩

/-- Real normalization derives an admitted weak Normal theta-zero Node
at the ORIGINAL source. It does not change the source epsilon. -/
theorem normalized_node (q c : Nat) (hc : inputCheck q c = true) :
    SourceLocalization.Node q (Normalization.normalizeCode q c) := by
  obtain ⟨a, rfl, ha⟩ := (inputCheck_exact q c).mp hc
  have hs := Normalization.normalize_checked q (.theta 0 a) ha
  refine ⟨Normalization.normalize q a, ?_, ?_, ?_⟩
  · simp only [Normalization.normalizeCode, checkCode_code, ha, Bool.cond_true,
      rawTree_code, Normalization.normalize]
  · simpa only [Normalization.normalize] using hs.1
  · simpa only [Normalization.normalize, Comparison.Normal] using hs.2.1

theorem normalized_input (q c : Nat) (hc : inputCheck q c = true) :
    SourceLocalization.inputCheck q (Normalization.normalizeCode q c) = true :=
  (SourceLocalization.inputCheck_exact q _).mpr (normalized_node q c hc)

theorem normalized_value (q c : Nat) (hc : inputCheck q c = true) :
    SourceLocalization.value q (Normalization.normalizeCode q c) = interpretation q c :=
  (Normalization.normalizeCode_accepted q c (Bool.and_eq_true.mp hc).1).2

def execute (q c : Nat) : Part Nat := cond (inputCheck q c)
  (fineLocalization q (Normalization.normalizeCode q c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (fineLocalization_partrec.comp Primrec.fst.to_comp
      Normalization.Effective.normalizeCode_primrec.to_comp) Partrec.none).to₂

theorem execute_graph (q c output : Nat) : output ∈ execute q c ↔
    inputCheck q c = true ∧ output ∈ fineLocalization q (Normalization.normalizeCode q c) := by
  cases hi : inputCheck q c <;>
    simp only [execute, hi, Bool.cond_true, Bool.cond_false, Part.notMem_none,
      Bool.false_eq_true, false_and, true_and]

/-- The partial raw operation is defined on precisely its original checked
theta-zero inputs, including all actual base spellings. -/
theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ inputCheck q c = true := by
  constructor
  · intro hd
    obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp hd
    exact ((execute_graph q c output).mp ho).1
  · intro hc
    have hd := (fineLocalization_domain q _).mpr (normalized_input q c hc)
    obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp hd
    exact Part.dom_iff_mem.mpr ⟨output, (execute_graph q c output).mpr ⟨hc, ho⟩⟩

/-- Every executing raw output is the actual encoded SAME-q FinePath of
its computed normalized root; that root has the ORIGINAL raw value. -/
theorem execute_spec (q c output : Nat) (ho : output ∈ execute q c) :
    inputCheck q c = true ∧ ∃ n,
      n ∈ search (Nat.pair q (Normalization.normalizeCode q c)) ∧
      output = Encodable.encode (word q (Normalization.normalizeCode q c) n) ∧
      FinePath q (Normalization.normalizeCode q c)
        (word q (Normalization.normalizeCode q c) n) ∧
      SourceLocalization.value q (Normalization.normalizeCode q c) = interpretation q c := by
  obtain ⟨hc, hm⟩ := (execute_graph q c output).mp ho
  obtain ⟨_, n, hn, he, hp⟩ := fineLocalization_source q _ output hm
  exact ⟨hc, n, hn, he, hp, normalized_value q c hc⟩

theorem execute_unique (q c : Nat) (hc : inputCheck q c = true) :
    ∃! output, output ∈ execute q c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((execute_domain q c).mpr hc)
  exact ⟨output, ho, fun other hother => Part.mem_unique hother ho⟩

/-- A raw base-value input really executes a one-node path. The numerical
last node is its actual normalizer output, with the SAME original value. -/
theorem execute_base (q c : Nat) (hc : inputCheck q c = true)
    (hb : interpretation q c = NativeContext.base q) :
    execute q c = Part.some (Encodable.encode
      ([Normalization.normalizeCode q c] : List Nat)) := by
  simp only [execute, hc, Bool.cond_true]
  exact fineLocalization_base q _ (normalized_node q c hc) ((normalized_value q c hc).trans hb)

def graphCertificate (q c n output : Nat) : Bool := inputCheck q c &&
  SourceFineLocalization.graphCertificate q (Normalization.normalizeCode q c) n output

theorem graphCertificate_primrec : Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
    graphCertificate p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hq : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn := Primrec.snd.comp Primrec.fst
  have hnormalized := Normalization.Effective.normalizeCode_primrec.comp hq hc
  have hrun := SourceFineLocalization.graphCertificate_primrec.comp
    (((hq.pair hnormalized).pair hn).pair Primrec.snd)
  exact Primrec.and.comp (inputCheck_primrec.comp hq hc) hrun

/-- Complete numerical output graph, including output zero. The finite
certificate checks the real normalization, halt and every preceding step. -/
theorem execute_graph_iff (q c output : Nat) : output ∈ execute q c ↔
    ∃ n, graphCertificate q c n output = true := by
  constructor
  · intro ho
    obtain ⟨hc, hm⟩ := (execute_graph q c output).mp ho
    obtain ⟨n, hn⟩ := (fineLocalization_graph_iff q _ output).mp hm
    exact ⟨n, Bool.and_eq_true.mpr ⟨hc, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨hc, hrun⟩ := Bool.and_eq_true.mp hn
    exact (execute_graph q c output).mpr ⟨hc,
      (fineLocalization_graph_iff q _ output).mpr ⟨n, hrun⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.Raw
