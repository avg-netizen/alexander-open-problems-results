import Alexander313.Wilken.PublicEpsilonNativeFineLocalizationRaw
import Alexander313.Wilken.PublicEpsilonNativeFinePredecessorBaseChange

/-!
# Genuine fine-localization transport with full original parameter provenance

Original chosen Par bounds derive the second-source Node and every actual
predecessor caller. The computed steps, first-halt search and encoded words
agree literally. Each original path node has FULL target payload admission,
so the real pi operation is defined on every node. Raw normalization and
its payload preservation are proved separately before the same argument.
No spelling invariance or value-cutoff-to-Par inference. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.BaseChange

open ThetaCourse

theorem step_context (q v c : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : step q c = step v c := by
  simp only [step,
    SourceFinePredecessor.BaseChange.inputCheck_context q v c hcq hcv,
    SourceFinePredecessor.BaseChange.predecessorCode_context q v c hcq hcv]

theorem iterate_context (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : iterate q c n = iterate v c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hq := iterate_node q c n hcq
    have hv : SourceLocalization.Node v (iterate q c n) := by
      rw [ih]; exact iterate_node v c n hcv
    rw [iterate_succ, iterate_succ, step_context q v _ hq hv, ih]

theorem haltCheck_context (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : haltCheck q c n = haltCheck v c n := by
  have he := iterate_context q v c n hcq hcv
  have hq := iterate_node q c n hcq
  have hv : SourceLocalization.Node v (iterate q c n) := by
    rw [he]; exact iterate_node v c n hcv
  simp only [haltCheck,
    SourceFinePredecessor.BaseChange.inputCheck_context q v _ hq hv, he]

/-- Genuine literal comparison agreement identifies the whole search
predicate; the independently derived termination theorem remains unchanged. -/
theorem search_context (q v c : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : search (Nat.pair q c) = search (Nat.pair v c) := by
  have he : (fun n => Part.some (haltCheck q c n)) =
      (fun n => Part.some (haltCheck v c n)) :=
    funext fun n => congrArg Part.some (haltCheck_context q v c n hcq hcv)
  simpa only [search, Nat.unpair_pair] using congrArg Nat.rfind he

theorem word_context (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : word q c n = word v c n := by
  have he : iterate q c = iterate v c := funext fun n => iterate_context q v c n hcq hcv
  simp only [word, he]

theorem fineLocalization_context (q v c : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : fineLocalization q c = fineLocalization v c := by
  have hi := SourceLocalization.BaseChange.inputCheck_context q v c hcq hcv
  have hs := search_context q v c hcq hcv
  have hw : (fun n => Encodable.encode (word q c n)) =
      (fun n => Encodable.encode (word v c n)) :=
    funext fun n => congrArg Encodable.encode (word_context q v c n hcq hcv)
  simp only [fineLocalization, evaluation, Nat.unpair_pair, hi, hs, hw]

/-- The chosen original root Par bound derives literal executing path
agreement. There is no second-source admission or first-halt premise. -/
theorem fineLocalization_change (q v c : Nat) (hc : SourceLocalization.Node q c)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    fineLocalization q c = fineLocalization v c :=
  fineLocalization_context q v c hc (SourceLocalization.BaseChange.node_change q v c hc hv hp)

theorem word_payloads (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) : ∀ d ∈ word q c n, Payloads v (rawTree d) := by
  intro d hd
  rw [word_context q v c n hcq hcv] at hd
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
  have hn := iterate_node v c k hcv
  exact (checked_admissible v _ (Arithmetic.raw_checked v _
    (SourceLocalization.BaseChange.node_checked v _ hn))).1

theorem word_Par (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) :
    ∀ d ∈ word q c n, BaseTransformation.ParBounded q v (rawTree d) := by
  intro d hd
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hd
  have hn : SourceLocalization.Node q d := by rw [← he]; exact iterate_node q c k hcq
  exact (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ (SourceLocalization.BaseChange.node_checked q d hn))
    (SourceLocalization.node_baseCheck v c hcv)).mpr (word_payloads q v c n hcq hcv d hd)

theorem word_pi_input (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) (hbase : base v < base q) :
    ∀ d ∈ word q c n, BaseTransformation.inputCheck q v d = true := by
  intro d hd
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hd
  have hn : SourceLocalization.Node q d := by rw [← he]; exact iterate_node q c k hcq
  exact (BaseTransformation.inputCheck_exact q v d).mpr
    ⟨SourceLocalization.BaseChange.node_checked q d hn,
      SourceLocalization.node_baseCheck v c hcv, hbase, word_Par q v c n hcq hcv d hd⟩

/-- Every real original run node is inside the actual pi domain, and
mapping actual pi across the run gives exactly the transported literal run. -/
theorem word_pi (q v c n : Nat) (hcq : SourceLocalization.Node q c)
    (hcv : SourceLocalization.Node v c) (hbase : base v < base q) :
    (word q c n).map (BaseTransformation.piCode q v) = word v c n := by
  calc
    (word q c n).map (BaseTransformation.piCode q v) = word q c n := by
      have he : (word q c n).map (BaseTransformation.piCode q v) =
          (word q c n).map (fun d => d) := List.map_congr_left (fun d hd =>
        BaseTransformation.piCode_eq q v d (word_pi_input q v c n hcq hcv hbase d hd))
      simpa only [List.map_id_fun'] using he
    _ = word v c n := word_context q v c n hcq hcv

theorem execute_provenance (q v c output : Nat) (ho : output ∈ fineLocalization q c)
    (hv : baseCheck v = true) (hbase : base v < base q)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    output ∈ fineLocalization v c ∧ ∃ n,
      output = Encodable.encode (word q c n) ∧
      (∀ d ∈ word q c n, Payloads v (rawTree d)) ∧
      (∀ d ∈ word q c n, BaseTransformation.ParBounded q v (rawTree d)) ∧
      (∀ d ∈ word q c n, BaseTransformation.inputCheck q v d = true) ∧
      (word q c n).map (BaseTransformation.piCode q v) = word v c n := by
  obtain ⟨hi, n, hn, he, hpath⟩ := fineLocalization_source q c output ho
  have hc := (SourceLocalization.inputCheck_exact q c).mp hi
  have ht := SourceLocalization.BaseChange.node_change q v c hc hv hp
  have hout : output ∈ fineLocalization v c := by
    rw [← fineLocalization_context q v c hc ht]; exact ho
  exact ⟨hout, n, he, word_payloads q v c n hc ht, word_Par q v c n hc ht,
    word_pi_input q v c n hc ht hbase, word_pi q v c n hc ht hbase⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.BaseChange
