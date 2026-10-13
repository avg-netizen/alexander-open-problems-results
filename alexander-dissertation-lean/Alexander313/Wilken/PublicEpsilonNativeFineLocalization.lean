import Alexander313.Wilken.PublicEpsilonNativeFinePredecessor

/-!
# Executing fine localization at the original coded epsilon

Iterate the genuinely computed original fine predecessor at the SAME literal
coded epsilon q. Admission and weak Normality are preserved at every step.
Strict ordinal decrease proves a finite halt at the actual source base; an
actual natural rfind computes its first occurrence, without a supplied fuel
bound. Every finite run has a primitive-recursive complete certificate.
The actual base Node is included and returns its one-node, zero-step path.
No public recoder, cross-base operation, spelling invariance or parameter
provenance is assumed or concluded. Source candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization

def step (q c : Nat) : Nat := cond (SourceFinePredecessor.inputCheck q c)
  (SourceFinePredecessor.predecessorCode q c) c

theorem step_primrec : Primrec₂ step :=
  (SourceFinePredecessor.inputCheck_primrec.cond SourceFinePredecessor.predecessorCode_primrec Primrec.snd).to₂

theorem step_node (q c : Nat) (hc : SourceLocalization.Node q c) : SourceLocalization.Node q (step q c) := by
  cases h : SourceFinePredecessor.inputCheck q c with
  | false => simpa only [step, h, Bool.cond_false] using hc
  | true => simpa only [step, h, Bool.cond_true] using (SourceFinePredecessor.predecessor_spec q c h).1

def iterate (q c : Nat) : Nat → Nat :=
  Nat.rec c (fun _ previous => step q previous)

theorem iterate_primrec : Primrec (fun p : (Nat × Nat) × Nat => iterate p.1.1 p.1.2 p.2) := by
  have hs : Primrec₂ (fun p : Nat × Nat => fun s : Nat × Nat => step p.1 s.2) :=
    (step_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.nat_rec Primrec.snd hs

@[simp] theorem iterate_zero (q c : Nat) : iterate q c 0 = c := rfl

@[simp] theorem iterate_succ (q c n : Nat) : iterate q c (n + 1) = step q (iterate q c n) := rfl

theorem iterate_shift (q c n : Nat) : iterate q (step q c) n = iterate q c (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate_succ, ih]

theorem iterate_node (q c n : Nat) (hc : SourceLocalization.Node q c) : SourceLocalization.Node q (iterate q c n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact step_node q _ ih

def haltCheck (q c n : Nat) : Bool := !SourceFinePredecessor.inputCheck q (iterate q c n)

theorem haltCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => haltCheck p.1.1 p.1.2 p.2) :=
  Primrec.not.comp (SourceFinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) iterate_primrec)

theorem haltCheck_exact (q c n : Nat) (hc : SourceLocalization.Node q c) : haltCheck q c n = true ↔
    SourceLocalization.value q (iterate q c n) = NativeContext.base q := by
  have hn := iterate_node q c n hc
  have hb : NativeContext.base q ≤ SourceLocalization.value q (iterate q c n) := by
    simpa only [SourceLocalization.baseRaw_value q (SourceLocalization.node_baseCheck q _ hn)] using SourceLocalization.baseRaw_le q _ hn
  have hi := SourceFinePredecessor.inputCheck_exact q (iterate q c n)
  cases h : SourceFinePredecessor.inputCheck q (iterate q c n) with
  | true =>
    have hl := (hi.mp h).2
    simp [haltCheck, h, ne_of_gt hl]
  | false =>
    have he : SourceLocalization.value q (iterate q c n) = NativeContext.base q := by
      apply le_antisymm ?_ hb
      apply le_of_not_gt
      intro hl
      have ht := hi.mpr ⟨hn, hl⟩
      simp only [h, Bool.false_eq_true] at ht
    simp only [haltCheck, h, Bool.not_false, he]

/-- Termination is derived from real strict ordinal decrease; its witness
is not a supplied bound and is not asserted primitive recursive. -/
theorem halt_exists (q c : Nat) (hc : SourceLocalization.Node q c) : ∃ n, haltCheck q c n = true := by
  have h : ∀ c, SourceLocalization.Node q c → ∃ n, haltCheck q c n = true := by
    intro c
    refine (InvImage.wf (SourceLocalization.value q) Ordinal.lt_wf).induction c ?_
    intro d ih hd
    by_cases hb : NativeContext.base q < SourceLocalization.value q d
    · have hi := (SourceFinePredecessor.inputCheck_exact q d).mpr ⟨hd, hb⟩
      have hs := SourceFinePredecessor.predecessor_spec q d hi
      have hstep : step q d = SourceFinePredecessor.predecessorCode q d := by simp only [step, hi, Bool.cond_true]
      obtain ⟨n, hn⟩ := ih (step q d) (by simpa only [hstep] using hs.2.2) (step_node q d hd)
      refine ⟨n + 1, ?_⟩
      simpa only [haltCheck, iterate_shift] using hn
    · have hbase : SourceLocalization.value q d = NativeContext.base q := le_antisymm (le_of_not_gt hb)
        (by simpa only [SourceLocalization.baseRaw_value q (SourceLocalization.node_baseCheck q d hd)] using SourceLocalization.baseRaw_le q d hd)
      exact ⟨0, (haltCheck_exact q d 0 hd).mpr hbase⟩
  exact h c hc

def search (input : Nat) : Part Nat := Nat.rfind (fun n =>
  Part.some (haltCheck input.unpair.1 input.unpair.2 n))

theorem search_partrec : Partrec search := by
  have h : Primrec₂ (fun input n => haltCheck input.unpair.1 input.unpair.2 n) :=
    (haltCheck_primrec.comp ((Primrec.unpair.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Partrec.rfind h.to_comp.partrec₂

theorem search_domain (q c : Nat) (hc : SourceLocalization.Node q c) : (search (Nat.pair q c)).Dom := by
  obtain ⟨n, hn⟩ := halt_exists q c hc
  rw [search, Nat.rfind_dom]
  refine ⟨n, ?_, fun m hm => Part.some_dom _⟩
  simpa only [Nat.unpair_pair, Part.mem_some_iff] using hn.symm

theorem search_halt (q c n : Nat) (hn : n ∈ search (Nat.pair q c)) : haltCheck q c n = true := by
  have h := Nat.rfind_spec hn
  simpa only [Nat.unpair_pair, Part.mem_some_iff, eq_comm] using h

theorem search_before (q c n : Nat) (hn : n ∈ search (Nat.pair q c)) :
    ∀ k < n, SourceFinePredecessor.inputCheck q (iterate q c k) = true := by
  intro k hk
  have h := Nat.rfind_min hn hk
  have hf : haltCheck q c k = false := by
    simpa only [Nat.unpair_pair, Part.mem_some_iff, eq_comm] using h
  cases hi : SourceFinePredecessor.inputCheck q (iterate q c k) <;> simp_all only [haltCheck, Bool.not_false,
    Bool.not_true, Bool.true_eq_false]

/-- Every actual base spelling halts at zero; numerical code equality to
the particular baseRaw spelling is unnecessary. -/
theorem search_zero (q c : Nat) (hc : SourceLocalization.Node q c)
    (hb : SourceLocalization.value q c = NativeContext.base q) :
    0 ∈ search (Nat.pair q c) := by
  rw [search, Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.unpair_pair, Part.mem_some_iff] using
      ((haltCheck_exact q c 0 hc).mpr hb).symm
  · intro m hm
    omega

def word (q c n : Nat) : List Nat := (List.range (n + 1)).reverse.map (iterate q c)

theorem word_primrec : Primrec (fun p : (Nat × Nat) × Nat => word p.1.1 p.1.2 p.2) := by
  have hl := Primrec.list_reverse.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
  have hm : Primrec₂ (fun p : (Nat × Nat) × Nat => fun k : Nat => iterate p.1.1 p.1.2 k) :=
    (iterate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Primrec.list_map hl hm

@[simp] theorem word_zero (q c : Nat) : word q c 0 = [c] := rfl

theorem word_succ (q c n : Nat) : word q c (n + 1) = word q (step q c) n ++ [c] := by
  rw [word, List.range_succ_eq_map, List.reverse_cons, List.reverse_map, List.map_append, List.map_map]
  simp only [Function.comp_def, ← iterate_shift, List.map_cons, List.map_nil, iterate_zero, word]

theorem word_length (q c n : Nat) : (word q c n).length = n + 1 := by
  simp only [word, List.length_map, List.length_reverse, List.length_range]

/-- The literal iterated fine-predecessor recurrence. Base spellings need
not equal the particular written baseRaw node. -/
inductive FinePath (q : Nat) : Nat → List Nat → Prop
  | base (c : Nat) (hc : SourceLocalization.Node q c) (he : SourceLocalization.value q c = NativeContext.base q) : FinePath q c [c]
  | next (c : Nat) (hc : SourceFinePredecessor.inputCheck q c = true) (path : List Nat)
      (hp : FinePath q (SourceFinePredecessor.predecessorCode q c) path) : FinePath q c (path ++ [c])

theorem FinePath.nodes {q c : Nat} {path : List Nat} (hp : FinePath q c path) :
    ∀ d ∈ path, SourceLocalization.Node q d := by
  induction hp with
  | base c hc he => intro d hd; simpa only [List.mem_singleton.mp hd] using hc
  | next c hc path hp ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih d hd
    · have he := List.mem_singleton.mp hd
      subst d
      exact ((SourceFinePredecessor.inputCheck_exact q c).mp hc).1

theorem FinePath.bound {q c : Nat} {path : List Nat} (hp : FinePath q c path) :
    ∀ d ∈ path, SourceLocalization.value q d ≤ SourceLocalization.value q c := by
  induction hp with
  | base c hc he => intro d hd; rw [List.mem_singleton.mp hd]
  | next c hc path hp ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (ih d hd).trans (SourceFinePredecessor.predecessor_spec q c hc).2.2.le
    · rw [List.mem_singleton.mp hd]

theorem FinePath.strict {q c : Nat} {path : List Nat} (hp : FinePath q c path) :
    (path.map (SourceLocalization.value q)).Pairwise (· < ·) := by
  induction hp with
  | base c hc he => simp
  | next c hc path hp ih =>
    rw [List.map_append]
    apply List.pairwise_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    have he : b = SourceLocalization.value q c := by simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hb
    subst b
    exact (hp.bound d hd).trans_lt (SourceFinePredecessor.predecessor_spec q c hc).2.2

theorem FinePath.end {q c : Nat} {path : List Nat} (hp : FinePath q c path) :
    ∃ pre, path = pre ++ [c] := by
  cases hp with
  | base c hc he => exact ⟨[], rfl⟩
  | next c hc path hp => exact ⟨path, rfl⟩

theorem FinePath.start {q c : Nat} {path : List Nat} (hp : FinePath q c path) :
    ∃ b tail, path = b :: tail ∧ SourceLocalization.value q b = NativeContext.base q := by
  induction hp with
  | base c hc he => exact ⟨c, [], rfl, he⟩
  | next c hc path hp ih =>
    obtain ⟨b, tail, he, hb⟩ := ih
    exact ⟨b, tail ++ [c], by rw [he]; rfl, hb⟩

theorem run_path (q c n : Nat) (hc : SourceLocalization.Node q c)
    (hh : haltCheck q c n = true)
    (hb : ∀ k < n, SourceFinePredecessor.inputCheck q (iterate q c k) = true) :
    FinePath q c (word q c n) := by
  revert c
  induction n with
  | zero =>
    intro c hc hh hb
    exact .base c hc ((haltCheck_exact q c 0 hc).mp hh)
  | succ n ih =>
    intro c hc hh hb
    have hi : SourceFinePredecessor.inputCheck q c = true := by simpa only [iterate_zero] using hb 0 (Nat.succ_pos n)
    have hs : step q c = SourceFinePredecessor.predecessorCode q c := by simp only [step, hi, Bool.cond_true]
    have hhalt : haltCheck q (step q c) n = true := by simpa only [haltCheck, iterate_shift] using hh
    have hbefore : ∀ k < n, SourceFinePredecessor.inputCheck q (iterate q (step q c) k) = true := by
      intro k hk
      rw [iterate_shift]
      exact hb (k + 1) (Nat.succ_lt_succ hk)
    have hp := ih (step q c) (step_node q c hc) hhalt hbefore
    rw [word_succ]
    exact .next c hi _ (by simpa only [hs] using hp)

def evaluation (input : Nat) : Part Nat := cond (SourceLocalization.inputCheck input.unpair.1 input.unpair.2)
  ((search input).map (fun n => Encodable.encode (word input.unpair.1 input.unpair.2 n))) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have hguard := SourceLocalization.inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hword : Primrec₂ (fun input n => Encodable.encode (word input.unpair.1 input.unpair.2 n)) :=
    (Primrec.encode.comp (word_primrec.comp ((Primrec.unpair.comp Primrec.fst).pair Primrec.snd))).to₂
  exact Partrec.cond hguard.to_comp (search_partrec.map hword.to_comp) Partrec.none

def fineLocalization (q c : Nat) : Part Nat := evaluation (Nat.pair q c)

theorem fineLocalization_partrec : Partrec₂ fineLocalization :=
  (evaluation_partrec.comp Primrec₂.natPair.to_comp).to₂

theorem fineLocalization_domain (q c : Nat) : (fineLocalization q c).Dom ↔
    SourceLocalization.inputCheck q c = true := by
  cases h : SourceLocalization.inputCheck q c with
  | false => simp [fineLocalization, evaluation, Nat.unpair_pair, h, Part.none]
  | true =>
    have hd := search_domain q c ((SourceLocalization.inputCheck_exact q c).mp h)
    simp only [fineLocalization, evaluation, Nat.unpair_pair, h, Bool.cond_true]
    change (search (Nat.pair q c)).Dom ↔ true = true
    exact ⟨fun _ => rfl, fun _ => hd⟩

theorem fineLocalization_source (q c output : Nat) (ho : output ∈ fineLocalization q c) :
    SourceLocalization.inputCheck q c = true ∧ ∃ n, n ∈ search (Nat.pair q c) ∧
      output = Encodable.encode (word q c n) ∧ FinePath q c (word q c n) := by
  have hc := (fineLocalization_domain q c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  have hm : output ∈ (search (Nat.pair q c)).map (fun n => Encodable.encode (word q c n)) := by
    simpa only [fineLocalization, evaluation, Nat.unpair_pair, hc, Bool.cond_true] using ho
  obtain ⟨n, hn, he⟩ := (Part.mem_map_iff _).mp hm
  exact ⟨hc, n, hn, he.symm, run_path q c n ((SourceLocalization.inputCheck_exact q c).mp hc)
    (search_halt q c n hn) (search_before q c n hn)⟩

theorem fineLocalization_unique (q c : Nat) (hc : SourceLocalization.inputCheck q c = true) :
    ∃! output, output ∈ fineLocalization q c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((fineLocalization_domain q c).mpr hc)
  exact ⟨output, ho, fun value hv => Part.mem_unique hv ho⟩

/-- The real base input executes its one-node path, with no predecessor
step and no requirement on its numerical source spelling. -/
theorem fineLocalization_base (q c : Nat) (hc : SourceLocalization.Node q c)
    (hb : SourceLocalization.value q c = NativeContext.base q) :
    fineLocalization q c = Part.some (Encodable.encode ([c] : List Nat)) := by
  have hg := (SourceLocalization.inputCheck_exact q c).mpr hc
  simp only [fineLocalization, evaluation, Nat.unpair_pair, hg, Bool.cond_true]
  apply Part.eq_some_iff.mpr
  apply (Part.mem_map_iff _).mpr
  exact ⟨0, search_zero q c hc hb, by rw [word_zero]⟩

/-- Strictly above-base inputs have at least one real predecessor step.
The base input itself is intentionally included in the execution domain. -/
theorem fineLocalization_nontrivial (q c output : Nat) (ho : output ∈ fineLocalization q c)
    (hproper : SourceFinePredecessor.inputCheck q c = true) :
    ∃ n, output = Encodable.encode (word q c n) ∧ 2 ≤ (word q c n).length := by
  obtain ⟨hc, n, hn, he, hp⟩ := fineLocalization_source q c output ho
  have hpos : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    have hh := search_halt q c n hn
    simp only [hz, haltCheck, iterate_zero, hproper, Bool.not_true, Bool.false_eq_true] at hh
  exact ⟨n, he, by rw [word_length]; omega⟩

def runCheck (q c n : Nat) : Bool := SourceLocalization.inputCheck q c && (haltCheck q c n &&
  (List.range n).all (fun k => SourceFinePredecessor.inputCheck q (iterate q c k)))

theorem runCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => runCheck p.1.1 p.1.2 p.2) := by
  have ht : Primrec₂ (fun p : (Nat × Nat) × Nat => fun k : Nat =>
      SourceFinePredecessor.inputCheck p.1.1 (iterate p.1.1 p.1.2 k)) :=
    (SourceFinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (iterate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂
  have hall := (SourceOne.Comparison.Effective.listAll_primrec _ ht).comp Primrec.id
    (Primrec.list_range.comp Primrec.snd)
  exact Primrec.and.comp (SourceLocalization.inputCheck_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) (Primrec.and.comp haltCheck_primrec hall)

theorem runCheck_exact (q c n : Nat) : runCheck q c n = true ↔
    SourceLocalization.inputCheck q c = true ∧ n ∈ search (Nat.pair q c) := by
  simp only [runCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  rw [search, Nat.mem_rfind]
  simp only [Nat.unpair_pair, Part.mem_some_iff]
  have he : haltCheck q c n = true ↔ true = haltCheck q c n := eq_comm
  rw [← he]
  apply and_congr_right
  intro hc
  apply and_congr_right
  intro hn
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  cases h : SourceFinePredecessor.inputCheck q (iterate q c k) <;> simp [haltCheck, h]

def graphCertificate (q c n output : Nat) : Bool := runCheck q c n &&
  (output == Encodable.encode (word q c n))

theorem graphCertificate_primrec : Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
    graphCertificate p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp (runCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (Primrec.encode.comp (word_primrec.comp Primrec.fst)))

theorem fineLocalization_graph_iff (q c output : Nat) : output ∈ fineLocalization q c ↔
    ∃ n, graphCertificate q c n output = true := by
  constructor
  · intro ho
    obtain ⟨hc, n, hn, he, hp⟩ := fineLocalization_source q c output ho
    exact ⟨n, Bool.and_eq_true.mpr ⟨(runCheck_exact q c n).mpr ⟨hc, hn⟩,
      by simpa only [beq_iff_eq] using he⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨hr, he⟩ := Bool.and_eq_true.mp hn
    obtain ⟨hc, hs⟩ := (runCheck_exact q c n).mp hr
    have hv : output = Encodable.encode (word q c n) := by simpa only [beq_iff_eq] using he
    simp only [fineLocalization, evaluation, Nat.unpair_pair, hc, Bool.cond_true]
    apply (Part.mem_map_iff _).mpr
    exact ⟨n, hs, hv.symm⟩


end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization
