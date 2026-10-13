import Alexander313.Wilken.HereditaryFinePredecessor

/-!
# Executing ordinally terminating fine localization

The actual fine predecessor is iterated until its value is the relative base.
The base test uses the proved original comparator, not equality of native
spellings. Strict ordinal decrease proves termination by ordinal well-foundedness.
An actual natural rfind locates the first halt; no primitive-recursive global
iteration bound is asserted. Every finite run and its encoded native word has
a primitive-recursive certificate. The fresh weak-normal P_0 VALUE-set bridge
supports the predecessor recurrence without asserting parameter-support or
alternate-spelling invariance. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization

def step (r c : Nat) : Nat := cond (FinePredecessor.inputCheck r c)
  (FinePredecessor.predecessorCode r c) c

theorem step_primrec : Primrec₂ step :=
  (FinePredecessor.inputCheck_primrec.cond FinePredecessor.predecessorCode_primrec Primrec.snd).to₂

theorem step_node (r c : Nat) (hc : Localization.Node r c) : Localization.Node r (step r c) := by
  cases h : FinePredecessor.inputCheck r c with
  | false => simpa only [step, h, Bool.cond_false] using hc
  | true => simpa only [step, h, Bool.cond_true] using (FinePredecessor.predecessor_spec r c h).1

def iterate (r c : Nat) : Nat → Nat
  | 0 => c
  | n + 1 => step r (iterate r c n)

theorem iterate_primrec : Primrec (fun p : (Nat × Nat) × Nat => iterate p.1.1 p.1.2 p.2) := by
  have hs : Primrec₂ (fun p : Nat × Nat => fun s : Nat × Nat => step p.1 s.2) :=
    (step_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.nat_rec Primrec.snd hs

@[simp] theorem iterate_zero (r c : Nat) : iterate r c 0 = c := rfl

@[simp] theorem iterate_succ (r c n : Nat) : iterate r c (n + 1) = step r (iterate r c n) := rfl

theorem iterate_shift (r c n : Nat) : iterate r (step r c) n = iterate r c (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate_succ, ih]

theorem iterate_node (r c n : Nat) (hc : Localization.Node r c) : Localization.Node r (iterate r c n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact step_node r _ ih

def haltCheck (r c n : Nat) : Bool := !FinePredecessor.inputCheck r (iterate r c n)

theorem haltCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => haltCheck p.1.1 p.1.2 p.2) :=
  Primrec.not.comp (FinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) iterate_primrec)

theorem haltCheck_exact (r c n : Nat) (hc : Localization.Node r c) : haltCheck r c n = true ↔
    Localization.value r (iterate r c n) = finiteBase r := by
  have hn := iterate_node r c n hc
  have hb : finiteBase r ≤ Localization.value r (iterate r c n) := by
    simpa only [Localization.baseRaw_value] using Localization.baseRaw_le r _ hn
  have hi := FinePredecessor.inputCheck_exact r (iterate r c n)
  cases h : FinePredecessor.inputCheck r (iterate r c n) with
  | true =>
    have hl := (hi.mp h).2
    simp [haltCheck, h, ne_of_gt hl]
  | false =>
    have he : Localization.value r (iterate r c n) = finiteBase r := by
      apply le_antisymm ?_ hb
      apply le_of_not_gt
      intro hl
      have ht := hi.mpr ⟨hn, hl⟩
      simp only [h, Bool.false_eq_true] at ht
    simp only [haltCheck, h, Bool.not_false, he]

/-- Termination is derived from real strict ordinal decrease; its witness
is not a supplied bound and is not asserted primitive recursive. -/
theorem halt_exists (r c : Nat) (hc : Localization.Node r c) : ∃ n, haltCheck r c n = true := by
  have h : ∀ c, Localization.Node r c → ∃ n, haltCheck r c n = true := by
    intro c
    refine (InvImage.wf (Localization.value r) Ordinal.lt_wf).induction c ?_
    intro d ih hd
    by_cases hb : finiteBase r < Localization.value r d
    · have hi := (FinePredecessor.inputCheck_exact r d).mpr ⟨hd, hb⟩
      have hs := FinePredecessor.predecessor_spec r d hi
      have hstep : step r d = FinePredecessor.predecessorCode r d := by simp only [step, hi, Bool.cond_true]
      obtain ⟨n, hn⟩ := ih (step r d) (by simpa only [hstep] using hs.2.2) (step_node r d hd)
      refine ⟨n + 1, ?_⟩
      simpa only [haltCheck, iterate_shift] using hn
    · have hbase : Localization.value r d = finiteBase r := le_antisymm (le_of_not_gt hb)
        (by simpa only [Localization.baseRaw_value] using Localization.baseRaw_le r d hd)
      exact ⟨0, (haltCheck_exact r d 0 hd).mpr hbase⟩
  exact h c hc

def search (input : Nat) : Part Nat := Nat.rfind (fun n =>
  Part.some (haltCheck input.unpair.1 input.unpair.2 n))

theorem search_partrec : Partrec search := by
  have h : Primrec₂ (fun input n => haltCheck input.unpair.1 input.unpair.2 n) :=
    (haltCheck_primrec.comp ((Primrec.unpair.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Partrec.rfind h.to_comp.partrec₂

theorem search_domain (r c : Nat) (hc : Localization.Node r c) : (search (Nat.pair r c)).Dom := by
  obtain ⟨n, hn⟩ := halt_exists r c hc
  rw [search, Nat.rfind_dom]
  refine ⟨n, ?_, fun m hm => Part.some_dom _⟩
  simpa only [Nat.unpair_pair, Part.mem_some_iff] using hn.symm

theorem search_halt (r c n : Nat) (hn : n ∈ search (Nat.pair r c)) : haltCheck r c n = true := by
  have h := Nat.rfind_spec hn
  simpa only [Nat.unpair_pair, Part.mem_some_iff, eq_comm] using h

theorem search_before (r c n : Nat) (hn : n ∈ search (Nat.pair r c)) :
    ∀ k < n, FinePredecessor.inputCheck r (iterate r c k) = true := by
  intro k hk
  have h := Nat.rfind_min hn hk
  have hf : haltCheck r c k = false := by
    simpa only [Nat.unpair_pair, Part.mem_some_iff, eq_comm] using h
  cases hi : FinePredecessor.inputCheck r (iterate r c k) <;> simp_all only [haltCheck, Bool.not_false,
    Bool.not_true, Bool.true_eq_false]

def word (r c n : Nat) : List Nat := (List.range (n + 1)).reverse.map (iterate r c)

theorem word_primrec : Primrec (fun p : (Nat × Nat) × Nat => word p.1.1 p.1.2 p.2) := by
  have hl := Primrec.list_reverse.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
  have hm : Primrec₂ (fun p : (Nat × Nat) × Nat => fun k : Nat => iterate p.1.1 p.1.2 k) :=
    (iterate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Primrec.list_map hl hm

@[simp] theorem word_zero (r c : Nat) : word r c 0 = [c] := rfl

theorem word_succ (r c n : Nat) : word r c (n + 1) = word r (step r c) n ++ [c] := by
  rw [word, List.range_succ_eq_map, List.reverse_cons, List.reverse_map, List.map_append, List.map_map]
  simp only [Function.comp_def, ← iterate_shift, List.map_cons, List.map_nil, iterate_zero, word]

theorem word_length (r c n : Nat) : (word r c n).length = n + 1 := by
  simp only [word, List.length_map, List.length_reverse, List.length_range]

/-- The literal iterated fine-predecessor recurrence. Base spellings need
not equal the particular written baseRaw node. -/
inductive FinePath (r : Nat) : Nat → List Nat → Prop
  | base (c : Nat) (hc : Localization.Node r c) (he : Localization.value r c = finiteBase r) : FinePath r c [c]
  | next (c : Nat) (hc : FinePredecessor.inputCheck r c = true) (path : List Nat)
      (hp : FinePath r (FinePredecessor.predecessorCode r c) path) : FinePath r c (path ++ [c])

theorem FinePath.nodes {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    ∀ d ∈ path, Localization.Node r d := by
  induction hp with
  | base c hc he => intro d hd; simpa only [List.mem_singleton.mp hd] using hc
  | next c hc path hp ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih d hd
    · have he := List.mem_singleton.mp hd
      subst d
      exact ((FinePredecessor.inputCheck_exact r c).mp hc).1

theorem FinePath.bound {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    ∀ d ∈ path, Localization.value r d ≤ Localization.value r c := by
  induction hp with
  | base c hc he => intro d hd; rw [List.mem_singleton.mp hd]
  | next c hc path hp ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (ih d hd).trans (FinePredecessor.predecessor_spec r c hc).2.2.le
    · rw [List.mem_singleton.mp hd]

theorem FinePath.strict {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    (path.map (Localization.value r)).Pairwise (· < ·) := by
  induction hp with
  | base c hc he => simp
  | next c hc path hp ih =>
    rw [List.map_append]
    apply List.pairwise_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    have he : b = Localization.value r c := by simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hb
    subst b
    exact (hp.bound d hd).trans_lt (FinePredecessor.predecessor_spec r c hc).2.2

theorem FinePath.end {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    ∃ pre, path = pre ++ [c] := by
  cases hp with
  | base c hc he => exact ⟨[], rfl⟩
  | next c hc path hp => exact ⟨path, rfl⟩

theorem FinePath.start {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    ∃ b tail, path = b :: tail ∧ Localization.value r b = finiteBase r := by
  induction hp with
  | base c hc he => exact ⟨c, [], rfl, he⟩
  | next c hc path hp ih =>
    obtain ⟨b, tail, he, hb⟩ := ih
    exact ⟨b, tail ++ [c], by rw [he]; rfl, hb⟩

theorem run_path (r c n : Nat) (hc : Localization.Node r c)
    (hh : haltCheck r c n = true)
    (hb : ∀ k < n, FinePredecessor.inputCheck r (iterate r c k) = true) :
    FinePath r c (word r c n) := by
  revert c
  induction n with
  | zero =>
    intro c hc hh hb
    exact .base c hc ((haltCheck_exact r c 0 hc).mp hh)
  | succ n ih =>
    intro c hc hh hb
    have hi : FinePredecessor.inputCheck r c = true := by simpa only [iterate_zero] using hb 0 (Nat.succ_pos n)
    have hs : step r c = FinePredecessor.predecessorCode r c := by simp only [step, hi, Bool.cond_true]
    have hhalt : haltCheck r (step r c) n = true := by simpa only [haltCheck, iterate_shift] using hh
    have hbefore : ∀ k < n, FinePredecessor.inputCheck r (iterate r (step r c) k) = true := by
      intro k hk
      rw [iterate_shift]
      exact hb (k + 1) (Nat.succ_lt_succ hk)
    have hp := ih (step r c) (step_node r c hc) hhalt hbefore
    rw [word_succ]
    exact .next c hi _ (by simpa only [hs] using hp)

def evaluation (input : Nat) : Part Nat := cond (FinePredecessor.inputCheck input.unpair.1 input.unpair.2)
  ((search input).map (fun n => Encodable.encode (word input.unpair.1 input.unpair.2 n))) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have hguard := FinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hword : Primrec₂ (fun input n => Encodable.encode (word input.unpair.1 input.unpair.2 n)) :=
    (Primrec.encode.comp (word_primrec.comp ((Primrec.unpair.comp Primrec.fst).pair Primrec.snd))).to₂
  exact Partrec.cond hguard.to_comp (search_partrec.map hword.to_comp) Partrec.none

def fineLocalization (r c : Nat) : Part Nat := evaluation (Nat.pair r c)

theorem fineLocalization_partrec : Partrec₂ fineLocalization :=
  (evaluation_partrec.comp Primrec₂.natPair.to_comp).to₂

theorem fineLocalization_domain (r c : Nat) : (fineLocalization r c).Dom ↔
    FinePredecessor.inputCheck r c = true := by
  cases h : FinePredecessor.inputCheck r c with
  | false => simp [fineLocalization, evaluation, Nat.unpair_pair, h, Part.none]
  | true =>
    have hd := search_domain r c ((FinePredecessor.inputCheck_exact r c).mp h).1
    simp only [fineLocalization, evaluation, Nat.unpair_pair, h, Bool.cond_true]
    change (search (Nat.pair r c)).Dom ↔ true = true
    exact ⟨fun _ => rfl, fun _ => hd⟩

theorem fineLocalization_source (r c output : Nat) (ho : output ∈ fineLocalization r c) :
    FinePredecessor.inputCheck r c = true ∧ ∃ n, n ∈ search (Nat.pair r c) ∧
      output = Encodable.encode (word r c n) ∧ FinePath r c (word r c n) := by
  have hc := (fineLocalization_domain r c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  have hm : output ∈ (search (Nat.pair r c)).map (fun n => Encodable.encode (word r c n)) := by
    simpa only [fineLocalization, evaluation, Nat.unpair_pair, hc, Bool.cond_true] using ho
  obtain ⟨n, hn, he⟩ := (Part.mem_map_iff _).mp hm
  exact ⟨hc, n, hn, he.symm, run_path r c n ((FinePredecessor.inputCheck_exact r c).mp hc).1
    (search_halt r c n hn) (search_before r c n hn)⟩

theorem fineLocalization_unique (r c : Nat) (hc : FinePredecessor.inputCheck r c = true) :
    ∃! output, output ∈ fineLocalization r c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((fineLocalization_domain r c).mpr hc)
  exact ⟨output, ho, fun value hv => Part.mem_unique hv ho⟩

theorem fineLocalization_nontrivial (r c output : Nat) (ho : output ∈ fineLocalization r c) :
    ∃ n, output = Encodable.encode (word r c n) ∧ 2 ≤ (word r c n).length := by
  obtain ⟨hc, n, hn, he, hp⟩ := fineLocalization_source r c output ho
  have hpos : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    have hh := search_halt r c n hn
    simp only [hz, haltCheck, iterate_zero, hc, Bool.not_true, Bool.false_eq_true] at hh
  exact ⟨n, he, by rw [word_length]; omega⟩

def runCheck (r c n : Nat) : Bool := FinePredecessor.inputCheck r c && (haltCheck r c n &&
  (List.range n).all (fun k => FinePredecessor.inputCheck r (iterate r c k)))

theorem runCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => runCheck p.1.1 p.1.2 p.2) := by
  have ht : Primrec₂ (fun p : (Nat × Nat) × Nat => fun k : Nat =>
      FinePredecessor.inputCheck p.1.1 (iterate p.1.1 p.1.2 k)) :=
    (FinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (iterate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂
  have hall := (SourceOne.Comparison.Effective.listAll_primrec _ ht).comp Primrec.id
    (Primrec.list_range.comp Primrec.snd)
  exact Primrec.and.comp (FinePredecessor.inputCheck_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) (Primrec.and.comp haltCheck_primrec hall)

theorem runCheck_exact (r c n : Nat) : runCheck r c n = true ↔
    FinePredecessor.inputCheck r c = true ∧ n ∈ search (Nat.pair r c) := by
  simp only [runCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  rw [search, Nat.mem_rfind]
  simp only [Nat.unpair_pair, Part.mem_some_iff]
  have he : haltCheck r c n = true ↔ true = haltCheck r c n := eq_comm
  rw [← he]
  apply and_congr_right
  intro hc
  apply and_congr_right
  intro hn
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  cases h : FinePredecessor.inputCheck r (iterate r c k) <;> simp [haltCheck, h]

def graphCertificate (r c n output : Nat) : Bool := runCheck r c n &&
  (output == Encodable.encode (word r c n))

theorem graphCertificate_primrec : Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
    graphCertificate p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp (runCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (Primrec.encode.comp (word_primrec.comp Primrec.fst)))

theorem fineLocalization_graph_iff (r c output : Nat) : output ∈ fineLocalization r c ↔
    ∃ n, graphCertificate r c n output = true := by
  constructor
  · intro ho
    obtain ⟨hc, n, hn, he, hp⟩ := fineLocalization_source r c output ho
    exact ⟨n, Bool.and_eq_true.mpr ⟨(runCheck_exact r c n).mpr ⟨hc, hn⟩,
      by simpa only [beq_iff_eq] using he⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨hr, he⟩ := Bool.and_eq_true.mp hn
    obtain ⟨hc, hs⟩ := (runCheck_exact r c n).mp hr
    have hv : output = Encodable.encode (word r c n) := by simpa only [beq_iff_eq] using he
    simp only [fineLocalization, evaluation, Nat.unpair_pair, hc, Bool.cond_true]
    apply (Part.mem_map_iff _).mpr
    exact ⟨n, hs, hv.symm⟩

def rawFineLocalization (r c : Nat) : Part Nat := cond (FinePredecessor.rawInputCheck r c)
  (fineLocalization r (Theta.Normalization.normalizeCode r c)) Part.none

theorem rawFineLocalization_partrec : Partrec₂ rawFineLocalization :=
  (Partrec.cond FinePredecessor.rawInputCheck_primrec.to_comp
    (fineLocalization_partrec.comp Primrec.fst.to_comp
      Theta.Normalization.Effective.normalizeCode_primrec.to_comp) Partrec.none).to₂

theorem rawFineLocalization_domain (r c : Nat) : (rawFineLocalization r c).Dom ↔
    FinePredecessor.rawInputCheck r c = true := by
  cases h : FinePredecessor.rawInputCheck r c with
  | false => simp [rawFineLocalization, h, Part.none]
  | true => simp only [rawFineLocalization, h, Bool.cond_true, fineLocalization_domain,
      FinePredecessor.raw_normalized_input r c h]

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization
