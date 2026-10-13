import Alexander313.Wilken.HereditaryFinePredecessorInvariance

/-!
# Derived same-public-base fine-path invariance

The genuine value-determined predecessor aligns every actual FinePath
recurrence by induction, including independently spelled base endpoints.
Finite iterations and the first-halt search agree in values and halt count.
Actual canonical emission gives equal canonical words from equal root
values; native path codes and literal support need not agree.

The executing normal and original raw adapters retain their existing exact
guards. Canonical producers map the actual returned native word through
real per-node canonical emission. The finite maps are PR and the producers
are Partrec, with no primitive-recursive global termination bound. Neither
fine lex order nor a cross-base translation follows just from invariance.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Invariance

open Localization

/-- Any two literal fine recurrences at equal root values have equal VALUE
paths. The theorem takes no support or native spelling equality premise. -/
theorem FinePath.values_eq {r c : Nat} {path : List Nat} (hp : FinePath r c path) :
    ∀ d other, FinePath r d other → value r c = value r d →
      path.map (value r) = other.map (value r) := by
  induction hp with
  | base c hc hb =>
    intro d other hq he
    cases hq with
    | base d hd hbase => simp only [List.map_cons, List.map_nil, he]
    | next d hd other hq =>
      have hproper := ((FinePredecessor.inputCheck_exact r d).mp hd).2
      exact False.elim ((ne_of_gt hproper) (he.symm.trans hb))
  | next c hc path hp ih =>
    intro d other hq he
    cases hq with
    | base d hd hb =>
      have hproper := ((FinePredecessor.inputCheck_exact r c).mp hc).2
      exact False.elim ((ne_of_gt hproper) (he.trans hb))
    | next d hd other hq =>
      have hpred := FinePredecessor.Invariance.predecessorCode_value_eq r c d hc hd he
      have ht := ih (FinePredecessor.predecessorCode r d) other hq hpred
      simp only [List.map_append, List.map_cons, List.map_nil, ht, he]

theorem FinePath.emissions_eq {r c d : Nat} {path other : List Nat}
    (hp : FinePath r c path) (hq : FinePath r d other) (he : value r c = value r d) :
    path.map (emit r) = other.map (emit r) :=
  Localization.Refinements.emit_map_eq_of_values_eq r _ _ hp.nodes hq.nodes
    (hp.values_eq d other hq he)

theorem FinePath.length_eq {r c d : Nat} {path other : List Nat}
    (hp : FinePath r c path) (hq : FinePath r d other) (he : value r c = value r d) :
    path.length = other.length := by
  simpa only [List.length_map] using congrArg List.length (hp.values_eq d other hq he)

theorem step_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : value r (step r c) = value r (step r d) := by
  have hi := FinePredecessor.Invariance.inputCheck_eq r c d hc hd he
  cases h : FinePredecessor.inputCheck r c with
  | false =>
    have hj : FinePredecessor.inputCheck r d = false := hi.symm.trans h
    simpa only [step, h, hj, Bool.cond_false] using he
  | true =>
    have hj : FinePredecessor.inputCheck r d = true := hi.symm.trans h
    simpa only [step, h, hj, Bool.cond_true] using
      FinePredecessor.Invariance.predecessorCode_value_eq r c d h hj he

theorem iterate_value_eq (r c d n : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : value r (iterate r c n) = value r (iterate r d n) := by
  induction n with
  | zero => exact he
  | succ n ih => exact step_value_eq r _ _ (iterate_node r c n hc) (iterate_node r d n hd) ih

theorem haltCheck_eq (r c d n : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : haltCheck r c n = haltCheck r d n := by
  unfold haltCheck
  rw [FinePredecessor.Invariance.inputCheck_eq r _ _
    (iterate_node r c n hc) (iterate_node r d n hd) (iterate_value_eq r c d n hc hd he)]

/-- Equality of the actual first-halt searches is derived pointwise from
the real finite iterations, not from a supplied common length bound. -/
theorem search_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : search (Nat.pair r c) = search (Nat.pair r d) := by
  have hp : (fun n => Part.some (haltCheck r c n)) = (fun n => Part.some (haltCheck r d n)) :=
    funext (fun n => congrArg (fun b : Bool => Part.some b) (haltCheck_eq r c d n hc hd he))
  simpa only [search, Nat.unpair_pair] using congrArg Nat.rfind hp

theorem word_values_eq (r c d n : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : (word r c n).map (value r) = (word r d n).map (value r) := by
  simp only [word, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k hk
  exact iterate_value_eq r c d k hc hd he

theorem word_nodes (r c n : Nat) (hc : Node r c) : ∀ d ∈ word r c n, Node r d := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
  exact iterate_node r c k hc

/-- A finite actual canonical emission map, meaningful on admitted runs. -/
def canonicalWord (r c n : Nat) : List Nat := (word r c n).map (emit r)

theorem canonicalWord_primrec : Primrec (fun p : (Nat × Nat) × Nat => canonicalWord p.1.1 p.1.2 p.2) := by
  have hm : Primrec₂ (fun p : (Nat × Nat) × Nat => fun d : Nat => emit p.1.1 d) :=
    (emit_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  exact Primrec.list_map word_primrec hm

theorem canonicalWord_eq (r c d n : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : canonicalWord r c n = canonicalWord r d n :=
  Localization.Refinements.emit_map_eq_of_values_eq r _ _ (word_nodes r c n hc) (word_nodes r d n hd)
    (word_values_eq r c d n hc hd he)

def decodedWord (output : Nat) : List Nat := (Encodable.decode (List Nat) output).getD []

theorem decodedWord_primrec : Primrec decodedWord :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodedWord_encode (path : List Nat) : decodedWord (Encodable.encode path) = path := by
  simp only [decodedWord, Encodable.encodek, Option.getD_some]

noncomputable def outputValues (r output : Nat) : List Ordinal.{0} := (decodedWord output).map (value r)

def outputWord (r output : Nat) : List Nat := (decodedWord output).map (emit r)

theorem outputWord_primrec : Primrec₂ outputWord := by
  have hm : Primrec₂ (fun p : Nat × Nat => fun d : Nat => emit p.1 d) :=
    (emit_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map (decodedWord_primrec.comp Primrec.snd) hm).to₂

theorem outputValues_eq (r c d output other : Nat)
    (ho : output ∈ fineLocalization r c) (hv : other ∈ fineLocalization r d)
    (he : value r c = value r d) : outputValues r output = outputValues r other := by
  obtain ⟨hc, n, hn, hout, hp⟩ := fineLocalization_source r c output ho
  obtain ⟨hd, m, hm, hother, hq⟩ := fineLocalization_source r d other hv
  simpa only [outputValues, hout, hother, decodedWord_encode] using hp.values_eq d _ hq he

theorem outputWord_eq (r c d output other : Nat)
    (ho : output ∈ fineLocalization r c) (hv : other ∈ fineLocalization r d)
    (he : value r c = value r d) : outputWord r output = outputWord r other := by
  obtain ⟨hc, n, hn, hout, hp⟩ := fineLocalization_source r c output ho
  obtain ⟨hd, m, hm, hother, hq⟩ := fineLocalization_source r d other hv
  simpa only [outputWord, hout, hother, decodedWord_encode] using hp.emissions_eq hq he

private theorem raw_output (r c output : Nat) (ho : output ∈ rawFineLocalization r c) :
    FinePredecessor.rawInputCheck r c = true ∧
      output ∈ fineLocalization r (Theta.Normalization.normalizeCode r c) := by
  have hc := (rawFineLocalization_domain r c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  exact ⟨hc, by simpa only [rawFineLocalization, hc, Bool.cond_true] using ho⟩

private theorem raw_normalized_values (r c d : Nat)
    (hc : FinePredecessor.rawInputCheck r c = true) (hd : FinePredecessor.rawInputCheck r d = true)
    (he : interpretation r c = interpretation r d) :
    value r (Theta.Normalization.normalizeCode r c) = value r (Theta.Normalization.normalizeCode r d) := by
  have hcc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  have hdd := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hd).1).1
  exact (Theta.Normalization.normalizeCode_checked r c hcc).2.2.trans
    (he.trans (Theta.Normalization.normalizeCode_checked r d hdd).2.2.symm)

theorem raw_outputValues_eq (r c d output other : Nat)
    (ho : output ∈ rawFineLocalization r c) (hv : other ∈ rawFineLocalization r d)
    (he : interpretation r c = interpretation r d) : outputValues r output = outputValues r other := by
  have hp := raw_output r c output ho
  have hq := raw_output r d other hv
  exact outputValues_eq r _ _ output other hp.2 hq.2 (raw_normalized_values r c d hp.1 hq.1 he)

theorem raw_outputWord_eq (r c d output other : Nat)
    (ho : output ∈ rawFineLocalization r c) (hv : other ∈ rawFineLocalization r d)
    (he : interpretation r c = interpretation r d) : outputWord r output = outputWord r other := by
  have hp := raw_output r c output ho
  have hq := raw_output r d other hv
  exact outputWord_eq r _ _ output other hp.2 hq.2 (raw_normalized_values r c d hp.1 hq.1 he)

/-- This producer executes the actual fine path and its finite canonical
emission map. The search remains genuinely partial recursive. -/
def canonicalLocalization (r c : Nat) : Part Nat :=
  (fineLocalization r c).map (fun output => Encodable.encode (outputWord r output))

theorem canonicalLocalization_partrec : Partrec₂ canonicalLocalization :=
  (Partrec.map fineLocalization_partrec
    (Primrec.encode.comp (outputWord_primrec.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd)).to_comp.to₂).to₂

theorem canonicalLocalization_domain (r c : Nat) : (canonicalLocalization r c).Dom ↔
    FinePredecessor.inputCheck r c = true := fineLocalization_domain r c

theorem canonicalLocalization_source (r c output : Nat) (ho : output ∈ canonicalLocalization r c) :
    FinePredecessor.inputCheck r c = true ∧ ∃ path, FinePath r c path ∧
      output = Encodable.encode (path.map (emit r)) ∧
      (∀ q ∈ path.map (emit r), Canonical.check q = true) := by
  obtain ⟨native, hn, rfl⟩ := (Part.mem_map_iff _).mp ho
  obtain ⟨hc, n, hh, hout, hp⟩ := fineLocalization_source r c native hn
  refine ⟨hc, word r c n, hp, ?_, ?_⟩
  · simp only [outputWord, hout, decodedWord_encode]
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact (emit_spec r d (hp.nodes d hd)).1

theorem canonicalLocalization_output_eq (r c d output other : Nat)
    (ho : output ∈ canonicalLocalization r c) (hv : other ∈ canonicalLocalization r d)
    (he : value r c = value r d) : output = other := by
  obtain ⟨native, hn, rfl⟩ := (Part.mem_map_iff _).mp ho
  obtain ⟨second, hs, rfl⟩ := (Part.mem_map_iff _).mp hv
  exact congrArg Encodable.encode (outputWord_eq r c d native second hn hs he)

def rawCanonicalLocalization (r c : Nat) : Part Nat :=
  (rawFineLocalization r c).map (fun output => Encodable.encode (outputWord r output))

theorem rawCanonicalLocalization_partrec : Partrec₂ rawCanonicalLocalization :=
  (Partrec.map rawFineLocalization_partrec
    (Primrec.encode.comp (outputWord_primrec.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd)).to_comp.to₂).to₂

theorem rawCanonicalLocalization_domain (r c : Nat) : (rawCanonicalLocalization r c).Dom ↔
    FinePredecessor.rawInputCheck r c = true := rawFineLocalization_domain r c

theorem rawCanonicalLocalization_source (r c output : Nat)
    (ho : output ∈ rawCanonicalLocalization r c) :
    FinePredecessor.rawInputCheck r c = true ∧ ∃ path,
      FinePath r (Theta.Normalization.normalizeCode r c) path ∧
      output = Encodable.encode (path.map (emit r)) ∧
      (∀ q ∈ path.map (emit r), Canonical.check q = true) := by
  obtain ⟨native, hn, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hp := raw_output r c native hn
  have hm : Encodable.encode (outputWord r native) ∈
      canonicalLocalization r (Theta.Normalization.normalizeCode r c) :=
    (Part.mem_map_iff _).mpr ⟨native, hp.2, rfl⟩
  exact ⟨hp.1, (canonicalLocalization_source r _ _ hm).2⟩

theorem rawCanonicalLocalization_output_eq (r c d output other : Nat)
    (ho : output ∈ rawCanonicalLocalization r c) (hv : other ∈ rawCanonicalLocalization r d)
    (he : interpretation r c = interpretation r d) : output = other := by
  obtain ⟨native, hn, rfl⟩ := (Part.mem_map_iff _).mp ho
  obtain ⟨second, hs, rfl⟩ := (Part.mem_map_iff _).mp hv
  exact congrArg Encodable.encode (raw_outputWord_eq r c d native second hn hs he)

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Invariance
