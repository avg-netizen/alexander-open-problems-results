import Alexander313.Wilken.HereditaryFineLocalization

/-!
# Executing fine-predecessor and fine-localization Programs

Predecessor tags 0/1 execute the literal native/canonical predecessor on
original normal theta-zero roots strictly above the base. Tags 2/3 execute
the native/canonical predecessor of the genuinely normalized original raw
root, with the full original raw guard. Positive input and complete literal
output graphs use the actual finite primitive-recursive routines. Every
column specializes the constructed Program. This does not assert native
spelling uniqueness or fine-predecessor invariance under arbitrary original
spellings. All proof candidates remain uncompiled.

Fine-path tags 0/1 execute the actual normal/raw termination search. Its
domain follows real strict ordinal descent, with no PR iteration bound.
The output is the encoded literal native word, beginning at a base-valued
node and ending at the given normal root, or the genuinely normalized raw
root. Its positive graph executes the search and tests its actual output.
The compiler maps and finite certificate checker are PR; the search is
claimed partial recursive.
-/

namespace Alexander313.HereditaryFineLocalizationProgram

open Wilken.RelativeTerm.Hereditary

def rawCanonicalCode (r c : Nat) : Nat := cond (FinePredecessor.rawInputCheck r c)
  (Localization.emit r (FinePredecessor.rawPredecessorCode r c)) 0

theorem rawCanonicalCode_primrec : Primrec₂ rawCanonicalCode :=
  (FinePredecessor.rawInputCheck_primrec.cond
    (Localization.emit_primrec.comp Primrec.fst FinePredecessor.rawPredecessorCode_primrec)
    (Primrec.const 0)).to₂

theorem rawCanonicalCode_spec (r c : Nat) (hc : FinePredecessor.rawInputCheck r c = true) :
    Canonical.check (rawCanonicalCode r c) = true ∧
      unionInterpretation (rawCanonicalCode r c) = Localization.value r (FinePredecessor.rawPredecessorCode r c) := by
  simpa only [rawCanonicalCode, hc, Bool.cond_true] using
    Localization.emit_spec r _ (FinePredecessor.rawPredecessor_spec r c hc).1

def predecessorOutput (tag r c : Nat) : Nat :=
  cond (tag == 0) (FinePredecessor.predecessorCode r c)
    (cond (tag == 1) (FinePredecessor.canonicalCode r c)
      (cond (tag == 2) (FinePredecessor.rawPredecessorCode r c)
        (cond (tag == 3) (rawCanonicalCode r c) 0)))

theorem predecessorOutput_primrec : Primrec (fun p : Nat × (Nat × Nat) => predecessorOutput p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact (ht 0).cond (FinePredecessor.predecessorCode_primrec.comp hr hc)
    ((ht 1).cond (FinePredecessor.canonicalCode_primrec.comp hr hc)
      ((ht 2).cond (FinePredecessor.rawPredecessorCode_primrec.comp hr hc)
        ((ht 3).cond (rawCanonicalCode_primrec.comp hr hc) (Primrec.const 0))))

def predecessorInput (tag r c : Nat) : Bool := decide (tag ≤ 3) &&
  cond (decide (tag < 2)) (FinePredecessor.inputCheck r c) (FinePredecessor.rawInputCheck r c)

theorem predecessorInput_primrec : Primrec (fun p : Nat × (Nat × Nat) => predecessorInput p.1 p.2.1 p.2.2) :=
  Primrec.and.comp ((Primrec.nat_le.comp Primrec.fst (Primrec.const 3)).decide)
    (((Primrec.nat_lt.comp Primrec.fst (Primrec.const 2)).decide).cond
      (FinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (FinePredecessor.rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem predecessorInput_exact (tag r c : Nat) : predecessorInput tag r c = true ↔
    tag ≤ 3 ∧ (if tag < 2 then FinePredecessor.inputCheck r c = true else FinePredecessor.rawInputCheck r c = true) := by
  by_cases ht : tag < 2 <;> simp [predecessorInput, ht]

def predecessorInputRaw (query : Nat) : Bool :=
  predecessorInput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

def predecessorOutputRaw (query : Nat) : Nat :=
  predecessorOutput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem predecessorInputRaw_primrec : Primrec predecessorInputRaw :=
  predecessorInput_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem predecessorOutputRaw_primrec : Primrec predecessorOutputRaw :=
  predecessorOutput_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def predecessorEvaluation (query : Nat) : Part Nat :=
  cond (predecessorInputRaw query) (Part.some (predecessorOutputRaw query)) Part.none

theorem predecessorEvaluation_partrec : Partrec predecessorEvaluation :=
  Partrec.cond predecessorInputRaw_primrec.to_comp predecessorOutputRaw_primrec.to_comp.partrec Partrec.none

theorem predecessorProgram_exists : ∃ p : Program, ∀ query, p.eval query = predecessorEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp predecessorEvaluation_partrec)

noncomputable def predecessorProgram : Program := Classical.choose predecessorProgram_exists

theorem predecessorProgram_eval (tag r c : Nat) : predecessorProgram.eval (Nat.pair tag (Nat.pair r c)) =
    cond (predecessorInput tag r c) (Part.some (predecessorOutput tag r c)) Part.none := by
  simpa only [predecessorEvaluation, predecessorInputRaw, predecessorOutputRaw, Nat.unpair_pair] using
    Classical.choose_spec predecessorProgram_exists (Nat.pair tag (Nat.pair r c))

theorem predecessorProgram_domain (tag r c : Nat) : predecessorProgram.domain (Nat.pair tag (Nat.pair r c)) ↔
    predecessorInput tag r c = true := by
  rw [Program.domain, predecessorProgram_eval]
  cases h : predecessorInput tag r c <;> simp [h]

theorem predecessorProgram_graph (tag r c d : Nat) : d ∈ predecessorProgram.eval (Nat.pair tag (Nat.pair r c)) ↔
    predecessorInput tag r c = true ∧ d = predecessorOutput tag r c := by
  rw [predecessorProgram_eval]
  cases h : predecessorInput tag r c <;> simp [h]

noncomputable def predecessorColumn (tag r : Nat) : Program := (predecessorProgram.column tag).column r

theorem predecessorColumn_primrec : Primrec₂ predecessorColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const predecessorProgram) Primrec.fst) Primrec.snd).to₂

theorem predecessorColumn_eval (tag r c : Nat) : (predecessorColumn tag r).eval c =
    cond (predecessorInput tag r c) (Part.some (predecessorOutput tag r c)) Part.none := by
  simp only [predecessorColumn, Nat.Partrec.Code.eval_curry, predecessorProgram_eval]

theorem predecessorColumn_domain (tag r c : Nat) : (predecessorColumn tag r).domain c ↔
    predecessorInput tag r c = true := by
  rw [predecessorColumn, Program.column_domain, Program.column_domain]
  exact predecessorProgram_domain tag r c

theorem predecessorColumn_graph (tag r c d : Nat) : d ∈ (predecessorColumn tag r).eval c ↔
    predecessorInput tag r c = true ∧ d = predecessorOutput tag r c := by
  simp only [predecessorColumn, Nat.Partrec.Code.eval_curry]
  exact predecessorProgram_graph tag r c d

theorem predecessorColumn_unique (tag r c : Nat) (hc : predecessorInput tag r c = true) :
    ∃! d, d ∈ (predecessorColumn tag r).eval c := by
  refine ⟨predecessorOutput tag r c, (predecessorColumn_graph tag r c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro d hd
  exact ((predecessorColumn_graph tag r c d).mp hd).2

theorem nativePredecessorColumn_eval (r c : Nat) : (predecessorColumn 0 r).eval c = FinePredecessor.predecessor r c := by
  simp only [predecessorColumn_eval, predecessorInput, predecessorOutput, FinePredecessor.predecessor]
  simp

theorem normalPredecessorColumn_domain (tag r c : Nat) (ht : tag < 2) :
    (predecessorColumn tag r).domain c ↔ Localization.Node r c ∧ finiteBase r < Localization.value r c := by
  rw [predecessorColumn_domain, predecessorInput_exact]
  have hb : tag ≤ 3 := by omega
  simp only [hb, if_pos ht, true_and, FinePredecessor.inputCheck_exact]

theorem rawPredecessorColumn_domain (tag r c : Nat) (hl : 2 ≤ tag) (hu : tag ≤ 3) :
    (predecessorColumn tag r).domain c ↔
      (∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true) ∧
        finiteBase r < interpretation r c := by
  rw [predecessorColumn_domain, predecessorInput_exact]
  simp only [hu, if_neg (by omega : ¬tag < 2), true_and, FinePredecessor.rawInputCheck_exact]

theorem predecessorColumn_unknown (tag r c : Nat) (ht : 3 < tag) : ¬ (predecessorColumn tag r).domain c := by
  rw [predecessorColumn_domain, predecessorInput_exact]
  omega

theorem nativePredecessorColumn_value (r c d : Nat) (hd : d ∈ (predecessorColumn 0 r).eval c) :
    Localization.Node r d ∧ finiteBase r ≤ Localization.value r d ∧ Localization.value r d < interpretation r c := by
  rw [nativePredecessorColumn_eval, FinePredecessor.predecessor_graph] at hd
  rw [hd.2]
  exact FinePredecessor.predecessor_spec r c hd.1

theorem canonicalPredecessorColumn_value (r c d : Nat) (hd : d ∈ (predecessorColumn 1 r).eval c) :
    Canonical.check d = true ∧ unionInterpretation d = Localization.value r (FinePredecessor.predecessorCode r c) := by
  have hs := (predecessorColumn_graph 1 r c d).mp hd
  have hi : FinePredecessor.inputCheck r c = true := by simpa [predecessorInput] using hs.1
  have he : d = FinePredecessor.canonicalCode r c := by simpa [predecessorOutput] using hs.2
  rw [he]
  exact FinePredecessor.canonicalCode_spec r c hi

theorem rawNativePredecessorColumn_value (r c d : Nat) (hd : d ∈ (predecessorColumn 2 r).eval c) :
    Localization.Node r d ∧ finiteBase r ≤ Localization.value r d ∧ Localization.value r d < interpretation r c := by
  have hs := (predecessorColumn_graph 2 r c d).mp hd
  have hi : FinePredecessor.rawInputCheck r c = true := by simpa [predecessorInput] using hs.1
  have he : d = FinePredecessor.rawPredecessorCode r c := by simpa [predecessorOutput] using hs.2
  rw [he]
  exact FinePredecessor.rawPredecessor_spec r c hi

theorem rawCanonicalPredecessorColumn_value (r c d : Nat) (hd : d ∈ (predecessorColumn 3 r).eval c) :
    Canonical.check d = true ∧ unionInterpretation d = Localization.value r (FinePredecessor.rawPredecessorCode r c) := by
  have hs := (predecessorColumn_graph 3 r c d).mp hd
  have hi : FinePredecessor.rawInputCheck r c = true := by simpa [predecessorInput] using hs.1
  have he : d = rawCanonicalCode r c := by simpa [predecessorOutput] using hs.2
  rw [he]
  exact rawCanonicalCode_spec r c hi

def predecessorInputEvaluation (query : Nat) : Part Nat :=
  cond (predecessorInputRaw query) (Part.some 0) Part.none

theorem predecessorInputEvaluation_partrec : Partrec predecessorInputEvaluation :=
  Partrec.cond predecessorInputRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem predecessorInputProgram_exists : ∃ p : Program, ∀ query, p.eval query = predecessorInputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp predecessorInputEvaluation_partrec)

noncomputable def predecessorInputProgram : Program := Classical.choose predecessorInputProgram_exists

theorem predecessorInputProgram_domain (tag r c : Nat) :
    predecessorInputProgram.domain (Nat.pair tag (Nat.pair r c)) ↔ predecessorInput tag r c = true := by
  rw [Program.domain, Classical.choose_spec predecessorInputProgram_exists]
  cases h : predecessorInput tag r c <;>
    simp [predecessorInputEvaluation, predecessorInputRaw, Nat.unpair_pair, h]

noncomputable def predecessorInputColumn (tag r : Nat) : Program := (predecessorInputProgram.column tag).column r

theorem predecessorInputColumn_primrec : Primrec₂ predecessorInputColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const predecessorInputProgram) Primrec.fst) Primrec.snd).to₂

theorem predecessorInputColumn_domain (tag r c : Nat) :
    (predecessorInputColumn tag r).domain c ↔ predecessorInput tag r c = true := by
  rw [predecessorInputColumn, Program.column_domain, Program.column_domain]
  exact predecessorInputProgram_domain tag r c

def predecessorGraphRaw (query : Nat) : Bool := predecessorInputRaw query.unpair.1 &&
  query.unpair.2 == predecessorOutputRaw query.unpair.1

theorem predecessorGraphRaw_primrec : Primrec predecessorGraphRaw :=
  Primrec.and.comp (predecessorInputRaw_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
      (predecessorOutputRaw_primrec.comp (Primrec.fst.comp Primrec.unpair)))

def predecessorGraphEvaluation (query : Nat) : Part Nat :=
  cond (predecessorGraphRaw query) (Part.some 0) Part.none

theorem predecessorGraphEvaluation_partrec : Partrec predecessorGraphEvaluation :=
  Partrec.cond predecessorGraphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem predecessorGraphProgram_exists : ∃ p : Program, ∀ query, p.eval query = predecessorGraphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp predecessorGraphEvaluation_partrec)

noncomputable def predecessorGraphProgram : Program := Classical.choose predecessorGraphProgram_exists

theorem predecessorGraphProgram_domain (tag r c d : Nat) :
    predecessorGraphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair r c)) d) ↔
      predecessorInput tag r c = true ∧ d = predecessorOutput tag r c := by
  rw [Program.domain, Classical.choose_spec predecessorGraphProgram_exists]
  simp only [predecessorGraphEvaluation, predecessorGraphRaw, predecessorInputRaw, predecessorOutputRaw, Nat.unpair_pair]
  cases h : predecessorInput tag r c <;> cases he : d == predecessorOutput tag r c <;>
    simp [h, he, ← beq_iff_eq]

noncomputable def predecessorGraphColumn (tag r c : Nat) : Program :=
  predecessorGraphProgram.column (Nat.pair tag (Nat.pair r c))

theorem predecessorGraphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) =>
    predecessorGraphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const predecessorGraphProgram)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem predecessorGraphColumn_domain (tag r c d : Nat) : (predecessorGraphColumn tag r c).domain d ↔
    predecessorInput tag r c = true ∧ d = predecessorOutput tag r c := by
  rw [predecessorGraphColumn, Program.column_domain]
  exact predecessorGraphProgram_domain tag r c d

theorem predecessorGraphColumn_execution (tag r c d : Nat) :
    (predecessorGraphColumn tag r c).domain d ↔ d ∈ (predecessorColumn tag r).eval c :=
  (predecessorGraphColumn_domain tag r c d).trans (predecessorColumn_graph tag r c d).symm

def fineInput (tag r c : Nat) : Bool := cond (tag == 0) (FinePredecessor.inputCheck r c)
  (cond (tag == 1) (FinePredecessor.rawInputCheck r c) false)

theorem fineInput_primrec : Primrec (fun p : Nat × (Nat × Nat) => fineInput p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (FinePredecessor.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (FinePredecessor.rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.const false))

def fineEvaluation (query : Nat) : Part Nat := cond (query.unpair.1 == 0)
  (FineLocalization.fineLocalization query.unpair.2.unpair.1 query.unpair.2.unpair.2)
  (cond (query.unpair.1 == 1)
    (FineLocalization.rawFineLocalization query.unpair.2.unpair.1 query.unpair.2.unpair.2) Part.none)

theorem fineEvaluation_partrec : Partrec fineEvaluation := by
  have hr := (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hc := (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have ht (k : Nat) := (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const k)).to_comp
  exact Partrec.cond (ht 0) (FineLocalization.fineLocalization_partrec.comp hr hc)
    (Partrec.cond (ht 1) (FineLocalization.rawFineLocalization_partrec.comp hr hc) Partrec.none)

theorem fineProgram_exists : ∃ p : Program, ∀ query, p.eval query = fineEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp fineEvaluation_partrec)

noncomputable def fineProgram : Program := Classical.choose fineProgram_exists

theorem fineProgram_eval (tag r c : Nat) : fineProgram.eval (Nat.pair tag (Nat.pair r c)) =
    cond (tag == 0) (FineLocalization.fineLocalization r c)
      (cond (tag == 1) (FineLocalization.rawFineLocalization r c) Part.none) := by
  simpa only [fineEvaluation, Nat.unpair_pair] using
    Classical.choose_spec fineProgram_exists (Nat.pair tag (Nat.pair r c))

theorem fineProgram_domain (tag r c : Nat) : fineProgram.domain (Nat.pair tag (Nat.pair r c)) ↔
    fineInput tag r c = true := by
  rw [Program.domain, fineProgram_eval]
  cases h0 : tag == 0 <;> cases h1 : tag == 1 <;>
    simp [fineInput, h0, h1, FineLocalization.fineLocalization_domain, FineLocalization.rawFineLocalization_domain]

noncomputable def fineColumn (tag r : Nat) : Program := (fineProgram.column tag).column r

theorem fineColumn_primrec : Primrec₂ fineColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const fineProgram) Primrec.fst) Primrec.snd).to₂

theorem fineColumn_eval (tag r c : Nat) : (fineColumn tag r).eval c =
    cond (tag == 0) (FineLocalization.fineLocalization r c)
      (cond (tag == 1) (FineLocalization.rawFineLocalization r c) Part.none) := by
  simp only [fineColumn, Nat.Partrec.Code.eval_curry, fineProgram_eval]

theorem normalFineColumn_eval (r c : Nat) : (fineColumn 0 r).eval c = FineLocalization.fineLocalization r c := by
  simp [fineColumn_eval]

theorem rawFineColumn_eval (r c : Nat) : (fineColumn 1 r).eval c = FineLocalization.rawFineLocalization r c := by
  simp [fineColumn_eval]

theorem fineColumn_domain (tag r c : Nat) : (fineColumn tag r).domain c ↔ fineInput tag r c = true := by
  rw [fineColumn, Program.column_domain, Program.column_domain]
  exact fineProgram_domain tag r c

theorem normalFineColumn_domain (r c : Nat) : (fineColumn 0 r).domain c ↔
    Localization.Node r c ∧ finiteBase r < Localization.value r c := by
  simp only [fineColumn_domain, fineInput, beq_self_eq_true, Bool.cond_true, FinePredecessor.inputCheck_exact]

theorem rawFineColumn_domain (r c : Nat) : (fineColumn 1 r).domain c ↔
    (∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true) ∧
      finiteBase r < interpretation r c := by
  rw [fineColumn_domain]
  simpa [fineInput] using FinePredecessor.rawInputCheck_exact r c

theorem fineColumn_unique (tag r c : Nat) (hc : fineInput tag r c = true) :
    ∃! output, output ∈ (fineColumn tag r).eval c := by
  have hd := (fineColumn_domain tag r c).mpr hc
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp hd
  exact ⟨output, ho, fun d hd => Part.mem_unique hd ho⟩

theorem normalFineColumn_source (r c output : Nat) (ho : output ∈ (fineColumn 0 r).eval c) :
    FinePredecessor.inputCheck r c = true ∧ ∃ n, n ∈ FineLocalization.search (Nat.pair r c) ∧
      output = Encodable.encode (FineLocalization.word r c n) ∧
      FineLocalization.FinePath r c (FineLocalization.word r c n) := by
  rw [normalFineColumn_eval] at ho
  exact FineLocalization.fineLocalization_source r c output ho

theorem rawFineColumn_source (r c output : Nat) (ho : output ∈ (fineColumn 1 r).eval c) :
    FinePredecessor.rawInputCheck r c = true ∧ ∃ n,
      n ∈ FineLocalization.search (Nat.pair r (Theta.Normalization.normalizeCode r c)) ∧
      output = Encodable.encode (FineLocalization.word r (Theta.Normalization.normalizeCode r c) n) ∧
      FineLocalization.FinePath r (Theta.Normalization.normalizeCode r c)
        (FineLocalization.word r (Theta.Normalization.normalizeCode r c) n) := by
  rw [rawFineColumn_eval] at ho
  have hc := (FineLocalization.rawFineLocalization_domain r c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  have hm : output ∈ FineLocalization.fineLocalization r (Theta.Normalization.normalizeCode r c) := by
    simpa only [FineLocalization.rawFineLocalization, hc, Bool.cond_true] using ho
  exact ⟨hc, (FineLocalization.fineLocalization_source r _ output hm).2⟩

theorem normalFineColumn_word (r c : Nat) (path : List Nat)
    (ho : Encodable.encode path ∈ (fineColumn 0 r).eval c) :
    FineLocalization.FinePath r c path ∧ (∀ d ∈ path, Localization.Node r d) ∧
      (path.map (Localization.value r)).Pairwise (· < ·) := by
  obtain ⟨hc, n, hn, he, hp⟩ := normalFineColumn_source r c _ ho
  have hw : path = FineLocalization.word r c n := Encodable.encode_injective he
  rw [hw]
  exact ⟨hp, hp.nodes, hp.strict⟩

private theorem endpoint_append (pre : List Nat) (c : Nat) : Localization.endpoint (pre ++ [c]) = c := by
  induction pre with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => exact ih

theorem normalFineColumn_end (r c : Nat) (path : List Nat)
    (ho : Encodable.encode path ∈ (fineColumn 0 r).eval c) : Localization.endpoint path = c := by
  have hp := (normalFineColumn_word r c path ho).1
  obtain ⟨pre, he⟩ := hp.end
  rw [he, endpoint_append]

theorem normalFineColumn_start (r c : Nat) (path : List Nat)
    (ho : Encodable.encode path ∈ (fineColumn 0 r).eval c) :
    ∃ b tail, path = b :: tail ∧ Localization.value r b = finiteBase r :=
  (normalFineColumn_word r c path ho).1.start

theorem rawFineColumn_end (r c : Nat) (path : List Nat)
    (ho : Encodable.encode path ∈ (fineColumn 1 r).eval c) :
    Localization.value r (Localization.endpoint path) = interpretation r c := by
  obtain ⟨hc, n, hn, he, hp⟩ := rawFineColumn_source r c _ ho
  have hw : path = FineLocalization.word r (Theta.Normalization.normalizeCode r c) n := Encodable.encode_injective he
  obtain ⟨pre, hend⟩ := hp.end
  have ht : checkCode r c = true := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  rw [hw, hend, endpoint_append, Localization.value]
  exact (Theta.Normalization.normalizeCode_checked r c ht).2.2

def fineInputRaw (query : Nat) : Bool := fineInput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem fineInputRaw_primrec : Primrec fineInputRaw :=
  fineInput_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def fineInputEvaluation (query : Nat) : Part Nat := cond (fineInputRaw query) (Part.some 0) Part.none

theorem fineInputEvaluation_partrec : Partrec fineInputEvaluation :=
  Partrec.cond fineInputRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem fineInputProgram_exists : ∃ p : Program, ∀ query, p.eval query = fineInputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp fineInputEvaluation_partrec)

noncomputable def fineInputProgram : Program := Classical.choose fineInputProgram_exists

theorem fineInputProgram_domain (tag r c : Nat) : fineInputProgram.domain (Nat.pair tag (Nat.pair r c)) ↔
    fineInput tag r c = true := by
  rw [Program.domain, Classical.choose_spec fineInputProgram_exists]
  cases h : fineInput tag r c <;> simp [fineInputEvaluation, fineInputRaw, Nat.unpair_pair, h]

noncomputable def fineInputColumn (tag r : Nat) : Program := (fineInputProgram.column tag).column r

theorem fineInputColumn_primrec : Primrec₂ fineInputColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const fineInputProgram) Primrec.fst) Primrec.snd).to₂

theorem fineInputColumn_domain (tag r c : Nat) : (fineInputColumn tag r).domain c ↔ fineInput tag r c = true := by
  rw [fineInputColumn, Program.column_domain, Program.column_domain]
  exact fineInputProgram_domain tag r c

/-- The positive graph executes the actual partial-recursive search and
then compares its returned word. No PR search bound is inferred. -/
def fineGraphEvaluation (query : Nat) : Part Nat := (fineEvaluation query.unpair.1).bind
  (fun output => cond (query.unpair.2 == output) (Part.some 0) Part.none)

theorem fineGraphEvaluation_partrec : Partrec fineGraphEvaluation := by
  have hf := fineEvaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have ht := Primrec.beq.comp ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst) Primrec.snd
  have hg := (Partrec.cond ht.to_comp (Computable.const 0).partrec Partrec.none).to₂
  exact hf.bind hg

theorem fineGraphEvaluation_domain (query : Nat) : (fineGraphEvaluation query).Dom ↔
    query.unpair.2 ∈ fineEvaluation query.unpair.1 := by
  constructor
  · intro hd
    obtain ⟨value, hv⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨output, ho, hm⟩ := Part.mem_bind_iff.mp hv
    cases he : query.unpair.2 == output with
    | false => simp only [he, Bool.cond_false, Part.notMem_none] at hm
    | true => simpa only [(beq_iff_eq.mp he)] using ho
  · intro ho
    apply Part.dom_iff_mem.mpr
    refine ⟨0, Part.mem_bind_iff.mpr ⟨query.unpair.2, ho, ?_⟩⟩
    simp

theorem fineGraphProgram_exists : ∃ p : Program, ∀ query, p.eval query = fineGraphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp fineGraphEvaluation_partrec)

noncomputable def fineGraphProgram : Program := Classical.choose fineGraphProgram_exists

theorem fineGraphProgram_domain (tag r c output : Nat) :
    fineGraphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair r c)) output) ↔
      output ∈ fineProgram.eval (Nat.pair tag (Nat.pair r c)) := by
  rw [Program.domain, Classical.choose_spec fineGraphProgram_exists, fineGraphEvaluation_domain]
  simpa only [Nat.unpair_pair] using
    (show output ∈ fineEvaluation (Nat.pair tag (Nat.pair r c)) ↔
      output ∈ fineProgram.eval (Nat.pair tag (Nat.pair r c)) by
      rw [Classical.choose_spec fineProgram_exists])

noncomputable def fineGraphColumn (tag r c : Nat) : Program :=
  fineGraphProgram.column (Nat.pair tag (Nat.pair r c))

theorem fineGraphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => fineGraphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const fineGraphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem fineGraphColumn_execution (tag r c output : Nat) : (fineGraphColumn tag r c).domain output ↔
    output ∈ (fineColumn tag r).eval c := by
  rw [fineGraphColumn, Program.column_domain, fineGraphProgram_domain]
  simp only [fineColumn, Nat.Partrec.Code.eval_curry]

theorem normalFineGraphColumn_certificate (r c output : Nat) : (fineGraphColumn 0 r c).domain output ↔
    ∃ n, FineLocalization.graphCertificate r c n output = true := by
  rw [fineGraphColumn_execution, normalFineColumn_eval, FineLocalization.fineLocalization_graph_iff]

theorem fineGraphColumn_unique (tag r c : Nat) (hc : fineInput tag r c = true) :
    ∃! output, (fineGraphColumn tag r c).domain output := by
  obtain ⟨output, ho, hu⟩ := fineColumn_unique tag r c hc
  exact ⟨output, (fineGraphColumn_execution tag r c output).mpr ho,
    fun d hd => hu d ((fineGraphColumn_execution tag r c d).mp hd)⟩

end Alexander313.HereditaryFineLocalizationProgram
