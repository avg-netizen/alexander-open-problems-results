import Alexander313.Wilken.HereditaryEvaluationFinalComponentSupport

/-!
# The actual final normal-form component of Definition3.35

The visible beta<=previous branch returns its printed singleton. Otherwise
the genuine principal logarithm computes beta's canonical reduced MNF;
its first factor enters the actual relative assignment. The real second
factor is appended exactly when the printed epsilon/strict-floor/mu-cover
test holds. Independent global Tracking derives every caller and proves
termination of this concrete final component. No factor word, LOW code,
block caller or output component is supplied to that global theorem.
Common height, lexical descent and recursive evaluation remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponent

open Support GlobalTrackingSequences EvaluationRelativeCallers
open GlobalTrackingSequences.RecognitionSupport (coverCheck coverCheck_primrec coverCheck_exact)
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem list_isEmpty_primrec)

def firstCode (word : List Nat) : Nat := (word.head?).getD MultiplicativeNormalForm.oneCode
def secondCode (word : List Nat) : Nat := firstCode word.tail

theorem firstCode_primrec : Primrec firstCode :=
  Primrec.option_getD.comp Primrec.list_head? (Primrec.const _)

theorem secondCode_primrec : Primrec secondCode := firstCode_primrec.comp Primrec.list_tail

def appendCheck (gamma : Nat) (word : List Nat) : Bool := !word.tail.isEmpty &&
  (GlobalMuDictionary.Support.inputCheck (firstCode word) &&
    (Canonical.less gamma (firstCode word) && coverCheck (firstCode word) (secondCode word)))

theorem appendCheck_primrec : Primrec₂ appendCheck := by
  have hf := firstCode_primrec.comp Primrec.snd
  have hs := secondCode_primrec.comp Primrec.snd
  exact (Primrec.and.comp (Primrec.not.comp (list_isEmpty_primrec.comp
    (Primrec.list_tail.comp Primrec.snd)))
    (Primrec.and.comp (GlobalMuDictionary.Support.inputCheck_primrec.comp hf)
      (Primrec.and.comp (Canonical.Effective.less_primrec.comp Primrec.fst hf)
        (coverCheck_primrec.comp hf hs)))).to₂

theorem appendCheck_two_exact (gamma first second : Nat) (rest : List Nat)
    (hg : Canonical.check gamma = true) (hf : Canonical.check first = true)
    (hs : Canonical.check second = true) :
    appendCheck gamma (first :: second :: rest) = true ↔
      GlobalMuDictionary.Support.inputCheck first = true ∧
        unionInterpretation gamma < unionInterpretation first ∧
          unionInterpretation second ≤ muValue first := by
  simp only [appendCheck, firstCode, secondCode, List.tail_cons, List.head?_cons,
    Option.getD_some, List.isEmpty_cons, Bool.not_false, Bool.true_and,
    Bool.and_eq_true, Canonical.less_exact, hg, hf, true_and,
    coverCheck_exact, hs, true_and]
  tauto

def finish (gamma : Nat) (factors word : List Nat) : List Nat :=
  cond (appendCheck gamma factors) (word ++ [secondCode factors]) word

theorem finish_primrec : Primrec (fun p : (Nat × List Nat) × List Nat => finish p.1.1 p.1.2 p.2) :=
  (appendCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)).cond
    (Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp (secondCode_primrec.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const [])))
    Primrec.snd

def aboveExecute (gamma beta : Nat) : Part (List Nat) :=
  (factors beta).bind fun fs => (blockExecute gamma (firstCode fs)).map (finish gamma fs)

theorem aboveExecute_partrec : Partrec₂ aboveExecute := by
  have hf := factors_partrec.comp Computable.snd
  have hb := blockExecute_partrec.comp (Primrec.fst.comp Primrec.fst).to_comp
    (firstCode_primrec.comp Primrec.snd).to_comp
  have hm : Computable₂ (fun p : (Nat × Nat) × List Nat => fun word : List Nat => finish p.1.1 p.2 word) :=
    (finish_primrec.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp.to₂
  exact (Partrec.bind hf (Partrec.map hb hm).to₂).to₂

def inputCheck (gamma beta : Nat) : Bool := startCheck gamma && PublicTrackingSequences.principalCheck beta

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (startCheck_primrec.comp Primrec.fst)
    (PublicTrackingSequences.principalCheck_primrec.comp Primrec.snd)).to₂

def execute (gamma beta : Nat) : Part (List Nat) := cond (inputCheck gamma beta)
  (cond (Canonical.less gamma beta) (aboveExecute gamma beta) (Part.some [beta])) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond Canonical.Effective.less_primrec.to_comp aboveExecute_partrec
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to_comp.partrec) Partrec.none).to₂

/-- The exact graph preserves all three printed final-component clauses:
singleton beta, actual relative first-factor word, or that word with the
actual second factor appended by the genuine numerical test. -/
theorem execute_clauses (gamma beta : Nat) (out : List Nat) : out ∈ execute gamma beta ↔
    inputCheck gamma beta = true ∧
      ((Canonical.less gamma beta = false ∧ out = [beta]) ∨
        (Canonical.less gamma beta = true ∧ ∃ fs word,
          fs ∈ factors beta ∧ word ∈ blockExecute gamma (firstCode fs) ∧ out = finish gamma fs word)) := by
  constructor
  · intro ho
    have hi : inputCheck gamma beta = true := by
      cases hc : inputCheck gamma beta with
      | true => rfl
      | false =>
        have hn : False := by simpa only [execute, hc, Bool.cond_false, Part.notMem_none] using ho
        exact False.elim hn
    refine ⟨hi, ?_⟩
    cases hc : Canonical.less gamma beta with
    | false =>
      exact Or.inl ⟨hc, by simpa only [execute, hi, hc, Bool.cond_true,
        Bool.cond_false, Part.mem_some_iff] using ho⟩
    | true =>
      have h : out ∈ aboveExecute gamma beta := by
        simpa only [execute, hi, hc, Bool.cond_true] using ho
      obtain ⟨fs, hf, hm⟩ := Part.mem_bind_iff.mp h
      obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hm
      exact Or.inr ⟨hc, fs, word, hf, hw, he.symm⟩
  · rintro ⟨hi, ⟨hc, rfl⟩ | ⟨hc, fs, word, hf, hw, rfl⟩⟩
    · simp only [execute, hi, hc, Bool.cond_true, Bool.cond_false, Part.mem_some_iff]
    · simpa only [execute, hi, hc, Bool.cond_true, aboveExecute] using
        Part.mem_bind hf (Part.mem_map _ hw)

theorem execute_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true)
    (hcover : unionInterpretation gamma < unionInterpretation beta → blockInputCheck gamma beta = true) :
    ∃ out, out ∈ execute gamma beta := by
  have h := Bool.and_eq_true.mp hi
  have hs := (PublicTrackingSequences.principalCheck_exact beta).mp h.2
  cases hc : Canonical.less gamma beta with
  | false => exact ⟨[beta], (execute_clauses gamma beta [beta]).mpr ⟨hi, Or.inl ⟨hc, rfl⟩⟩⟩
  | true =>
    have hgt := (Canonical.less_exact gamma beta).mp hc
    have hprincipal := (Principal.unionPrincipalCheck_exact beta).mpr
      ⟨Canonical.check_original hs.1, hs.2.1, hs.2.2⟩
    obtain ⟨fs, hf⟩ := factors_returns beta hprincipal
    cases fs with
    | nil => exact False.elim (factors_nonempty gamma beta h.1 hgt.2.2 hf)
    | cons first rest =>
      have hb := first_factor_caller gamma beta first rest h.1 (hcover hgt.2.2) hf hgt.2.2
      obtain ⟨word, hw⟩ := blockExecute_returns gamma first hb
      refine ⟨finish gamma (first :: rest) word, (execute_clauses _ _ _).mpr
        ⟨hi, Or.inr ⟨hc, first :: rest, word, hf, ?_, rfl⟩⟩⟩
      simpa only [firstCode, List.head?_cons, Option.getD_some] using hw

def previousCode (codes : List Nat) : Nat :=
  cond (stripLast codes).isEmpty (endpointCode 0) (lastCode (stripLast codes))

theorem previousCode_primrec : Primrec previousCode :=
  (list_isEmpty_primrec.comp stripLast_primrec).cond (Primrec.const _)
    (lastCode_primrec.comp stripLast_primrec)

/-- The independently defined global tracker derives the actual final
MNF component and every recursive relative caller, without an input LOW
representative or a supplied first-factor assignment. -/
theorem global_returns (codes : List Nat) (ht : Tracking codes) :
    ∃ out, out ∈ execute (previousCode codes) (lastCode codes) := by
  have hc := ht.2.1 _ (lastCode_mem codes ht.1)
  have hp := (PublicTrackingSequences.principalCheck_exact _).mpr
    ⟨hc, ht.2.2.2.1, ht.2.2.2.2.1⟩
  by_cases he : stripLast codes = []
  · have hg : startCheck (endpointCode 0) = true := (startCheck_exact _).mpr (Or.inl rfl)
    have hi : inputCheck (endpointCode 0) (lastCode codes) = true := Bool.and_eq_true.mpr ⟨hg, hp⟩
    have hb : 1 ≤ unionInterpretation (lastCode codes) ∧
        unionInterpretation (lastCode codes) ≤ sourceUpsilon (1 : Ordinal.{0}) := by
      simpa only [if_pos he] using ht.2.2.2.2.2
    have hcover : blockInputCheck (endpointCode 0) (lastCode codes) = true := by
      simp only [blockInputCheck, beq_self_eq_true, Bool.cond_true]
      exact (SourceOneRelativeAssignment.inputCheck_exact _).mpr
        ⟨hc, ht.2.2.2.1, ht.2.2.2.2.1,
          hb.2.trans_eq (PublicUpsilonSegment.successor_value 0)⟩
    simpa only [previousCode, he, List.isEmpty_nil, Bool.cond_true] using
      execute_returns _ _ hi (fun _ => hcover)
  · have hg : startCheck (lastCode (stripLast codes)) = true :=
      (startCheck_exact _).mpr (Or.inr (ht.2.2.1.last_mu_input he))
    have hi : inputCheck (lastCode (stripLast codes)) (lastCode codes) = true :=
      Bool.and_eq_true.mpr ⟨hg, hp⟩
    have hem : (stripLast codes).isEmpty = false := List.isEmpty_eq_false_iff.mpr he
    simpa only [previousCode, hem, Bool.cond_false] using
      execute_returns _ _ hi (fun hgt => tracking_final_caller codes ht he hgt.le)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponent
