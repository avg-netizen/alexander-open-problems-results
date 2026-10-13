import Alexander313.Wilken.HereditarySourceOneRelativeAssignment
import Alexander313.Wilken.HereditaryMuCoveredRelativeAssignment

/-!
# Actual relative callers of the finite evaluation-length components

The independent global reference supplies every increasing epsilon pair
and original extended-mu cover. Its true first source gap supplies the
initial pair at alpha0=1+upsilon_m: original check zero for m=0 and the
literal endpoint epsilon for m>0. Thus every real component assignment
terminates without a supplied representation, LOW caller or block word.
This does not supply the final MNF branch, a length bound, descent, or o.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationRelativeCallers

open GlobalTrackingSequences
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton stripLast_singleton)
open Hereditary.FinePredecessor (stripLast)

def blockInputCheck (gamma beta : Nat) : Bool := cond (gamma == endpointCode 0)
  (SourceOneRelativeAssignment.inputCheck beta)
  (MuCoveredRelativeAssignment.Support.inputCheck gamma beta)

theorem blockInputCheck_primrec : Primrec₂ blockInputCheck :=
  ((Primrec.beq.comp Primrec.fst (Primrec.const _)).cond
    (SourceOneRelativeAssignment.inputCheck_primrec.comp Primrec.snd)
    MuCoveredRelativeAssignment.Support.inputCheck_primrec).to₂

def blockExecute (gamma beta : Nat) : Part (List Nat) := cond (gamma == endpointCode 0)
  (SourceOneRelativeAssignment.execute beta) (MuCoveredRelativeAssignment.execute gamma beta)

theorem blockExecute_partrec : Partrec₂ blockExecute :=
  (Partrec.cond (Primrec.beq.comp Primrec.fst (Primrec.const _)).to_comp
    (SourceOneRelativeAssignment.execute_partrec.comp Computable.snd)
    MuCoveredRelativeAssignment.execute_partrec).to₂

theorem blockExecute_domain (gamma beta : Nat) :
    (blockExecute gamma beta).Dom ↔ blockInputCheck gamma beta = true := by
  cases h : (gamma == endpointCode 0) <;>
    simp only [blockExecute, blockInputCheck, h, Bool.cond_true, Bool.cond_false,
      SourceOneRelativeAssignment.execute_domain, MuCoveredRelativeAssignment.execute_domain]

theorem blockExecute_returns (gamma beta : Nat) (hi : blockInputCheck gamma beta = true) :
    ∃ out, out ∈ blockExecute gamma beta :=
  Part.dom_iff_mem.mp ((blockExecute_domain gamma beta).mpr hi)

theorem epsilon_not_initial (gamma : Nat)
    (hi : GlobalMuDictionary.Support.inputCheck gamma = true) :
    (gamma == endpointCode 0) = false := by
  cases he : (gamma == endpointCode 0) with
  | false => rfl
  | true =>
    have hc := beq_iff_eq.mp he
    have hl := EpsilonOffsets.epsilon_one_lt
      ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi).2
    rw [hc, PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero] at hl
    exact False.elim (lt_irrefl _ hl)

theorem epsilon_principal (c : Nat) (hi : GlobalMuDictionary.Support.inputCheck c = true) :
    Canonical.check c = true ∧ 0 < unionInterpretation c ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation c) := by
  have hs := (GlobalMuDictionary.Support.inputCheck_exact c).mp hi
  refine ⟨hs.1, zero_lt_one.trans (EpsilonOffsets.epsilon_one_lt hs.2), ?_⟩
  rw [← hs.2]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem reference_tail (a : Nat) (xs : List Nat) (hr : EpsilonReference (a :: xs)) :
    EpsilonReference xs := by
  cases hr with
  | one => exact .nil
  | cons a b xs ha hab hcover ht => exact ht

/-- Every printed increasing adjacent epsilon pair gives the actual
independent relative-assignment caller at its literal previous epsilon. -/
theorem adjacent_caller (a b : Nat) (xs : List Nat)
    (hr : EpsilonReference (a :: b :: xs)) : blockInputCheck a b = true := by
  cases hr with
  | cons a b xs ha hab hcover ht =>
    have hb := epsilon_principal b (ht.nodes b List.mem_cons_self)
    simp only [blockInputCheck, epsilon_not_initial a ha, Bool.cond_false]
    exact (MuCoveredRelativeAssignment.Support.inputCheck_exact a b).mpr
      ⟨ha, hb.1, hb.2.1, hb.2.2, hab.le, hcover⟩

/-- The actual first gap derives the initial source-one or endpoint
caller, including the literal zero-source convention upsilon_0=0. -/
theorem initial_caller (m a : Nat) (xs : List Nat)
    (hr : EpsilonReference (a :: xs)) (hg : TailGap m (a :: xs)) :
    blockInputCheck (endpointCode m) a = true := by
  have ha := epsilon_principal a (hr.nodes a List.mem_cons_self)
  cases m with
  | zero =>
    have hb : unionInterpretation a < sourceUpsilon (1 : Ordinal.{0}) := hg.2
    simp only [blockInputCheck, beq_self_eq_true, Bool.cond_true]
    exact (SourceOneRelativeAssignment.inputCheck_exact a).mpr
      ⟨ha.1, ha.2.1, ha.2.2, hb.le.trans_eq (PublicUpsilonSegment.successor_value 0)⟩
  | succ n =>
    have hi := GlobalMuDictionary.Support.endpoint_input n
    have hfloor : unionInterpretation (endpointCode (n + 1)) ≤ unionInterpretation a := by
      rw [PublicEpsilonSourceDictionary.endpointCode_value,
        ← PublicUpsilonSegment.successor_value n]
      exact hg.1.le
    have hmu : muValue (endpointCode (n + 1)) =
        sourceUpsilon (((n + 1) + 1 : Nat) : Ordinal.{0}) := by
      rw [muValue, GlobalMuDictionary.publicCode_endpoint n,
        PublicEpsilonSourceDictionary.endpointCode_value]
      exact (PublicUpsilonSegment.successor_value (n + 1)).symm
    have hcover : unionInterpretation a ≤ muValue (endpointCode (n + 1)) := by
      rw [hmu]
      exact hg.2.le
    simp only [blockInputCheck, epsilon_not_initial _ hi, Bool.cond_false]
    exact (MuCoveredRelativeAssignment.Support.inputCheck_exact _ a).mpr
      ⟨hi, ha.1, ha.2.1, ha.2.2, hfloor, hcover⟩

theorem initial_returns (m a : Nat) (xs : List Nat)
    (hr : EpsilonReference (a :: xs)) (hg : TailGap m (a :: xs)) :
    ∃ out, out ∈ blockExecute (endpointCode m) a :=
  blockExecute_returns _ _ (initial_caller m a xs hr hg)

theorem adjacent_returns (a b : Nat) (xs : List Nat)
    (hr : EpsilonReference (a :: b :: xs)) : ∃ out, out ∈ blockExecute a b :=
  blockExecute_returns a b (adjacent_caller a b xs hr)

/-- The actual final cover supplies the relative caller whenever the
visible final value is at least its previous epsilon. The other visible
branch of Definition3.35 is the printed singleton, not a hidden caller. -/
theorem tracking_final_caller (codes : List Nat) (ht : Tracking codes)
    (hne : stripLast codes ≠ [])
    (hfloor : unionInterpretation (lastCode (stripLast codes)) ≤
      unionInterpretation (lastCode codes)) :
    blockInputCheck (lastCode (stripLast codes)) (lastCode codes) = true := by
  have hi := ht.2.2.1.last_mu_input hne
  have hc := ht.2.1 _ (lastCode_mem codes ht.1)
  have hb : 1 < unionInterpretation (lastCode codes) ∧
      unionInterpretation (lastCode codes) ≤ muValue (lastCode (stripLast codes)) := by
    simpa only [if_neg hne] using ht.2.2.2.2.2
  simp only [blockInputCheck, epsilon_not_initial _ hi, Bool.cond_false]
  exact (MuCoveredRelativeAssignment.Support.inputCheck_exact _ _).mpr
    ⟨hi, hc, ht.2.2.2.1, ht.2.2.2.2.1, hfloor, hb.2⟩

theorem empty_prefix_final_caller (beta : Nat) (ht : Tracking [beta]) :
    blockInputCheck (endpointCode 0) beta = true := by
  have hc := ht.2.1 beta List.mem_cons_self
  have hb : 1 ≤ unionInterpretation beta ∧
      unionInterpretation beta ≤ sourceUpsilon (1 : Ordinal.{0}) := by
    simpa only [stripLast_singleton, lastCode_singleton, if_pos rfl] using ht.2.2.2.2.2
  have hp : 0 < unionInterpretation beta := by
    simpa only [lastCode_singleton] using ht.2.2.2.1
  have ha : Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) := by
    simpa only [lastCode_singleton] using ht.2.2.2.2.1
  simp only [blockInputCheck, beq_self_eq_true, Bool.cond_true]
  exact (SourceOneRelativeAssignment.inputCheck_exact beta).mpr
    ⟨hc, hp, ha, hb.2.trans_eq (PublicUpsilonSegment.successor_value 0)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationRelativeCallers
