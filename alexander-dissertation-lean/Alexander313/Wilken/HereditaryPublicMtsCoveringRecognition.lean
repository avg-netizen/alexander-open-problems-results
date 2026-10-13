import Alexander313.Wilken.HereditaryPublicMtsCoveringRecognitionSupport
import Alexander313.Wilken.HereditaryPublicMtsInfinityHat

/-!
# Exact primitive recursive recognition of genuine public covering

Actual root admission, the literal first and last codes and the finite
independent adjacency fold recognize exactly the original covering predicate.
For actual full-domain mts execution on strict M targets, this concrete
Boolean test is exactly the true semantic singleton-boundary inequality.
No numerical minimum or graph reach is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringRecognition

open CoveringSupport (Covering)
open CoveringRecognitionSupport

theorem step_primrec : Primrec₂ step :=
  (Primrec.snd.pair (Primrec.and.comp (Primrec.snd.comp Primrec.fst)
    (PublicTrackingSequences.adjacencyCheck_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂

theorem run_primrec : Primrec₂ run := by
  have hs : Primrec₂ (fun p : Nat × List Nat => fun e : State × Nat => step e.1 e.2) :=
    (step_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldl Primrec.snd (Primrec.fst.pair (Primrec.const true)) hs).to₂

def coveringCheck (gamma beta : Nat) (codes : List Nat) : Bool :=
  (MuPublicDictionary.Support.inputCheck gamma && !codes.isEmpty) &&
    ((codes.head?.getD 0 == gamma) &&
      ((run gamma codes.tail).2 && ((run gamma codes.tail).1 == beta)))

theorem coveringCheck_primrec : Primrec (fun p : Nat × (Nat × List Nat) =>
    coveringCheck p.1 p.2.1 p.2.2) := by
  have hg := Primrec.fst
  have hb := Primrec.fst.comp Primrec.snd
  have hw := Primrec.snd.comp Primrec.snd
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hw) (Primrec.const 0)
  have hr := run_primrec.comp hg (Primrec.list_tail.comp hw)
  exact Primrec.and.comp
    (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp hg)
      (Primrec.not.comp (NativeContext.SourceTrackingSequences.list_isEmpty_primrec.comp hw)))
    (Primrec.and.comp (Primrec.beq.comp hh hg)
      (Primrec.and.comp (Primrec.snd.comp hr) (Primrec.beq.comp (Primrec.fst.comp hr) hb)))

theorem coveringCheck_exact (gamma beta : Nat) (codes : List Nat) :
    coveringCheck gamma beta codes = true ↔ Covering gamma beta codes := by
  constructor
  · intro h
    have hs := Bool.and_eq_true.mp h
    have hg := (Bool.and_eq_true.mp hs.1).1
    have hn : codes ≠ [] := by
      intro he
      have hz := (Bool.and_eq_true.mp hs.1).2
      simpa only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] using hz
    obtain ⟨first, tail, he⟩ := List.exists_cons_of_ne_nil hn
    have hh := (Bool.and_eq_true.mp hs.2).1
    have hfirst : first = gamma := by
      simpa only [he, List.head?_cons, Option.getD_some, beq_iff_eq] using hh
    have hr := Bool.and_eq_true.mp (Bool.and_eq_true.mp hs.2).2
    have hvalid : (run gamma tail).2 = true := by
      simpa only [he, List.tail_cons] using hr.1
    have hlast : (run gamma tail).1 = beta := by
      simpa only [he, List.tail_cons, beq_iff_eq] using hr.2
    have hc := ((run_valid gamma tail).mp hvalid).covering (Covering.root hg)
    simpa only [List.singleton_append, he, hfirst, hlast] using hc
  · intro hc
    obtain ⟨tail, he, ht⟩ := covering_steps hc
    have hg : MuPublicDictionary.Support.inputCheck gamma = true := by
      induction hc with
      | root hg => exact hg
      | append previous current codes hp hnext ih => exact ih
    have hv : (run gamma tail).2 = true ∧ (run gamma tail).1 = beta := by
      induction ht with
      | nil previous => exact ⟨rfl, rfl⟩
      | cons previous current last rest hedge hrest ih =>
        have hs := fold_valid (previous, true) (current :: rest)
        have hend : ((current :: rest).foldl step (previous, true)).1 = last := by
          simp only [List.foldl_cons, step, hedge, Bool.true_and]
          exact ih.2
        have hsteps : Steps previous (current :: rest)
            (((current :: rest).foldl step (previous, true)).1) := by
          rw [hend]
          exact .cons previous current last rest hedge hrest
        exact ⟨hs.mpr ⟨rfl, hsteps⟩, hend⟩
    simp only [coveringCheck, he, List.isEmpty_cons, Bool.not_false, hg,
      List.head?_cons, Option.getD_some, beq_self_eq_true, List.tail_cons, hv.1, hv.2,
      Bool.and_self, Bool.true_and]

/-- The actual finite covering test decides the semantic cut on the full
mts grammar domain, including all cases outside the original OWN interval. -/
theorem execute_check_iff_lt_value (gamma beta : Nat) (codes : List Nat)
    (ho : codes ∈ Infinity.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    coveringCheck gamma beta codes = true ↔ unionInterpretation beta <
      InfinityHat.value gamma
        ((Infinity.inputCheck_exact gamma beta).mp (Infinity.execute_spec gamma beta codes ho).1).1 :=
  (coveringCheck_exact gamma beta codes).trans
    (InfinityHat.execute_covering_iff_lt_value gamma beta codes ho hm hlt)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringRecognition
