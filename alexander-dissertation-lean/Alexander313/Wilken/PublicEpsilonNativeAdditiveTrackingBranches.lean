import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingBranchesSupport

/-!
# Executing the printed non-M additive branches 2.1 and 2.2

The real final-epsilon, preceding-head comparison and original mu cover
choose literal factor append exactly when branch 2.1 applies. Otherwise
the independently executing greatest insertion computes branch 2.2. Each
branch derives a genuine original RAW tracker on the honest joint recursive
headword/factor domain. No assignment or output word is supplied. The full
factor descent and unwind are separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Branches

open PublicEpsilonUnboundedIota
open SourceTrackingSequences (lastCode)

abbrev Query := Insertion.Query

def execute (p : Query) : Part (List Nat) :=
  cond (BranchesSupport.appendCheck p.1.1 p.1.2 p.2)
    (Part.some (p.2 ++ [p.1.2])) (Insertion.execute p)

theorem execute_partrec : Partrec execute := by
  have hw : Primrec (fun p : Query => p.2 ++ [p.1.2]) :=
    Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))
  exact Partrec.cond BranchesSupport.appendCheck_primrec.to_comp hw.to_comp.partrec
    Insertion.execute_partrec

/-- Every genuine recursive headword/factor caller reaches one of the
literal source branches. Actual insertion termination supplies the false
branch; the true branch emits the unchanged heads followed by the factor. -/
theorem execute_returns (q factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads)) :
    ∃ out, out ∈ execute ((q, factor), heads) := by
  cases hc : BranchesSupport.appendCheck q factor heads with
  | true =>
    refine ⟨heads ++ [factor], ?_⟩
    simpa only [execute, hc, Bool.cond_true] using Part.mem_some (heads ++ [factor])
  | false =>
    simpa only [execute, hc, Bool.cond_false] using
      Insertion.execute_returns q factor heads hh hf hm hb

theorem execute_branch (q factor : Nat) (heads out : List Nat)
    (ho : out ∈ execute ((q, factor), heads)) :
    (BranchesSupport.appendCheck q factor heads = true ∧ out = heads ++ [factor]) ∨
      (BranchesSupport.appendCheck q factor heads = false ∧
        out ∈ Insertion.execute ((q, factor), heads)) := by
  cases hc : BranchesSupport.appendCheck q factor heads with
  | true =>
    exact Or.inl ⟨hc, by simpa only [execute, hc, Bool.cond_true, Part.mem_some_iff] using ho⟩
  | false => exact Or.inr ⟨hc, by simpa only [execute, hc, Bool.cond_false] using ho⟩

/-- Both real printed branches construct an actual original RAW tracker.
The factor>1 and factor<=headword FINAL conditions are the honest joint
Lemma3.21 recursive hypotheses, to be derived by the full P assignment. -/
theorem execute_tracking (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfactor : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ execute ((q, factor), heads)) : SourceTrackingRaw.trackingCheck q out = true := by
  rcases execute_branch q factor heads out ho with ⟨hc, he⟩ | ⟨hc, hi⟩
  · rw [he]
    exact BranchesSupport.append_tracking q factor heads hh hm hfactor hc
  · exact InsertionFidelity.execute_tracking q factor heads out hh hf hm hfactor hb hi

theorem execute_nonempty (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfactor : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ execute ((q, factor), heads)) : out ≠ [] :=
  ((SourceTrackingRaw.trackingCheck_conditions q out).mp
    (execute_tracking q factor heads out hh hf hm hfactor hb ho)).1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Branches
