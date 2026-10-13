import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBranchesSupport

/-!
# Actual original source-one printed non-M branches

The genuine final-epsilon, actual preceding-head strict comparison and
original raw mu cover choose exactly the printed literal factor append.
Otherwise the actual greatest original cover insertion executes. Both
branches derive real original check-zero RAW tracking on the honest joint
recursive headword/factor domain. Full factor-stack assignment is separate.
No Native base-one parser, supplied branch, cover or output tracker.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Branches

open NativeContext.SourceTrackingSequences (lastCode)

abbrev Query := Insertion.Query

def execute (p : Query) : Part (List Nat) :=
  cond (BranchesSupport.appendCheck p.1 p.2)
    (Part.some (p.2 ++ [p.1])) (Insertion.execute p)

theorem execute_partrec : Partrec execute := by
  have hw : Primrec (fun p : Query => p.2 ++ [p.1]) :=
    Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  exact Partrec.cond BranchesSupport.appendCheck_primrec.to_comp hw.to_comp.partrec
    Insertion.execute_partrec

theorem execute_returns (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads)) :
    ∃ out, out ∈ execute (factor, heads) := by
  cases hc : BranchesSupport.appendCheck factor heads with
  | true =>
    refine ⟨heads ++ [factor], ?_⟩
    simpa only [execute, hc, Bool.cond_true] using Part.mem_some (heads ++ [factor])
  | false =>
    simpa only [execute, hc, Bool.cond_false] using
      Insertion.execute_returns factor heads hh hf hm hb

theorem execute_branch (factor : Nat) (heads out : List Nat)
    (ho : out ∈ execute (factor, heads)) :
    (BranchesSupport.appendCheck factor heads = true ∧ out = heads ++ [factor]) ∨
      (BranchesSupport.appendCheck factor heads = false ∧ out ∈ Insertion.execute (factor, heads)) := by
  cases hc : BranchesSupport.appendCheck factor heads with
  | true =>
    exact Or.inl ⟨hc, by simpa only [execute, hc, Bool.cond_true, Part.mem_some_iff] using ho⟩
  | false => exact Or.inr ⟨hc, by simpa only [execute, hc, Bool.cond_false] using ho⟩

/-- Both actual printed branches derive a real original RAW tracker. The
full assignment must derive the retained honest factor-to-FINAL bound. -/
theorem execute_tracking (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hfactor : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ execute (factor, heads)) : SourceTrackingRaw.trackingCheck out = true := by
  rcases execute_branch factor heads out ho with ⟨hc, he⟩ | ⟨hc, hi⟩
  · rw [he]
    exact BranchesSupport.append_tracking factor heads hh hm hfactor hc
  · exact InsertionFidelity.execute_tracking factor heads out hh hf hm hb hi

theorem execute_nonempty (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hfactor : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ execute (factor, heads)) : out ≠ [] :=
  ((SourceTrackingRaw.trackingCheck_exact out).mp
    (execute_tracking factor heads out hh hf hm hfactor hb ho)).1

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Branches
