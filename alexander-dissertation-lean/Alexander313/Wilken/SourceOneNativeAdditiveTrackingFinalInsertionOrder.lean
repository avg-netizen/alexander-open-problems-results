import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFinalInsertionOrderSupport

/-!
# Actual final insertion order at a multiplicative recursive child

The independently executing multiplicative child ends in its original
input. When the real insertion selector chooses its final row, the actual
small product is therefore the greater input itself. The retained proper
heads have an independently executing multiplicative assignment at their
last epsilon, and the actual chosen cover licenses every smaller covered
prefix. Actual ALL bounds finish comparison of all smaller inputs, even
outside the subsidiary factor interval. Earlier selected raised rows and
general nonmultiplicative children remain separate. Check zero throughout.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FinalInsertionOrder

open FinalInsertionOrderSupport
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)

/-- Actual greater insertion at its final row and a genuine multiplicative
recursive child suffice for strict whole-word order against every actual
smaller full assignment. The actual table, selection and all outputs are
independently executed; no retained endpoint or comparison is supplied. -/
theorem execute_final_insertion_lex (greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (n : Nat) (replacement : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hm : SourceMultiplicativePrincipal.inputCheck prefix = true)
    (hh : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (hs : Insertion.choose rows = some (n, replacement))
    (hfinal : n + 1 = rows.length)
    (hx : xs ∈ Assignment.execute input) (hy : ys ∈ Assignment.execute greater)
    (hlt : interpretation 0 input < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨middle, hmiddle, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have hmiddleEq : middle = heads := Part.mem_unique hmiddle hh
  have hi : ys ∈ Insertion.execute (factor, heads) := by
    simpa only [hmiddleEq, Branches.execute, ha, Bool.cond_false] using hb
  have hw : Insertion.word rows ∈ Insertion.execute (factor, heads) := Part.mem_map Insertion.word hr
  have hys : ys = Insertion.word rows := Part.mem_unique hi hw
  obtain ⟨before, current, hne, hrows, hword, hcover⟩ := final_choice_shape rows n replacement hs hfinal
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hsplit : heads = before.map Prod.fst ++ [current.1] := by
    simpa only [hrows, List.map_append, List.map_singleton] using hheads.symm
  have hlast := (MultiplicativePrefix.execute_multiplicative_prefix prefix heads hm hh).1
  have hcurrent : current.1 = prefix := by
    calc
      current.1 = lastCode heads := by rw [hsplit, lastCode_append_singleton]
      _ = prefix := hlast
  have hmem : current ∈ rows := by
    rw [hrows]
    exact List.mem_append_right _ List.mem_cons_self
  have hcall := (InsertionSupport.relation_members factor hrel current hmem).2
  rw [hcurrent] at hcall
  obtain ⟨_, _, hlowFactor, _, _, _, _, _, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  have hlowPrefix := ((Assignment.inputCheck_exact prefix).mp (Assignment.execute_spec prefix heads hh).1).1
  obtain ⟨d, hd, hchecked, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    prefix factor current.2 hlowPrefix ((Theta.acceptedLowCode_iff 0 factor).mp hlowFactor).1
    (Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf) hcall
  have hout : ys = before.map Prod.fst ++ [d] := by
    simp only [hys, hword, hd]
  have hcovered : SourceTrackingRaw.Support.inputCheck (lastCode (before.map Prod.fst)) = true ∧
      interpretation 0 greater ≤ SourceTrackingRaw.Support.muValue (lastCode (before.map Prod.fst)) := by
    have hc := (Insertion.coverCheck_exact _ _).mp hcover
    have hc' : SourceTrackingRaw.Support.inputCheck (lastCode (before.map Prod.fst)) = true ∧
        lowCheckCode 0 d = true ∧ interpretation 0 d ≤
          SourceTrackingRaw.Support.muValue (lastCode (before.map Prod.fst)) := by
      simpa only [hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
    exact ⟨hc'.1, by rw [hproduct, ← hv]; exact hc'.2.2⟩
  have hretainedNe : before.map Prod.fst ≠ [] := by
    intro he
    exact hne (List.map_eq_nil_iff.mp he)
  obtain ⟨b, hretained, hlastRetained⟩ := stripLast_split (before.map Prod.fst) hretainedNe
  have hlastB : lastCode (before.map Prod.fst) = b := by rw [hretained, lastCode_append_singleton]
  have hheadsFinal : heads = before.map Prod.fst ++ [prefix] := by
    simpa only [hcurrent] using hsplit
  have hcut : heads = stripLast (before.map Prod.fst) ++ b :: [prefix] := by
    calc
      heads = before.map Prod.fst ++ [prefix] := hheadsFinal
      _ = (stripLast (before.map Prod.fst) ++ [b]) ++ [prefix] :=
        congrArg (fun word : List Nat => word ++ [prefix]) hretained
      _ = stripLast (before.map Prod.fst) ++ b :: [prefix] := by
        simp only [List.append_assoc, List.singleton_append]
  obtain ⟨hb, prefixOut, hprefixOut, hprefixValues⟩ :=
    (MultiplicativePrefix.execute_multiplicative_prefix prefix heads hm hh).2
      (stripLast (before.map Prod.fst)) b [prefix] hcut
  have hprefixValues : prefixOut.map (interpretation 0) = (before.map Prod.fst).map (interpretation 0) := by
    simpa only [← hretained] using hprefixValues
  have hlex := execute_covered_final_lex b input prefixOut xs (interpretation 0 greater)
    (by simpa only [hlastB] using hcovered.1) hb hprefixOut hx hlt
    (by simpa only [hlastB] using hcovered.2)
  have hysValues : ys.map (interpretation 0) =
      (before.map Prod.fst).map (interpretation 0) ++ [interpretation 0 greater] := by
    rw [hout, List.map_append, List.map_singleton, hv, ← hproduct]
  rw [hysValues]
  simpa only [hprefixValues] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FinalInsertionOrder
