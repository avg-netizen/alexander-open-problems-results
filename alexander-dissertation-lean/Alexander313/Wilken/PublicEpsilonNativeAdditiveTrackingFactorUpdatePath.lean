import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorUpdateExecution

/-!
# Complete assignments along real finite descending update observations

Every step records an actual dispatcher membership. A genuine current
Assignment identifies the next whole VALUES even at another RAW spelling.
The actual product producer constructs its input and carries the computed
last factor to the next descending step. Finite induction reconstructs a
complete Assignment for the entire multiplied input; no intermediate code,
word or accumulated equation is supplied. Contextual cuts, an initial reset
and extraction from the original factor-removal trace remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdatePath

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- A finite sequence of observed calls to the actual dispatcher. -/
inductive Updates (q : Nat) : List Nat → List Nat → List Nat → Prop
  | nil (heads : List Nat) : Updates q heads [] heads
  | cons (heads : List Nat) (factor : Nat) (rest middle out : List Nat)
      (hstep : middle ∈ Branches.execute ((q, factor), heads))
      (htail : Updates q middle rest out) : Updates q heads (factor :: rest) out

theorem related_update_returns (q input factor : Nat) (heads actualHeads out : List Nat)
    (hh : actualHeads ∈ Assignment.execute q input)
    (ht : SourceTrackingRaw.trackingCheck q heads = true)
    (hv : heads.map (interpretation q) = actualHeads.map (interpretation q))
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hbase : base q < interpretation q input)
    (hcut : interpretation q factor ≤ lf (interpretation q input))
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    ∃ next nextWord,
      nextWord ∈ Assignment.execute q next ∧
      base q < interpretation q next ∧
      interpretation q next = interpretation q input * interpretation q factor ∧
      lf (interpretation q next) = interpretation q factor ∧
      SourceTrackingRaw.trackingCheck q out = true ∧
      out.map (interpretation q) = nextWord.map (interpretation q) := by
  have hhRaw := Assignment.execute_tracking q input actualHeads hh
  have hne := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp ht).1
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation q) heads actualHeads hne hv
  have hb : interpretation q factor ≤ interpretation q (lastCode actualHeads) :=
    hcut.trans (Assignment.execute_last_bounds q input actualHeads hh).1
  have hb' : interpretation q factor ≤ interpretation q (lastCode heads) := hb.trans_eq hlast.symm
  obtain ⟨word, hw⟩ := Branches.execute_returns q factor actualHeads hhRaw hf hm hb
  have he := Assignment.ValueInvariance.branches_values_eq q factor factor heads actualHeads
    ht hhRaw hf hf hm hb' hb rfl hv out word ho hw
  obtain ⟨next, nextWord, hn, hl, ha, hproduct, hstrict, hnext, hvalues, hlf⟩ :=
    FactorUpdateExecution.product_update_returns q input factor actualHeads word hh hf hm hone hbase hcut hw
  exact ⟨next, nextWord, hnext, hstrict, hproduct, hlf,
    Branches.execute_tracking q factor heads out ht hf hm hone hb' ho, he.trans hvalues⟩

/-- All callers follow the actual descending factors. The entire final
execution and product value are conclusions of finite actual observations. -/
theorem execute_updates_values (q input : Nat) (heads actualHeads factors out : List Nat)
    (hh : actualHeads ∈ Assignment.execute q input)
    (ht : SourceTrackingRaw.trackingCheck q heads = true)
    (hv : heads.map (interpretation q) = actualHeads.map (interpretation q))
    (hbase : base q < interpretation q input)
    (hc : ∀ factor ∈ factors, lowCheckCode q factor = true ∧
      IsMultiplicativePrincipal (interpretation q factor) ∧ 1 < interpretation q factor)
    (hdesc : factors.Pairwise (fun a b => interpretation q b ≤ interpretation q a))
    (hcut : ∀ factor ∈ factors, interpretation q factor ≤ lf (interpretation q input))
    (hp : Updates q heads factors out) :
    ∃ next nextWord,
      nextWord ∈ Assignment.execute q next ∧
      base q < interpretation q next ∧
      interpretation q next = interpretation q input * factorProduct (factors.map (interpretation q)) ∧
      out.map (interpretation q) = nextWord.map (interpretation q) := by
  induction factors generalizing input heads actualHeads out with
  | nil =>
    cases hp
    exact ⟨input, actualHeads, hh, hbase,
      by simp only [List.map_nil, factorProduct, mul_one], hv⟩
  | cons factor rest ih =>
    cases hp with
    | cons heads factor rest middle out hstep htail =>
      have hf := hc factor List.mem_cons_self
      obtain ⟨next, actualMiddle, hn, hs, hproduct, hlf, hraw, hvalues⟩ :=
        related_update_returns q input factor heads actualHeads middle hh ht hv
          hf.1 hf.2.1 hf.2.2 hbase (hcut factor List.mem_cons_self) hstep
      have hclasses : ∀ f ∈ rest, lowCheckCode q f = true ∧
          IsMultiplicativePrincipal (interpretation q f) ∧ 1 < interpretation q f :=
        fun f hf => hc f (List.mem_cons_of_mem _ hf)
      have hrest := (List.pairwise_cons.mp hdesc).2
      have hbound : ∀ f ∈ rest, interpretation q f ≤ lf (interpretation q next) := by
        intro f hf
        rw [hlf]
        exact (List.pairwise_cons.mp hdesc).1 f hf
      obtain ⟨last, word, hw, hb, hvalue, he⟩ :=
        ih (input := next) (heads := middle) (actualHeads := actualMiddle) (out := out)
          hn hraw hvalues hs hclasses hrest hbound htail
      refine ⟨last, word, hw, hb, ?_, he⟩
      rw [hvalue, hproduct, List.map_cons, factorProduct, mul_assoc]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdatePath
