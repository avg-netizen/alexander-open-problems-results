import Alexander313.Wilken.PublicEpsilonNativeSkTrackingSupport

/-!
# Actual tracking recognition of the executing original-source sk word

Path induction carries each real original-source HIGH representative and
its actual mu fidelity. Every returned prefix code therefore has the real
RAW epsilon and mu-cover callers. The final value is either that genuine
epsilon or the actual positive principal MNF truncation. The original M>1
cutoff supplies its strict lower bound. The concrete RAW tracking checker
accepts the executing flat word; no tracking-assignment premise is used.
Spelling-independent sk assignment, evaluation and Par remain separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkTracking

open Support SkSourceWord.Support (EntryMatches)

/-- Genuine original source provenance and actual emitted edges derive
every RAW reference and final-principal condition of the source tracker. -/
theorem path_tracking {cutoff r current : Nat} {word : SkIteration.Support.Word}
    (hp : SkIteration.Path cutoff (r, current) word)
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) (q root : Nat)
    (ha : Mu.inputCheck q root = true)
    (hv : interpretation q root = interpretation r current)
    (hm : Mu.sourceValue q root = Mu.sourceValue r current)
    (codes : List Nat) (hrel : List.Forall₂ (EntryMatches q) word codes) :
    SourceTrackingRaw.trackingCheck q codes = true := by
  induction hp generalizing root codes with
  | stop r current hc hcheck hbound =>
    cases hrel with
    | cons hd ht =>
      cases ht
      have he : interpretation q _ = interpretation q root := hd.2.2.trans hv.symm
      apply singleton_tracking q _ hd.1
      · rw [he]; exact root_pos q root ha
      · rw [he, ← RootLowCollapse.root_epsilon q root ha]
        exact Ordinal.isPrincipal_add_omega0_opow _
      · rw [he]; exact RootLowCollapse.root_base_le q root ha
  | nextStop r current out helig ho hh =>
    cases hrel with
    | cons hd ht =>
      cases ht with
      | cons hn hnil =>
        cases hnil
        have hraw := entry_root q root r current _ ha hv hm hd
        have hs := SkNextSearch.execute_spec r current cutoff out ho
        have hb := SkNextSearch.execute_source_bounds r current cutoff out ho hmul hcut
          ((SkIteration.Support.eligible_exact cutoff r current).mp helig).2.2
        have hpnext := Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_pos_principal
          (Mu.sourceValue r current) (unionInterpretation cutoff)
        apply pair_tracking q _ _ hraw.1 hn.1
        · rw [hn.2.2, hs.2.2.2.1]; exact hpnext.1
        · rw [hn.2.2, hs.2.2.2.1]; exact hpnext.2
        · rw [hn.2.2]; exact hcut.trans_le hb.1
        · rw [hn.2.2, hraw.2]; exact hb.2.1
  | nextContinue r current out tail helig ho hh ht ih =>
    cases hrel with
    | cons hd htail =>
      have hs := SkContextFidelity.continued_source q root r current cutoff out ha ho hh hv hm
      have htracking := ih (ContextTranslation.Return.returnedRoot q root out.2)
        hs.1 hs.2.1 hs.2.2.2.1 _ htail
      obtain ⟨rest, hhead⟩ := ht.head
      rw [hhead] at htail
      cases htail with
      | cons hn hrest =>
        have hraw := entry_root q root r current _ ha hv hm hd
        have hnraw := entry_root q (ContextTranslation.Return.returnedRoot q root out.2)
          (betaCode r current) out.2 _ hs.1 hs.2.1 hs.2.2.2.1 hn
        have hspec := SkNextSearch.execute_spec r current cutoff out ho
        have hnext := hspec.2.2.2.2.mp hh
        have hb := SkNextSearch.execute_source_bounds r current cutoff out ho hmul hcut
          ((SkIteration.Support.eligible_exact cutoff r current).mp helig).2.2
        apply tracking_prepend q _ _ _ hraw.1 hnraw.1
        · rw [hd.2.2, hn.2.2, hspec.2.2.2.1]; exact hnext.2
        · rw [hn.2.2, hraw.2]; exact hb.2.1
        · rw [hn.2.2]; exact hcut.trans_le hb.1
        · exact htracking

/-- The actually executing original-source output is accepted by the
real RAW tracking checker under the printed M>1 cutoff hypotheses. -/
theorem execute_tracking (q root cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff))
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) :
    SourceTrackingRaw.trackingCheck q codes = true := by
  obtain ⟨hi, word, hw, hp, hr⟩ := SkSourceWord.execute_relation q root cutoff codes ho
  have ha := ((SkIteration.inputCheck_exact q root cutoff).mp hi).1
  exact path_tracking hp hmul hcut q root ha rfl rfl codes hr

/-- The computed proper prefix is an actual original-source RAW reference
sequence, with genuine epsilon callers, strict order and real mu covers. -/
theorem execute_reference_prefix (q root cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff))
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) :
    SourceTrackingRaw.referenceCheck q (Hereditary.FinePredecessor.stripLast codes) = true :=
  SourceTrackingRaw.tracking_erasure q codes (execute_tracking q root cutoff codes ho hmul hcut)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkTracking
