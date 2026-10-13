import Alexander313.Wilken.HereditaryPublicMtsLocalization
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertion

/-!
# Real FIRST transport along independently checked mu edges

The independently executed native multiplicative word has a nonempty
FIRST bounded by its input. A genuine internal mu edge extends the earlier
word in VALUES, so both words have the same FIRST. Original contextual mu
fidelity transports this statement to independently checked public edges.
Below the external root's FIRST cut, the actual native covered table
supplies an eligible earlier predecessor, or its singleton branch gives
the original root itself. No reachable-row or covering oracle is used.
The complete least-table covering induction remains separate. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.FirstSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open SourceMultiplicativeTracking (word properPrefix)

def firstValue (gamma current : Nat) : Ordinal.{0} :=
  interpretation gamma (SourceAdditiveTracking.Insertion.firstCode (word gamma current))

theorem word_first_shape (gamma current : Nat) :
    ∃ first : Nat, ∃ tail : List Nat, word gamma current = first :: tail ∧
      firstValue gamma current = interpretation gamma first := by
  have hn : word gamma current ≠ [] :=
    SourceMultiplicativeTracking.Support.extend_ne_nil gamma current _
  obtain ⟨first, tail, hw⟩ := List.exists_cons_of_ne_nil hn
  exact ⟨first, tail, hw, by
    simp only [firstValue, hw, SourceAdditiveTracking.Insertion.firstCode,
      List.head?_cons, Option.getD_some]⟩

theorem firstValue_le_current (gamma current : Nat)
    (hi : SourceLocalization.inputCheck gamma current = true) :
    firstValue gamma current ≤ interpretation gamma current := by
  obtain ⟨first, tail, hw, hv⟩ := word_first_shape gamma current
  rw [hv]
  apply SourceMultiplicativeTracking.OrderSupport.word_values_bound gamma current hi
  rw [hw, List.map_cons]
  exact List.mem_cons_self

/-- The FIRST equality follows from the actual independent word prefix,
not an order or identity of written native support representatives. -/
theorem firstValue_eq_of_cover (gamma previous current : Nat)
    (hp : Mu.inputCheck gamma previous = true)
    (hc : SourceLocalization.inputCheck gamma current = true)
    (hlt : interpretation gamma previous < interpretation gamma current)
    (hcover : interpretation gamma current ≤ Mu.sourceValue gamma previous) :
    firstValue gamma previous = firstValue gamma current := by
  have hprefix := SourceMultiplicativeTracking.OrderSupport.word_direct_cover_prefix
    gamma previous current hp hc hlt hcover
  have hhead := hprefix.head
    (SourceMultiplicativeTracking.OrderSupport.word_values_ne_nil gamma previous)
  obtain ⟨a, as, ha, hva⟩ := word_first_shape gamma previous
  obtain ⟨b, bs, hb, hvb⟩ := word_first_shape gamma current
  have he : interpretation gamma a = interpretation gamma b := by
    simpa only [ha, hb, List.map_cons, List.head_cons] using hhead
  exact hva.trans (he.trans hvb.symm)

theorem firstValue_eq_of_value (gamma left right : Nat)
    (hl : SourceLocalization.inputCheck gamma left = true)
    (hr : SourceLocalization.inputCheck gamma right = true)
    (he : interpretation gamma left = interpretation gamma right) :
    firstValue gamma left = firstValue gamma right := by
  have hv := SourceMultiplicativeTracking.Spelling.word_values_eq gamma left right hl hr he
  obtain ⟨a, as, ha, hva⟩ := word_first_shape gamma left
  obtain ⟨b, bs, hb, hvb⟩ := word_first_shape gamma right
  have hcons := List.cons.inj (by simpa only [ha, hb, List.map_cons] using hv)
  exact hva.trans (hcons.1.trans hvb.symm)

/-- A public edge from the original root supplies the actual FIRST cut
without an additional reached-target or native Mu premise. -/
theorem root_edge_first_bound (gamma current : Nat)
    (hn : SourceLocalization.Node gamma current)
    (hcover : PublicTrackingSequences.adjacencyCheck gamma
      (UniformPublicReturn.publicCode gamma current) = true) :
    firstValue gamma current ≤ SkPublicRecurrence.muValue gamma := by
  have hs := (Support.eligible_exact gamma _).mp hcover
  have hp := node_public_spec gamma current hn
  exact (firstValue_le_current gamma current
    ((SourceLocalization.inputCheck_exact gamma current).mpr hn)).trans
      (by rw [← hp.2]; exact hs.2.2.2)

/-- The actual original OWN interval derives the public Mu column before
the independently checked public edge is interpreted as a native edge. -/
theorem public_edge_first_eq (gamma previous current : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hp : Mu.inputCheck gamma previous = true)
    (hc : SourceLocalization.Node gamma current)
    (hcut : interpretation gamma previous < ContextSupport.ownCeiling gamma)
    (hedge : PublicTrackingSequences.adjacencyCheck
      (UniformPublicReturn.publicCode gamma previous)
      (UniformPublicReturn.publicCode gamma current) = true) :
    firstValue gamma previous = firstValue gamma current := by
  have hpn := (SourceLocalization.inputCheck_exact gamma previous).mp
    (SourceMultiplicativeTracking.OrderSupport.high_node_input gamma previous hp)
  have hpp := node_public_spec gamma previous hpn
  have hcp := node_public_spec gamma current hc
  have hm := ContextSupport.high_public_mu gamma previous hg hp hcut
  have hs := (Support.eligible_exact _ _).mp hedge
  have hlt : interpretation gamma previous < interpretation gamma current := by
    rw [← hpp.2, ← hcp.2]
    exact hs.2.2.1
  have hcover : interpretation gamma current ≤ Mu.sourceValue gamma previous := by
    rw [← hcp.2, ← hm.2]
    exact hs.2.2.2
  exact firstValue_eq_of_cover gamma previous current hp
    ((SourceLocalization.inputCheck_exact gamma current).mpr hc) hlt hcover

/-- An independently computed target below the FIRST cut has a real
eligible earlier root or proper localization entry. The concrete reverse
native table supplies that predecessor; nothing asserts it is reached. -/
theorem earlier_eligible (gamma current : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hn : SourceLocalization.Node gamma current)
    (hlt : unionInterpretation gamma < interpretation gamma current)
    (hcut : interpretation gamma current < ContextSupport.ownCeiling gamma)
    (hfirst : firstValue gamma current ≤ SkPublicRecurrence.muValue gamma) :
    ∃ a : Nat,
      (a = gamma ∨ ∃ previous ∈ properPrefix gamma current,
        a = UniformPublicReturn.publicCode gamma previous ∧
          firstValue gamma previous = firstValue gamma current) ∧
      PublicTrackingSequences.adjacencyCheck a
        (UniformPublicReturn.publicCode gamma current) = true := by
  have hi := (SourceLocalization.inputCheck_exact gamma current).mpr hn
  have hpublic := node_public_spec gamma current hn
  cases hs : SourceMultiplicativeTracking.Support.select gamma current
      (SourceMultiplicativeTracking.Support.table gamma (properPrefix gamma current)) with
  | none =>
    have hw := SourceMultiplicativeTracking.Recurrence.word_none gamma current hs
    have hv : firstValue gamma current = interpretation gamma current := by
      simp only [firstValue, hw, SourceAdditiveTracking.Insertion.firstCode,
        List.head?_cons, Option.getD_some]
    refine ⟨gamma, Or.inl rfl, (Support.eligible_exact gamma _).mpr
      ⟨hg, hpublic.1, ?_, ?_⟩⟩
    · rw [hpublic.2]
      exact hlt
    · rw [hpublic.2, ← hv]
      exact hfirst
  | some e =>
    have he := SourceMultiplicativeTracking.Recurrence.selected_node gamma current current e hi hs
    have hless := SourceAdditiveTracking.ProperPrefix.properPrefix_lt_root gamma current hi e.1 he.1
    have hep := (SourceLocalization.inputCheck_exact gamma e.1).mp
      (SourceMultiplicativeTracking.OrderSupport.high_node_input gamma e.1 he.2.1)
    have hepublic := node_public_spec gamma e.1 hep
    have hecut := hless.trans hcut
    have hemu := ContextSupport.high_public_mu gamma e.1 hg he.2.1 hecut
    have hhead := firstValue_eq_of_cover gamma e.1 current he.2.1 hi hless he.2.2
    refine ⟨UniformPublicReturn.publicCode gamma e.1,
      Or.inr ⟨e.1, he.1, rfl, hhead⟩, (Support.eligible_exact _ _).mpr
        ⟨hemu.1, hpublic.1, ?_, ?_⟩⟩
    · rw [hepublic.2, hpublic.2]
      exact hless
    · rw [hpublic.2, hemu.2]
      exact he.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.FirstSupport
