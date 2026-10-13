import Alexander313.Wilken.PublicEpsilonNativeLocalizationOrderSupport

/-!
# Genuine native ordinary localization value-path invariance

The actual cross-support selection laws force equal ordinal-value paths
at equally valued checked Normal roots, even with different written
supports. The base value has the actual singleton value path. This derives
value equality; it supplies no equality of native spellings. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.ValueInvariance

open SourceLocalization.OrderSupport

/-- Value-path equality follows from genuine selections on two possibly
different root supports. It is not assumed as a spelling invariant. -/
theorem sourcePath_values_eq (q left right c : Nat) (xs : List Nat)
    (hl : Node q left) (hr : Node q right)
    (hp : SourcePath q (support left) (c :: xs))
    (hroots : value q left = value q right)
    (hendp : value q (endpoint (c :: xs)) = value q left)
    (d : Nat) (ys : List Nat) (hq : SourcePath q (support right) (d :: ys))
    (hendq : value q (endpoint (d :: ys)) = value q right)
    (hhead : value q c = value q d) :
    (c :: xs).map (value q) = (d :: ys).map (value q) := by
  revert hendp d ys
  induction hp with
  | stop c hc hmax =>
    intro hendp d ys hq hendq hhead
    have hcroot : value q c = value q left := by simpa only [endpoint] using hendp
    cases hq with
    | stop d hd hmax => simp only [List.map_cons, List.map_nil, hhead]
    | next d b ys hd hdb hbs harg hrest =>
      have hbroot : value q b ≤ value q right :=
        (hrest.le_endpoint b List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendq)
      have hdroot : value q d = value q right := hhead.symm.trans (hcroot.trans hroots)
      exact False.elim ((hdroot ▸ hdb).not_ge hbroot)
  | next c a xs hc hca has harg hrest ih =>
    intro hendp d ys hq hendq hhead
    have haroot : value q a ≤ value q left :=
      (hrest.le_endpoint a List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendp)
    cases hq with
    | stop d hd hmax =>
      have hdroot : value q d = value q right := by simpa only [endpoint] using hendq
      have hcroot : value q c = value q left := hhead.trans (hdroot.trans hroots.symm)
      exact False.elim ((hcroot ▸ hca).not_ge haroot)
    | next d b ys hd hdb hbs hbarg hbrest =>
      have hpfull := SourcePath.next c a xs hc hca has harg hrest
      have hqfull := SourcePath.next d b ys hd hdb hbs hbarg hbrest
      have hbroot : value q b ≤ value q right :=
        (hbrest.le_endpoint b List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendq)
      have hab := selected_cross_order q left right c d a b xs ys hl hr hpfull hqfull
        hhead (haroot.trans_eq hroots)
      have hba := selected_cross_order q right left d c b a ys xs hr hl hqfull hpfull
        hhead.symm (hbroot.trans_eq hroots.symm)
      have he := le_antisymm hab hba
      have ht := ih (by simpa only [endpoint] using hendp) b ys hbrest
        (by simpa only [endpoint] using hendq) he
      simp only [List.map_cons, hhead, ht]

theorem nativePath_values_eq (q c d : Nat)
    (hc : inputCheck q c = true) (hd : inputCheck q d = true)
    (he : value q c = value q d) :
    (nativePath q c).map (value q) = (nativePath q d).map (value q) := by
  obtain ⟨xs, hp⟩ := nativePath_head q c
  obtain ⟨ys, hq⟩ := nativePath_head q d
  have hps := nativePath_source q c hc
  have hqs := nativePath_source q d hd
  have hep := nativePath_end q c hc
  have heq := nativePath_end q d hd
  rw [hp] at hps hep ⊢
  rw [hq] at hqs heq ⊢
  exact sourcePath_values_eq q c d (baseRaw q) xs
    ((inputCheck_exact q c).mp hc) ((inputCheck_exact q d).mp hd)
    hps he hep (baseRaw q) ys hqs heq rfl

/-- At the original base value the actual complete path has just that
one ordinal value. Literal written-node equality is unnecessary. -/
theorem nativePath_base_values (q c : Nat) (hc : inputCheck q c = true)
    (he : value q c = base q) :
    (nativePath q c).map (value q) = [base q] := by
  have hn := (inputCheck_exact q c).mp hc
  have hbase := node_baseCheck q c hn
  have hbp : SourcePath q (support c) [baseRaw q] := SourcePath.stop
    (baseRaw q) (baseRaw_node q hbase) (fun d hd => by
      exact (support_bound q c d hn hd).trans_eq
        (he.trans (baseRaw_value q hbase).symm))
  obtain ⟨xs, hp⟩ := nativePath_head q c
  have hps := nativePath_source q c hc
  have hep := nativePath_end q c hc
  rw [hp] at hps hep ⊢
  have hbend : value q (endpoint [baseRaw q]) = value q c := by
    simpa only [endpoint] using (baseRaw_value q hbase).trans he.symm
  have hv := sourcePath_values_eq q c c (baseRaw q) xs hn hn
    hps rfl hep (baseRaw q) [] hbp hbend rfl
  simpa only [List.map_cons, List.map_nil, baseRaw_value q hbase] using hv

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.ValueInvariance
