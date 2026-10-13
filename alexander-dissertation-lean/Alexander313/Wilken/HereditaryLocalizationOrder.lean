import Alexander313.Wilken.HereditaryLocalizationOrderSupport
import Alexander313.Wilken.HereditarySourceZeta

/-!
# Genuine ordinary localization lexicographic order

The interval argument maximum and the actual intermediate-node argument bound
force cross-path selections into the right order. SourcePath induction proves
literal source 2.35 on actual ordinal-value paths, including base endpoints,
and its converse. Equal root values yield equal ordinary value paths by the
same derived selection law; native spellings and literal support need not
agree. No lex, support or spelling oracle is an input. Fine localization order
is not inferred from the old ordinary/fine subsequence. Original raw theta-zero
roots use their genuinely normalized spelling; the raw adapters do not assert
literal support or path preservation through normalization. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Order

open Localization.Refinements Localization.OrderSupport

/-- Value-path equality follows from genuine selections on two possibly
different root supports. It is not assumed as a spelling invariant. -/
theorem sourcePath_values_eq (r left right c : Nat) (xs : List Nat)
    (hl : Node r left) (hr : Node r right)
    (hp : SourcePath r (support left) (c :: xs))
    (hroots : value r left = value r right)
    (hendp : value r (endpoint (c :: xs)) = value r left)
    (d : Nat) (ys : List Nat) (hq : SourcePath r (support right) (d :: ys))
    (hendq : value r (endpoint (d :: ys)) = value r right)
    (hhead : value r c = value r d) :
    (c :: xs).map (value r) = (d :: ys).map (value r) := by
  revert hendp d ys
  induction hp with
  | stop c hc hmax =>
    intro hendp d ys hq hendq hhead
    have hcroot : value r c = value r left := by simpa only [endpoint] using hendp
    cases hq with
    | stop d hd hmax => simp only [List.map_cons, List.map_nil, hhead]
    | next d b ys hd hdb hbs harg hrest =>
      have hbroot : value r b ≤ value r right :=
        (hrest.le_endpoint b List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendq)
      have hdroot : value r d = value r right := hhead.symm.trans (hcroot.trans hroots)
      exact False.elim ((hdroot ▸ hdb).not_ge hbroot)
  | next c a xs hc hca has harg hrest ih =>
    intro hendp d ys hq hendq hhead
    have haroot : value r a ≤ value r left :=
      (hrest.le_endpoint a List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendp)
    cases hq with
    | stop d hd hmax =>
      have hdroot : value r d = value r right := by simpa only [endpoint] using hendq
      have hcroot : value r c = value r left := hhead.trans (hdroot.trans hroots.symm)
      exact False.elim ((hcroot ▸ hca).not_ge haroot)
    | next d b ys hd hdb hbs hbarg hbrest =>
      have hpfull := SourcePath.next c a xs hc hca has harg hrest
      have hqfull := SourcePath.next d b ys hd hdb hbs hbarg hbrest
      have hbroot : value r b ≤ value r right :=
        (hbrest.le_endpoint b List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendq)
      have hab := selected_cross_order r left right c d a b xs ys hl hr hpfull hqfull
        hhead (haroot.trans_eq hroots)
      have hba := selected_cross_order r right left d c b a ys xs hr hl hqfull hpfull
        hhead.symm (hbroot.trans_eq hroots.symm)
      have he := le_antisymm hab hba
      have ht := ih (by simpa only [endpoint] using hendp) b ys hbrest
        (by simpa only [endpoint] using hendq) he
      simp only [List.map_cons, hhead, ht]

/-- The first different selected values have the right orientation whenever
the roots are ordered. The two support lists may differ literally. -/
theorem sourcePath_values_lex (r left right c : Nat) (xs : List Nat)
    (hl : Node r left) (hr : Node r right)
    (hp : SourcePath r (support left) (c :: xs))
    (hroots : value r left < value r right)
    (hendp : value r (endpoint (c :: xs)) = value r left)
    (d : Nat) (ys : List Nat) (hq : SourcePath r (support right) (d :: ys))
    (hendq : value r (endpoint (d :: ys)) = value r right)
    (hhead : value r c = value r d) :
    List.Lex (· < ·) ((c :: xs).map (value r)) ((d :: ys).map (value r)) := by
  revert hendp d ys
  induction hp with
  | stop c hc hmax =>
    intro hendp d ys hq hendq hhead
    have hcroot : value r c = value r left := by simpa only [endpoint] using hendp
    cases hq with
    | stop d hd hmax =>
      have hdroot : value r d = value r right := by simpa only [endpoint] using hendq
      have he := hcroot.symm.trans (hhead.trans hdroot)
      exact False.elim (he.not_lt hroots)
    | next d b ys hd hdb hbs harg hrest =>
      simp only [List.map_cons, List.map_nil, hhead]
      exact List.Lex.cons List.Lex.nil
  | next c a xs hc hca has harg hrest ih =>
    intro hendp d ys hq hendq hhead
    have hcroot : value r c ≤ value r left :=
      ((SourcePath.next c a xs hc hca has harg hrest).le_endpoint c List.mem_cons_self).trans_eq hendp
    have haroot : value r a ≤ value r left :=
      (hrest.le_endpoint a List.mem_cons_self).trans_eq (by simpa only [endpoint] using hendp)
    cases hq with
    | stop d hd hmax =>
      have hdroot : value r d = value r right := by simpa only [endpoint] using hendq
      have hb : value r right ≤ value r left := by rw [← hdroot, ← hhead]; exact hcroot
      exact False.elim (hroots.not_ge hb)
    | next d b ys hd hdb hbs hbarg hbrest =>
      have hpfull := SourcePath.next c a xs hc hca has harg hrest
      have hqfull := SourcePath.next d b ys hd hdb hbs hbarg hbrest
      have hab := selected_cross_order r left right c d a b xs ys hl hr hpfull hqfull
        hhead (haroot.trans hroots.le)
      simp only [List.map_cons, hhead]
      apply List.Lex.cons
      by_cases he : value r a = value r b
      · have ht := ih (by simpa only [endpoint] using hendp) b ys hbrest
          (by simpa only [endpoint] using hendq) he
        exact ht
      · exact List.Lex.rel (lt_of_le_of_ne hab he)

theorem sourcePath_values_lex_iff (r left right c d : Nat) (xs ys : List Nat)
    (hl : Node r left) (hr : Node r right)
    (hp : SourcePath r (support left) (c :: xs))
    (hq : SourcePath r (support right) (d :: ys))
    (hendp : value r (endpoint (c :: xs)) = value r left)
    (hendq : value r (endpoint (d :: ys)) = value r right)
    (hhead : value r c = value r d) :
    List.Lex (· < ·) ((c :: xs).map (value r)) ((d :: ys).map (value r)) ↔
      value r left < value r right := by
  constructor
  · intro hx
    rcases lt_trichotomy (value r left) (value r right) with h | h | h
    · exact h
    · have he := sourcePath_values_eq r left right c xs hl hr hp h hendp d ys hq hendq hhead
      rw [he] at hx
      exact False.elim ((asymm hx) hx)
    · have hy := sourcePath_values_lex r right left d ys hr hl hq h hendq c xs hp hendp hhead.symm
      exact False.elim ((asymm hy) hx)
  · intro h
    exact sourcePath_values_lex r left right c xs hl hr hp h hendp d ys hq hendq hhead

noncomputable def values (r c : Nat) : List Ordinal.{0} := (nativePath r c).map (value r)

noncomputable def selectedValues (r c : Nat) : List Ordinal.{0} :=
  ((nativePath r c).tail).map (value r)

theorem values_eq_of_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : values r c = values r d := by
  have hi := (inputCheck_exact r c).mpr hc
  have hj := (inputCheck_exact r d).mpr hd
  obtain ⟨xs, hx⟩ := nativePath_head r c
  obtain ⟨ys, hy⟩ := nativePath_head r d
  have hp := nativePath_source r c hi
  have hq := nativePath_source r d hj
  have hep := nativePath_end r c hi
  have heq := nativePath_end r d hj
  rw [hx] at hp hep
  rw [hy] at hq heq
  simpa only [values, hx, hy] using
    sourcePath_values_eq r c d (baseRaw r) xs hc hd hp he hep _ ys hq heq rfl

/-- Actual value-path equality implies equal canonical emissions, even when
the two native roots and support lists have different spellings. -/
theorem word_eq_of_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : Localization.word r c = Localization.word r d := by
  have hi := (inputCheck_exact r c).mpr hc
  have hj := (inputCheck_exact r d).mpr hd
  exact emit_map_eq_of_values_eq r _ _ (nativePath_nodes r c hi) (nativePath_nodes r d hj)
    (values_eq_of_value_eq r c d hc hd he)

theorem values_lex_iff (r c d : Nat) (hc : Node r c) (hd : Node r d) :
    List.Lex (· < ·) (values r c) (values r d) ↔ value r c < value r d := by
  have hi := (inputCheck_exact r c).mpr hc
  have hj := (inputCheck_exact r d).mpr hd
  obtain ⟨xs, hx⟩ := nativePath_head r c
  obtain ⟨ys, hy⟩ := nativePath_head r d
  have hp := nativePath_source r c hi
  have hq := nativePath_source r d hj
  have hep := nativePath_end r c hi
  have heq := nativePath_end r d hj
  rw [hx] at hp hep
  rw [hy] at hq heq
  simpa only [values, hx, hy] using
    sourcePath_values_lex_iff r c d (baseRaw r) (baseRaw r) xs ys hc hd hp hq hep heq rfl

/-- Literal source 2.35, with the initial relative base removed as printed.
The converse and base-valued endpoints are included. -/
theorem selectedValues_lex_iff (r c d : Nat) (hc : Node r c) (hd : Node r d) :
    List.Lex (· < ·) (selectedValues r c) (selectedValues r d) ↔ value r c < value r d := by
  obtain ⟨xs, hx⟩ := nativePath_head r c
  obtain ⟨ys, hy⟩ := nativePath_head r d
  have h := values_lex_iff r c d hc hd
  simpa only [values, selectedValues, hx, hy, List.tail_cons, List.map_cons,
    List.lex_cons_iff] using h

theorem source_lemma_2_35 (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (hproper : finiteBase r < value r c) (hlt : value r c < value r d) :
    List.Lex (· < ·) (selectedValues r c) (selectedValues r d) :=
  (selectedValues_lex_iff r c d hc hd).mpr hlt

/-- The separate base endpoint is a singleton regardless of its native spelling. -/
theorem base_values (r c : Nat) (hc : Node r c) (hv : value r c = finiteBase r) :
    values r c = [finiteBase r] := by
  have hi := (inputCheck_exact r c).mpr hc
  obtain ⟨xs, hx⟩ := nativePath_head r c
  have hp := nativePath_source r c hi
  have hep := nativePath_end r c hi
  have hs : SourcePath r (support c) [baseRaw r] := SourcePath.stop _ (baseRaw_node r)
    (fun e he => by rw [baseRaw_value]; exact (support_bound r c e hc he).trans_eq hv)
  have hes : value r (endpoint [baseRaw r]) = value r c := by
    simp only [endpoint, baseRaw_value, hv]
  rw [hx] at hp hep
  have he := sourcePath_values_eq r c c (baseRaw r) xs hc hc hp rfl hep
    (baseRaw r) [] hs hes rfl
  simpa only [values, hx, List.map_cons, List.map_nil, baseRaw_value] using he

theorem base_selectedValues (r c : Nat) (hc : Node r c) (hv : value r c = finiteBase r) :
    selectedValues r c = [] := by
  obtain ⟨xs, hx⟩ := nativePath_head r c
  have h := base_values r c hc hv
  have ht : xs.map (value r) = [] := by
    have he : finiteBase r :: xs.map (value r) = [finiteBase r] := by
      simpa only [values, hx, List.map_cons, baseRaw_value] using h
    exact (List.cons.inj he).2
  simpa only [selectedValues, hx, List.tail_cons] using ht

noncomputable def rawValues (r c : Nat) : List Ordinal.{0} :=
  values r (Theta.Normalization.normalizeCode r c)

noncomputable def rawSelectedValues (r c : Nat) : List Ordinal.{0} :=
  selectedValues r (Theta.Normalization.normalizeCode r c)

def rawWord (r c : Nat) : List Nat := Localization.word r (Theta.Normalization.normalizeCode r c)

theorem rawWord_primrec : Primrec₂ rawWord :=
  (Localization.word_primrec.comp Primrec.fst Theta.Normalization.Effective.normalizeCode_primrec).to₂

/-- Original admission and literal theta-zero shape suffice; no input
normality premise is added to the raw adapter. -/
theorem raw_values_lex_iff (r c d : Nat)
    (hc : SourceZeta.rawInputCheck r c = true) (hd : SourceZeta.rawInputCheck r d = true) :
    List.Lex (· < ·) (rawValues r c) (rawValues r d) ↔ value r c < value r d := by
  have hcn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r c hc)
  have hdn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r d hd)
  have hcv := (Theta.Normalization.normalizeCode_checked r c (Bool.and_eq_true.mp hc).1).2.2
  have hdv := (Theta.Normalization.normalizeCode_checked r d (Bool.and_eq_true.mp hd).1).2.2
  simpa only [rawValues, value, hcv, hdv] using values_lex_iff r _ _ hcn hdn

theorem raw_selectedValues_lex_iff (r c d : Nat)
    (hc : SourceZeta.rawInputCheck r c = true) (hd : SourceZeta.rawInputCheck r d = true) :
    List.Lex (· < ·) (rawSelectedValues r c) (rawSelectedValues r d) ↔ value r c < value r d := by
  have hcn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r c hc)
  have hdn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r d hd)
  have hcv := (Theta.Normalization.normalizeCode_checked r c (Bool.and_eq_true.mp hc).1).2.2
  have hdv := (Theta.Normalization.normalizeCode_checked r d (Bool.and_eq_true.mp hd).1).2.2
  simpa only [rawSelectedValues, value, hcv, hdv] using selectedValues_lex_iff r _ _ hcn hdn

theorem raw_values_eq_of_value_eq (r c d : Nat)
    (hc : SourceZeta.rawInputCheck r c = true) (hd : SourceZeta.rawInputCheck r d = true)
    (he : value r c = value r d) : rawValues r c = rawValues r d := by
  have hcn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r c hc)
  have hdn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r d hd)
  have hcv := (Theta.Normalization.normalizeCode_checked r c (Bool.and_eq_true.mp hc).1).2.2
  have hdv := (Theta.Normalization.normalizeCode_checked r d (Bool.and_eq_true.mp hd).1).2.2
  exact values_eq_of_value_eq r _ _ hcn hdn (hcv.trans (he.trans hdv.symm))

theorem rawWord_eq_of_value_eq (r c d : Nat)
    (hc : SourceZeta.rawInputCheck r c = true) (hd : SourceZeta.rawInputCheck r d = true)
    (he : value r c = value r d) : rawWord r c = rawWord r d := by
  have hcn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r c hc)
  have hdn := (SourceZeta.inputCheck_exact r _).mp (SourceZeta.raw_normalized_input r d hd)
  have hcv := (Theta.Normalization.normalizeCode_checked r c (Bool.and_eq_true.mp hc).1).2.2
  have hdv := (Theta.Normalization.normalizeCode_checked r d (Bool.and_eq_true.mp hd).1).2.2
  exact word_eq_of_value_eq r _ _ hcn hdn (hcv.trans (he.trans hdv.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Order
