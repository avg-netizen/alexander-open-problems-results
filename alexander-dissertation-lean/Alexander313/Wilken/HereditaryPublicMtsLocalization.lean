import Alexander313.Wilken.HereditaryPublicMts
import Alexander313.Wilken.PublicEpsilonNativeLocalizationValueInvariance

/-!
# Independent numerical localization prefixes for the least-cover recursion

Actual checked native paths have genuine ordinal VALUE-prefix locality.
Their canonical public returns turn that VALUE law into literal numerical
path equality. The real OWN interval derives the independent public query
at every selected endpoint, so a recursive stored prefix is the same
localization used by actual execution there. No written native identity,
subquery, localization-prefix or output word is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Localization

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota

def publicPath (gamma root : Nat) : List Nat :=
  (SourceLocalization.nativePath gamma root).map (UniformPublicReturn.publicCode gamma)

theorem public_values (gamma : Nat) (xs : List Nat)
    (hn : ∀ c ∈ xs, SourceLocalization.Node gamma c) :
    (xs.map (UniformPublicReturn.publicCode gamma)).map unionInterpretation =
      xs.map (SourceLocalization.value gamma) := by
  rw [List.map_map]
  exact List.map_congr_left (fun c hc => (node_public_spec gamma c (hn c hc)).2)

theorem publicPath_checked (gamma root : Nat)
    (hi : SourceLocalization.inputCheck gamma root = true) :
    ∀ c ∈ publicPath gamma root, Canonical.check c = true := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact (node_public_spec gamma d (SourceLocalization.nativePath_nodes gamma root hi d hd)).1

theorem publicPath_values (gamma root : Nat)
    (hi : SourceLocalization.inputCheck gamma root = true) :
    (publicPath gamma root).map unionInterpretation =
      (SourceLocalization.nativePath gamma root).map (SourceLocalization.value gamma) :=
  public_values gamma _ (SourceLocalization.nativePath_nodes gamma root hi)

theorem publicPath_eq (gamma left right : Nat)
    (hl : SourceLocalization.inputCheck gamma left = true)
    (hr : SourceLocalization.inputCheck gamma right = true)
    (he : interpretation gamma left = interpretation gamma right) :
    publicPath gamma left = publicPath gamma right := by
  apply SkPublicValueInvariance.canonical_words_eq _ _
    (publicPath_checked gamma left hl) (publicPath_checked gamma right hr)
  exact (publicPath_values gamma left hl).trans
    ((SourceLocalization.ValueInvariance.nativePath_values_eq gamma left right hl hr he).trans
      (publicPath_values gamma right hr).symm)

/-- Genuine native VALUE-prefix locality becomes literal canonical public
prefix locality, without equality of any written native support witness. -/
theorem publicPath_prefix (gamma root : Nat)
    (hi : SourceLocalization.inputCheck gamma root = true)
    (before : List Nat) (current : Nat) (after : List Nat)
    (he : SourceLocalization.nativePath gamma root = before ++ current :: after) :
    (before ++ [current]).map (UniformPublicReturn.publicCode gamma) = publicPath gamma current := by
  have hc : current ∈ SourceLocalization.nativePath gamma root := by
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hn := SourceLocalization.nativePath_nodes gamma root hi current hc
  have hj := (SourceLocalization.inputCheck_exact gamma current).mpr hn
  have hprefixNodes : ∀ c ∈ before ++ [current], SourceLocalization.Node gamma c := by
    intro c hc
    apply SourceLocalization.nativePath_nodes gamma root hi c
    rw [he]
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append.mpr (Or.inl hc)
    · rw [List.mem_singleton.mp hc]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  apply SkPublicValueInvariance.canonical_words_eq _ _
    (fun c hc => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact (node_public_spec gamma d (hprefixNodes d hd)).1)
    (publicPath_checked gamma current hj)
  exact (public_values gamma _ hprefixNodes).trans
    ((SourceLocalization.Properties.nativePath_value_prefix gamma root hi before current after he).trans
      (publicPath_values gamma current hj).symm)

theorem localization_eq (gamma beta d e : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (he : e ∈ SkNextSearch.Support.search gamma beta) :
    localization gamma d = localization gamma e :=
  publicPath_eq gamma _ _ (nativeRoot_spec gamma beta d hi hd).1
    (nativeRoot_spec gamma beta e hi he).1
    ((nativeRoot_spec gamma beta d hi hd).2.trans (nativeRoot_spec gamma beta e hi he).2.symm)

/-- Node admission derives real positive principal status, not an extra
canonical subquery premise. -/
theorem node_principal (gamma current : Nat) (hn : SourceLocalization.Node gamma current) :
    0 < interpretation gamma current ∧ Ordinal.IsPrincipal (· + ·) (interpretation gamma current) := by
  obtain ⟨a, rfl, ha, hnormal⟩ := hn
  simpa only [interpretation_code] using Iota.OrderInduction.checked_theta_pos_principal gamma 0 a ha

theorem current_caller (gamma beta d current : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hc : current ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d)) :
    inputCheck gamma (UniformPublicReturn.publicCode gamma current) = true := by
  have hn := SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 current hc
  have hp := node_public_spec gamma current hn
  have ht := node_principal gamma current hn
  have hfloor : unionInterpretation gamma ≤ interpretation gamma current := by
    have hf := SourceLocalization.baseRaw_le gamma current hn
    simpa only [SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi)] using hf
  have hcut := (localization_bounded gamma beta d hi hd current hc).trans_lt
    ((inputCheck_exact gamma beta).mp hi).2.2.2.2.2
  exact (inputCheck_exact gamma _).mpr
    ⟨((inputCheck_exact gamma beta).mp hi).1, hp.1,
      hp.2.symm ▸ ht.1, hp.2.symm ▸ ht.2, hfloor.trans_eq hp.2.symm, hp.2.symm ▸ hcut⟩

/-- The independent search at an actually selected endpoint computes the
same whole numerical localization as that endpoint's actual native Node. -/
theorem current_localization_eq (gamma beta d current e : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hc : current ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d))
    (he : e ∈ SkNextSearch.Support.search gamma (UniformPublicReturn.publicCode gamma current)) :
    localization gamma e = publicPath gamma current := by
  have hcaller := current_caller gamma beta d current hi hd hc
  have hs := nativeRoot_spec gamma _ e hcaller he
  have hn := SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1 current hc
  have hp := node_public_spec gamma current hn
  exact publicPath_eq gamma _ current hs.1
    ((SourceLocalization.inputCheck_exact gamma current).mpr hn) (hs.2.trans hp.2)

/-- A stored chronological prefix is an actual independent execution at
its selected endpoint. Both its search caller and its entire localization
are derived from the original executing query. -/
theorem execute_at_prefix (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (before : List Nat) (current : Nat) (after : List Nat)
    (he : SourceLocalization.nativePath gamma (nativeRoot gamma d) = before ++ current :: after) :
    Support.word gamma ((before ++ [current]).map (UniformPublicReturn.publicCode gamma)).tail ∈
      execute gamma (UniformPublicReturn.publicCode gamma current) := by
  have hc : current ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d) := by
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hcaller := current_caller gamma beta d current hi hd hc
  obtain ⟨e, hs⟩ := search_returns gamma _ hcaller
  have hprefix := publicPath_prefix gamma (nativeRoot gamma d)
    (nativeRoot_spec gamma beta d hi hd).1 before current after he
  have hlocal := current_localization_eq gamma beta d current e hi hd hc hs
  have hw : Support.word gamma ((before ++ [current]).map (UniformPublicReturn.publicCode gamma)).tail =
      Support.word gamma (localization gamma e).tail :=
    congrArg (fun cs => Support.word gamma cs.tail) (hprefix.trans hlocal.symm)
  rw [hw]
  simpa only [execute, hcaller, Bool.cond_true] using
    Part.mem_map (fun e => Support.word gamma (localization gamma e).tail) hs

theorem execute_word_eq (gamma beta : Nat) (xs ys : List Nat)
    (hx : xs ∈ execute gamma beta) (hy : ys ∈ execute gamma beta) : xs = ys := by
  obtain ⟨hi, d, hd, rfl⟩ := execute_spec gamma beta xs hx
  obtain ⟨hj, e, he, rfl⟩ := execute_spec gamma beta ys hy
  exact congrArg (fun cs => Support.word gamma cs.tail) (localization_eq gamma beta d e hi hd he)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Localization
