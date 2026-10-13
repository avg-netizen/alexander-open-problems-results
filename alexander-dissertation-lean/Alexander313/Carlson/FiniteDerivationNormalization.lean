import Alexander313.Carlson.GeneratingRelabeling
import Alexander313.Carlson.FiniteFrame
import Alexander313.Carlson.FiniteRecognition

/-!
# Finite certificates for derivations in an ambient order

In every nonempty linear order, a generating rule, exact chain or generation
by restriction is equivalent to an accepted finite certificate on one common
increasing grid of ambient labels. In particular this closes the finite-label
gap for rational derivations.

The grid includes the hidden carriers of the entire derivation. Both endpoint
isomorphisms use the same grid, and the reverse implication transports all
intermediate structures. An empty endpoint carrier is allowed; the positive
bound is obtained by adding one ambient point to the supporting frame.

Finite acceptance remains executable. Extracting a frame or encoding arbitrary
propositional relation tables belongs to the classical existence proof; no
termination claim is made for searching for a nonexistent derivation.
-/

noncomputable section

namespace Alexander313.Carlson.Finite

variable {α : Type*} [LinearOrder α]

/-- A finite frame yields a common increasing presentation of both endpoints
and any property known to survive relabeling that frame. -/
private theorem normalize_supported [Nonempty α] {P Q : Str α} {S : Finset α}
    (hP : P.U ⊆ S) (hQ : Q.U ⊆ S)
    (R : ∀ n : ℕ, Str (Fin n) → Str (Fin n) → Prop)
    (hR : ∀ (n : ℕ) (F : FiniteRelabeling S (Fin n)),
      R n (P.map F.toFun) (Q.map F.toFun)) :
    ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n),
      StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
        Str.IsIso D.toStr Q labels ∧ R n C.toStr D.toStr := by
  let a : α := Classical.choice inferInstance
  let T : Finset α := insert a S
  have hST : S ⊆ T := Finset.subset_insert a S
  have hT : T.Nonempty := Finset.insert_nonempty a S
  let F := FiniteRelabeling.toFinOfNonempty T hT
  refine ⟨T.card, Finset.card_pos.mpr hT, F.invFun,
    PatternCode.encode (P.map F.toFun), PatternCode.encode (Q.map F.toFun),
    FiniteRelabeling.toFinOfNonempty_invFun_strictMono T hT, ?_, ?_, ?_⟩
  · simpa only [PatternCode.toStr_encode] using F.inverse_isIso (hP.trans hST)
  · simpa only [PatternCode.toStr_encode] using F.inverse_isIso (hQ.trans hST)
  · simpa only [PatternCode.toStr_encode, FiniteRelabeling.restrict] using
      hR T.card (F.restrict hST)

/-- An accepted rule on one increasing grid proves the rule between its
ambient endpoints. The grid covers the full finite ambient type. -/
theorem checkRule_sound_of_labels {n : ℕ} (hn : 0 < n)
    {labels : Fin n → α} (hmono : StrictMono labels) {C D : PatternCode n}
    {P Q : Str α} (eP : Str.IsIso C.toStr P labels) (eQ : Str.IsIso D.toStr Q labels)
    {code : ℕ} (hc : checkRule C D code = true) : Str.GeneratingRule P Q := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have d := (checkRule_sound hc).map_of_strictMono hmono
  have iP := (C.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eP
  have iQ := (D.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eQ
  exact d.of_isIso iP iQ (fun _ _ => rfl)

/-- An accepted chain on a common increasing grid proves ambient exact generation. -/
theorem checkChain_sound_of_labels {n : ℕ} (hn : 0 < n)
    {labels : Fin n → α} (hmono : StrictMono labels) {C D : PatternCode n}
    {P Q : Str α} (eP : Str.IsIso C.toStr P labels) (eQ : Str.IsIso D.toStr Q labels)
    {code : ℕ} (hc : checkChain C D code = true) : Str.ExactlyGenerates P Q := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have d := (checkChain_sound hc).map_of_strictMono hmono
  have iP := (C.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eP
  have iQ := (D.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eQ
  exact d.of_identity_isos iP iQ

/-- An accepted generation certificate on a common increasing grid proves
ambient generation, including its larger exact-chain witness. -/
theorem checkGeneration_sound_of_labels {n : ℕ} (hn : 0 < n)
    {labels : Fin n → α} (hmono : StrictMono labels) {C D : PatternCode n}
    {P Q : Str α} (eP : Str.IsIso C.toStr P labels) (eQ : Str.IsIso D.toStr Q labels)
    {code : ℕ} (hc : checkGeneration C D code = true) : Str.Generates P Q := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have d := (checkGeneration_sound hc).map_of_strictMono hmono
  have iP := (C.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eP
  have iQ := (D.toStr.map_isIso labels (fun _ _ _ _ h => hmono h)).id_of_same_map eQ
  exact d.of_identity_isos iP iQ

/-- Every ambient rule has an accepted finite certificate on a common grid. -/
theorem generatingRule_finite_complete [Nonempty α] {P Q : Str α}
    (d : Str.GeneratingRule P Q) :
    ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
      StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
        Str.IsIso D.toStr Q labels ∧ checkRule C D code = true := by
  obtain ⟨S, hP, hQ, hS⟩ := d.exists_relabeling_support
  obtain ⟨n, hn, labels, C, D, hm, eP, eQ, hd⟩ :=
    normalize_supported hP hQ (fun _ => Str.GeneratingRule)
      (fun n F => hS (Fin n) F)
  obtain ⟨code, hc⟩ := checkRule_complete hd
  exact ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩

/-- Every ambient exact chain has an accepted finite certificate. -/
theorem exactlyGenerates_finite_complete [Nonempty α] {P Q : Str α}
    (d : Str.ExactlyGenerates P Q) :
    ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
      StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
        Str.IsIso D.toStr Q labels ∧ checkChain C D code = true := by
  obtain ⟨S, hP, hQ, hS⟩ := d.exists_relabeling_support
  obtain ⟨n, hn, labels, C, D, hm, eP, eQ, hd⟩ :=
    normalize_supported hP hQ (fun _ => Str.ExactlyGenerates)
      (fun n F => hS (Fin n) F)
  obtain ⟨code, hc⟩ := checkChain_complete hd
  exact ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩

/-- Every ambient generation witness has an accepted finite certificate. -/
theorem generates_finite_complete [Nonempty α] {P Q : Str α}
    (d : Str.Generates P Q) :
    ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
      StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
        Str.IsIso D.toStr Q labels ∧ checkGeneration C D code = true := by
  obtain ⟨S, hP, hQ, hS⟩ := d.exists_relabeling_support
  obtain ⟨n, hn, labels, C, D, hm, eP, eQ, hd⟩ :=
    normalize_supported hP hQ (fun _ => Str.Generates)
      (fun n F => hS (Fin n) F)
  obtain ⟨code, hc⟩ := checkGeneration_complete hd
  exact ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩

/-- Exact finite-certificate characterization of generating rules in any
nonempty linear order, in particular on rational labels. -/
theorem generatingRule_iff_finite_certificate [Nonempty α] (P Q : Str α) :
    Str.GeneratingRule P Q ↔
      ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
        StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
          Str.IsIso D.toStr Q labels ∧ checkRule C D code = true := by
  constructor
  · exact generatingRule_finite_complete
  · rintro ⟨_, hn, _, _, _, _, hm, eP, eQ, hc⟩
    exact checkRule_sound_of_labels hn hm eP eQ hc

/-- Exact finite-certificate characterization of exact generation. -/
theorem exactlyGenerates_iff_finite_certificate [Nonempty α] (P Q : Str α) :
    Str.ExactlyGenerates P Q ↔
      ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
        StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
          Str.IsIso D.toStr Q labels ∧ checkChain C D code = true := by
  constructor
  · exact exactlyGenerates_finite_complete
  · rintro ⟨_, hn, _, _, _, _, hm, eP, eQ, hc⟩
    exact checkChain_sound_of_labels hn hm eP eQ hc

/-- Exact finite-certificate characterization of generation by restriction. -/
theorem generates_iff_finite_certificate [Nonempty α] (P Q : Str α) :
    Str.Generates P Q ↔
      ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
        StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
          Str.IsIso D.toStr Q labels ∧ checkGeneration C D code = true := by
  constructor
  · exact generates_finite_complete
  · rintro ⟨_, hn, _, _, _, _, hm, eP, eQ, hc⟩
    exact checkGeneration_sound_of_labels hn hm eP eQ hc

end Alexander313.Carlson.Finite
