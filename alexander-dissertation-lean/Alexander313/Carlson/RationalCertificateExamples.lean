import Alexander313.Carlson.RationalRecognition

/-!
# Kernel-checked rational certificate regressions

The examples use a two-point labeling grid with a one-point carrier. The
unused grid point makes it possible to distinguish the required global
strict monotonicity from order preservation merely on the carrier.

Both the outer rational witness and its inner finite derivation are
encoded as natural numbers. Acceptance is proved through the two decoder
specifications, using encode/decode identities as propositions. Only the
separate small grid, endpoint, and finite-certificate facts are reduced by
Lean's kernel; no numerical encoder or decoder is passed to `decide`.
-/

namespace Alexander313.Carlson.Finite.RationalCertificateExamples

set_option maxRecDepth 8192

/-- Prove acceptance from the stated witness, without reducing either its
encoding or the decoder. This proof is generic in the witness data. -/
private theorem checkCertificate_of_witness
    (finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) (c : RationalCertificate)
    (hc : c.2.check (finiteCheck c.1) P Q = true) :
    RationalPresentation.checkCertificate finiteCheck P Q (Encodable.encode c) = true :=
  (RationalPresentation.checkCertificate_eq_true
    finiteCheck P Q (Encodable.encode c)).mpr ⟨c, Encodable.encodek c, hc⟩

private theorem accepts_encoded_rule {n : ℕ} (labels : Fin n → ℚ)
    (d : RuleCertificate n) (P Q : RationalPresentation)
    (hn : 0 < n) (hm : StrictMono labels)
    (eP : Str.IsIso d.source.toStr P.toStr labels)
    (eQ : Str.IsIso d.target.toStr Q.toStr labels) (hd : d.check = true) :
    RationalPresentation.checkRule P Q
      (Encodable.encode
        (⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩ : RationalCertificate)) =
      true := by
  apply checkCertificate_of_witness
  apply (RationalWitness.check_eq_true _ _ P Q).mpr
  refine ⟨hn, hm, eP, eQ, ?_⟩
  exact (checkRule_eq_true d.source d.target (Encodable.encode d)).mpr
    ⟨d, Encodable.encodek d, hd, rfl, rfl⟩

private theorem accepts_encoded_chain {n : ℕ} (labels : Fin n → ℚ)
    (d : ChainCertificate n) (P Q : RationalPresentation)
    (hn : 0 < n) (hm : StrictMono labels)
    (eP : Str.IsIso d.source.toStr P.toStr labels)
    (eQ : Str.IsIso d.target.toStr Q.toStr labels) (hd : d.check = true) :
    RationalPresentation.checkChain P Q
      (Encodable.encode
        (⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩ : RationalCertificate)) =
      true := by
  apply checkCertificate_of_witness
  apply (RationalWitness.check_eq_true _ _ P Q).mpr
  refine ⟨hn, hm, eP, eQ, ?_⟩
  exact (checkChain_eq_true d.source d.target (Encodable.encode d)).mpr
    ⟨d, Encodable.encodek d, hd, rfl, rfl⟩

private theorem accepts_encoded_generation {n : ℕ} (labels : Fin n → ℚ)
    (d : GenerationCertificate n) (P Q : RationalPresentation)
    (hn : 0 < n) (hm : StrictMono labels)
    (eP : Str.IsIso d.source.toStr P.toStr labels)
    (eQ : Str.IsIso d.target.toStr Q.toStr labels) (hd : d.check = true) :
    RationalPresentation.checkGeneration P Q
      (Encodable.encode
        (⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩ : RationalCertificate)) =
      true := by
  apply checkCertificate_of_witness
  apply (RationalWitness.check_eq_true _ _ P Q).mpr
  refine ⟨hn, hm, eP, eQ, ?_⟩
  exact (checkGeneration_eq_true d.source d.target (Encodable.encode d)).mpr
    ⟨d, Encodable.encodek d, hd, rfl, rfl⟩

/-- Project the fields of an accepted encoded rule. The only rewrite is
performed while the witness is a variable, before inspecting its data. -/
private theorem encoded_rule_iff {n : ℕ} (c : RationalWitness n)
    (P Q : RationalPresentation) :
    RationalPresentation.checkRule P Q
      (Encodable.encode (⟨n, c⟩ : RationalCertificate)) = true ↔
      0 < n ∧ StrictMono c.labels ∧
        Str.IsIso c.source.toStr P.toStr c.labels ∧
        Str.IsIso c.target.toStr Q.toStr c.labels ∧
        checkRule c.source c.target c.derivation = true := by
  rw [RationalPresentation.checkRule, RationalPresentation.checkCertificate_encode]
  exact RationalWitness.check_eq_true c _ P Q

private theorem bool_eq_false_of_not_true {b : Bool} (h : b = true → False) :
    b = false := by
  cases b with
  | false => rfl
  | true => exact (h rfl).elim

/-- The point `0` is the whole carrier; grid point `1` is unused. -/
def point : PatternCode 2 where
  U := {0}
  r₁ _ _ := true
  r₂ _ _ := true

def labels (i : Fin 2) : ℚ := i.val

def singleton : RationalPresentation where
  U := {0}
  r₁ := {(0, 0)}
  r₂ := {(0, 0)}

def rule : RuleCertificate 2 := .arithmetic point point

def chain : ChainCertificate 2 := .tail (.refl point) rule

def generation : GenerationCertificate 2 := ⟨chain, point⟩

def ruleWitness : RationalWitness 2 :=
  ⟨labels, point, point, Encodable.encode rule⟩

def chainWitness : RationalWitness 2 :=
  ⟨labels, point, point, Encodable.encode chain⟩

def generationWitness : RationalWitness 2 :=
  ⟨labels, point, point, Encodable.encode generation⟩

def ruleCode : ℕ := Encodable.encode (⟨2, ruleWitness⟩ : RationalCertificate)

def chainCode : ℕ := Encodable.encode (⟨2, chainWitness⟩ : RationalCertificate)

def generationCode : ℕ := Encodable.encode (⟨2, generationWitness⟩ : RationalCertificate)

theorem rational_nat_roundtrip :
    Encodable.decode (α := RationalCertificate) ruleCode = some ⟨2, ruleWitness⟩ :=
  Encodable.encodek _

theorem rule_accepts :
    RationalPresentation.checkRule singleton singleton ruleCode = true := by
  exact accepts_encoded_rule labels rule singleton singleton
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

theorem chain_accepts :
    RationalPresentation.checkChain singleton singleton chainCode = true := by
  exact accepts_encoded_chain labels chain singleton singleton
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

theorem generation_accepts :
    RationalPresentation.checkGeneration singleton singleton generationCode = true := by
  exact accepts_encoded_generation labels generation singleton singleton
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

/-- The carrier has a negative nonintegral label, followed by an unused positive label. -/
def fractionalLabels (i : Fin 2) : ℚ := if i = 0 then -(1 : ℚ) / 2 else 1

def fractionalSingleton : RationalPresentation where
  U := {-(1 : ℚ) / 2}
  r₁ := {(-(1 : ℚ) / 2, -(1 : ℚ) / 2)}
  r₂ := {(-(1 : ℚ) / 2, -(1 : ℚ) / 2)}

def fractionalWitness : RationalWitness 2 := { ruleWitness with labels := fractionalLabels }

def fractionalCode : ℕ := Encodable.encode (⟨2, fractionalWitness⟩ : RationalCertificate)

theorem rule_accepts_negative_fraction :
    RationalPresentation.checkRule fractionalSingleton fractionalSingleton fractionalCode =
      true := by
  exact accepts_encoded_rule fractionalLabels rule fractionalSingleton fractionalSingleton
    (by decide) (by unfold StrictMono; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide)

/-- Equal labels at the unused grid point still preserve the one-point carrier. -/
def duplicateLabels (_ : Fin 2) : ℚ := 0

/-- The unused point is placed before the carrier point. -/
def reversedUnusedLabels (i : Fin 2) : ℚ := -(i.val : ℚ)

theorem duplicate_labels_preserve_carrier :
    RationalPresentation.checkIso point duplicateLabels singleton = true := by decide

theorem reversed_unused_labels_preserve_carrier :
    RationalPresentation.checkIso point reversedUnusedLabels singleton = true := by decide

def duplicateWitness : RationalWitness 2 := { ruleWitness with labels := duplicateLabels }

def reversedUnusedWitness : RationalWitness 2 :=
  { ruleWitness with labels := reversedUnusedLabels }

def duplicateCode : ℕ := Encodable.encode (⟨2, duplicateWitness⟩ : RationalCertificate)

def reversedUnusedCode : ℕ :=
  Encodable.encode (⟨2, reversedUnusedWitness⟩ : RationalCertificate)

/-- The whole labeling grid must be injective, including points outside the carrier. -/
theorem rule_rejects_duplicate_unused_label :
    RationalPresentation.checkRule singleton singleton duplicateCode = false := by
  apply bool_eq_false_of_not_true
  intro h
  have hm : StrictMono duplicateLabels :=
    ((encoded_rule_iff duplicateWitness singleton singleton).mp h).2.1
  have hbad : ¬ StrictMono duplicateLabels := by
    unfold StrictMono
    decide
  exact hbad hm

/-- The whole labeling grid must also have the right order. -/
theorem rule_rejects_reversed_unused_label :
    RationalPresentation.checkRule singleton singleton reversedUnusedCode = false := by
  apply bool_eq_false_of_not_true
  intro h
  have hm : StrictMono reversedUnusedLabels :=
    ((encoded_rule_iff reversedUnusedWitness singleton singleton).mp h).2.1
  have hbad : ¬ StrictMono reversedUnusedLabels := by
    unfold StrictMono
    decide
  exact hbad hm

def wrongCarrier : RationalPresentation := { singleton with U := {1} }

def missingEdge : RationalPresentation := { singleton with r₁ := ∅ }

theorem rule_rejects_wrong_carrier :
    RationalPresentation.checkRule singleton wrongCarrier ruleCode = false := by
  apply bool_eq_false_of_not_true
  intro h
  have eQ : Str.IsIso point.toStr wrongCarrier.toStr labels :=
    ((encoded_rule_iff ruleWitness singleton wrongCarrier).mp h).2.2.2.1
  have hbad : ¬ Str.IsIso point.toStr wrongCarrier.toStr labels := by decide
  exact hbad eQ

theorem rule_rejects_wrong_on_carrier_edge :
    RationalPresentation.checkRule singleton missingEdge ruleCode = false := by
  apply bool_eq_false_of_not_true
  intro h
  have eQ : Str.IsIso point.toStr missingEdge.toStr labels :=
    ((encoded_rule_iff ruleWitness singleton missingEdge).mp h).2.2.2.1
  have hbad : ¬ Str.IsIso point.toStr missingEdge.toStr labels := by decide
  exact hbad eQ

/-- Off-carrier edges need not satisfy the order or relation-inclusion axioms. -/
def offCarrierEdges : RationalPresentation where
  U := singleton.U
  r₁ := {(0, 0), (1, 0)}
  r₂ := {(0, 0), (0, 1)}

theorem off_carrier_tables_differ : offCarrierEdges ≠ singleton := by decide

/-- Recognition compares the induced finite structures at both endpoints. -/
theorem rule_accepts_off_carrier_edges :
    RationalPresentation.checkRule offCarrierEdges offCarrierEdges ruleCode = true := by
  exact accepts_encoded_rule labels rule offCarrierEdges offCarrierEdges
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

def empty : PatternCode 0 where
  U := ∅
  r₁ _ _ := false
  r₂ _ _ := false

def emptyPresentation : RationalPresentation := ⟨∅, ∅, ∅⟩

def zeroWitness : RationalWitness 0 where
  labels := Fin.elim0
  source := empty
  target := empty
  derivation := Encodable.encode (RuleCertificate.arithmetic empty empty)

def zeroCode : ℕ := Encodable.encode (⟨0, zeroWitness⟩ : RationalCertificate)

/-- An empty carrier is permitted, but the certificate's ambient grid must
be nonempty so its maps extend to total rational maps in the soundness proof. -/
theorem rule_rejects_zero_grid :
    RationalPresentation.checkRule emptyPresentation emptyPresentation zeroCode = false := by
  apply bool_eq_false_of_not_true
  intro h
  have hn : 0 < (0 : ℕ) :=
    ((encoded_rule_iff zeroWitness emptyPresentation emptyPresentation).mp h).1
  exact (by decide : ¬ 0 < (0 : ℕ)) hn

/-- An empty endpoint carrier represented inside a positive one-point grid. -/
def positiveEmpty : PatternCode 1 where
  U := ∅
  r₁ _ _ := false
  r₂ _ _ := false

/-- Both edge sets are nonempty, but every edge is outside the empty carrier. -/
def emptyWithEdges : RationalPresentation where
  U := ∅
  r₁ := {(1, 0)}
  r₂ := {(0, 1)}

def positiveEmptyWitness : RationalWitness 1 where
  labels := fun _ => 0
  source := positiveEmpty
  target := positiveEmpty
  derivation := Encodable.encode (RuleCertificate.arithmetic positiveEmpty positiveEmpty)

def positiveEmptyCode : ℕ :=
  Encodable.encode (⟨1, positiveEmptyWitness⟩ : RationalCertificate)

theorem rule_accepts_empty_carriers :
    RationalPresentation.checkRule emptyWithEdges emptyWithEdges positiveEmptyCode = true := by
  exact accepts_encoded_rule (fun _ => 0)
    (RuleCertificate.arithmetic positiveEmpty positiveEmpty) emptyWithEdges emptyWithEdges
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

/-- One audit entry point covers accepted derivations, complete-grid label
checks, endpoint checks, negative fractions, off-carrier freedom, and the
difference between empty carriers and a zero grid. -/
theorem regression_suite :
    RationalPresentation.checkRule singleton singleton ruleCode = true ∧
    RationalPresentation.checkChain singleton singleton chainCode = true ∧
    RationalPresentation.checkGeneration singleton singleton generationCode = true ∧
    RationalPresentation.checkRule fractionalSingleton fractionalSingleton fractionalCode = true ∧
    RationalPresentation.checkIso point duplicateLabels singleton = true ∧
    RationalPresentation.checkIso point reversedUnusedLabels singleton = true ∧
    RationalPresentation.checkRule singleton singleton duplicateCode = false ∧
    RationalPresentation.checkRule singleton singleton reversedUnusedCode = false ∧
    RationalPresentation.checkRule singleton wrongCarrier ruleCode = false ∧
    RationalPresentation.checkRule singleton missingEdge ruleCode = false ∧
    offCarrierEdges ≠ singleton ∧
    RationalPresentation.checkRule offCarrierEdges offCarrierEdges ruleCode = true ∧
    RationalPresentation.checkRule emptyPresentation emptyPresentation zeroCode = false ∧
    RationalPresentation.checkRule emptyWithEdges emptyWithEdges positiveEmptyCode = true :=
  ⟨rule_accepts, chain_accepts, generation_accepts, rule_accepts_negative_fraction,
    duplicate_labels_preserve_carrier, reversed_unused_labels_preserve_carrier,
    rule_rejects_duplicate_unused_label, rule_rejects_reversed_unused_label,
    rule_rejects_wrong_carrier, rule_rejects_wrong_on_carrier_edge,
    off_carrier_tables_differ, rule_accepts_off_carrier_edges, rule_rejects_zero_grid,
    rule_accepts_empty_carriers⟩

end Alexander313.Carlson.Finite.RationalCertificateExamples
