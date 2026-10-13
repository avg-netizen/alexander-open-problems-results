import Alexander313.Carlson.RationalPresentation
import Alexander313.Carlson.FiniteDerivationNormalization

/-!
# Natural-number recognition of rational generating derivations

A rational certificate consists of one finite increasing grid, two Boolean
endpoint tables, and a natural-number certificate for the finite calculus.
The grid covers the entire finite ambient type, including points used only
by intermediate structures. Its positive size permits the existing
finite-derivation transport theorem; empty endpoint carriers are allowed.

The executable checks verify the grid and both carrier-sensitive endpoint
isomorphisms before accepting the finite derivation. Raw rational edge
tables may contain off-carrier entries, which do not affect these endpoint
isomorphisms. All decoding and bounded-search operations are total.

Soundness and completeness identify existential acceptance with rational
generating rules, exact generation, and generation by restriction. The
classical supporting-frame argument appears only in completeness proofs.
No termination claim is made for an unsuccessful unbounded search, and no
`Program` computability theorem or effective fair sequence is asserted.
-/

namespace Alexander313.Carlson.Finite

/-- Untrusted finite data for a rational derivation on one common grid. -/
structure RationalWitness (n : ℕ) where
  labels : Fin n → ℚ
  source : PatternCode n
  target : PatternCode n
  derivation : ℕ
  deriving Encodable

/-- The grid size is part of the natural-number certificate. -/
abbrev RationalCertificate := Σ n, RationalWitness n

namespace RationalWitness

variable {n : ℕ}

/-- Check the whole ordered grid, its two claimed rational endpoints,
and the finite derivation selected by `finiteCheck`. -/
def check (c : RationalWitness n)
    (finiteCheck : PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) : Bool :=
  letI : Decidable (StrictMono c.labels) := by
    unfold StrictMono
    infer_instance
  decide (0 < n ∧ StrictMono c.labels ∧
    Str.IsIso c.source.toStr P.toStr c.labels ∧
    Str.IsIso c.target.toStr Q.toStr c.labels) &&
      finiteCheck c.source c.target c.derivation

@[simp] theorem check_eq_true (c : RationalWitness n)
    (finiteCheck : PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) :
    c.check finiteCheck P Q = true ↔
      0 < n ∧ StrictMono c.labels ∧
        Str.IsIso c.source.toStr P.toStr c.labels ∧
        Str.IsIso c.target.toStr Q.toStr c.labels ∧
        finiteCheck c.source c.target c.derivation = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end RationalWitness

/-- Search the first `bound` candidate codes with a supplied total check. -/
def acceptsBelow (test : ℕ → Bool) (bound : ℕ) : Bool :=
  (List.range bound).any test

@[simp] theorem acceptsBelow_eq_true (test : ℕ → Bool) (bound : ℕ) :
    acceptsBelow test bound = true ↔
      ∃ code, code < bound ∧ test code = true := by
  simp only [acceptsBelow, List.any_eq_true, List.mem_range]

/-- Once a bounded search accepts, every larger search accepts as well. -/
theorem acceptsBelow_mono {test : ℕ → Bool} {m n : ℕ} (hmn : m ≤ n)
    (h : acceptsBelow test m = true) : acceptsBelow test n = true := by
  obtain ⟨code, hcode, hc⟩ := (acceptsBelow_eq_true test m).mp h
  exact (acceptsBelow_eq_true test n).mpr ⟨code, hcode.trans_le hmn, hc⟩

/-- Bounded search eventually succeeds exactly when an accepted code exists. -/
theorem exists_acceptsBelow_iff (test : ℕ → Bool) :
    (∃ bound, acceptsBelow test bound = true) ↔ ∃ code, test code = true := by
  constructor
  · rintro ⟨bound, h⟩
    obtain ⟨code, _, hc⟩ := (acceptsBelow_eq_true test bound).mp h
    exact ⟨code, hc⟩
  · rintro ⟨code, hc⟩
    exact ⟨code + 1, (acceptsBelow_eq_true test (code + 1)).mpr
      ⟨code, Nat.lt_succ_self code, hc⟩⟩

namespace RationalPresentation

/-- Decode a common-grid witness and reject every failed decode or check. -/
def checkCertificate
    (finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) (code : ℕ) : Bool :=
  match Encodable.decode (α := RationalCertificate) code with
  | none => false
  | some c => c.2.check (finiteCheck c.1) P Q

theorem checkCertificate_eq_true
    (finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) (code : ℕ) :
    checkCertificate finiteCheck P Q code = true ↔
      ∃ c : RationalCertificate, Encodable.decode code = some c ∧
        c.2.check (finiteCheck c.1) P Q = true := by
  cases hd : Encodable.decode (α := RationalCertificate) code <;>
    simp [checkCertificate, hd]

/-- A known witness can be checked without evaluating its numeric encoding. -/
@[simp] theorem checkCertificate_encode
    (finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool)
    (P Q : RationalPresentation) (c : RationalCertificate) :
    checkCertificate finiteCheck P Q (Encodable.encode c) =
      c.2.check (finiteCheck c.1) P Q := by
  simp only [checkCertificate, Encodable.encodek]

/-- Recognize a rational generating rule by a finite common-grid certificate. -/
def checkRule (P Q : RationalPresentation) (code : ℕ) : Bool :=
  checkCertificate (fun n => @Alexander313.Carlson.Finite.checkRule n) P Q code

/-- Recognize an exact generating chain on rational labels. -/
def checkChain (P Q : RationalPresentation) (code : ℕ) : Bool :=
  checkCertificate (fun n => @Alexander313.Carlson.Finite.checkChain n) P Q code

/-- Recognize rational generation by restriction of an exact chain. -/
def checkGeneration (P Q : RationalPresentation) (code : ℕ) : Bool :=
  checkCertificate (fun n => @Alexander313.Carlson.Finite.checkGeneration n) P Q code

theorem checkRule_sound {P Q : RationalPresentation} {code : ℕ}
    (h : checkRule P Q code = true) : Str.GeneratingRule P.toStr Q.toStr := by
  obtain ⟨⟨n, c⟩, _, hc⟩ :=
    (checkCertificate_eq_true
      (fun n => @Alexander313.Carlson.Finite.checkRule n) P Q code).mp h
  obtain ⟨hn, hm, eP, eQ, hd⟩ := (RationalWitness.check_eq_true c _ P Q).mp hc
  exact checkRule_sound_of_labels hn hm eP eQ hd

theorem checkChain_sound {P Q : RationalPresentation} {code : ℕ}
    (h : checkChain P Q code = true) : Str.ExactlyGenerates P.toStr Q.toStr := by
  obtain ⟨⟨n, c⟩, _, hc⟩ :=
    (checkCertificate_eq_true
      (fun n => @Alexander313.Carlson.Finite.checkChain n) P Q code).mp h
  obtain ⟨hn, hm, eP, eQ, hd⟩ := (RationalWitness.check_eq_true c _ P Q).mp hc
  exact checkChain_sound_of_labels hn hm eP eQ hd

theorem checkGeneration_sound {P Q : RationalPresentation} {code : ℕ}
    (h : checkGeneration P Q code = true) : Str.Generates P.toStr Q.toStr := by
  obtain ⟨⟨n, c⟩, _, hc⟩ :=
    (checkCertificate_eq_true
      (fun n => @Alexander313.Carlson.Finite.checkGeneration n) P Q code).mp h
  obtain ⟨hn, hm, eP, eQ, hd⟩ := (RationalWitness.check_eq_true c _ P Q).mp hc
  exact checkGeneration_sound_of_labels hn hm eP eQ hd

/-- Every rational generating rule has an accepted natural-number witness. -/
theorem checkRule_complete {P Q : RationalPresentation}
    (h : Str.GeneratingRule P.toStr Q.toStr) :
    ∃ code, checkRule P Q code = true := by
  obtain ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩ :=
    generatingRule_finite_complete h
  let c : RationalCertificate := ⟨n, ⟨labels, C, D, code⟩⟩
  refine ⟨Encodable.encode c, ?_⟩
  rw [checkRule, checkCertificate_encode]
  exact (RationalWitness.check_eq_true _ _ P Q).mpr ⟨hn, hm, eP, eQ, hc⟩

/-- Every exact rational chain has an accepted natural-number witness. -/
theorem checkChain_complete {P Q : RationalPresentation}
    (h : Str.ExactlyGenerates P.toStr Q.toStr) :
    ∃ code, checkChain P Q code = true := by
  obtain ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩ :=
    exactlyGenerates_finite_complete h
  let c : RationalCertificate := ⟨n, ⟨labels, C, D, code⟩⟩
  refine ⟨Encodable.encode c, ?_⟩
  rw [checkChain, checkCertificate_encode]
  exact (RationalWitness.check_eq_true _ _ P Q).mpr ⟨hn, hm, eP, eQ, hc⟩

/-- Every rational generation witness has an accepted natural-number code. -/
theorem checkGeneration_complete {P Q : RationalPresentation}
    (h : Str.Generates P.toStr Q.toStr) :
    ∃ code, checkGeneration P Q code = true := by
  obtain ⟨n, hn, labels, C, D, code, hm, eP, eQ, hc⟩ :=
    generates_finite_complete h
  let c : RationalCertificate := ⟨n, ⟨labels, C, D, code⟩⟩
  refine ⟨Encodable.encode c, ?_⟩
  rw [checkGeneration, checkCertificate_encode]
  exact (RationalWitness.check_eq_true _ _ P Q).mpr ⟨hn, hm, eP, eQ, hc⟩

/-- Exact positive certificate recognition of rational generating rules. -/
theorem generatingRule_iff_exists_code (P Q : RationalPresentation) :
    Str.GeneratingRule P.toStr Q.toStr ↔ ∃ code, checkRule P Q code = true :=
  ⟨checkRule_complete, fun ⟨_, h⟩ => checkRule_sound h⟩

/-- Exact positive certificate recognition of rational exact generation. -/
theorem exactlyGenerates_iff_exists_code (P Q : RationalPresentation) :
    Str.ExactlyGenerates P.toStr Q.toStr ↔ ∃ code, checkChain P Q code = true :=
  ⟨checkChain_complete, fun ⟨_, h⟩ => checkChain_sound h⟩

/-- Exact positive certificate recognition of rational generation. -/
theorem generates_iff_exists_code (P Q : RationalPresentation) :
    Str.Generates P.toStr Q.toStr ↔ ∃ code, checkGeneration P Q code = true :=
  ⟨checkGeneration_complete, fun ⟨_, h⟩ => checkGeneration_sound h⟩

/-- Arbitrary off-carrier propositional values do not affect recognition
after choosing finite presentations of the endpoints. -/
theorem generatingRule_iff_encoded_code (P Q : Str ℚ) :
    Str.GeneratingRule P Q ↔
      ∃ code, checkRule (encode P) (encode Q) code = true := by
  constructor
  · intro h
    exact checkRule_complete
      (h.of_isIso (presentation_iso P) (presentation_iso Q) (fun _ _ => rfl))
  · intro h
    have hd := (generatingRule_iff_exists_code (encode P) (encode Q)).mpr h
    exact hd.of_isIso (presentation_iso P).symm_id (presentation_iso Q).symm_id
      (fun _ _ => rfl)

/-- Exact-chain recognition also respects arbitrary off-carrier values. -/
theorem exactlyGenerates_iff_encoded_code (P Q : Str ℚ) :
    Str.ExactlyGenerates P Q ↔
      ∃ code, checkChain (encode P) (encode Q) code = true := by
  constructor
  · intro h
    exact checkChain_complete
      (h.of_identity_isos (presentation_iso P) (presentation_iso Q))
  · intro h
    have hd := (exactlyGenerates_iff_exists_code (encode P) (encode Q)).mpr h
    exact hd.of_identity_isos (presentation_iso P).symm_id (presentation_iso Q).symm_id

/-- Generation recognition also respects arbitrary off-carrier values. -/
theorem generates_iff_encoded_code (P Q : Str ℚ) :
    Str.Generates P Q ↔
      ∃ code, checkGeneration (encode P) (encode Q) code = true := by
  constructor
  · intro h
    exact checkGeneration_complete
      (h.of_identity_isos (presentation_iso P) (presentation_iso Q))
  · intro h
    have hd := (generates_iff_exists_code (encode P) (encode Q)).mpr h
    exact hd.of_identity_isos (presentation_iso P).symm_id (presentation_iso Q).symm_id

/-- Bounded certificate search eventually accepts exactly the rational rules. -/
theorem generatingRule_iff_eventually_accepts (P Q : RationalPresentation) :
    Str.GeneratingRule P.toStr Q.toStr ↔
      ∃ bound, acceptsBelow (checkRule P Q) bound = true :=
  (generatingRule_iff_exists_code P Q).trans (exists_acceptsBelow_iff _).symm

/-- Bounded certificate search eventually accepts exactly the exact chains. -/
theorem exactlyGenerates_iff_eventually_accepts (P Q : RationalPresentation) :
    Str.ExactlyGenerates P.toStr Q.toStr ↔
      ∃ bound, acceptsBelow (checkChain P Q) bound = true :=
  (exactlyGenerates_iff_exists_code P Q).trans (exists_acceptsBelow_iff _).symm

/-- Bounded certificate search eventually accepts exactly generation. -/
theorem generates_iff_eventually_accepts (P Q : RationalPresentation) :
    Str.Generates P.toStr Q.toStr ↔
      ∃ bound, acceptsBelow (checkGeneration P Q) bound = true :=
  (generates_iff_exists_code P Q).trans (exists_acceptsBelow_iff _).symm

end RationalPresentation
end Alexander313.Carlson.Finite
