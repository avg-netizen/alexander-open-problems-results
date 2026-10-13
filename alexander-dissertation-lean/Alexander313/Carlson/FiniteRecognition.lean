import Alexander313.Carlson.FiniteCertificates

/-!
# Natural-number recognition of finite generating certificates

These total Boolean recognizers decode an untrusted natural number, verify
the resulting finite certificate, and compare both endpoints with the
claimed Boolean tables. Acceptance is sound for the existing generating
calculus; every derivation on `Fin n` has an accepted natural-number code.

The existential characterizations provide certificate recognition and
effective enumeration by natural-number search. They do not give a
termination bound for searching for a derivation that may not exist, or
a decision procedure for unbounded generation on rational labels.
-/

namespace Alexander313.Carlson.Finite

variable {n : ℕ}

/-- Decode, verify, and check both endpoints of a generating-rule certificate. -/
def checkRule (P Q : PatternCode n) (code : ℕ) : Bool :=
  match Encodable.decode (α := RuleCertificate n) code with
  | none => false
  | some c => c.check && decide (c.source = P ∧ c.target = Q)

theorem checkRule_eq_true (P Q : PatternCode n) (code : ℕ) :
    checkRule P Q code = true ↔ ∃ c : RuleCertificate n,
      Encodable.decode code = some c ∧ c.check = true ∧ c.source = P ∧ c.target = Q := by
  cases hd : Encodable.decode (α := RuleCertificate n) code <;>
    simp [checkRule, hd, Bool.and_eq_true]

/-- A decoded certificate proves the original rule between the claimed endpoints. -/
theorem checkRule_sound {P Q : PatternCode n} {code : ℕ} (h : checkRule P Q code = true) :
    Str.GeneratingRule P.toStr Q.toStr := by
  obtain ⟨c, _, hc, hs, ht⟩ := (checkRule_eq_true P Q code).mp h
  simpa only [hs, ht] using c.sound hc

theorem checkRule_complete {P Q : PatternCode n} (h : Str.GeneratingRule P.toStr Q.toStr) :
    ∃ code : ℕ, checkRule P Q code = true := by
  obtain ⟨c, hc, hs, ht⟩ := RuleCertificate.complete h
  refine ⟨Encodable.encode c, (checkRule_eq_true P Q _).mpr ?_⟩
  exact ⟨c, Encodable.encodek c, hc, PatternCode.toStr_injective hs,
    PatternCode.toStr_injective ht⟩

/-- Exact certificate characterization of finite generating rules. -/
theorem generatingRule_iff_exists_code (P Q : PatternCode n) :
    Str.GeneratingRule P.toStr Q.toStr ↔ ∃ code : ℕ, checkRule P Q code = true :=
  ⟨checkRule_complete, fun ⟨_, h⟩ => checkRule_sound h⟩

/-- Decode, verify, and check both endpoints of an exact-generation certificate. -/
def checkChain (P Q : PatternCode n) (code : ℕ) : Bool :=
  match Encodable.decode (α := ChainCertificate n) code with
  | none => false
  | some c => c.check && decide (c.source = P ∧ c.target = Q)

theorem checkChain_eq_true (P Q : PatternCode n) (code : ℕ) :
    checkChain P Q code = true ↔ ∃ c : ChainCertificate n,
      Encodable.decode code = some c ∧ c.check = true ∧ c.source = P ∧ c.target = Q := by
  cases hd : Encodable.decode (α := ChainCertificate n) code <;>
    simp [checkChain, hd, Bool.and_eq_true]

theorem checkChain_sound {P Q : PatternCode n} {code : ℕ} (h : checkChain P Q code = true) :
    Str.ExactlyGenerates P.toStr Q.toStr := by
  obtain ⟨c, _, hc, hs, ht⟩ := (checkChain_eq_true P Q code).mp h
  simpa only [hs, ht] using c.sound hc

theorem checkChain_complete {P Q : PatternCode n} (h : Str.ExactlyGenerates P.toStr Q.toStr) :
    ∃ code : ℕ, checkChain P Q code = true := by
  obtain ⟨c, hc, hs, ht⟩ := ChainCertificate.complete h
  refine ⟨Encodable.encode c, (checkChain_eq_true P Q _).mpr ?_⟩
  exact ⟨c, Encodable.encodek c, hc, PatternCode.toStr_injective hs,
    PatternCode.toStr_injective ht⟩

/-- Exact certificate characterization of finite exact generation. -/
theorem exactlyGenerates_iff_exists_code (P Q : PatternCode n) :
    Str.ExactlyGenerates P.toStr Q.toStr ↔ ∃ code : ℕ, checkChain P Q code = true :=
  ⟨checkChain_complete, fun ⟨_, h⟩ => checkChain_sound h⟩

/-- Decode, verify, and check both endpoints of a generation-by-restriction certificate. -/
def checkGeneration (P Q : PatternCode n) (code : ℕ) : Bool :=
  match Encodable.decode (α := GenerationCertificate n) code with
  | none => false
  | some c => c.check && decide (c.source = P ∧ c.target = Q)

theorem checkGeneration_eq_true (P Q : PatternCode n) (code : ℕ) :
    checkGeneration P Q code = true ↔ ∃ c : GenerationCertificate n,
      Encodable.decode code = some c ∧ c.check = true ∧ c.source = P ∧ c.target = Q := by
  cases hd : Encodable.decode (α := GenerationCertificate n) code <;>
    simp [checkGeneration, hd, Bool.and_eq_true]

theorem checkGeneration_sound {P Q : PatternCode n} {code : ℕ}
    (h : checkGeneration P Q code = true) : Str.Generates P.toStr Q.toStr := by
  obtain ⟨c, _, hc, hs, ht⟩ := (checkGeneration_eq_true P Q code).mp h
  simpa only [hs, ht] using c.sound hc

theorem checkGeneration_complete {P Q : PatternCode n} (h : Str.Generates P.toStr Q.toStr) :
    ∃ code : ℕ, checkGeneration P Q code = true := by
  obtain ⟨c, hc, hs, ht⟩ := GenerationCertificate.complete h
  refine ⟨Encodable.encode c, (checkGeneration_eq_true P Q _).mpr ?_⟩
  exact ⟨c, Encodable.encodek c, hc, PatternCode.toStr_injective hs,
    PatternCode.toStr_injective ht⟩

/-- Exact certificate characterization of finite generation by restriction. -/
theorem generates_iff_exists_code (P Q : PatternCode n) :
    Str.Generates P.toStr Q.toStr ↔ ∃ code : ℕ, checkGeneration P Q code = true :=
  ⟨checkGeneration_complete, fun ⟨_, h⟩ => checkGeneration_sound h⟩

/-- Accepted natural-number certificates inherit cofinal validity. -/
theorem checkRule_cofinallyValid {P Q : PatternCode n} {code : ℕ}
    (h : checkRule P Q code = true) : Str.CofinallyValid P.toStr Q.toStr :=
  (checkRule_sound h).cofinallyValid

theorem checkChain_cofinallyValid {P Q : PatternCode n} {code : ℕ}
    (h : checkChain P Q code = true) : Str.CofinallyValid P.toStr Q.toStr :=
  (checkChain_sound h).cofinallyValid

theorem checkGeneration_cofinallyValid {P Q : PatternCode n} {code : ℕ}
    (h : checkGeneration P Q code = true) : Str.CofinallyValid P.toStr Q.toStr :=
  (checkGeneration_sound h).cofinallyValid

/-- Ordinal coveredness remains an explicit source hypothesis. -/
theorem checkGeneration_covered {P Q : PatternCode n} {code : ℕ}
    (h : checkGeneration P Q code = true) (hP : Str.Covered P.toStr) :
    Str.Covered Q.toStr :=
  (checkGeneration_sound h).valid.covered hP

/-- A checked generated extension inherits covering rigidity. -/
theorem checkGeneration_le_of_coversInto {P Q : PatternCode n} {code : ℕ}
    (h : checkGeneration P Q code = true) (hP : Str.Covered P.toStr)
    {f : Fin n → Fin n} (hf : Str.CoversInto P.toStr Q.toStr f)
    {x : Fin n} (hx : x ∈ P.U) : x ≤ f x :=
  (checkGeneration_sound h).le_of_coversInto hP hf hx

end Alexander313.Carlson.Finite
