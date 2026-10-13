import Alexander313.Carlson.RationalExactness
import Alexander313.Carlson.RationalMaps
import Alexander313.Carlson.RationalAmalgamation

/-!
# Executable finite certificates for actual amalgamations

The target, each embedding's finite map table, and each exactness certificate
are ordinary finite data. The verifier checks the original Definition 15.8
obligations. Completeness uses the proved rational finite-edge existence;
the checker itself uses neither ordinal labels nor a comparison oracle.
-/

namespace Alexander313.Carlson.Finite

/-- Existing product and finite-function codecs store all candidate data.
The last field contains the generation certificate for each input image. -/
abbrev AmalgamationCertificate (n : ℕ) :=
  RationalPresentation × (Fin n → RationalMap.Table) × (Fin n → ℕ)

/-- Pin the existing vector-based finite-function codecs for the new
candidate format. This also agrees with mathlib's primitive-recursive
finite-function codec; general `Fintype` enumeration is not involved. -/
instance instEncodableAmalgamationCertificate (n : ℕ) : Encodable (AmalgamationCertificate n) :=
  @Encodable.Prod.encodable RationalPresentation _ inferInstance
    (@Encodable.Prod.encodable (Fin n → RationalMap.Table) (Fin n → ℕ)
      (@Encodable.finArrow RationalMap.Table inferInstance n)
      (@Encodable.finArrow ℕ inferInstance n))

namespace AmalgamationCertificate

variable {n : ℕ}

/-- The total map given by a candidate's finite table for an input. -/
def maps (c : AmalgamationCertificate n) (i : Fin n) : ℚ → ℚ :=
  RationalMap.eval (c.2.1 i)

/-- The induced input image in the proposed target, preserving stored tables. -/
def image (P : Fin n → RationalPresentation) (c : AmalgamationCertificate n)
    (i : Fin n) : RationalPresentation :=
  c.1.restrict ((P i).U.image (c.maps i))

private def isoDecidable (P Q : RationalPresentation) (f : ℚ → ℚ) :
    Decidable (Str.IsIso P.toStr Q.toStr f) := by
  unfold Str.IsIso
  infer_instance

/-- Every stored input embedding is checked on its actual finite carrier. -/
def checkEmbeddings (P : Fin n → RationalPresentation) (c : AmalgamationCertificate n) : Bool :=
  letI : ∀ i, Decidable (Str.IsIso (P i).toStr (c.image P i).toStr (c.maps i)) :=
    fun i => isoDecidable (P i) (c.image P i) (c.maps i)
  decide (∀ i, Str.IsIso (P i).toStr (c.image P i).toStr (c.maps i))

@[simp] theorem checkEmbeddings_eq_true (P : Fin n → RationalPresentation)
    (c : AmalgamationCertificate n) :
    c.checkEmbeddings P = true ↔
      ∀ i, Str.IsIso (P i).toStr (c.image P i).toStr (c.maps i) := by
  simp only [checkEmbeddings, decide_eq_true_eq]

/-- A total finite verifier for the proposed amalgamation and all of its
exactness witnesses. An ordinary covered union is not enough for acceptance. -/
def check (P : Fin n → RationalPresentation) (c : AmalgamationCertificate n) : Bool :=
  decide c.1.toStr.IsPattern && c.checkEmbeddings P &&
    decide (c.1.U = Finset.univ.biUnion (fun i => (P i).U.image (c.maps i))) &&
    decide (∀ i, RationalPresentation.checkExact (c.image P i) c.1 (c.2.2 i) = true)

@[simp] theorem check_eq_true (P : Fin n → RationalPresentation)
    (c : AmalgamationCertificate n) :
    c.check P = true ↔ c.1.toStr.IsPattern ∧
      (∀ i, Str.IsIso (P i).toStr (c.image P i).toStr (c.maps i)) ∧
      c.1.U = Finset.univ.biUnion (fun i => (P i).U.image (c.maps i)) ∧
      (∀ i, RationalPresentation.checkExact (c.image P i) c.1 (c.2.2 i) = true) := by
  simp only [check, Bool.and_eq_true, checkEmbeddings_eq_true, decide_eq_true_eq, and_assoc]

/-- Acceptance gives the original amalgamation on the actual decoded target. -/
theorem check_sound {P : Fin n → RationalPresentation} {c : AmalgamationCertificate n}
    (hc : c.check P = true) :
    Str.Amalgamation (fun i => (P i).toStr) c.1.toStr c.maps := by
  obtain ⟨hp, he, hu, hx⟩ := (check_eq_true P c).mp hc
  refine ⟨hp, ?_, hu, ?_⟩
  · intro i
    simpa only [image, RationalPresentation.toStr_restrict, RationalPresentation.toStr_U] using he i
  · intro i
    simpa only [image, RationalPresentation.toStr_restrict, RationalPresentation.toStr_U] using
      RationalPresentation.checkExact_sound (hx i)

/-- Every actual rational amalgamation has certificate tables that agree
with its supplied maps on the input carriers, with the same target. -/
theorem check_complete {P : Fin n → RationalPresentation} {Q : RationalPresentation}
    {f : Fin n → ℚ → ℚ} (d : Str.Amalgamation (fun i => (P i).toStr) Q.toStr f) :
    ∃ c : AmalgamationCertificate n, c.1 = Q ∧ c.check P = true ∧
      ∀ i, ∀ x ∈ (P i).U, c.maps i x = f i x := by
  classical
  let t (i : Fin n) := RationalMap.graph (P i).U (f i)
  let g (i : Fin n) := RationalMap.eval (t i)
  have hfix : ∀ i, ∀ x ∈ (P i).U, g i x = f i x :=
    fun _ _ hx => RationalMap.eval_graph hx
  have dg := d.congr_on_carriers hfix
  have hex : ∀ i, ∃ k, RationalPresentation.checkExact
      (Q.restrict ((P i).U.image (g i))) Q k = true := by
    intro i
    apply RationalPresentation.checkExact_complete
    simpa only [RationalPresentation.toStr_restrict, RationalPresentation.toStr_U] using dg.exact i
  choose k hk using hex
  let c : AmalgamationCertificate n := (Q, t, k)
  refine ⟨c, rfl, (check_eq_true P c).mpr ?_, hfix⟩
  refine ⟨dg.pattern, ?_, dg.union, hk⟩
  intro i
  change Str.IsIso (P i).toStr (Q.toStr.restrict ((P i).U.image (g i))) (g i)
  simpa only [RationalPresentation.toStr_U] using dg.embeddings i

/-- Decode an untrusted candidate and reject a malformed code. -/
def checkCode (P : Fin n → RationalPresentation) (code : ℕ) : Bool :=
  match Encodable.decode (α := AmalgamationCertificate n) code with
  | none => false
  | some c => c.check P

@[simp] theorem checkCode_encode (P : Fin n → RationalPresentation)
    (c : AmalgamationCertificate n) :
    checkCode P (Encodable.encode c) = c.check P := by
  simp only [checkCode, Encodable.encodek]

theorem checkCode_eq_true (P : Fin n → RationalPresentation) (code : ℕ) :
    checkCode P code = true ↔ ∃ c : AmalgamationCertificate n,
      Encodable.decode code = some c ∧ c.check P = true := by
  cases hd : Encodable.decode (α := AmalgamationCertificate n) code <;>
    simp [checkCode, hd]

/-- Sound and complete positive certificate recognition of finite-edge
amalgamation existence for arbitrary finite input presentations. -/
theorem exists_amalgamation_iff_code (P : Fin n → RationalPresentation) :
    (∃ (Q : RationalPresentation) (f : Fin n → ℚ → ℚ),
      Str.Amalgamation (fun i => (P i).toStr) Q.toStr f) ↔
        ∃ code, checkCode P code = true := by
  constructor
  · rintro ⟨Q, f, d⟩
    obtain ⟨c, _, hc, _⟩ := check_complete d
    exact ⟨Encodable.encode c, (checkCode_encode P c).trans hc⟩
  · rintro ⟨code, hc⟩
    obtain ⟨c, _, h⟩ := (checkCode_eq_true P code).mp hc
    exact ⟨c.1, c.maps, check_sound h⟩

/-- Every finite family of pure pattern presentations has an accepted code.
This is the termination witness for an exhaustive certificate search. -/
theorem exists_code (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern) :
    ∃ code, checkCode P code = true :=
  (exists_amalgamation_iff_code P).mp (exists_presented_amalgamation _ hP)

end AmalgamationCertificate
end Alexander313.Carlson.Finite
