import Alexander313.Wilken.HereditaryThetaNormalizationAtoms
import Alexander313.Wilken.HereditaryThetaNormal

/-!
# Actual full hereditary theta normalization and normal-code coverage

Normalization recurses on the finite hereditary level, then on the literal
tree. A positive-level parameter opens its actual earlier payload and records
the normalized low payload's code. Theta bodies normalize at the same level;
sums execute principal suffix absorption and source-normal reconstruction.

The proofs construct source admission, hereditary normality and genuine
finite/global denotation preservation from old admission alone. Actual normal
codes cover every old global notation and every ordinal below each next base.
Raw comparison after normalization is correct on all old-checked inputs.
No syntactic uniqueness or uniform compiler is asserted here. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization

private def normalizeTree (r : Nat) (parameterOp : Nat → RelativeTerm Nat) :
    RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => parameterOp p
  | .theta k a => .theta k (normalizeTree r parameterOp a)
  | .sum a b => buildAtoms r (normalizeAtoms r
      (atoms r (normalizeTree r parameterOp a) ++ atoms r (normalizeTree r parameterOp b)))

def normalize : Nat → RelativeTerm Nat → RelativeTerm Nat
  | 0, t => normalizeTree 0 (fun _ => .parameter 0) t
  | r + 1, t => normalizeTree (r + 1)
      (fun p => .parameter (normalize r (ThetaCourse.rawTree p)).code) t

@[simp] theorem normalize_parameter_zero (p : Nat) :
    normalize 0 (.parameter p) = .parameter 0 := rfl

@[simp] theorem normalize_parameter_succ (r p : Nat) :
    normalize (r + 1) (.parameter p) =
      .parameter (normalize r (ThetaCourse.rawTree p)).code := rfl

@[simp] theorem normalize_parameter_succ_code (r : Nat) (u : RelativeTerm Nat) :
    normalize (r + 1) (.parameter u.code) = .parameter (normalize r u).code := by
  simp only [normalize_parameter_succ, ThetaCourse.rawTree_code]

@[simp] theorem normalize_theta (r k : Nat) (a : RelativeTerm Nat) :
    normalize r (.theta k a) = .theta k (normalize r a) := by
  cases r <;> rfl

@[simp] theorem normalize_sum (r : Nat) (a b : RelativeTerm Nat) :
    normalize r (.sum a b) =
      buildAtoms r (normalizeAtoms r (atoms r (normalize r a) ++ atoms r (normalize r b))) := by
  cases r <;> rfl

private theorem lowCheck_of_value (r : Nat) (a : RelativeTerm Nat)
    (ha : check r a = true) (hvalue : denote r a < finiteBase (r + 1)) :
    lowCheck r a = true := by
  have hsort : a.outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le r a ha 1 (Nat.zero_lt_succ 0)).mp
      (hvalue.trans (finiteBase_lt_cardinal r))
  simp only [lowCheck, ha, hsort, decide_true, Bool.true_and]

/-- No normality assumption is made on the input. The lower parameter
induction constructs normal payloads and their actual retained low admission. -/
theorem normalize_spec (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    admissible r n (normalize r t) ∧ Normal r (normalize r t) ∧
      denote r (normalize r t) = denote r t := by
  induction r using Nat.strong_induction_on generalizing n t with
  | h r ihr =>
    revert ht
    induction t with
    | parameter p =>
      intro ht
      cases r with
      | zero =>
        have hp : p = 0 := by
          simpa only [Payloads, parameterCheck_zero, beq_iff_eq] using ht.1
        subst p
        exact ⟨ht, trivial, rfl⟩
      | succ r =>
        have hp : lowCheckCode r p = true := ht.1
        obtain ⟨u, hu, hlow⟩ := (lowCheckCode_iff r p).mp hp
        subst p
        have huc : check r u = true := (Bool.and_eq_true_iff.mp hlow).1
        let q := SourceOne.PublicCodes.fragment u
        have hua : admissible r q u := (finiteCheck_iff r q u).mp huc
        have hprev := ihr r (Nat.lt_succ_self r) q u hua
        have huvalue : denote r u < finiteBase (r + 1) :=
          (lt_nextBase_iff_checked r _).mpr ⟨u, hlow, rfl⟩
        have hnewlow : lowCheck r (normalize r u) = true :=
          lowCheck_of_value r (normalize r u) (admitted_checked hprev.1)
            (by rw [hprev.2.2]; exact huvalue)
        have hnewpayload : parameterCheck (r + 1) (normalize r u).code = true := by
          simpa only [parameterCheck_succ, lowCheckCode_code] using hnewlow
        have hnewad : admissible (r + 1) n (.parameter (normalize r u).code) :=
          ⟨hnewpayload, .parameter (by
            simpa only [omegaSequence_zero] using
              parameter_sound (r + 1) (normalize r u).code hnewpayload)⟩
        rw [normalize_parameter_succ_code]
        refine ⟨hnewad, ?_, ?_⟩
        · simpa only [normal_parameter_succ, decode_code, Option.getD_some] using hprev.2.1
        · change interpretation r (normalize r u).code = interpretation r u.code
          simpa only [interpretation_code] using hprev.2.2
    | theta k a ih =>
      intro ht
      cases ht.2 with
      | theta h0k hkn hsort ha =>
        have hprev := ih ⟨ht.1, ha⟩
        have hfinite : finiteDenote r n (normalize r a) = finiteDenote r n a := by
          rw [← denote_eq_finite r n (normalize r a) hprev.1.2,
            ← denote_eq_finite r n a ha]
          exact hprev.2.2
        have hnew : admissible r n (.theta k (normalize r a)) :=
          ⟨hprev.1.1, .theta h0k hkn (by
            change finiteDenote r n (normalize r a) < omegaSequence (finiteBase r) (k + 2)
            rw [hfinite]
            exact hsort) hprev.1.2⟩
        rw [normalize_theta]
        refine ⟨hnew, (normal_theta r k (normalize r a)).mpr hprev.2.1, ?_⟩
        change globalCollapse (finiteBase r) k (denote r (normalize r a)) =
          globalCollapse (finiteBase r) k (denote r a)
        rw [hprev.2.2]
    | sum a b iha ihb =>
      intro ht
      cases ht.2 with
      | sum ha hb =>
        have hpa := iha ⟨ht.1.1, ha⟩
        have hpb := ihb ⟨ht.1.2, hb⟩
        let word := atoms r (normalize r a) ++ atoms r (normalize r b)
        have hgood : GoodAtoms r n word :=
          (GoodAtoms.atoms r n (normalize r a) hpa.1 hpa.2.1).append
            (GoodAtoms.atoms r n (normalize r b) hpb.1 hpb.2.1)
        have hnormal := normalizeAtoms_normal r n word hgood
        have hretained := hgood.normalizeAtoms
        rw [normalize_sum]
        refine ⟨buildAtoms_admissible r n (normalizeAtoms r word) hretained,
          buildAtoms_normal r n (normalizeAtoms r word) hretained hnormal, ?_⟩
        calc
          denote r (buildAtoms r (normalizeAtoms r word)) =
              principalSum ((normalizeAtoms r word).map (denote r)) :=
            buildAtoms_denote r (normalizeAtoms r word)
          _ = principalSum (word.map (denote r)) := normalizeAtoms_denote r n word hgood
          _ = denote r (normalize r a) + denote r (normalize r b) := by
            rw [List.map_append, principalSum_append,
              atoms_denote_sum r n (normalize r a) hpa.1 hpa.2.1,
              atoms_denote_sum r n (normalize r b) hpb.1 hpb.2.1]
          _ = denote r (.sum a b) := by rw [hpa.2.2, hpb.2.2]; rfl

theorem normalize_admissible (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    admissible r n (normalize r t) := (normalize_spec r n t ht).1

theorem normalize_normal (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    Normal r (normalize r t) := (normalize_spec r n t ht).2.1

theorem normalize_denote (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    denote r (normalize r t) = denote r t := (normalize_spec r n t ht).2.2

theorem normalize_finiteDenote (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    finiteDenote r n (normalize r t) = finiteDenote r n t := by
  rw [← denote_eq_finite r n (normalize r t) (normalize_admissible r n t ht).2,
    ← denote_eq_finite r n t ht.2]
  exact normalize_denote r n t ht

theorem normalize_normalSums (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    NormalSums (finiteBase r) (parameters r) n (normalize r t) :=
  (normalize_normal r n t ht).finite (normalize_admissible r n t ht)

theorem normalize_checked (r n : Nat) (t : RelativeTerm Nat) (ht : admissible r n t) :
    check r (normalize r t) = true := admitted_checked (normalize_admissible r n t ht)

theorem normalize_lowChecked (r : Nat) (t : RelativeTerm Nat) (ht : lowCheck r t = true) :
    lowCheck r (normalize r t) = true := by
  have hac : check r t = true := (Bool.and_eq_true_iff.mp ht).1
  have ha := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp hac
  have hvalue := (lt_nextBase_iff_checked r _).mpr ⟨t, ht, rfl⟩
  apply lowCheck_of_value r (normalize r t) (normalize_checked r _ t ha)
  rw [normalize_denote r _ t ha]
  exact hvalue

def normalizeCode (r c : Nat) : Nat :=
  ((decode c).map (fun t => (normalize r t).code)).getD 0

@[simp] theorem normalizeCode_code (r : Nat) (t : RelativeTerm Nat) :
    normalizeCode r t.code = (normalize r t).code := by
  simp only [normalizeCode, decode_code, Option.map_some, Option.getD_some]

/-- The original checker rejects malformed whole codes before the default
interpretation is used. All output payloads retain real lower admissions. -/
theorem normalizeCode_checked (r c : Nat) (hc : checkCode r c = true) :
    checkCode r (normalizeCode r c) = true ∧
      Normal r (ThetaCourse.rawTree (normalizeCode r c)) ∧
      interpretation r (normalizeCode r c) = interpretation r c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff r c).mp hc
  have ha := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp ht
  have hs := normalize_spec r _ t ha
  simp only [normalizeCode_code, checkCode_code, ThetaCourse.rawTree_code, interpretation_code]
  exact ⟨admitted_checked hs.1, hs.2.1, hs.2.2⟩

theorem normalizeCode_lowChecked (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode r (normalizeCode r c) = true ∧
      Normal r (ThetaCourse.rawTree (normalizeCode r c)) ∧
      interpretation r (normalizeCode r c) = interpretation r c := by
  obtain ⟨t, rfl, ht⟩ := (lowCheckCode_iff r c).mp hc
  have hac : check r t = true := (Bool.and_eq_true_iff.mp ht).1
  have ha := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp hac
  have hs := normalize_spec r _ t ha
  simp only [normalizeCode_code, lowCheckCode_code, ThetaCourse.rawTree_code, interpretation_code]
  exact ⟨normalize_lowChecked r t ht, hs.2.1, hs.2.2⟩

theorem globalNotation_iff_normalCode (r : Nat) (ξ : Ordinal.{0}) :
    GlobalNotation (finiteBase r) 0 ξ ↔
      ∃ c : Nat, checkCode r c = true ∧ Normal r (ThetaCourse.rawTree c) ∧
        interpretation r c = ξ := by
  constructor
  · intro hξ
    obtain ⟨c, hc, hv⟩ := (globalNotation_iff_code r ξ).mp hξ
    have hn := normalizeCode_checked r c hc
    exact ⟨normalizeCode r c, hn.1, hn.2.1, hn.2.2.trans hv⟩
  · rintro ⟨c, hc, hn, hv⟩
    exact (globalNotation_iff_code r ξ).mpr ⟨c, hc, hv⟩

theorem lt_nextBase_iff_normalCode (r : Nat) (ξ : Ordinal.{0}) :
    ξ < finiteBase (r + 1) ↔
      ∃ c : Nat, lowCheckCode r c = true ∧ Normal r (ThetaCourse.rawTree c) ∧
        interpretation r c = ξ := by
  constructor
  · intro hξ
    obtain ⟨c, hc, hv⟩ := (lt_nextBase_iff_code r ξ).mp hξ
    have hn := normalizeCode_lowChecked r c hc
    exact ⟨normalizeCode r c, hn.1, hn.2.1, hn.2.2.trans hv⟩
  · rintro ⟨c, hc, hn, hv⟩
    exact (lt_nextBase_iff_code r ξ).mpr ⟨c, hc, hv⟩

theorem normalizeCode_accepted (r c : Nat) (hc : checkCode r c = true) :
    acceptedCode r (normalizeCode r c) = true ∧
      interpretation r (normalizeCode r c) = interpretation r c := by
  have hs := normalizeCode_checked r c hc
  exact ⟨(acceptedCode_iff r _).mpr ⟨hs.1, hs.2.1⟩, hs.2.2⟩

theorem normalizeCode_acceptedLow (r c : Nat) (hc : lowCheckCode r c = true) :
    acceptedLowCode r (normalizeCode r c) = true ∧
      interpretation r (normalizeCode r c) = interpretation r c := by
  have hs := normalizeCode_lowChecked r c hc
  exact ⟨(acceptedLowCode_iff r _).mpr ⟨hs.1, hs.2.1⟩, hs.2.2⟩

theorem globalNotation_iff_acceptedCode (r : Nat) (ξ : Ordinal.{0}) :
    GlobalNotation (finiteBase r) 0 ξ ↔
      ∃ c : Nat, acceptedCode r c = true ∧ interpretation r c = ξ := by
  simpa only [acceptedCode_iff, and_assoc] using globalNotation_iff_normalCode r ξ

theorem lt_nextBase_iff_acceptedLowCode (r : Nat) (ξ : Ordinal.{0}) :
    ξ < finiteBase (r + 1) ↔
      ∃ c : Nat, acceptedLowCode r c = true ∧ interpretation r c = ξ := by
  simpa only [acceptedLowCode_iff, and_assoc] using lt_nextBase_iff_normalCode r ξ

def lessRawCode (r c d : Nat) : Bool := lessCode r (normalizeCode r c) (normalizeCode r d)

def equalRawCode (r c d : Nat) : Bool := equalCode r (normalizeCode r c) (normalizeCode r d)

theorem lessRawCode_correct (r c d : Nat)
    (hc : checkCode r c = true) (hd : checkCode r d = true) :
    lessRawCode r c d = true ↔ interpretation r c < interpretation r d := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff r c).mp hc
  obtain ⟨u, rfl, hu⟩ := (checkCode_iff r d).mp hd
  have hat := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp ht
  have hau := (finiteCheck_iff r (SourceOne.PublicCodes.fragment u) u).mp hu
  have hst := normalize_spec r _ t hat
  have hsu := normalize_spec r _ u hau
  simpa only [lessRawCode, normalizeCode_code, lessCode_code, interpretation_code,
    hst.2.2, hsu.2.2] using less_correct r (normalize r t) (normalize r u)
      (admitted_checked hst.1) (admitted_checked hsu.1) hst.2.1 hsu.2.1

theorem equalRawCode_correct (r c d : Nat)
    (hc : checkCode r c = true) (hd : checkCode r d = true) :
    equalRawCode r c d = true ↔ interpretation r c = interpretation r d := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff r c).mp hc
  obtain ⟨u, rfl, hu⟩ := (checkCode_iff r d).mp hd
  have hat := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp ht
  have hau := (finiteCheck_iff r (SourceOne.PublicCodes.fragment u) u).mp hu
  have hst := normalize_spec r _ t hat
  have hsu := normalize_spec r _ u hau
  simpa only [equalRawCode, normalizeCode_code, equalCode_code, interpretation_code,
    hst.2.2, hsu.2.2] using equal_correct r (normalize r t) (normalize r u)
      (admitted_checked hst.1) (admitted_checked hsu.1) hst.2.1 hsu.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization
