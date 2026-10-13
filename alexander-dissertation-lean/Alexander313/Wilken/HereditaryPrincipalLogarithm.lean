import Alexander313.Wilken.HereditaryOmegaPowers

/-!
# An executing logarithm for actual positive additive principals

A genuine unbounded Nat search tests canonical exponent codes with the actual
omega-power algorithm. Every original positive additive principal has a real
omega exponent; that exponent is at most the original value, hence remains in
the actual canonical interval. This proves search termination. Strict increase
of actual omega powers and canonical value injection prove output uniqueness.
The search orders numerical codes, not ordinal values. No logarithm graph,
semantic decision, output chooser or effectivity oracle is assumed.
All proof terms are uncompiled, including the Nat.rfind output-specification API.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalLogarithm

/-- Both the positive-principal input and the canonical exponent output are
checked before genuine omega exponentiation and source equality are used. -/
def graph (q c : Nat) : Bool :=
  (Principal.unionPrincipalCheck q && Canonical.check c) &&
    Canonical.graph q (OmegaPowers.powerCode c)

theorem graph_primrec : Primrec₂ graph :=
  (Primrec.and.comp
    (Primrec.and.comp (Principal.unionPrincipalCheck_primrec.comp Primrec.fst)
      (Canonical.Effective.check_primrec.comp Primrec.snd))
    (Canonical.Effective.graph_primrec.comp Primrec.fst
      (OmegaPowers.powerCode_primrec.comp Primrec.snd))).to₂

theorem graph_exact (q c : Nat) : graph q c = true ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    have hd := (Principal.unionPrincipalCheck_exact q).mp (Bool.and_eq_true_iff.mp hs.1).1
    have hc := (Bool.and_eq_true_iff.mp hs.1).2
    have he := (Canonical.graph_exact q (OmegaPowers.powerCode c)).mp hs.2
    have hw := OmegaPowers.powerCode_value c (Canonical.check_original hc)
    exact ⟨hd.1, hd.2.1, hd.2.2, hc, hw.symm.trans he.2.2.symm⟩
  · rintro ⟨hq, hp, hprincipal, hc, he⟩
    have hu := Canonical.check_original hc
    have hw := OmegaPowers.powerCode_value c hu
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨(Principal.unionPrincipalCheck_exact q).mpr
      ⟨hq, hp, hprincipal⟩, hc⟩, ?_⟩
    exact (Canonical.graph_exact q _).mpr
      ⟨hq, OmegaPowers.powerCode_checked c hu, he.symm.trans hw.symm⟩

/-- The exponent is bounded by the actual principal value. Canonical interval
coverage constructs a legitimate search witness; termination is not assumed. -/
theorem graph_witness (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃ c : Nat, graph q c = true := by
  have hs := (Principal.unionPrincipalCheck_exact q).mp hq
  obtain ⟨η, hη⟩ := positive_additivePrincipal_eq_omegaPower hs.2.1 hs.2.2
  have hinput : unionInterpretation q < finiteBaseLimit :=
    (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨q, hs.1, rfl⟩
  have hηsmall : η < finiteBaseLimit :=
    ((omegaPower_self_le η).trans_eq hη.symm).trans_lt hinput
  obtain ⟨c, hc, hv⟩ := (Canonical.lt_finiteBaseLimit_iff_code η).mp hηsmall
  refine ⟨c, (graph_exact q c).mpr ⟨hs.1, hs.2.1, hs.2.2, hc, ?_⟩⟩
  rw [hv]
  exact hη.symm

theorem graph_exists_iff (q : Nat) : (∃ c : Nat, graph q c = true) ↔
    Principal.unionPrincipalCheck q = true := by
  constructor
  · rintro ⟨c, hc⟩
    have hs := (graph_exact q c).mp hc
    exact (Principal.unionPrincipalCheck_exact q).mpr ⟨hs.1, hs.2.1, hs.2.2.1⟩
  · exact graph_witness q

theorem graph_output_unique (q c d : Nat) (hc : graph q c = true) (hd : graph q d = true) : c = d := by
  have hcs := (graph_exact q c).mp hc
  have hds := (graph_exact q d).mp hd
  apply Canonical.check_value_injective c d hcs.2.2.2.1 hds.2.2.2.1
  exact omegaPower_strictMono.injective (hcs.2.2.2.2.trans hds.2.2.2.2.symm)

theorem graph_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c : Nat, graph q c = true := by
  obtain ⟨c, hc⟩ := graph_witness q hq
  exact ⟨c, hc, fun d hd => graph_output_unique q d c hd hc⟩

/-- Actual rfind executes the proved total Boolean graph test at each candidate. -/
def logarithm (q : Nat) : Part Nat := Nat.rfind (fun c => Part.some (graph q c))

theorem logarithm_partrec : Partrec logarithm := Partrec.rfind graph_primrec.to_comp.partrec.to₂

theorem logarithm_domain (q : Nat) : (logarithm q).Dom ↔ Principal.unionPrincipalCheck q = true := by
  simpa [logarithm, Nat.rfind_dom] using graph_exists_iff q

/-- This is the concrete rfind output-specification obligation, proved from
the library search construction rather than supplied as a semantic premise. -/
theorem logarithm_graph (q c : Nat) (hc : c ∈ logarithm q) : graph q c = true := by
  have hs : true ∈ Part.some (graph q c) := Nat.rfind_spec hc
  simpa using hs

theorem logarithm_value (q c : Nat) (hc : c ∈ logarithm q) :
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q :=
  (graph_exact q c).mp (logarithm_graph q c hc)

theorem logarithm_original (q c : Nat) (hc : c ∈ logarithm q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  have hs := logarithm_value q c hc
  exact ⟨Canonical.check_original hs.2.2.2.1, Canonical.check_normal hs.2.2.2.1, hs.2.2.2.2⟩

theorem logarithm_bound (q c : Nat) (hc : c ∈ logarithm q) :
    unionInterpretation c ≤ unionInterpretation q :=
  (omegaPower_self_le _).trans_eq (logarithm_value q c hc).2.2.2.2

theorem logarithm_output_unique (q c d : Nat) (hc : c ∈ logarithm q) (hd : d ∈ logarithm q) : c = d :=
  graph_output_unique q c d (logarithm_graph q c hc) (logarithm_graph q d hd)

/-- An admitted principal input really returns a canonical exponent value. -/
theorem logarithm_returns (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃ c : Nat, c ∈ logarithm q ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  have hd := (logarithm_domain q).mpr hq
  have hm : (logarithm q).get hd ∈ logarithm q := ⟨hd, rfl⟩
  have hs := logarithm_value q _ hm
  exact ⟨_, hm, hs.2.2.2.1, hs.2.2.2.2⟩

theorem logarithm_terminates (q : Nat) (hq : unionCheck q = true)
    (hp : 0 < unionInterpretation q)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation q)) : (logarithm q).Dom :=
  (logarithm_domain q).mpr ((Principal.unionPrincipalCheck_exact q).mpr ⟨hq, hp, hprincipal⟩)

theorem graph_invariant (q v c : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : graph q c = graph v c := by
  apply Bool.eq_iff_iff.mpr
  simp only [graph_exact, hq, hv, true_and, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalLogarithm
