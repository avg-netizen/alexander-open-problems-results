import Alexander313.Wilken.PublicEpsilonNativeSkNextSearchSupport

/-!
# Executing native truncation next step with a genuine continuation flag

The actual public mu enters the existing overlined factor truncation.
An actual rfind search returns an admitted Normal LOW code at the current
root context. The epsilon and strict-above-current-root tests decide the
real continuation branch; that branch emits the actual final-atom HIGH
root. The complete original domain is the high-root mu guard and original
public cutoff admission. Source M>1 cutoff bounds are derived separately.
No input Normality, representative, boundary, plus or return oracle is
supplied. No primitive recursive search bound, Par preservation or full
sk iteration is claimed. All candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextSearch

open Support

abbrev Step := Bool × Nat

def inputCheck (q root cutoff : Nat) : Bool := Mu.inputCheck q root && unionCheck cutoff

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Primrec.comp Mu.inputCheck_primrec Primrec.fst)
    (Uniform.unionCheck_primrec.comp Primrec.snd)

theorem inputCheck_exact (q root cutoff : Nat) : inputCheck q root cutoff = true ↔
    Mu.inputCheck q root = true ∧ unionCheck cutoff = true := Bool.and_eq_true

def continuationCheck (q root d : Nat) : Bool :=
  Epsilon.unionEpsilonCheck (UniformPublicReturn.publicCode (betaCode q root) d) &&
    Canonical.less (betaCode q root) (UniformPublicReturn.publicCode (betaCode q root) d)

theorem continuationCheck_primrec : Primrec
    (fun p : Context × Nat => continuationCheck p.1.1 p.1.2 p.2) := by
  have hb := Primrec.comp betaCode_primrec Primrec.fst
  have hp := UniformPublicReturn.publicCode_primrec.comp hb Primrec.snd
  exact Primrec.and.comp (Epsilon.unionEpsilonCheck_primrec.comp hp)
    (Canonical.Effective.less_primrec.comp hb hp)

theorem continuationCheck_exact (q root d : Nat) (ha : Mu.inputCheck q root = true)
    (hd : lowCheckCode (betaCode q root) d = true) :
    continuationCheck q root d = true ↔
      Ordinal.omega0 ^ interpretation (betaCode q root) d = interpretation (betaCode q root) d ∧
        interpretation q root < interpretation (betaCode q root) d := by
  have hs := UniformPublicReturn.publicCode_spec (betaCode q root) d
    ((UniformPublicReturn.inputCheck_exact _ _).mpr hd)
  rw [continuationCheck, Bool.and_eq_true, Epsilon.unionEpsilonCheck_exact, Canonical.less_exact]
  simp only [Canonical.check_original hs.1, hs.1, hs.2,
    (betaCode_spec q root ha).1, (betaCode_spec q root ha).2, true_and]

def emit (q root d : Nat) : Step :=
  (continuationCheck q root d, cond (continuationCheck q root d)
    (ContextTranslation.Support.rootAtomCode (betaCode q root) d) d)

theorem emit_primrec : Primrec (fun p : Context × Nat => emit p.1.1 p.1.2 p.2) := by
  have hh := ContextTranslation.Support.rootAtomCode_primrec.comp
    (Primrec.comp betaCode_primrec Primrec.fst) Primrec.snd
  exact continuationCheck_primrec.pair (continuationCheck_primrec.cond hh Primrec.snd)

theorem emit_spec (q root d : Nat) (ha : Mu.inputCheck q root = true)
    (hd : lowCheckCode (betaCode q root) d = true)
    (hn : Comparison.acceptedCode (betaCode q root) d = true) :
    lowCheckCode (betaCode q root) (emit q root d).2 = true ∧
      Comparison.acceptedCode (betaCode q root) (emit q root d).2 = true ∧
        interpretation (betaCode q root) (emit q root d).2 = interpretation (betaCode q root) d := by
  cases hh : continuationCheck q root d with
  | false => simpa only [emit, hh, Bool.cond_false] using And.intro hd (And.intro hn rfl)
  | true =>
    have ht := (continuationCheck_exact q root d ha hd).mp hh
    have hs := ContextTranslation.Support.rootAtomCode_spec (betaCode q root) d hd
      (by rw [beta_base q root ha]; exact ht.2) ht.1
    simpa only [emit, hh, Bool.cond_true] using
      And.intro (RootLowCollapse.root_low _ _ hs.1)
        (And.intro (RootLowCollapse.root_accepted _ _ hs.1) hs.2)

theorem emit_continue (q root d : Nat) (ha : Mu.inputCheck q root = true)
    (hd : lowCheckCode (betaCode q root) d = true)
    (hh : (emit q root d).1 = true) : Mu.inputCheck (betaCode q root) (emit q root d).2 = true := by
  have ht := (continuationCheck_exact q root d ha hd).mp hh
  have hs := ContextTranslation.Support.rootAtomCode_spec (betaCode q root) d hd
    (by rw [beta_base q root ha]; exact ht.2) ht.1
  have hcheck : continuationCheck q root d = true := hh
  simpa only [emit, hcheck, Bool.cond_true] using hs.1

def execute (p : Query) : Part Step := cond (inputCheck p.1.1 p.1.2 p.2)
  ((FactorTruncation.truncate (muPublicCode p.1.1 p.1.2) p.2).bind fun out =>
    (search (betaCode p.1.1 p.1.2) out).map (emit p.1.1 p.1.2)) Part.none

theorem execute_partrec : Partrec execute := by
  have ht := FactorTruncation.truncate_partrec.comp
    (muPublicCode_primrec.comp Primrec.fst).to_comp Primrec.snd.to_comp
  have hs : Partrec₂ (fun p : Query => fun out : Nat => search (betaCode p.1.1 p.1.2) out) :=
    (search_partrec.comp ((Primrec.comp betaCode_primrec Primrec.fst).comp Primrec.fst).to_comp
      Primrec.snd.to_comp).to₂
  have he : Computable₂ (fun p : Query × Nat => fun d : Nat => emit p.1.1.1 p.1.1.2 d) :=
    (emit_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      Primrec.snd)).to_comp.to₂
  exact Partrec.cond inputCheck_primrec.to_comp
    (Partrec.bind ht (Partrec.map hs he).to₂) Partrec.none

theorem execute_domain (q root cutoff : Nat) : (execute ((q, root), cutoff)).Dom ↔
    inputCheck q root cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck q root cutoff with
    | false =>
      have hx : (Part.none : Part Step).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
    | true => rfl
  · intro hi
    obtain ⟨ha, hc⟩ := (inputCheck_exact q root cutoff).mp hi
    obtain ⟨out, ho, _⟩ := FactorTruncation.truncate_returns _ cutoff (muPublicCode_principal q root ha) hc
    obtain ⟨d, hd⟩ := truncation_search_returns q root cutoff out ha ho
    apply Part.dom_iff_mem.mpr
    refine ⟨emit q root d, ?_⟩
    rw [execute, hi, Bool.cond_true]
    exact Part.mem_bind ho (Part.mem_map (emit q root) hd)

theorem execute_returns (q root cutoff : Nat) (hi : inputCheck q root cutoff = true) :
    ∃ out, out ∈ execute ((q, root), cutoff) := Part.dom_iff_mem.mp ((execute_domain q root cutoff).mpr hi)

/-- The actual original guard computes a checked Normal next code and
the exact overlined value; its flag is the genuine epsilon continuation. -/
theorem execute_spec (q root cutoff : Nat) (out : Step)
    (ho : out ∈ execute ((q, root), cutoff)) :
    inputCheck q root cutoff = true ∧
      lowCheckCode (betaCode q root) out.2 = true ∧
      Comparison.acceptedCode (betaCode q root) out.2 = true ∧
      interpretation (betaCode q root) out.2 = SkNextStep.nextValue q root (unionInterpretation cutoff) ∧
      (out.1 = true ↔ Ordinal.omega0 ^ SkNextStep.nextValue q root (unionInterpretation cutoff) =
        SkNextStep.nextValue q root (unionInterpretation cutoff) ∧
          interpretation q root < SkNextStep.nextValue q root (unionInterpretation cutoff)) := by
  have hi := (execute_domain q root cutoff).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have ha := ((inputCheck_exact q root cutoff).mp hi).1
  rw [execute, hi, Bool.cond_true] at ho
  obtain ⟨publicOut, hp, hm⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit q root)).mp hm
  have hs := search_spec _ publicOut d hd
  have ht := truncation_spec q root cutoff publicOut ha hp
  have he := emit_spec q root d ha hs.1 hs.2.1
  have hv := hs.2.2.2.trans ht.2
  refine ⟨hi, he.1, he.2.1, he.2.2.trans hv, ?_⟩
  simpa only [emit, hv] using continuationCheck_exact q root d ha hs.1

/-- True continuation returns an actual HIGH next root and strict height
decrease; no next root or height premise is supplied. -/
theorem execute_continue (q root cutoff : Nat) (out : Step)
    (ho : out ∈ execute ((q, root), cutoff)) (hc : out.1 = true) :
    Mu.inputCheck (betaCode q root) out.2 = true ∧ heightCode out.2 < heightCode root := by
  have hs := execute_spec q root cutoff out ho
  have ha := ((inputCheck_exact q root cutoff).mp hs.1).1
  rw [execute, hs.1, Bool.cond_true] at ho
  obtain ⟨publicOut, hp, hm⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (emit q root)).mp hm
  have ht := search_spec _ publicOut d hd
  have hh := emit_continue q root d ha ht.1 (by rw [he]; exact hc)
  have hn : Mu.inputCheck (betaCode q root) out.2 = true := by simpa only [he] using hh
  exact ⟨hn, SkHeight.next_root_height_lt_root q root out.2 ha hn
    (hs.2.2.2.1.le.trans (SkNextStep.nextValue_le_mu q root (unionInterpretation cutoff)))⟩

theorem execute_height (q root cutoff : Nat) (out : Step)
    (ho : out ∈ execute ((q, root), cutoff)) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) out.2 < CanonicalHeight.canonicalHeightCode q root := by
  have hs := execute_spec q root cutoff out ho
  exact SkHeight.low_next_height_lt_root q root out.2
    ((inputCheck_exact q root cutoff).mp hs.1).1 hs.2.1
    (hs.2.2.2.1.le.trans (SkNextStep.nextValue_le_mu q root (unionInterpretation cutoff)))

theorem execute_stop (q root cutoff : Nat) (out : Step)
    (ho : out ∈ execute ((q, root), cutoff)) (hc : out.1 = false) :
    ¬(Ordinal.omega0 ^ interpretation (betaCode q root) out.2 =
      interpretation (betaCode q root) out.2 ∧ interpretation q root < interpretation (betaCode q root) out.2) := by
  have hs := execute_spec q root cutoff out ho
  intro ht
  have hh := hs.2.2.2.2.mpr (by simpa only [hs.2.2.2.1] using ht)
  rw [hc] at hh
  cases hh

/-- The actual source M>1 eligibility supplies the retained-factor bounds
for the computed native next code, including the eventual stop case. -/
theorem execute_source_bounds (q root cutoff : Nat) (out : Step)
    (ho : out ∈ execute ((q, root), cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hpos : 1 < unionInterpretation cutoff) (hc : unionInterpretation cutoff ≤ Mu.sourceValue q root) :
    unionInterpretation cutoff ≤ interpretation (betaCode q root) out.2 ∧
      interpretation (betaCode q root) out.2 ≤ Mu.sourceValue q root ∧
        unionInterpretation cutoff ≤ Alexander313.Wilken.MultiplicativeNormalForm.lf
          (interpretation (betaCode q root) out.2) := by
  rw [(execute_spec q root cutoff out ho).2.2.2.1]
  exact SkNextStep.source_definition_3_33_bounds q root (unionInterpretation cutoff) hm hpos hc

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextSearch
