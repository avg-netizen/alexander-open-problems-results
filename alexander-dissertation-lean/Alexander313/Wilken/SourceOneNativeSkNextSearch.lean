import Alexander313.Wilken.SourceOneNativeSkNextStepSupport

/-!
# Executing the genuine original source-one first sk next step

The original check-zero HIGH root executes source-one mu. Its real public
output enters overlined factor truncation, then the terminating native LOW
return search at the genuine epsilon alpha context. Actual epsilon and
strict-above-original-root tests give the continuation flag and construct
the HIGH next caller with strictly smaller written height. All source-one
input admission is original check0 and Normal0. No Native base-one parser,
representative, endpoint, height, plus or search-bound oracle is supplied.
This is the first step, not a complete sk iteration. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkNextSearch

open SkNextStepSupport
open NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support (search search_spec search_partrec)

abbrev Query := Nat × Nat
abbrev Step := Bool × Nat

def inputCheck (root cutoff : Nat) : Bool := Mu.inputCheck root && unionCheck cutoff

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (Mu.inputCheck_primrec.comp Primrec.fst)
    (Uniform.unionCheck_primrec.comp Primrec.snd)).to₂

theorem inputCheck_exact (root cutoff : Nat) : inputCheck root cutoff = true ↔
    Mu.inputCheck root = true ∧ unionCheck cutoff = true := Bool.and_eq_true

def continuationCheck (root d : Nat) : Bool :=
  Epsilon.unionEpsilonCheck (NativeContext.UniformPublicReturn.publicCode (alphaCode root) d) &&
    Canonical.less (alphaCode root) (NativeContext.UniformPublicReturn.publicCode (alphaCode root) d)

theorem continuationCheck_primrec : Primrec₂ continuationCheck := by
  have hb := alphaCode_primrec.comp Primrec.fst
  have hp := NativeContext.UniformPublicReturn.publicCode_primrec.comp hb Primrec.snd
  exact (Primrec.and.comp (Epsilon.unionEpsilonCheck_primrec.comp hp)
    (Canonical.Effective.less_primrec.comp hb hp)).to₂

theorem continuationCheck_exact (root d : Nat) (ha : Mu.inputCheck root = true)
    (hd : NativeContext.lowCheckCode (alphaCode root) d = true) :
    continuationCheck root d = true ↔
      Ordinal.omega0 ^ NativeContext.interpretation (alphaCode root) d =
        NativeContext.interpretation (alphaCode root) d ∧
          interpretation 0 root < NativeContext.interpretation (alphaCode root) d := by
  have hs := NativeContext.UniformPublicReturn.publicCode_spec (alphaCode root) d
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ _).mpr hd)
  rw [continuationCheck, Bool.and_eq_true, Epsilon.unionEpsilonCheck_exact, Canonical.less_exact]
  simp only [Canonical.check_original hs.1, hs.1, hs.2,
    (alphaCode_spec root ha).1, (alphaCode_spec root ha).2, true_and]

def emit (root d : Nat) : Step :=
  (continuationCheck root d, cond (continuationCheck root d)
    (NativeContext.PublicEpsilonUnboundedIota.ContextTranslation.Support.rootAtomCode (alphaCode root) d) d)

theorem emit_primrec : Primrec₂ emit := by
  have hh := NativeContext.PublicEpsilonUnboundedIota.ContextTranslation.Support.rootAtomCode_primrec.comp
    (alphaCode_primrec.comp Primrec.fst) Primrec.snd
  exact (continuationCheck_primrec.pair (continuationCheck_primrec.cond hh Primrec.snd)).to₂

theorem emit_spec (root d : Nat) (ha : Mu.inputCheck root = true)
    (hd : NativeContext.lowCheckCode (alphaCode root) d = true)
    (hn : NativeContext.Comparison.acceptedCode (alphaCode root) d = true) :
    NativeContext.lowCheckCode (alphaCode root) (emit root d).2 = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode root) (emit root d).2 = true ∧
        NativeContext.interpretation (alphaCode root) (emit root d).2 =
          NativeContext.interpretation (alphaCode root) d := by
  cases hh : continuationCheck root d with
  | false => simpa only [emit, hh, Bool.cond_false] using And.intro hd (And.intro hn rfl)
  | true =>
    have ht := (continuationCheck_exact root d ha hd).mp hh
    have hs := NativeContext.PublicEpsilonUnboundedIota.ContextTranslation.Support.rootAtomCode_spec
      (alphaCode root) d hd (by rw [OrderSupport.alpha_base root ha]; exact ht.2) ht.1
    simpa only [emit, hh, Bool.cond_true] using
      And.intro (NativeContext.RootLowCollapse.root_low _ _ hs.1)
        (And.intro (NativeContext.RootLowCollapse.root_accepted _ _ hs.1) hs.2)

theorem emit_continue (root d : Nat) (ha : Mu.inputCheck root = true)
    (hd : NativeContext.lowCheckCode (alphaCode root) d = true)
    (hh : (emit root d).1 = true) :
    NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) (emit root d).2 = true := by
  have ht := (continuationCheck_exact root d ha hd).mp hh
  have hs := NativeContext.PublicEpsilonUnboundedIota.ContextTranslation.Support.rootAtomCode_spec
    (alphaCode root) d hd (by rw [OrderSupport.alpha_base root ha]; exact ht.2) ht.1
  have hcheck : continuationCheck root d = true := hh
  simpa only [emit, hcheck, Bool.cond_true] using hs.1

def execute (p : Query) : Part Step := cond (inputCheck p.1 p.2)
  ((FactorTruncation.truncate (SourceTrackingSupport.muPublicCode p.1) p.2).bind fun out =>
    (search (alphaCode p.1) out).map (emit p.1)) Part.none

theorem execute_partrec : Partrec execute := by
  have ht := FactorTruncation.truncate_partrec.comp
    (SourceTrackingSupport.muPublicCode_primrec.comp Primrec.fst).to_comp Primrec.snd.to_comp
  have hs : Partrec₂ (fun p : Query => fun out : Nat => search (alphaCode p.1) out) :=
    (search_partrec.comp ((alphaCode_primrec.comp Primrec.fst).comp Primrec.fst).to_comp
      Primrec.snd.to_comp).to₂
  have he : Computable₂ (fun p : Query × Nat => fun d : Nat => emit p.1.1 d) :=
    (Primrec.comp emit_primrec ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      Primrec.snd)).to_comp.to₂
  exact Partrec.cond inputCheck_primrec.to_comp
    (Partrec.bind ht (Partrec.map hs he).to₂) Partrec.none

theorem execute_domain (root cutoff : Nat) : (execute (root, cutoff)).Dom ↔ inputCheck root cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck root cutoff with
    | false =>
      have hx : (Part.none : Part Step).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
    | true => rfl
  · intro hi
    obtain ⟨ha, hc⟩ := (inputCheck_exact root cutoff).mp hi
    obtain ⟨out, ho, _⟩ := FactorTruncation.truncate_returns _ cutoff (muPublicCode_principal root ha) hc
    obtain ⟨d, hd⟩ := truncation_search_returns root cutoff out ha ho
    apply Part.dom_iff_mem.mpr
    refine ⟨emit root d, ?_⟩
    rw [execute, hi, Bool.cond_true]
    exact Part.mem_bind ho (Part.mem_map (emit root) hd)

theorem execute_returns (root cutoff : Nat) (hi : inputCheck root cutoff = true) :
    ∃ out, out ∈ execute (root, cutoff) := Part.dom_iff_mem.mp ((execute_domain root cutoff).mpr hi)

theorem execute_spec (root cutoff : Nat) (out : Step) (ho : out ∈ execute (root, cutoff)) :
    inputCheck root cutoff = true ∧
      NativeContext.lowCheckCode (alphaCode root) out.2 = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode root) out.2 = true ∧
      NativeContext.interpretation (alphaCode root) out.2 = nextValue root (unionInterpretation cutoff) ∧
      (out.1 = true ↔ Ordinal.omega0 ^ nextValue root (unionInterpretation cutoff) =
        nextValue root (unionInterpretation cutoff) ∧
          interpretation 0 root < nextValue root (unionInterpretation cutoff)) := by
  have hi := (execute_domain root cutoff).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have ha := ((inputCheck_exact root cutoff).mp hi).1
  rw [execute, hi, Bool.cond_true] at ho
  obtain ⟨publicOut, hp, hm⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit root)).mp hm
  have hs := search_spec _ publicOut d hd
  have ht := truncation_spec root cutoff publicOut ha hp
  have he := emit_spec root d ha hs.1 hs.2.1
  have hv := hs.2.2.2.trans ht.2
  refine ⟨hi, he.1, he.2.1, he.2.2.trans hv, ?_⟩
  simpa only [emit, hv] using continuationCheck_exact root d ha hs.1

theorem execute_continue (root cutoff : Nat) (out : Step)
    (ho : out ∈ execute (root, cutoff)) (hc : out.1 = true) :
    NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) out.2 = true ∧
      heightCode out.2 < heightCode root := by
  have hs := execute_spec root cutoff out ho
  have ha := ((inputCheck_exact root cutoff).mp hs.1).1
  rw [execute, hs.1, Bool.cond_true] at ho
  obtain ⟨publicOut, hp, hm⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (emit root)).mp hm
  have ht := search_spec _ publicOut d hd
  have hh := emit_continue root d ha ht.1 (by rw [he]; exact hc)
  have hn : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) out.2 = true := by
    simpa only [he] using hh
  exact ⟨hn, next_root_height_lt_root root out.2 ha hn
    (hs.2.2.2.1.le.trans (nextValue_le_mu root (unionInterpretation cutoff)))⟩

theorem execute_height (root cutoff : Nat) (out : Step) (ho : out ∈ execute (root, cutoff)) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode root) out.2 <
      SourceOne.CanonicalHeight.canonicalHeightCode root := by
  have hs := execute_spec root cutoff out ho
  exact low_next_height_lt_root root out.2 ((inputCheck_exact root cutoff).mp hs.1).1 hs.2.1
    (hs.2.2.2.1.le.trans (nextValue_le_mu root (unionInterpretation cutoff)))

theorem execute_stop (root cutoff : Nat) (out : Step)
    (ho : out ∈ execute (root, cutoff)) (hc : out.1 = false) :
    ¬(Ordinal.omega0 ^ NativeContext.interpretation (alphaCode root) out.2 =
      NativeContext.interpretation (alphaCode root) out.2 ∧
        interpretation 0 root < NativeContext.interpretation (alphaCode root) out.2) := by
  have hs := execute_spec root cutoff out ho
  intro ht
  have hh := hs.2.2.2.2.mpr (by simpa only [hs.2.2.2.1] using ht)
  rw [hc] at hh
  cases hh

theorem execute_source_bounds (root cutoff : Nat) (out : Step) (ho : out ∈ execute (root, cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hpos : 1 < unionInterpretation cutoff) (hc : unionInterpretation cutoff ≤ Mu.sourceValue root) :
    unionInterpretation cutoff ≤ NativeContext.interpretation (alphaCode root) out.2 ∧
      NativeContext.interpretation (alphaCode root) out.2 ≤ Mu.sourceValue root ∧
        unionInterpretation cutoff ≤ Alexander313.Wilken.MultiplicativeNormalForm.lf
          (NativeContext.interpretation (alphaCode root) out.2) := by
  rw [(execute_spec root cutoff out ho).2.2.2.1]
  exact source_definition_3_33_bounds root (unionInterpretation cutoff) hm hpos hc

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkNextSearch
