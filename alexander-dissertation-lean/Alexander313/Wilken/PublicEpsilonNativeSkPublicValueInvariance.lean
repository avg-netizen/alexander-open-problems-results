import Alexander313.Wilken.PublicEpsilonNativeSkSourceValueInvariance

/-!
# Canonical public sk outputs are independent of SAME-source spelling

The actual public output and the executing original-source return have
the identical native chronological word. Genuine source-recurrence value
invariance therefore identifies all public ordinal values for equal
original root and cutoff values. Canonical public value injection then
identifies the entire numerical public word. No written original-source
identity or cross-source/global dictionary sk assignment is inferred.
Par and evaluation remain separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance

theorem public_source_values (q root cutoff : Nat) (public source : List Nat)
    (hp : public ∈ SkSourceWord.executePublic ((q, root), cutoff))
    (hs : source ∈ SkSourceWord.execute ((q, root), cutoff)) :
    public.map unionInterpretation = source.map (interpretation q) := by
  obtain ⟨hi, hc, pword, hw, hv⟩ := SkSourceWord.executePublic_spec q root cutoff public hp
  obtain ⟨hne, hd, sword, ht, hvsource⟩ := SkSourceWord.execute_spec q root cutoff source hs
  have he : pword = sword := Part.mem_unique hw ht
  exact hv.trans (by rw [he]; exact hvsource.symm)

/-- The actual canonical public outputs have equal value words whenever
their original SAME-source roots and public cutoff values agree. -/
theorem executePublic_values_eq (q root other cutoff otherCutoff : Nat)
    (public otherPublic : List Nat)
    (hp : public ∈ SkSourceWord.executePublic ((q, root), cutoff))
    (ht : otherPublic ∈ SkSourceWord.executePublic ((q, other), otherCutoff))
    (hroot : interpretation q root = interpretation q other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    public.map unionInterpretation = otherPublic.map unionInterpretation := by
  have hi := (SkSourceWord.executePublic_spec q root cutoff public hp).1
  have hj := (SkSourceWord.executePublic_spec q other otherCutoff otherPublic ht).1
  obtain ⟨source, hs⟩ := SkSourceWord.execute_returns q root cutoff hi
  obtain ⟨otherSource, ho⟩ := SkSourceWord.execute_returns q other otherCutoff hj
  exact (public_source_values q root cutoff public source hp hs).trans
    ((SkSourceRecurrence.execute_values_eq q root other cutoff otherCutoff source otherSource
      hs ho hroot hcut).trans
      (public_source_values q other otherCutoff otherPublic otherSource ht ho).symm)

theorem canonical_words_eq (xs ys : List Nat)
    (hx : ∀ c ∈ xs, Canonical.check c = true) (hy : ∀ c ∈ ys, Canonical.check c = true)
    (hv : xs.map unionInterpretation = ys.map unionInterpretation) : xs = ys := by
  revert hx ys
  induction xs with
  | nil =>
    intro hx ys hy hv
    exact (List.map_eq_nil_iff.mp hv.symm).symm
  | cons a xs ih =>
    intro hx ys hy hv
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b ys =>
      have he := List.cons.inj hv
      have hab := Canonical.check_value_injective a b
        (hx a List.mem_cons_self) (hy b List.mem_cons_self) he.1
      have ht := ih (fun c hc => hx c (List.mem_cons_of_mem _ hc)) ys
        (fun c hc => hy c (List.mem_cons_of_mem _ hc)) he.2
      exact List.cons_eq_cons.mpr ⟨hab, ht⟩

/-- Equal original SAME-source roots and cutoff values produce literally
equal complete canonical public words; all canonical checks are derived. -/
theorem executePublic_eq (q root other cutoff otherCutoff : Nat)
    (public otherPublic : List Nat)
    (hp : public ∈ SkSourceWord.executePublic ((q, root), cutoff))
    (ht : otherPublic ∈ SkSourceWord.executePublic ((q, other), otherCutoff))
    (hroot : interpretation q root = interpretation q other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : public = otherPublic :=
  canonical_words_eq public otherPublic
    (SkSourceWord.executePublic_spec q root cutoff public hp).2.1
    (SkSourceWord.executePublic_spec q other otherCutoff otherPublic ht).2.1
    (executePublic_values_eq q root other cutoff otherCutoff public otherPublic hp ht hroot hcut)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance
