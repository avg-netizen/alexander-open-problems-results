import Alexander313.Wilken.PublicEpsilonNativeSkSourceRecurrence

/-!
# Actual SAME-source sk value invariance

The genuine RAW mu spelling theorem identifies the current mu of equal
original-source epsilon entries. Consequently the actual cutoff tests,
MNF truncation and epsilon-above-current continuation agree. Structural
induction on the independently derived finite source recurrence proves
uniqueness of its chronological value word and maximal stop position.
Executing outputs with equal original root and cutoff values therefore
have equal value words. Cross-source/global dictionary assignment, Par
and evaluation remain separate. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence

/-- Actual source mu invariance makes the finite maximal recurrence
deterministic in original ordinal values, including equal cutoff spellings. -/
theorem SourcePath.values_eq {q cutoff other a b : Nat} {xs ys : List Nat}
    (hp : SourcePath q cutoff (a :: xs)) (ht : SourcePath q other (b :: ys))
    (hcut : unionInterpretation cutoff = unionInterpretation other)
    (hab : interpretation q a = interpretation q b) :
    (a :: xs).map (interpretation q) = (b :: ys).map (interpretation q) := by
  induction hp generalizing other b ys with
  | stop a ha hstop =>
    cases ht with
    | stop b hb hhalt => simp only [List.map_cons, List.map_nil, hab]
    | nextStop b d hb hl he hv hs =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hle : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
    | nextContinue b d ys hb hd he hv hbd ht =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hle : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
  | nextStop a d ha hl he hv hstop =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hlt : SourceTrackingRaw.Support.muValue q a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hvalue : interpretation q d = interpretation q e := by
        calc
          interpretation q d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation q e := hevalue.symm
      simp only [List.map_cons, List.map_nil, hab, hvalue]
    | nextContinue b e ys hb heinput het hevalue hbe htail =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hvalue : interpretation q d = interpretation q e := by
        calc
          interpretation q d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation q e := hevalue.symm
      apply False.elim
      apply hstop
      rw [hab, hvalue]
      exact ⟨((SourceTrackingRaw.Support.inputCheck_exact q e).mp heinput).2.2, hbe⟩
  | nextContinue a d xs ha hd he hv had htail ih =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hlt : SourceTrackingRaw.Support.muValue q a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hvalue : interpretation q d = interpretation q e := by
        calc
          interpretation q d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation q e := hevalue.symm
      apply False.elim
      apply hestop
      rw [← hab, ← hvalue]
      exact ⟨((SourceTrackingRaw.Support.inputCheck_exact q d).mp hd).2.2, had⟩
    | nextContinue b e ys hb heinput het hevalue hbe hother =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant q a b ha hb hab
      have hvalue : interpretation q d = interpretation q e := by
        calc
          interpretation q d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue q b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation q e := hevalue.symm
      have hrec := ih hother hcut hvalue
      simpa only [List.map_cons, hab] using congrArg (List.cons (interpretation q a)) hrec

/-- Equal original root and cutoff values derive equal full executing
value words; no current-mu equality or recurrence is supplied as premise. -/
theorem execute_values_eq (q root other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff))
    (ht : otherCodes ∈ SkSourceWord.execute ((q, other), otherCutoff))
    (hroot : interpretation q root = interpretation q other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.map (interpretation q) = otherCodes.map (interpretation q) := by
  obtain ⟨hp, a, xs, hcodes, ha, hone, hterminal⟩ := execute_spec q root cutoff codes ho
  obtain ⟨ht, b, ys, hother, hb, htwo, hfinal⟩ := execute_spec q other otherCutoff otherCodes ht
  rw [hcodes] at hp ⊢
  rw [hother] at ht ⊢
  exact hp.values_eq ht hcut (ha.trans (hroot.trans hb.symm))

theorem execute_length_eq (q root other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff))
    (ht : otherCodes ∈ SkSourceWord.execute ((q, other), otherCutoff))
    (hroot : interpretation q root = interpretation q other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.length = otherCodes.length := by
  simpa only [List.length_map] using congrArg List.length
    (execute_values_eq q root other cutoff otherCutoff codes otherCodes ho ht hroot hcut)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence
