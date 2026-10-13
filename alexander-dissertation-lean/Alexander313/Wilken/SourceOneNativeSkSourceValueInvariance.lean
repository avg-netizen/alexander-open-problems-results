import Alexander313.Wilken.SourceOneNativeSkSourceRecurrence

/-!
# Actual SAME-source sk value invariance

The genuine original source-zero RAW mu spelling theorem identifies the
current mu of equal original-source epsilon entries. Actual cutoff tests,
MNF truncation and epsilon-above-current continuation agree. Structural
induction on the independently derived finite source recurrence proves
uniqueness of its chronological value word and maximal stop position.
Executing original source-one outputs with equal root and cutoff values
have equal value words. No Native base-one parser is used. Cross-source
global dictionary assignment, Par and evaluation remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceRecurrence

/-- Actual source mu invariance makes the finite maximal recurrence
deterministic in original ordinal values, including equal cutoff spellings. -/
theorem SourcePath.values_eq {cutoff other a b : Nat} {xs ys : List Nat}
    (hp : SourcePath cutoff (a :: xs)) (ht : SourcePath other (b :: ys))
    (hcut : unionInterpretation cutoff = unionInterpretation other)
    (hab : interpretation 0 a = interpretation 0 b) :
    (a :: xs).map (interpretation 0) = (b :: ys).map (interpretation 0) := by
  induction hp generalizing other b ys with
  | stop a ha hstop =>
    cases ht with
    | stop b hb hhalt => simp only [List.map_cons, List.map_nil, hab]
    | nextStop b d hb hl he hv hs =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hle : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
    | nextContinue b d ys hb hd he hv hbd ht =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hle : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue a := by
        rw [hcut, hmu]; exact he
      exact False.elim (hstop.not_ge hle)
  | nextStop a d ha hl he hv hstop =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hlt : SourceTrackingRaw.Support.muValue a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hvalue : interpretation 0 d = interpretation 0 e := by
        calc
          interpretation 0 d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation 0 e := hevalue.symm
      simp only [List.map_cons, List.map_nil, hab, hvalue]
    | nextContinue b e ys hb heinput het hevalue hbe htail =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hvalue : interpretation 0 d = interpretation 0 e := by
        calc
          interpretation 0 d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation 0 e := hevalue.symm
      apply False.elim
      apply hstop
      rw [hab, hvalue]
      exact ⟨((SourceTrackingRaw.Support.inputCheck_exact e).mp heinput).2.2, hbe⟩
  | nextContinue a d xs ha hd he hv had htail ih =>
    cases ht with
    | stop b hb hhalt =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hlt : SourceTrackingRaw.Support.muValue a < unionInterpretation cutoff := by
        rw [hmu, hcut]; exact hhalt
      exact False.elim (hlt.not_ge he)
    | nextStop b e hb helow het hevalue hestop =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hvalue : interpretation 0 d = interpretation 0 e := by
        calc
          interpretation 0 d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation 0 e := hevalue.symm
      apply False.elim
      apply hestop
      rw [← hab, ← hvalue]
      exact ⟨((SourceTrackingRaw.Support.inputCheck_exact d).mp hd).2.2, had⟩
    | nextContinue b e ys hb heinput het hevalue hbe hother =>
      have hmu := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
      have hvalue : interpretation 0 d = interpretation 0 e := by
        calc
          interpretation 0 d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff) := hv
          _ = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
              (SourceTrackingRaw.Support.muValue b) (unionInterpretation other) := by rw [hmu, hcut]
          _ = interpretation 0 e := hevalue.symm
      have hrec := ih hother hcut hvalue
      simpa only [List.map_cons, hab] using congrArg (List.cons (interpretation 0 a)) hrec

/-- Equal original root and cutoff values derive equal full executing
value words; no current-mu equality or recurrence is supplied as premise. -/
theorem execute_values_eq (root other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ SkSourceWord.execute (root, cutoff))
    (ht : otherCodes ∈ SkSourceWord.execute (other, otherCutoff))
    (hroot : interpretation 0 root = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.map (interpretation 0) = otherCodes.map (interpretation 0) := by
  have hp := execute_source root cutoff codes ho
  have hsourceOther := execute_source other otherCutoff otherCodes ht
  obtain ⟨xs, hcodes⟩ := (SkSourceWord.execute_spec root cutoff codes ho).2.2.1
  obtain ⟨ys, hother⟩ := (SkSourceWord.execute_spec other otherCutoff otherCodes ht).2.2.1
  rw [hcodes] at hp ⊢
  rw [hother] at hsourceOther ⊢
  exact hp.values_eq hsourceOther hcut hroot

theorem execute_length_eq (root other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ SkSourceWord.execute (root, cutoff))
    (ht : otherCodes ∈ SkSourceWord.execute (other, otherCutoff))
    (hroot : interpretation 0 root = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) :
    codes.length = otherCodes.length := by
  simpa only [List.length_map] using congrArg List.length
    (execute_values_eq root other cutoff otherCutoff codes otherCodes ho ht hroot hcut)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceRecurrence
