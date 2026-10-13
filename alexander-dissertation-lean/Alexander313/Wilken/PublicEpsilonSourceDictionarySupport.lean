import Alexander313.Wilken.SourceOneNativeIota
import Alexander313.Wilken.HereditaryNativeIota
import Alexander313.Wilken.HereditarySourceDecomposition
import Alexander313.Wilken.HereditaryEpsilonOffsets

/-!
# Actual bounded source-level selection and principal-root extraction

The numerical stored public level supplies a genuine finite endpoint witness,
but is never assumed least. A literal bounded endpoint scan derives the real
least level. The actual bounded source return and the original complete ANF
produce a literal checked Normal theta-zero representative. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary

def inputCheck (q : Nat) : Bool := Canonical.check q && Epsilon.unionEpsilonCheck q

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec Epsilon.unionEpsilonCheck_primrec

theorem inputCheck_exact (q : Nat) : inputCheck q = true ↔
    Canonical.check q = true ∧ Ordinal.omega0 ^ unionInterpretation q = unionInterpretation q := by
  simp only [inputCheck, Bool.and_eq_true, Epsilon.unionEpsilonCheck_exact]
  constructor
  · rintro ⟨hq, _, he⟩; exact ⟨hq, he⟩
  · rintro ⟨hq, he⟩; exact ⟨hq, Canonical.check_original hq, he⟩

def endpointCode (m : Nat) : Nat := Canonical.canonicalize (EpsilonOffsets.baseCode m)

theorem endpointCode_primrec : Primrec endpointCode :=
  Canonical.Effective.canonicalize_primrec.comp EpsilonOffsets.baseCode_primrec

theorem endpointCode_checked (m : Nat) : Canonical.check (endpointCode m) = true :=
  Canonical.canonicalize_check _ (EpsilonOffsets.baseCode_checked m)

theorem endpointCode_value (m : Nat) : unionInterpretation (endpointCode m) = finiteBase m :=
  (Canonical.canonicalize_value _ (EpsilonOffsets.baseCode_checked m)).trans
    (EpsilonOffsets.baseCode_value m)

def belowNext (q m : Nat) : Bool := Canonical.less q (endpointCode (m + 1))

theorem belowNext_primrec : Primrec₂ belowNext :=
  Canonical.Effective.less_primrec.comp Primrec.fst
    (endpointCode_primrec.comp (Primrec.succ.comp Primrec.snd))

theorem belowNext_exact (q m : Nat) (hq : Canonical.check q = true) :
    belowNext q m = true ↔ unionInterpretation q < finiteBase (m + 1) := by
  simp only [belowNext, Canonical.less_exact, hq, endpointCode_checked, endpointCode_value, true_and]

/-- Retain the first successful endpoint, otherwise retain the current
numerical bound. Actual public admission proves success at the stored level. -/
def scan (q : Nat) : Nat → Nat :=
  Nat.rec 0 (fun n previous => cond (belowNext q previous) previous (n + 1))

theorem scan_primrec : Primrec₂ scan := by
  have hs : Primrec₂ (fun q : Nat => fun p : Nat × Nat =>
      cond (belowNext q p.2) p.2 (p.1 + 1)) :=
    ((belowNext_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).cond
      (Primrec.snd.comp Primrec.snd) (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.nat_rec (Primrec.const 0) hs

theorem scan_spec (q n : Nat) : scan q n ≤ n ∧
    (∀ m < scan q n, belowNext q m = false) ∧
    (belowNext q (scan q n) = false → scan q n = n) := by
  induction n with
  | zero => exact ⟨le_rfl, fun m hm => False.elim (Nat.not_lt_zero m hm), fun _ => rfl⟩
  | succ n ih =>
    cases he : belowNext q (scan q n) with
    | true =>
      have hstep : scan q (n + 1) = scan q n := by
        change cond (belowNext q (scan q n)) (scan q n) (n + 1) = _
        simp only [he, Bool.cond_true]
      rw [hstep]
      refine ⟨ih.1.trans (Nat.le_succ n), ih.2.1, ?_⟩
      intro hfalse
      rw [he] at hfalse
      cases hfalse
    | false =>
      have hstep : scan q (n + 1) = n + 1 := by
        change cond (belowNext q (scan q n)) (scan q n) (n + 1) = _
        simp only [he, Bool.cond_false]
      rw [hstep]
      refine ⟨le_rfl, ?_, fun _ => rfl⟩
      intro m hm
      have hlast : scan q n = n := ih.2.2 he
      by_cases hmn : m < n
      · exact ih.2.1 m (by simpa only [hlast] using hmn)
      · have hme : m = n := by omega
        simpa only [hme, hlast] using he

theorem scan_success (q n : Nat) (hn : belowNext q n = true) :
    belowNext q (scan q n) = true := by
  have hs := scan_spec q n
  cases he : belowNext q (scan q n) with
  | true => rfl
  | false =>
    have hlast := hs.2.2 he
    rw [hlast] at he
    rw [hn] at he
    cases he

def level (q : Nat) : Nat := scan q q.unpair.1

theorem level_primrec : Primrec level :=
  scan_primrec.comp Primrec.id (Primrec.fst.comp Primrec.unpair)

theorem level_bound (q : Nat) (hq : Canonical.check q = true) :
    level q ≤ q.unpair.1 ∧ unionInterpretation q < finiteBase (level q + 1) ∧
      (∀ m < level q, finiteBase (m + 1) ≤ unionInterpretation q) := by
  have hb : unionInterpretation q < finiteBase (q.unpair.1 + 1) :=
    (lt_nextBase_iff_code q.unpair.1 _).mpr
      ⟨q.unpair.2, Canonical.check_original hq, rfl⟩
  have hs := scan_spec q q.unpair.1
  refine ⟨hs.1, (belowNext_exact q _ hq).mp
    (scan_success q _ ((belowNext_exact q _ hq).mpr hb)), ?_⟩
  intro m hm
  apply le_of_not_gt
  intro hlt
  have he := (belowNext_exact q m hq).mpr hlt
  have hf := hs.2.1 m hm
  rw [he] at hf
  cases hf

theorem level_lower (q : Nat) (hq : inputCheck q = true) :
    finiteBase (level q) ≤ unionInterpretation q := by
  have hs := (inputCheck_exact q).mp hq
  cases hm : level q with
  | zero =>
    rw [hm, finiteBase_zero]
    exact (EpsilonOffsets.epsilon_one_lt hs.2).le
  | succ m =>
    have hlt : m < level q := by rw [hm]; exact Nat.lt_succ_self m
    simpa only [hm] using (level_bound q hs.1).2.2 m hlt

def sourceCode (q : Nat) : Nat := SourceZeta.Transport.returnCode (level q) q

theorem sourceCode_primrec : Primrec sourceCode :=
  SourceZeta.Transport.returnCode_primrec.comp level_primrec Primrec.id

theorem sourceCode_spec (q : Nat) (hq : inputCheck q = true) :
    Theta.acceptedLowCode (level q) (sourceCode q) = true ∧
      interpretation (level q) (sourceCode q) = unionInterpretation q :=
  SourceZeta.Transport.returnCode_spec _ q ((inputCheck_exact q).mp hq).1
    (level_bound q ((inputCheck_exact q).mp hq).1).2.1

def sourceTerm (q : Nat) : RelativeTerm Nat :=
  (SourceDecomposition.word (level q) (sourceCode q)).head?.getD (Theta.Normalization.zeroTree (level q))

theorem sourceTerm_primrec : Primrec sourceTerm :=
  Primrec.option_getD.comp
    (Primrec.list_head?.comp (SourceDecomposition.word_primrec.comp level_primrec sourceCode_primrec))
    (Theta.Normalization.Effective.zeroTree_primrec.comp level_primrec)

/-- The actual complete word is singleton because epsilon is positive
principal. Actual source parameter soundness excludes its parameter branch;
the genuine LOW range excludes every positive theta index. -/
theorem sourceTerm_spec (q : Nat) (hq : inputCheck q = true) :
    ∃ b : RelativeTerm Nat, sourceTerm q = .theta 0 b ∧
      check (level q) (.theta 0 b) = true ∧ Theta.Normal (level q) (.theta 0 b) ∧
      denote (level q) (.theta 0 b) = unionInterpretation q := by
  have he := (inputCheck_exact q).mp hq
  have hs := sourceCode_spec q hq
  have hl := (Theta.acceptedLowCode_iff _ _).mp hs.1
  have hc : checkCode (level q) (sourceCode q) = true :=
    (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hl.1)).1
  have hi := (SourceDecomposition.inputCheck_exact _ _).mpr ⟨hc, hl.2⟩
  have hw := SourceDecomposition.word_spec _ _ hi
  have hpos : 0 < unionInterpretation q := by
    rw [← he.2]; exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hp : Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
    rw [← he.2]; exact Ordinal.isPrincipal_add_omega0_opow _
  have hmap : (SourceDecomposition.word (level q) (sourceCode q)).map (denote (level q)) =
      [unionInterpretation q] := by
    rw [hw.2, hs.2, canonicalANF_principal hpos hp]
  have hlength : (SourceDecomposition.word (level q) (sourceCode q)).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hmap
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlength
  have htmem : t ∈ SourceDecomposition.word (level q) (sourceCode q) := by
    rw [ht]; exact List.mem_singleton_self _
  have hts := hw.1 t htmem
  have htv : denote (level q) t = unionInterpretation q := by
    simpa only [ht, List.map_singleton, List.singleton_inj] using hmap
  have hout : t.outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le _ t hts.1 1 (by omega)).mp (by
      rw [htv]
      exact (level_bound q he.1).2.1.trans (finiteBase_lt_cardinal (level q)))
  rcases SourceDecomposition.word_shape _ _ t htmem with ⟨p, rfl⟩ | ⟨k, b, rfl⟩
  · have had := Theta.checked_admissible (level q) (SourceOne.PublicCodes.fragment (.parameter p))
      (.parameter p) hts.1 (SourceOne.PublicCodes.height_le_fragment _)
    have hsmall : denote (level q) (.parameter p) < finiteBase (level q) :=
      parameter_sound _ p had.1
    exact False.elim ((hsmall.trans_le (level_lower q hq)).ne htv)
  · have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hout; omega
    subst k
    refine ⟨b, ?_, hts.1, hts.2.1, htv⟩
    simp only [sourceTerm, ht, List.head?_cons, Option.getD_some]

theorem sourceTerm_high (q : Nat) (hq : inputCheck q = true)
    (hp : finiteBase (level q) < unionInterpretation q) :
    ∃ b : RelativeTerm Nat, sourceTerm q = .theta 0 b ∧
      check (level q) (.theta 0 b) = true ∧ Theta.Normal (level q) (.theta 0 b) ∧
      1 < b.outerSort ∧ denote (level q) (.theta 0 b) = unionInterpretation q := by
  obtain ⟨b, hb, hc, hn, hv⟩ := sourceTerm_spec q hq
  have he : Ordinal.omega0 ^ denote (level q) (.theta 0 b) = denote (level q) (.theta 0 b) :=
    by rw [hv]; exact ((inputCheck_exact q).mp hq).2
  have hh : 1 < b.outerSort := by
    rcases (Epsilon.theta_epsilon_iff _ 0 b hc).mp he with hh | hz
    · simpa only [Nat.zero_add] using hh
    · have hbase : denote (level q) (.theta 0 b) = finiteBase (level q) := by
        change globalCollapse (finiteBase (level q)) 0 (denote (level q) b) = _
        rw [hz.1, finiteBase_collapse_zero_base]
      exact False.elim ((hp.trans_eq hv.symm).ne hbase.symm)
  exact ⟨b, hb, hc, hn, hh, hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary
