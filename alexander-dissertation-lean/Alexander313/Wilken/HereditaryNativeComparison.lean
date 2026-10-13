import Alexander313.Wilken.HereditaryNativeContexts
import Alexander313.Wilken.HereditaryCanonicalCoefficients
import Alexander313.Wilken.ComparisonPrimitiveLists

/-!
# Actual comparison in native coded epsilon contexts

Native parameter leaves stay atomic original public union codes. Their actual
public principal words supply comparison representatives at written sums;
exposed native theta support never opens a public payload. Normality is the
real base-dependent weak final-principal sum condition at every native sum.
The comparator's genuine finite table and exact normality checker retain
original epsilon-context admission. No arbitrary native evaluation, supplied
order oracle, public recoding or translation is assumed. Arbitrary admitted
native normalization and the stronger source-normal convention remain separate.
All candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Comparison

open SourceOne.Comparison (lexLT)
open SourceOne.Comparison.Effective

def Normal (q : Nat) : RelativeTerm Nat → Prop
  | .parameter _ => True
  | .sum a b => Normal q a ∧ Normal q b ∧
      SourceNormalSum (denote q (.sum a b)) (denote q a) (denote q b)
  | .theta _ a => Normal q a

theorem normal_finite_iff (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : Admissible parameters (omegaSequence (base q)) (sourceFiniteCollapse (base q) n) n 0 t) :
    NormalSums (base q) parameters n t ↔ Normal q t := by
  induction ht with
  | parameter hp => rfl
  | @sum a b ha hb iha ihb =>
    change (NormalSums _ _ n a ∧ NormalSums _ _ n b ∧
      SourceNormalSum (finiteDenote q n (.sum a b)) (finiteDenote q n a) (finiteDenote q n b)) ↔ _
    rw [iha, ihb, ← denote_eq_finite q n hq (.sum a b) (.sum ha hb),
      ← denote_eq_finite q n hq a ha, ← denote_eq_finite q n hq b hb]
    rfl
  | theta h0k hkn hsort ha ih => exact ih

theorem checked_admissible (q n : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (hheight : t.height ≤ n) : admissible q n t :=
  (finiteCheck_exact q n t).mp (finiteCheck_transfer q (SourceOne.PublicCodes.fragment t) t
    (Bool.and_eq_true_iff.mp ht).2 n hheight)

theorem admitted_checked (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) : check q t = true := (check_exact q t).mpr ⟨hq, n, ht⟩

theorem admitted_argument {q n k : Nat} {a : RelativeTerm Nat}
    (ht : admissible q n (.theta k a)) : admissible q n a := by
  cases ht.2 with
  | theta h0k hkn hsort ha => exact ⟨ht.1, ha⟩

theorem Normal.exposed {q : Nat} {t s : RelativeTerm Nat}
    (ht : Normal q t) (m : Nat) (hs : s ∈ exposedThetaList m t) : Normal q s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [exposedThetaList] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by simpa only [exposedThetaList, if_pos hkm, List.mem_singleton] using hs
      subst s; exact ht
    · by_cases hmk : m < k
      · apply ih ht
        simpa only [exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem payloads_exposed {q : Nat} {t s : RelativeTerm Nat}
    (ht : Payloads q t) (m : Nat) (hs : s ∈ exposedThetaList m t) : Payloads q s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [exposedThetaList] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2 hs
  | theta k a ih =>
    intro ht hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by simpa only [exposedThetaList, if_pos hkm, List.mem_singleton] using hs
      subst s; exact ht
    · by_cases hmk : m < k
      · apply ih ht
        simpa only [exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem admitted_exposed {q n : Nat} {t s : RelativeTerm Nat}
    (ht : admissible q n t) (m : Nat) (hs : s ∈ exposedThetaList m t) : admissible q n s :=
  ⟨payloads_exposed ht.1 m hs, ht.2.exposedThetaList m hs⟩

def atoms : RelativeTerm Nat → List (RelativeTerm Nat)
  | .parameter p => (CanonicalCoefficients.word p).map RelativeTerm.parameter
  | .sum a b => atoms a ++ atoms b
  | .theta k a => [.theta k a]

private def atomParameter (_ : Unit) (p : Nat) : RelativeTerm Nat × List (RelativeTerm Nat) :=
  (.parameter p, (CanonicalCoefficients.word p).map RelativeTerm.parameter)
private def atomSum (a b : RelativeTerm Nat × List (RelativeTerm Nat)) : RelativeTerm Nat × List (RelativeTerm Nat) :=
  (.sum a.1 b.1, a.2 ++ b.2)
private def atomTheta (_ : Unit) (k : Nat) (a : RelativeTerm Nat × List (RelativeTerm Nat)) :
    RelativeTerm Nat × List (RelativeTerm Nat) := (.theta k a.1, [.theta k a.1])

theorem atoms_primrec : Primrec atoms := by
  have hw : Primrec (fun p : Nat => (CanonicalCoefficients.word p).map RelativeTerm.parameter) :=
    Primrec.list_map CanonicalCoefficients.word_primrec (parameter_primrec.comp Primrec.snd).to₂
  have hp : Primrec₂ atomParameter :=
    ((parameter_primrec.comp Primrec.snd).pair (hw.comp Primrec.snd)).to₂
  have hs : Primrec₂ atomSum :=
    ((sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  have ht : Primrec (fun p : Unit × (Nat × (RelativeTerm Nat × List (RelativeTerm Nat))) => atomTheta p.1 p.2.1 p.2.2) := by
    have hterm : Primrec (fun p : Unit × (Nat × (RelativeTerm Nat × List (RelativeTerm Nat))) =>
        RelativeTerm.theta p.2.1 p.2.2.1) := theta_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact hterm.pair (Primrec.list_cons.comp hterm (Primrec.const []))
  let fold := ValueFold.term atomParameter atomSum atomTheta ()
  have hf : Primrec fold := (ValueFold.term_primrec atomParameter atomSum atomTheta
    (.parameter 0, []) hp hs ht).comp (Primrec.const ()) Primrec.id
  have he : ∀ t : RelativeTerm Nat, fold t = (t, atoms t) := by
    intro t; induction t <;> simp_all [fold, ValueFold.term, atomParameter, atomSum, atomTheta, atoms]
  have heq : (fun t => (fold t).2) = atoms := by funext t; rw [he]
  have h := Primrec.snd.comp hf
  rw [heq] at h
  exact h

theorem atoms_size_le (t s : RelativeTerm Nat) (hs : s ∈ atoms t) : s.size ≤ t.size := by
  induction t with
  | parameter p =>
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact le_rfl
  | sum a b iha ihb =>
    rcases List.mem_append.mp hs with hs | hs
    · exact (iha hs).trans (RelativeTerm.sum_left_size_lt a b).le
    · exact (ihb hs).trans (RelativeTerm.sum_right_size_lt a b).le
  | theta k a => have he := List.mem_singleton.mp hs; subst s; exact le_rfl

/-- Only native theta representatives require previous-table calls. Their
codes remain literal constituents; new public parameter heads are direct calls. -/
theorem atoms_parameter_or_code_le (t s : RelativeTerm Nat) (hs : s ∈ atoms t) :
    (∃ p, s = .parameter p) ∨ s.code ≤ t.code := by
  induction t with
  | parameter p =>
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact Or.inl ⟨c, rfl⟩
  | sum a b iha ihb =>
    rcases List.mem_append.mp hs with hs | hs
    · rcases iha hs with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (sum_left_code_lt a b).le)
    · rcases ihb hs with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (sum_right_code_lt a b).le)
  | theta k a => have he := List.mem_singleton.mp hs; subst s; exact Or.inr le_rfl

theorem theta_pos_principal (q n k : Nat) (hq : baseCheck q = true) (a : RelativeTerm Nat)
    (ha : admissible q n (.theta k a)) : 0 < finiteDenote q n (.theta k a) ∧
      Ordinal.IsPrincipal (· + ·) (finiteDenote q n (.theta k a)) := by
  cases ha.2 with
  | theta h0k hkn hsort ha =>
    exact ⟨sourceFiniteCollapse_pos (base q) (base_pos q hq) n k hkn _,
      sourceFiniteCollapse_add_closed (base q) n k hkn _⟩

theorem atoms_spec (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hn : Normal q t) :
    (∀ a ∈ atoms t, admissible q n a ∧ Normal q a) ∧
      (atoms t).map (finiteDenote q n) = canonicalANF (finiteDenote q n t) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    have hp := (parameterCheck_exact q p).mp ht.1
    have hw := CanonicalCoefficients.word_anf p hp.1
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      have hs := CanonicalCoefficients.word_head_spec p hp.1 c hc
      have hm : unionInterpretation c ∈ canonicalANF (parameters p) := by
        change unionInterpretation c ∈ canonicalANF (unionInterpretation p)
        rw [← hw]; exact List.mem_map.mpr ⟨c, hc, rfl⟩
      have hb : parameters c < base q := (canonicalANF_mem_le hm).trans_lt hp.2.2
      exact ⟨⟨(parameterCheck_exact q c).mpr ⟨Canonical.check_original hs.1, hp.2.1, hb⟩,
        .parameter (by simpa only [omegaSequence_zero] using hb)⟩, trivial⟩
    · simpa only [atoms, List.map_map, Function.comp_def, finiteDenote, eval, parameters] using hw
  | sum a b iha ihb =>
    intro ht hn
    cases ht.2 with
    | sum ha hb =>
      have hasa := iha ⟨ht.1.1, ha⟩ hn.1
      have hasb := ihb ⟨ht.1.2, hb⟩ hn.2.1
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hasa.1 s hs
        · exact hasb.1 s hs
      · rw [atoms, List.map_append, hasa.2, hasb.2]
        exact (NormalSums.sum_anf ((normal_finite_iff q n hq (.sum a b)
          (.sum ha hb)).mpr hn)).symm
  | theta k a ih =>
    intro ht hn
    refine ⟨?_, ?_⟩
    · intro s hs; have he := List.mem_singleton.mp hs; subst s; exact ⟨ht, hn⟩
    · have hp := theta_pos_principal q n k hq a ht
      rw [canonicalANF_principal hp.1 hp.2]
      rfl

theorem atoms_anf (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hn : Normal q t) :
    (atoms t).map (denote q) = canonicalANF (denote q t) := by
  have hs := atoms_spec q n hq t ht hn
  have hm : (atoms t).map (denote q) = (atoms t).map (finiteDenote q n) := by
    apply List.map_congr_left
    intro a ha
    exact denote_eq_finite q n hq a (hs.1 a ha).1.2
  rw [hm, hs.2, denote_eq_finite q n hq t ht.2]

theorem atoms_normal (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hn : Normal q t) : IsAdditiveNormalForm ((atoms t).map (denote q)) := by
  rw [atoms_anf q n hq t ht hn]; exact canonicalANF_normal _

theorem atoms_value (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hn : Normal q t) : principalSum ((atoms t).map (denote q)) = denote q t := by
  rw [atoms_anf q n hq t ht hn, principalSum_canonicalANF]

theorem parameter_before_theta (q n p k : Nat) (a : RelativeTerm Nat)
    (hp : admissible q n (.parameter p)) (ha : admissible q n (.theta k a)) :
    finiteDenote q n (.parameter p) < finiteDenote q n (.theta k a) := by
  cases hp.2 with
  | parameter hp =>
    cases ha.2 with
    | theta h0k hkn hsort ha =>
      exact hp.trans_le (((omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)).trans
        (source_theta_range (base q) parameters n k a hkn ha hsort).1)

theorem theta_lt_of_level_lt (q n k l : Nat) (a b : RelativeTerm Nat)
    (ha : admissible q n (.theta k a)) (hb : admissible q n (.theta l b)) (hkl : k < l) :
    finiteDenote q n (.theta k a) < finiteDenote q n (.theta l b) := by
  cases ha.2 with
  | theta h0k hkn hsorta ha =>
    cases hb.2 with
    | theta h0l hln hsortb hb =>
      exact (source_theta_range (base q) parameters n k a hkn ha hsorta).2.trans_le
        (((omegaSequence_strictMono (base q)).monotone (Nat.succ_le_of_lt hkl)).trans
          (source_theta_range (base q) parameters n l b hln hb hsortb).1)

theorem theta_finite_lt_iff_exposed (q n k : Nat) (hq : baseCheck q = true) (a b : RelativeTerm Nat)
    (ha : admissible q n (.theta k a)) (hb : admissible q n (.theta k b))
    (hna : NormalSums (base q) parameters n a) (hnb : NormalSums (base q) parameters n b) :
    finiteDenote q n (.theta k a) < finiteDenote q n (.theta k b) ↔
      (finiteDenote q n a < finiteDenote q n b ∧
        ∀ s ∈ exposedThetaList k a, finiteDenote q n s < finiteDenote q n (.theta k b)) ∨
      ∃ s ∈ exposedThetaList k b, finiteDenote q n (.theta k a) ≤ finiteDenote q n s := by
  classical
  cases ha.2 with
  | theta h0k hkn hsorta ha =>
    cases hb.2 with
    | theta h0k' hkn' hsortb hb =>
      let α := sourceAdmittedOrdinal (base q) parameters n k hkn a ha
      let β := sourceAdmittedOrdinal (base q) parameters n k hkn b hb
      have star_lt (t : RelativeTerm Nat)
          (ht : Admissible parameters (omegaSequence (base q)) (sourceFiniteCollapse (base q) n) n 0 t)
          (hnt : NormalSums (base q) parameters n t) (c : Ordinal.{0}) (hc : 0 < c) :
          sourceStar (base q) (base_pos q hq) n k hkn
            (sourceAdmittedOrdinal (base q) parameters n k hkn t ht) < c ↔
              ∀ s ∈ exposedThetaList k t, finiteDenote q n s < c := by
        rw [sourceStar_eq_exposedTheta (base q) (base_pos q hq) parameters n k hkn t ht hnt,
          Finset.sup_lt_iff hc]
        constructor
        · intro h s hs
          exact h _ (Finset.mem_image.mpr ⟨s, (mem_exposedThetaList_iff k t s).mp hs, rfl⟩)
        · intro h p hp
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
          exact h s ((mem_exposedThetaList_iff k t s).mpr hs)
      have star_le : finiteDenote q n (.theta k a) ≤
          sourceStar (base q) (base_pos q hq) n k hkn β ↔
            ∃ s ∈ exposedThetaList k b, finiteDenote q n (.theta k a) ≤ finiteDenote q n s := by
        change finiteDenote q n (.theta k a) ≤ sourceStar (base q) (base_pos q hq) n k hkn
          (sourceAdmittedOrdinal (base q) parameters n k hkn b hb) ↔ _
        have hpos : 0 < finiteDenote q n (.theta k a) :=
          sourceFiniteCollapse_pos (base q) (base_pos q hq) n k hkn _
        rw [← not_lt, star_lt b hb hnb _ hpos]
        simp only [not_forall, _root_.not_imp, not_lt, exists_prop]
      have hs := sourceFiniteCollapse_lt_iff_sourceStar (base q) (base_pos q hq) n k hkn α β hsorta hsortb
      change finiteDenote q n (.theta k a) < finiteDenote q n (.theta k b) ↔
        (finiteDenote q n a < finiteDenote q n b ∧
          sourceStar (base q) (base_pos q hq) n k hkn α < finiteDenote q n (.theta k b)) ∨
        finiteDenote q n (.theta k a) ≤ sourceStar (base q) (base_pos q hq) n k hkn β at hs
      have hpos : 0 < finiteDenote q n (.theta k b) :=
        sourceFiniteCollapse_pos (base q) (base_pos q hq) n k hkn _
      rw [star_lt a ha hna _ hpos, star_le] at hs
      exact hs

theorem theta_lt_iff_exposed (q n k : Nat) (hq : baseCheck q = true) (a b : RelativeTerm Nat)
    (ha : admissible q n (.theta k a)) (hb : admissible q n (.theta k b))
    (hna : Normal q a) (hnb : Normal q b) :
    denote q (.theta k a) < denote q (.theta k b) ↔
      (denote q a < denote q b ∧ ∀ s ∈ exposedThetaList k a, denote q s < denote q (.theta k b)) ∨
      ∃ s ∈ exposedThetaList k b, denote q (.theta k a) ≤ denote q s := by
  have haa := admitted_argument ha
  have hbb := admitted_argument hb
  rw [denote_eq_finite q n hq (.theta k a) ha.2, denote_eq_finite q n hq (.theta k b) hb.2,
    theta_finite_lt_iff_exposed q n k hq a b ha hb
      ((normal_finite_iff q n hq a haa.2).mpr hna) ((normal_finite_iff q n hq b hbb.2).mpr hnb)]
  apply or_congr
  · apply and_congr
    · rw [denote_eq_finite q n hq a haa.2, denote_eq_finite q n hq b hbb.2]
    · apply forall_congr'; intro s; apply imp_congr_right; intro hs
      rw [denote_eq_finite q n hq s (haa.2.exposedThetaList k hs)]
  · apply exists_congr; intro s; apply and_congr_right; intro hs
    rw [denote_eq_finite q n hq s (hbb.2.exposedThetaList k hs)]

def lessFuel : Nat → Nat → RelativeTerm Nat → RelativeTerm Nat → Bool
  | _, _, .parameter p, .parameter v => Alexander313.HereditaryOrdinalFormation.unionLess p v
  | _, _, .parameter _, .theta _ _ => true
  | _, _, .theta _ _, .parameter _ => false
  | 0, _, _, _ => false
  | fuel + 1, q, .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (lessFuel fuel q a b && (exposedThetaList k a).all (fun s => lessFuel fuel q s (.theta l b))) ||
          (exposedThetaList k b).any (fun s => !lessFuel fuel q s (.theta k a))
  | fuel + 1, q, t, u => lexLT (lessFuel fuel q) (atoms t) (atoms u)

private theorem bool_not_true (b : Bool) : ((!b) = true) ↔ ¬ (b = true) := by cases b <;> decide

private theorem atoms_sum_size_lt (a b s : RelativeTerm Nat) (hs : s ∈ atoms (.sum a b)) :
    s.size < (.sum a b : RelativeTerm Nat).size := by
  rcases List.mem_append.mp hs with hs | hs
  · exact (atoms_size_le a s hs).trans_lt (RelativeTerm.sum_left_size_lt a b)
  · exact (atoms_size_le b s hs).trans_lt (RelativeTerm.sum_right_size_lt a b)

theorem lessFuel_correct (fuel q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) (hnt : Normal q t) (hnu : Normal q u)
    (hbudget : t.size + u.size ≤ fuel) : lessFuel fuel q t u = true ↔ denote q t < denote q u := by
  induction fuel generalizing q t u with
  | zero => cases t <;> cases u <;> simp only [RelativeTerm.size] at hbudget <;> omega
  | succ fuel ih =>
    have hq := (Bool.and_eq_true_iff.mp ht).1
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn := checked_admissible q n t ht ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun := checked_admissible q n u hu ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    have lex_case (x y : RelativeTerm Nat) (hx : check q x = true) (hy : check q y = true)
        (hnx : Normal q x) (hny : Normal q y)
        (hsmall : ∀ a ∈ atoms x, ∀ b ∈ atoms y, a.size + b.size ≤ fuel) :
        lexLT (lessFuel fuel q) (atoms x) (atoms y) = true ↔ denote q x < denote q y := by
      let m := max (SourceOne.PublicCodes.fragment x) (SourceOne.PublicCodes.fragment y)
      have hxm := checked_admissible q m x hx ((SourceOne.PublicCodes.height_le_fragment x).trans (le_max_left _ _))
      have hym := checked_admissible q m y hy ((SourceOne.PublicCodes.height_le_fragment y).trans (le_max_right _ _))
      have hc : ∀ a ∈ atoms x, ∀ b ∈ atoms y,
          (lessFuel fuel q a b = true ↔ denote q a < denote q b) ∧
          (lessFuel fuel q b a = true ↔ denote q b < denote q a) := by
        intro a ha b hb
        have has := (atoms_spec q m hq x hxm hnx).1 a ha
        have hbs := (atoms_spec q m hq y hym hny).1 b hb
        exact ⟨ih q a b (admitted_checked q m hq a has.1) (admitted_checked q m hq b hbs.1)
          has.2 hbs.2 (hsmall a ha b hb),
          ih q b a (admitted_checked q m hq b hbs.1) (admitted_checked q m hq a has.1)
            hbs.2 has.2 (by have h := hsmall a ha b hb; omega)⟩
      have he := Theta.lexLT_correct (lessFuel fuel q) (denote q) (atoms x) (atoms y)
        (atoms_normal q m hq x hxm hnx) (atoms_normal q m hq y hym hny) hc
      simpa only [atoms_value q m hq x hxm hnx, atoms_value q m hq y hym hny] using he
    cases t with
    | parameter p =>
      cases u with
      | parameter v =>
        have hp := (parameterCheck_exact q p).mp htn.1
        have hv := (parameterCheck_exact q v).mp hun.1
        simpa only [lessFuel, denote, eval, parameters, hp.1, hv.1, true_and] using
          Alexander313.HereditaryOrdinalFormation.unionLess_exact p v
      | theta k a =>
        have hv := parameter_before_theta q n p k a htn hun
        rw [← denote_eq_finite q n hq (.parameter p) htn.2,
          ← denote_eq_finite q n hq (.theta k a) hun.2] at hv
        simpa [lessFuel] using hv
      | sum a b =>
        change lexLT (lessFuel fuel q) (atoms (.parameter p)) (atoms (.sum a b)) = true ↔ _
        apply lex_case (.parameter p) (.sum a b) ht hu hnt hnu
        intro x hx y hy
        have hsx := atoms_size_le (.parameter p) x hx
        have hsy := atoms_sum_size_lt a b y hy
        omega
    | sum a b =>
      change lexLT (lessFuel fuel q) (atoms (.sum a b)) (atoms u) = true ↔ _
      apply lex_case (.sum a b) u ht hu hnt hnu
      intro x hx y hy
      have hsx := atoms_sum_size_lt a b x hx
      have hsy := atoms_size_le u y hy
      omega
    | theta k a =>
      cases u with
      | parameter p =>
        have hv := parameter_before_theta q n p k a hun htn
        rw [← denote_eq_finite q n hq (.parameter p) hun.2,
          ← denote_eq_finite q n hq (.theta k a) htn.2] at hv
        simpa [lessFuel] using not_lt_of_gt hv
      | sum b c =>
        change lexLT (lessFuel fuel q) (atoms (.theta k a)) (atoms (.sum b c)) = true ↔ _
        apply lex_case (.theta k a) (.sum b c) ht hu hnt hnu
        intro x hx y hy
        have hsx := atoms_size_le (.theta k a) x hx
        have hsy := atoms_sum_size_lt b c y hy
        omega
      | theta l b =>
        by_cases hkl : k < l
        · have hv := theta_lt_of_level_lt q n k l a b htn hun hkl
          rw [← denote_eq_finite q n hq (.theta k a) htn.2,
            ← denote_eq_finite q n hq (.theta l b) hun.2] at hv
          simpa [lessFuel, hkl] using hv
        · by_cases hlk : l < k
          · have hv := theta_lt_of_level_lt q n l k b a hun htn hlk
            rw [← denote_eq_finite q n hq (.theta k a) htn.2,
              ← denote_eq_finite q n hq (.theta l b) hun.2] at hv
            simpa [lessFuel, hkl, hlk] using not_lt_of_gt hv
          · have he : l = k := by omega
            subst l
            have haa := admitted_argument htn
            have hbb := admitted_argument hun
            have hna : Normal q a := hnt
            have hnb : Normal q b := hnu
            have hab := ih q a b (admitted_checked q n hq a haa) (admitted_checked q n hq b hbb)
              hna hnb (by simp only [RelativeTerm.size] at hbudget; omega)
            have hall : (exposedThetaList k a).all (fun s => lessFuel fuel q s (.theta k b)) = true ↔
                ∀ s ∈ exposedThetaList k a, denote q s < denote q (.theta k b) := by
              rw [List.all_eq_true]
              apply forall_congr'; intro s; apply imp_congr_right; intro hs
              exact ih q s (.theta k b) (admitted_checked q n hq s (admitted_exposed haa k hs)) hu
                (hna.exposed k hs) hnu (by
                  have hb := exposedTheta_size_le k a s ((mem_exposedThetaList_iff k a s).mp hs)
                  simp only [RelativeTerm.size] at hbudget ⊢; omega)
            have hany : (exposedThetaList k b).any (fun s => !lessFuel fuel q s (.theta k a)) = true ↔
                ∃ s ∈ exposedThetaList k b, denote q (.theta k a) ≤ denote q s := by
              rw [List.any_eq_true]
              apply exists_congr; intro s; apply and_congr_right; intro hs
              rw [bool_not_true, ih q s (.theta k a)
                (admitted_checked q n hq s (admitted_exposed hbb k hs)) ht (hnb.exposed k hs) hnt (by
                  have hb := exposedTheta_size_le k b s ((mem_exposedThetaList_iff k b s).mp hs)
                  simp only [RelativeTerm.size] at hbudget ⊢; omega), not_lt]
            simp only [lessFuel, lt_self_iff_false, if_false, Bool.or_eq_true, Bool.and_eq_true, hab, hall, hany]
            exact (theta_lt_iff_exposed q n k hq a b htn hun hna hnb).symm

def less (q : Nat) (t u : RelativeTerm Nat) : Bool := lessFuel (t.size + u.size) q t u

theorem less_correct (q : Nat) (t u : RelativeTerm Nat) (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) : less q t u = true ↔ denote q t < denote q u :=
  lessFuel_correct _ q t u ht hu hnt hnu le_rfl

def equal (q : Nat) (t u : RelativeTerm Nat) : Bool := !less q t u && !less q u t

theorem equal_correct (q : Nat) (t u : RelativeTerm Nat) (ht : check q t = true) (hu : check q u = true)
    (hnt : Normal q t) (hnu : Normal q u) : equal q t u = true ↔ denote q t = denote q u := by
  simp only [equal, Bool.and_eq_true, bool_not_true, less_correct q t u ht hu hnt hnu,
    less_correct q u t hu ht hnu hnt, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem atoms_shape (t s : RelativeTerm Nat) (hs : s ∈ atoms t) :
    (∃ p, s = .parameter p) ∨ ∃ k a, s = .theta k a := by
  induction t with
  | parameter p => obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs; exact Or.inl ⟨c, rfl⟩
  | sum a b iha ihb => rcases List.mem_append.mp hs with hs | hs; exact iha hs; exact ihb hs
  | theta k a => have he := List.mem_singleton.mp hs; subst s; exact Or.inr ⟨k, a, rfl⟩

theorem atoms_theta_code_le (t : RelativeTerm Nat) (k : Nat) (a : RelativeTerm Nat)
    (hs : (.theta k a : RelativeTerm Nat) ∈ atoms t) : (.theta k a : RelativeTerm Nat).code ≤ t.code := by
  rcases atoms_parameter_or_code_le t (.theta k a) hs with ⟨p, hp⟩ | h
  · cases hp
  · exact h

namespace Effective

open ThetaCourse (rawTree rawTree_primrec rawTree_code)

abbrev Table := List (List Bool)
abbrev Configuration := Nat × Nat

def lookup (table : Table) (t u : RelativeTerm Nat) : Bool :=
  ((table[t.code]?.getD [])[u.code]?).getD false

theorem lookup_primrec : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => lookup p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1.code) :=
    code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hu : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2.code) :=
    code_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hrow := Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst ht) (Primrec.const ([] : List Bool))
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hrow hu) (Primrec.const false)

private def rootTag (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.1
private def rootPayload (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.2
private def rootIndex (t : RelativeTerm Nat) : Nat := (rootPayload t).unpair.1
private def rootArgument (t : RelativeTerm Nat) : RelativeTerm Nat := rawTree (rootPayload t).unpair.2

private theorem rootTag_primrec : Primrec rootTag :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))
private theorem rootPayload_primrec : Primrec rootPayload :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))
private theorem rootIndex_primrec : Primrec rootIndex := Primrec.fst.comp (Primrec.unpair.comp rootPayload_primrec)
private theorem rootArgument_primrec : Primrec rootArgument :=
  rawTree_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp rootPayload_primrec))

/-- Atomic public comparisons bypass the native previous-answer table. -/
def dispatch (cmp : RelativeTerm Nat → RelativeTerm Nat → Bool) : RelativeTerm Nat → RelativeTerm Nat → Bool
  | .parameter p, .parameter v => Alexander313.HereditaryOrdinalFormation.unionLess p v
  | .parameter _, .theta _ _ => true
  | .theta _ _, .parameter _ => false
  | t, u => cmp t u

def dispatchNumeric (table : Table) (t u : RelativeTerm Nat) : Bool :=
  cond ((rootTag t == 0) && (rootTag u == 0))
    (Alexander313.HereditaryOrdinalFormation.unionLess (rootPayload t) (rootPayload u))
    (cond ((rootTag t == 0) && (rootTag u == 2)) true
      (cond ((rootTag t == 2) && (rootTag u == 0)) false (lookup table t u)))

theorem dispatchNumeric_eq (table : Table) (t u : RelativeTerm Nat) :
    dispatchNumeric table t u = dispatch (lookup table) t u := by
  cases t <;> cases u <;> simp [dispatchNumeric, dispatch, rootTag, rootPayload, code, Nat.unpair_pair]

theorem dispatchNumeric_primrec : Primrec
    (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => dispatchNumeric p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have htagT := rootTag_primrec.comp ht
  have htagU := rootTag_primrec.comp hu
  have tag (i j : Nat) := Primrec.and.comp (Primrec.beq.comp htagT (Primrec.const i)) (Primrec.beq.comp htagU (Primrec.const j))
  exact (tag 0 0).cond (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp
    (rootPayload_primrec.comp ht) (rootPayload_primrec.comp hu))
    ((tag 0 2).cond (Primrec.const true) ((tag 2 0).cond (Primrec.const false) lookup_primrec))

theorem dispatch_lessFuel (fuel q : Nat) (t u : RelativeTerm Nat) :
    dispatch (lessFuel fuel q) t u = lessFuel fuel q t u := by cases fuel <;> cases t <;> cases u <;> rfl

def advance (cmp : RelativeTerm Nat → RelativeTerm Nat → Bool) : RelativeTerm Nat → RelativeTerm Nat → Bool
  | .parameter p, .parameter v => Alexander313.HereditaryOrdinalFormation.unionLess p v
  | .parameter _, .theta _ _ => true
  | .theta _ _, .parameter _ => false
  | .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (dispatch cmp a b && (exposedThetaList k a).all (fun s => dispatch cmp s (.theta l b))) ||
          (exposedThetaList k b).any (fun s => !dispatch cmp s (.theta k a))
  | t, u => lexLT (dispatch cmp) (atoms t) (atoms u)

def tableStep (table : Table) (t u : RelativeTerm Nat) : Bool :=
  let k := rootIndex t
  let l := rootIndex u
  let a := rootArgument t
  let b := rootArgument u
  cond ((rootTag t == 0) && (rootTag u == 0))
    (Alexander313.HereditaryOrdinalFormation.unionLess (rootPayload t) (rootPayload u))
    (cond ((rootTag t == 0) && (rootTag u == 2)) true
      (cond ((rootTag t == 2) && (rootTag u == 0)) false
        (cond ((rootTag t == 2) && (rootTag u == 2))
          (cond (decide (k < l)) true (cond (decide (l < k)) false
            ((dispatchNumeric table a b && (exposedThetaList k a).all (fun s => dispatchNumeric table s u)) ||
              (exposedThetaList k b).any (fun s => !dispatchNumeric table s t))))
          (lexLT (dispatchNumeric table) (atoms t) (atoms u)))))

theorem tableStep_eq (table : Table) (t u : RelativeTerm Nat) : tableStep table t u = advance (lookup table) t u := by
  have hd : dispatchNumeric table = dispatch (lookup table) := funext fun t => funext fun u => dispatchNumeric_eq table t u
  cases t <;> cases u <;> simp [tableStep, advance, hd, rootTag, rootPayload,
    rootIndex, rootArgument, code, Nat.unpair_pair, rawTree]

theorem tableStep_primrec : Primrec
    (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => tableStep p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hk := rootIndex_primrec.comp ht
  have hl := rootIndex_primrec.comp hu
  have ha := rootArgument_primrec.comp ht
  have hb := rootArgument_primrec.comp hu
  have htagT := rootTag_primrec.comp ht
  have htagU := rootTag_primrec.comp hu
  have tag (i j : Nat) := Primrec.and.comp (Primrec.beq.comp htagT (Primrec.const i)) (Primrec.beq.comp htagU (Primrec.const j))
  have hab := dispatchNumeric_primrec.comp (Primrec.fst.pair (ha.pair hb))
  have hall : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) =>
      (exposedThetaList (rootIndex p.2.1) (rootArgument p.2.1)).all (fun s => dispatchNumeric p.1 s p.2.2)) := by
    have htest : Primrec₂ (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) =>
        fun s : RelativeTerm Nat => dispatchNumeric p.1 s p.2.2) :=
      (dispatchNumeric_primrec.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair (hu.comp Primrec.fst)))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk ha)
  have hany : Primrec (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) =>
      (exposedThetaList (rootIndex p.2.1) (rootArgument p.2.2)).any (fun s => !dispatchNumeric p.1 s p.2.1)) := by
    have htest : Primrec₂ (fun p : Table × (RelativeTerm Nat × RelativeTerm Nat) =>
        fun s : RelativeTerm Nat => !dispatchNumeric p.1 s p.2.1) :=
      (Primrec.not.comp (dispatchNumeric_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (ht.comp Primrec.fst))))).to₂
    exact (listAny_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk hb)
  have hlex := (lexLT_primrec (.parameter 0) dispatchNumeric dispatchNumeric_primrec).comp
    (Primrec.fst.pair ((atoms_primrec.comp ht).pair (atoms_primrec.comp hu)))
  exact (tag 0 0).cond (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp
    (rootPayload_primrec.comp ht) (rootPayload_primrec.comp hu))
    ((tag 0 2).cond (Primrec.const true) ((tag 2 0).cond (Primrec.const false)
      ((tag 2 2).cond ((Primrec.nat_lt.comp hk hl).decide.cond (Primrec.const true)
        ((Primrec.nat_lt.comp hl hk).decide.cond (Primrec.const false)
          (Primrec.or.comp (Primrec.and.comp hab hall) hany))) hlex)))

private theorem dispatch_congr (bound : Nat) (t u : RelativeTerm Nat)
    (f g : RelativeTerm Nat → RelativeTerm Nat → Bool) (ht : t.code < bound) (hu : u.code < bound)
    (h : ∀ x y, x.code < bound → y.code < bound → f x y = g x y) : dispatch f t u = dispatch g t u := by
  cases t <;> cases u <;> simp only [dispatch, h _ _ ht hu]

private theorem advance_congr (bound : Nat) (t u : RelativeTerm Nat)
    (f g : RelativeTerm Nat → RelativeTerm Nat → Bool) (ht : t.code < bound) (hu : u.code < bound)
    (h : ∀ x y, x.code < bound → y.code < bound → f x y = g x y) : advance f t u = advance g t u := by
  have hlex (x y : RelativeTerm Nat) (hx : x.code < bound) (hy : y.code < bound) :
      lexLT (dispatch f) (atoms x) (atoms y) = lexLT (dispatch g) (atoms x) (atoms y) := by
    apply lex_congr_on
    intro a ha b hb
    rcases atoms_shape x a ha with ⟨p, rfl⟩ | ⟨k, aa, rfl⟩ <;>
      rcases atoms_shape y b hb with ⟨v, rfl⟩ | ⟨l, bb, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · have hac := (atoms_theta_code_le x k aa ha).trans_lt hx
      have hbc := (atoms_theta_code_le y l bb hb).trans_lt hy
      exact ⟨h _ _ hac hbc, h _ _ hbc hac⟩
  cases t with
  | parameter p => cases u with
    | parameter v => rfl
    | theta k a => rfl
    | sum a b => exact hlex _ _ ht hu
  | sum a b => exact hlex _ _ ht hu
  | theta k a => cases u with
    | parameter p => rfl
    | sum b c => exact hlex _ _ ht hu
    | theta l b =>
      have ha := (theta_argument_code_lt k a).trans ht
      have hb := (theta_argument_code_lt l b).trans hu
      have hall : (exposedThetaList k a).all (fun s => dispatch f s (.theta l b)) =
          (exposedThetaList k a).all (fun s => dispatch g s (.theta l b)) := by
        apply all_congr_on; intro s hs
        exact dispatch_congr bound _ _ f g ((exposedThetaList_code_le k a s hs).trans_lt ha) hu h
      have hany : (exposedThetaList k b).any (fun s => !dispatch f s (.theta k a)) =
          (exposedThetaList k b).any (fun s => !dispatch g s (.theta k a)) := by
        apply any_congr_on; intro s hs
        rw [dispatch_congr bound _ _ f g ((exposedThetaList_code_le k b s hs).trans_lt hb) ht h]
      simp only [advance, dispatch_congr bound a b f g ha hb h, hall, hany]

private def zeroSquare (bound : Nat) : Table := (List.range bound).map (fun x =>
  (List.range bound).map (fun y => dispatch (fun _ _ => false) (rawTree x) (rawTree y)))

private def squareStep (previous : Table) (bound : Nat) : Table := (List.range bound).map (fun x =>
  (List.range bound).map (fun y => tableStep previous (rawTree x) (rawTree y)))

private theorem zeroSquare_primrec : Primrec zeroSquare := by
  have hz : Primrec (fun p : RelativeTerm Nat × RelativeTerm Nat => dispatch (fun _ _ => false) p.1 p.2) := by
    have hf : Primrec (fun p : RelativeTerm Nat × RelativeTerm Nat => false) := Primrec.const false
    have h := dispatchNumeric_primrec.comp ((Primrec.const ([] : Table)).pair Primrec.id)
    have he : ∀ t u : RelativeTerm Nat, dispatchNumeric [] t u = dispatch (fun _ _ => false) t u := by
      intro t u; rw [dispatchNumeric_eq]; cases t <;> cases u <;> simp [dispatch, lookup]
    simpa only [he, id_eq] using h
  have hrow : Primrec₂ (fun bound : Nat => fun x : Nat => (List.range bound).map
      (fun y => dispatch (fun _ _ => false) (rawTree x) (rawTree y))) := by
    have hlist : Primrec (fun p : Nat × Nat => List.range p.1) := Primrec.list_range.comp Primrec.fst
    have hcell : Primrec₂ (fun p : Nat × Nat => fun y : Nat =>
        dispatch (fun _ _ => false) (rawTree p.2) (rawTree y)) := (hz.comp ((rawTree_primrec.comp (Primrec.snd.comp Primrec.fst)).pair
      (rawTree_primrec.comp Primrec.snd))).to₂
    exact (Primrec.list_map hlist hcell).to₂
  exact Primrec.list_map Primrec.list_range hrow

private theorem squareStep_primrec : Primrec₂ squareStep := by
  have hrows : Primrec (fun p : Table × Nat => List.range p.2) := Primrec.list_range.comp Primrec.snd
  have hrow : Primrec₂ (fun p : Table × Nat => fun x : Nat => (List.range p.2).map
      (fun y => tableStep p.1 (rawTree x) (rawTree y))) := by
    have hlist : Primrec (fun p : (Table × Nat) × Nat => List.range p.1.2) :=
      Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)
    have hcell : Primrec₂ (fun p : (Table × Nat) × Nat => fun y : Nat =>
        tableStep p.1.1 (rawTree p.2) (rawTree y)) := (tableStep_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((rawTree_primrec.comp (Primrec.snd.comp Primrec.fst)).pair (rawTree_primrec.comp Primrec.snd)))).to₂
    exact (Primrec.list_map hlist hcell).to₂
  exact (Primrec.list_map hrows hrow).to₂

def table (bound fuel : Nat) : Table := Nat.rec (zeroSquare bound) (fun _ previous => squareStep previous bound) fuel

theorem table_primrec : Primrec₂ table := Primrec.nat_rec zeroSquare_primrec
  ((squareStep_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)

private theorem lookup_zero (bound : Nat) (t u : RelativeTerm Nat) (ht : t.code < bound) (hu : u.code < bound) :
    lookup (zeroSquare bound) t u = dispatch (fun _ _ => false) t u := by
  simp [lookup, zeroSquare, List.getElem?_range ht, List.getElem?_range hu, rawTree_code]

private theorem lookup_step (bound : Nat) (previous : Table) (t u : RelativeTerm Nat)
    (ht : t.code < bound) (hu : u.code < bound) : lookup (squareStep previous bound) t u = tableStep previous t u := by
  simp [lookup, squareStep, List.getElem?_range ht, List.getElem?_range hu, rawTree_code]

/-- The finite table equals the literal algorithm on all raw trees, without
admission, normality, semantic coverage or a comparator premise. -/
theorem table_correct (bound fuel q : Nat) (t u : RelativeTerm Nat) (ht : t.code < bound) (hu : u.code < bound) :
    lookup (table bound fuel) t u = lessFuel fuel q t u := by
  induction fuel generalizing t u with
  | zero =>
    change lookup (zeroSquare bound) t u = lessFuel 0 q t u
    rw [lookup_zero bound t u ht hu]
    cases t <;> cases u <;> rfl
  | succ fuel ih =>
    change lookup (squareStep (table bound fuel) bound) t u = _
    rw [lookup_step bound _ t u ht hu, tableStep_eq, advance_congr bound t u
      (lookup (table bound fuel)) (lessFuel fuel q) ht hu (fun x y hx hy => ih x y hx hy)]
    have hd : dispatch (lessFuel fuel q) = lessFuel fuel q :=
      funext fun t => funext fun u => dispatch_lessFuel fuel q t u
    cases t <;> cases u <;> simp only [advance, lessFuel, hd]

theorem lessFuel_primrec : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
    lessFuel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) => p.2.2.1.code) :=
    code_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) => p.2.2.2.code) :=
    code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb := Primrec.succ.comp (Primrec.nat_max.comp ht hu)
  have htable := table_primrec.comp hb Primrec.fst
  have h := lookup_primrec.comp (htable.pair (Primrec.snd.comp Primrec.snd))
  have he : (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      lookup (table (max p.2.2.1.code p.2.2.2.code + 1) p.1) p.2.2.1 p.2.2.2) =
      (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) => lessFuel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    funext p
    exact table_correct _ _ _ _ _ (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _))
  rw [he] at h
  exact h

theorem less_primrec : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => less p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1.size + p.2.2.size) :=
    Primrec.nat_add.comp (size_primrec.comp (Primrec.fst.comp Primrec.snd))
    (size_primrec.comp (Primrec.snd.comp Primrec.snd))
  exact lessFuel_primrec.comp (hs.pair Primrec.id)

theorem equal_primrec : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => equal p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.not.comp less_primrec) (Primrec.not.comp (less_primrec.comp
    (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))))

end Effective

private theorem normal_list_zero_iff {α : Type} (value : α → Ordinal.{0}) (as : List α)
    (has : IsAdditiveNormalForm (as.map value)) :
    principalSum (as.map value) = 0 ↔ as = [] := by
  cases as with
  | nil => simp [principalSum]
  | cons a as =>
    have ha : 0 < value a := (has.1 _ (List.mem_cons_self)).1
    have hsum : 0 < principalSum ((a :: as).map value) := ha.trans_le le_self_add
    have hsum' : 0 < principalSum (value a :: as.map value) := by simpa only [List.map_cons] using hsum
    simp [ne_of_gt hsum']

private theorem list_singleton_of_map_length {α : Type} (as : List α) (h : as.length = 1) :
    ∃ a, as = [a] := by
  cases as with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons b bs => simp at h

private theorem normalSum_iff_lists {α : Type} (value : α → Ordinal.{0}) (as bs : List α)
    (has : IsAdditiveNormalForm (as.map value)) (hbs : IsAdditiveNormalForm (bs.map value)) :
    SourceNormalSum (principalSum (as.map value) + principalSum (bs.map value))
      (principalSum (as.map value)) (principalSum (bs.map value)) ↔
      (as = [] ∧ bs = []) ∨ ∃ b, bs = [b] ∧ ∀ a ∈ as, value b ≤ value a := by
  constructor
  · intro h
    rcases h with hzero | ⟨xs, hxs, hα, hξ⟩
    · exact Or.inl ⟨(normal_list_zero_iff value as has).mp hzero.2.1,
        (normal_list_zero_iff value bs hbs).mp hzero.2.2⟩
    · have hlast := hxs.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
      have heq : bs.map value = [principalSum (bs.map value)] := by
        exact (canonicalANF_eq_of_normal hbs rfl).symm.trans
          (canonicalANF_principal hlast.1 hlast.2)
      have hlength : bs.length = 1 := by
        have h := congrArg List.length heq
        simpa only [List.length_map, List.length_singleton] using h
      obtain ⟨b, hb⟩ := list_singleton_of_map_length bs hlength
      subst bs
      have hsum : SourceNormalSum
          (principalSum (as.map value) + principalSum ([b].map value))
          (principalSum (as.map value)) (principalSum ([b].map value)) :=
        Or.inr ⟨xs, hxs, hα, hξ⟩
      have hconcat := sourceNormalSum_canonical_concat hsum
      rw [canonicalANF_eq_of_normal has rfl, canonicalANF_eq_of_normal hbs rfl] at hconcat
      apply Or.inr
      refine ⟨b, rfl, ?_⟩
      intro a ha
      exact (List.pairwise_append.mp hconcat.2).2.2 _
        (List.mem_map.mpr ⟨a, ha, rfl⟩) _ (by simp)
  · rintro (⟨rfl, rfl⟩ | ⟨b, rfl, hcross⟩)
    · exact Or.inl ⟨by simp [principalSum], rfl, rfl⟩
    · have hconcat : IsAdditiveNormalForm ((as.map value) ++ [value b]) := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact has.1 p hp
          · have he : p = value b := List.mem_singleton.mp hp
            subst p
            exact hbs.1 _ (by simp)
        · apply List.pairwise_append.mpr
          refine ⟨has.2, by simp, ?_⟩
          intro p hp q hq
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
          have he : q = value b := List.mem_singleton.mp hq
          subst q
          exact hcross a ha
      refine Or.inr ⟨as.map value, ?_, rfl, ?_⟩
      · simpa only [List.map_cons, List.map_nil, principalSum, add_zero] using hconcat
      · rw [principalSum_append]
        simp [principalSum]

def normalAppend (q : Nat) (as bs : List (RelativeTerm Nat)) : Bool :=
  match bs with
  | [] => as.isEmpty
  | [b] => as.all (fun a => !less q a b)
  | _ => false

theorem normalAppend_correct (q : Nat) (a b : RelativeTerm Nat)
    (ha : check q a = true) (hb : check q b = true) (hna : Normal q a) (hnb : Normal q b) :
    normalAppend q (atoms a) (atoms b) = true ↔
      SourceNormalSum (denote q (.sum a b)) (denote q a) (denote q b) := by
  have hq := (Bool.and_eq_true_iff.mp ha).1
  let n := max (SourceOne.PublicCodes.fragment a) (SourceOne.PublicCodes.fragment b)
  have had := checked_admissible q n a ha ((SourceOne.PublicCodes.height_le_fragment a).trans (le_max_left _ _))
  have hbd := checked_admissible q n b hb ((SourceOne.PublicCodes.height_le_fragment b).trans (le_max_right _ _))
  have he := normalSum_iff_lists (denote q) (atoms a) (atoms b)
    (atoms_normal q n hq a had hna) (atoms_normal q n hq b hbd hnb)
  rw [atoms_value q n hq a had hna, atoms_value q n hq b hbd hnb] at he
  change normalAppend q (atoms a) (atoms b) = true ↔ SourceNormalSum (denote q a + denote q b) (denote q a) (denote q b)
  rw [he]
  generalize hlist : atoms b = bs
  cases bs with
  | nil => simp [normalAppend]
  | cons s ss =>
    cases ss with
    | cons v vs => simp [normalAppend]
    | nil =>
      have hs : s ∈ atoms b := by rw [hlist]; simp
      have hss := (atoms_spec q n hq b hbd hnb).1 s hs
      simp only [normalAppend, List.all_eq_true, List.cons_ne_nil, false_and, false_or,
        List.cons.injEq, and_true, and_false, exists_eq_left, exists_eq_left', exists_eq_right]
      apply forall_congr'; intro t; apply imp_congr_right; intro ht
      have hts := (atoms_spec q n hq a had hna).1 t ht
      have hc := less_correct q t s (admitted_checked q n hq t hts.1) (admitted_checked q n hq s hss.1) hts.2 hss.2
      rw [bool_not_true, hc, not_lt]

def normalCheck (q : Nat) : RelativeTerm Nat → Bool
  | .parameter _ => true
  | .sum a b => (normalCheck q a && normalCheck q b) && normalAppend q (atoms a) (atoms b)
  | .theta _ a => normalCheck q a

theorem normalCheck_correct (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    normalCheck q t = true ↔ Normal q t := by
  revert ht
  induction t with
  | parameter p => intro ht; simp only [normalCheck, Normal, Bool.true_eq]
  | sum a b iha ihb =>
    intro ht
    have hq := (Bool.and_eq_true_iff.mp ht).1
    have had := (checked_admissible q (SourceOne.PublicCodes.fragment (.sum a b)) (.sum a b) ht
      (SourceOne.PublicCodes.height_le_fragment _))
    cases had.2 with
    | sum ha hb =>
      have hca := admitted_checked q _ hq a ⟨had.1.1, ha⟩
      have hcb := admitted_checked q _ hq b ⟨had.1.2, hb⟩
      constructor
      · intro hc
        have hs : normalCheck q a = true ∧ normalCheck q b = true ∧ normalAppend q (atoms a) (atoms b) = true := by
          simpa only [normalCheck, Bool.and_eq_true, and_assoc] using hc
        have hna := (iha hca).mp hs.1
        have hnb := (ihb hcb).mp hs.2.1
        exact ⟨hna, hnb, (normalAppend_correct q a b hca hcb hna hnb).mp hs.2.2⟩
      · rintro ⟨hna, hnb, hsum⟩
        simp only [normalCheck, (iha hca).mpr hna, (ihb hcb).mpr hnb,
          (normalAppend_correct q a b hca hcb hna hnb).mpr hsum, Bool.true_and]
  | theta k a ih =>
    intro ht
    have hq := (Bool.and_eq_true_iff.mp ht).1
    have ha := admitted_argument (checked_admissible q (SourceOne.PublicCodes.fragment (.theta k a)) _ ht
      (SourceOne.PublicCodes.height_le_fragment _))
    exact ih (admitted_checked q _ hq a ha)

namespace Effective

open ThetaCourse (rawTree rawTree_primrec rawTree_code)

private def appendNumeric (q : Nat) (as bs : List (RelativeTerm Nat)) : Bool :=
  cond (bs.length == 0) (as.length == 0)
    (cond (bs.length == 1) (as.all (fun a => !less q a (bs[0]?.getD (.parameter 0)))) false)

theorem normalAppend_primrec : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
    normalAppend p.1 p.2.1 p.2.2) := by
  have hlen : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) => p.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hhead : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      p.2.2[0]?.getD (RelativeTerm.parameter 0)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)) (Primrec.const (RelativeTerm.parameter 0))
  have hall : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      p.2.1.all (fun a => !less p.1 a (p.2.2[0]?.getD (.parameter 0)))) := by
    have htest : Primrec₂ (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
        fun a : RelativeTerm Nat => !less p.1 a (p.2.2[0]?.getD (.parameter 0))) :=
      (Primrec.not.comp (less_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (hhead.comp Primrec.fst))))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id (Primrec.fst.comp Primrec.snd)
  have h := (Primrec.beq.comp hlen (Primrec.const 0)).cond
    (Primrec.beq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
    ((Primrec.beq.comp hlen (Primrec.const 1)).cond hall (Primrec.const false))
  have he : (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) => appendNumeric p.1 p.2.1 p.2.2) =
      (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) => normalAppend p.1 p.2.1 p.2.2) := by
    funext p
    cases p.2.2 with
    | nil => cases p.2.1 <;> rfl
    | cons b bs => cases bs <;> simp [appendNumeric, normalAppend]
  change Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) => appendNumeric p.1 p.2.1 p.2.2) at h
  rw [he] at h
  exact h

abbrev NormalState := Nat × (RelativeTerm Nat × Bool)

private def normalParameter (q p : Nat) : NormalState := (q, (.parameter p, true))
private def normalSum (a b : NormalState) : NormalState :=
  (a.1, (.sum a.2.1 b.2.1, (a.2.2 && b.2.2) && normalAppend a.1 (atoms a.2.1) (atoms b.2.1)))
private def normalTheta (q k : Nat) (a : NormalState) : NormalState := (q, (.theta k a.2.1, a.2.2))

def normalStateCode (q c : Nat) : NormalState :=
  ValueFold.code normalParameter normalSum normalTheta (0, (.parameter 0, true)) q c

theorem normalStateCode_primrec : Primrec₂ normalStateCode := by
  have hp : Primrec₂ normalParameter :=
    (Primrec.fst.pair ((parameter_primrec.comp Primrec.snd).pair (Primrec.const true))).to₂
  have hs : Primrec₂ normalSum := by
    have hq : Primrec (fun p : NormalState × NormalState => p.1.1) := Primrec.fst.comp Primrec.fst
    have ha : Primrec (fun p : NormalState × NormalState => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hb : Primrec (fun p : NormalState × NormalState => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hca : Primrec (fun p : NormalState × NormalState => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hcb : Primrec (fun p : NormalState × NormalState => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hv := Primrec.and.comp (Primrec.and.comp hca hcb)
      (normalAppend_primrec.comp (hq.pair ((atoms_primrec.comp ha).pair (atoms_primrec.comp hb))))
    exact (hq.pair ((sum_primrec.comp ha hb).pair hv)).to₂
  have ht : Primrec (fun p : Nat × (Nat × NormalState) => normalTheta p.1 p.2.1 p.2.2) :=
    Primrec.fst.pair ((theta_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact ValueFold.code_primrec normalParameter normalSum normalTheta (0, (.parameter 0, true)) hp hs ht

theorem normalStateCode_code (q : Nat) (t : RelativeTerm Nat) : normalStateCode q t.code = (q, (t, normalCheck q t)) := by
  rw [normalStateCode, ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, normalParameter, normalSum, normalTheta, normalCheck]

theorem normalCheck_primrec : Primrec₂ normalCheck := by
  have h := Primrec.snd.comp (Primrec.snd.comp (normalStateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  simpa only [normalStateCode_code] using h.to₂

end Effective

def acceptedCode (q c : Nat) : Bool := checkCode q c && normalCheck q (ThetaCourse.rawTree c)

theorem acceptedCode_primrec : Primrec₂ acceptedCode :=
  (Primrec.and.comp checkCode_primrec (Effective.normalCheck_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

theorem acceptedCode_exact (q c : Nat) : acceptedCode q c = true ↔
    checkCode q c = true ∧ Normal q (ThetaCourse.rawTree c) := by
  simp only [acceptedCode, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hn⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    exact ⟨hc, by simpa only [← ht, ThetaCourse.rawTree_code] using
      (normalCheck_correct q t hct).mp (by simpa only [← ht, ThetaCourse.rawTree_code] using hn)⟩
  · rintro ⟨hc, hn⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    exact ⟨hc, by simpa only [← ht, ThetaCourse.rawTree_code] using
      (normalCheck_correct q t hct).mpr (by simpa only [← ht, ThetaCourse.rawTree_code] using hn)⟩

def lessCode (q c d : Nat) : Bool :=
  (acceptedCode q c && acceptedCode q d) && less q (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)

def equalCode (q c d : Nat) : Bool :=
  (acceptedCode q c && acceptedCode q d) && equal q (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)

theorem lessCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => lessCode p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => acceptedCode p.1 p.2.1) :=
    acceptedCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × (Nat × Nat) => acceptedCode p.1 p.2.2) :=
    acceptedCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.and.comp hc hd) (Effective.less_primrec.comp (Primrec.fst.pair
    ((ThetaCourse.rawTree_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd)))))

theorem equalCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => equalCode p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => acceptedCode p.1 p.2.1) :=
    acceptedCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × (Nat × Nat) => acceptedCode p.1 p.2.2) :=
    acceptedCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.and.comp hc hd) (Effective.equal_primrec.comp (Primrec.fst.pair
    ((ThetaCourse.rawTree_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd)))))

theorem lessCode_exact (q c d : Nat) : lessCode q c d = true ↔
    checkCode q c = true ∧ Normal q (ThetaCourse.rawTree c) ∧
      checkCode q d = true ∧ Normal q (ThetaCourse.rawTree d) ∧ interpretation q c < interpretation q d := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    have hc := (acceptedCode_exact q c).mp (Bool.and_eq_true_iff.mp hs.1).1
    have hd := (acceptedCode_exact q d).mp (Bool.and_eq_true_iff.mp hs.1).2
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc.1
    obtain ⟨u, hu, hdu⟩ := (checkCode_exact q d).mp hd.1
    refine ⟨hc.1, hc.2, hd.1, hd.2, ?_⟩
    simpa only [← ht, ← hu, ThetaCourse.rawTree_code, interpretation_code] using
      (less_correct q t u hct hdu (by simpa only [← ht, ThetaCourse.rawTree_code] using hc.2)
        (by simpa only [← hu, ThetaCourse.rawTree_code] using hd.2)).mp
          (by simpa only [← ht, ← hu, ThetaCourse.rawTree_code] using hs.2)
  · rintro ⟨hc, hn, hd, hm, hv⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    obtain ⟨u, hu, hdu⟩ := (checkCode_exact q d).mp hd
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨(acceptedCode_exact q c).mpr ⟨hc, hn⟩,
      (acceptedCode_exact q d).mpr ⟨hd, hm⟩⟩, ?_⟩
    simpa only [← ht, ← hu, ThetaCourse.rawTree_code] using
      (less_correct q t u hct hdu (by simpa only [← ht, ThetaCourse.rawTree_code] using hn)
        (by simpa only [← hu, ThetaCourse.rawTree_code] using hm)).mpr
          (by simpa only [← ht, ← hu, interpretation_code] using hv)

theorem equalCode_exact (q c d : Nat) : equalCode q c d = true ↔
    checkCode q c = true ∧ Normal q (ThetaCourse.rawTree c) ∧
      checkCode q d = true ∧ Normal q (ThetaCourse.rawTree d) ∧ interpretation q c = interpretation q d := by
  have semantic (hc : checkCode q c = true) (hd : checkCode q d = true)
      (hn : Normal q (ThetaCourse.rawTree c)) (hm : Normal q (ThetaCourse.rawTree d)) :
      equal q (ThetaCourse.rawTree c) (ThetaCourse.rawTree d) = true ↔ interpretation q c = interpretation q d := by
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    obtain ⟨u, hu, hdu⟩ := (checkCode_exact q d).mp hd
    simpa only [← ht, ← hu, ThetaCourse.rawTree_code, interpretation_code] using
      equal_correct q t u hct hdu (by simpa only [← ht, ThetaCourse.rawTree_code] using hn)
        (by simpa only [← hu, ThetaCourse.rawTree_code] using hm)
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    have hc := (acceptedCode_exact q c).mp (Bool.and_eq_true_iff.mp hs.1).1
    have hd := (acceptedCode_exact q d).mp (Bool.and_eq_true_iff.mp hs.1).2
    exact ⟨hc.1, hc.2, hd.1, hd.2, (semantic hc.1 hd.1 hc.2 hd.2).mp hs.2⟩
  · rintro ⟨hc, hn, hd, hm, hv⟩
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨(acceptedCode_exact q c).mpr ⟨hc, hn⟩,
      (acceptedCode_exact q d).mpr ⟨hd, hm⟩⟩, (semantic hc hd hn hm).mpr hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Comparison
