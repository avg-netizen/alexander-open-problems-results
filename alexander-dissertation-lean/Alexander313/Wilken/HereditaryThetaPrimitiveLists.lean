import Alexander313.Wilken.HereditaryThetaCourse
import Alexander313.Wilken.HereditaryThetaAtoms
import Alexander313.Wilken.ComparisonPrimitiveLists

/-! # Literal opened hereditary atoms: bounds and uniform effectivity

The earlier payloads are actually decoded and their real constituent atoms
are rewrapped by literal parameter constructors. Code and expanded-fuel bounds
hold on every raw tree, without admission or normality. A uniform course table
executes that exact atom algorithm; malformed payload decodes remain empty.
No ordinal-order test or hereditary effectivity assumption enters these proofs.
All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Effective

open ThetaCourse
open SourceOne.Comparison.Effective

theorem atoms_parameter_succ (r p : Nat) : atoms (r + 1) (.parameter p) =
    ((decode p).map (fun u => (atoms r u).map (fun a => .parameter a.code))).getD [] := rfl

@[simp] theorem atoms_default (r : Nat) : atoms r (.parameter 0) = [] := by
  cases r with
  | zero => rfl
  | succ r => simp [atoms_parameter_succ, decode]

private theorem parameter_code_mono {p q : Nat} (h : p ≤ q) :
    (.parameter p : RelativeTerm Nat).code ≤ (.parameter q : RelativeTerm Nat).code := by
  have pairZero (n : Nat) : Nat.pair 0 n = n * n := by
    cases n <;> simp [Nat.pair]
  simp only [code_parameter, pairZero]
  exact Nat.succ_le_succ (Nat.mul_le_mul h h)

private theorem thetaAtoms_size_le (r : Nat) (t a : RelativeTerm Nat)
    (ha : a ∈ thetaAtoms t) : expandedSize r a.code ≤ expandedSize r t.code := by
  revert ha
  induction t with
  | parameter p => intro ha; simp [thetaAtoms] at ha
  | sum x y ihx ihy =>
    intro ha
    rcases List.mem_append.mp ha with hx | hy
    · exact (ihx hx).trans (ThetaCourse.sum_left_size_lt r x y).le
    · exact (ihy hy).trans (ThetaCourse.sum_right_size_lt r x y).le
  | theta k x =>
    intro ha
    have he : a = .theta k x := List.mem_singleton.mp ha
    subst a
    exact le_rfl

/-- These are literal bounds on all outputs, with no semantic hypotheses. -/
theorem atoms_bounds (r : Nat) (t a : RelativeTerm Nat) (ha : a ∈ atoms r t) :
    a.code ≤ t.code ∧ expandedSize r a.code ≤ expandedSize r t.code := by
  induction r generalizing t a with
  | zero =>
    change a ∈ thetaAtoms t at ha
    exact ⟨thetaAtoms_code_le t a ha, thetaAtoms_size_le 0 t a ha⟩
  | succ r ih =>
    revert ha
    induction t with
    | parameter p =>
      intro ha
      rw [atoms_parameter_succ] at ha
      cases hd : decode p with
      | none => simp [hd] at ha
      | some u =>
        have hu := decode_sound p u hd
        have hm : a ∈ (atoms r u).map (fun b => .parameter b.code) := by
          simpa only [hd, Option.map_some, Option.getD_some] using ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
        have hbound := ih u b hb
        refine ⟨?_, ?_⟩
        · exact parameter_code_mono (hbound.1.trans_eq hu)
        · rw [expandedSize_parameter_succ, expandedSize_parameter_succ, ← hu]
          exact Nat.add_le_add_right hbound.2 1
    | sum x y ihx ihy =>
      intro ha
      rw [atoms_sum] at ha
      rcases List.mem_append.mp ha with hx | hy
      · have hb := ihx hx
        exact ⟨hb.1.trans (sum_left_code_lt x y).le,
          hb.2.trans (ThetaCourse.sum_left_size_lt (r + 1) x y).le⟩
      · have hb := ihy hy
        exact ⟨hb.1.trans (sum_right_code_lt x y).le,
          hb.2.trans (ThetaCourse.sum_right_size_lt (r + 1) x y).le⟩
    | theta k x ihx =>
      intro ha
      have he : a = .theta k x := by simpa only [atoms_theta, List.mem_singleton] using ha
      subst a
      exact ⟨le_rfl, le_rfl⟩

theorem atoms_code_le (r : Nat) (t a : RelativeTerm Nat) (ha : a ∈ atoms r t) :
    a.code ≤ t.code := (atoms_bounds r t a ha).1

theorem atoms_expandedSize_le (r : Nat) (t a : RelativeTerm Nat) (ha : a ∈ atoms r t) :
    expandedSize r a.code ≤ expandedSize r t.code := (atoms_bounds r t a ha).2

private def wrap (as : List (RelativeTerm Nat)) : List (RelativeTerm Nat) :=
  as.map (fun a => .parameter a.code)

private theorem wrap_primrec : Primrec wrap := by
  have hm : Primrec₂ (fun (_ : List (RelativeTerm Nat)) (a : RelativeTerm Nat) =>
      RelativeTerm.parameter a.code) :=
    ((parameter_primrec.comp code_primrec).comp Primrec.snd).to₂
  exact Primrec.list_map Primrec.id hm

private def parameterOp (_ : Nat × Nat) (p : Nat) (as : List (RelativeTerm Nat)) :
    List (RelativeTerm Nat) := cond (isCode p) (wrap as) []

private def thetaOp (q : Nat × Nat) (_ : Nat) (_ : List (RelativeTerm Nat)) :
    List (RelativeTerm Nat) := [rawTree q.2]

private def fold : Nat → Nat → List (RelativeTerm Nat) :=
  run (fun _ => []) (fun _ _ => []) parameterOp (fun _ => List.append) thetaOp

private theorem fold_primrec : Primrec₂ fold := by
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × List (RelativeTerm Nat)) =>
      parameterOp p.1 p.2.1 p.2.2) :=
    (isCode_primrec.comp (Primrec.fst.comp Primrec.snd)).cond
      (wrap_primrec.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const [])
  have hs : Primrec
      (fun p : (Nat × Nat) × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
        p.2.1 ++ p.2.2) :=
    Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × List (RelativeTerm Nat)) =>
      thetaOp p.1 p.2.1 p.2.2) :=
    Primrec.list_cons.comp (rawTree_primrec.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.const [])
  exact run_primrec _ _ _ _ _ (Primrec.const []) (Primrec.const []).to₂ hp hs ht

private theorem fold_code (r : Nat) (t : RelativeTerm Nat) : fold r t.code = atoms r t := by
  induction r generalizing t with
  | zero =>
    induction t <;>
      simp_all [fold, run, code, Nat.unpair_pair, atoms, thetaAtoms, thetaOp, rawTree]
    rename_i k a ih
    exact rawTree_code (.theta k a)
  | succ r ihr =>
    induction t with
    | parameter p =>
      cases hd : decode p with
      | none =>
        have hs := (decode_eq_none_iff p).mp hd
        simp [fold, run, code, Nat.unpair_pair, parameterOp, hs, atoms_parameter_succ, hd]
      | some u =>
        have hu := decode_sound p u hd
        have hprevious := ihr u
        simp only [fold] at hprevious
        rw [← hu]
        simp [fold, run, code, Nat.unpair_pair, parameterOp, wrap,
          atoms_parameter_succ_code, hprevious]
    | sum a b iha ihb =>
      simp only [fold] at iha ihb
      simp [fold, run, code, Nat.unpair_pair, iha, ihb, atoms_sum]
    | theta k a ih =>
      simp [fold, run, code, Nat.unpair_pair, thetaOp, rawTree, atoms_theta]
      exact rawTree_code (.theta k a)

/-- Exact opened atoms for every raw code. Failed whole decodes return empty. -/
def atomsCode (r c : Nat) : List (RelativeTerm Nat) := cond (isCode c) (fold r c) []

theorem atomsCode_primrec : Primrec₂ atomsCode :=
  ((isCode_primrec.comp Primrec.snd).cond fold_primrec (Primrec.const [])).to₂

@[simp] theorem atomsCode_code (r : Nat) (t : RelativeTerm Nat) :
    atomsCode r t.code = atoms r t := by
  simp only [atomsCode, isCode_code, Bool.cond_true, fold_code]

theorem atomsCode_eq (r c : Nat) : atomsCode r c = atoms r (rawTree c) := by
  cases hd : decode c with
  | none =>
    have hs := (decode_eq_none_iff c).mp hd
    simp only [atomsCode, hs, Bool.cond_false, rawTree, hd, Option.getD_none, atoms_default]
  | some t =>
    have ht := decode_sound c t hd
    rw [← ht, rawTree_code, atomsCode_code]

theorem atoms_primrec : Primrec₂ atoms := by
  have h := atomsCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)
  simpa only [atomsCode_code] using h.to₂

theorem atoms_computable : Computable₂ atoms := atoms_primrec.to_comp

theorem exposedThetaList_expandedSize_le (r m : Nat) (t a : RelativeTerm Nat)
    (ha : a ∈ exposedThetaList m t) : expandedSize r a.code ≤ expandedSize r t.code := by
  revert ha
  induction t with
  | parameter p => intro ha; simp [exposedThetaList] at ha
  | sum x y ihx ihy =>
    intro ha
    rcases List.mem_append.mp ha with hx | hy
    · exact (ihx hx).trans (ThetaCourse.sum_left_size_lt r x y).le
    · exact (ihy hy).trans (ThetaCourse.sum_right_size_lt r x y).le
  | theta k x ih =>
    intro ha
    by_cases hkm : k = m
    · have he : a = .theta k x := by simpa [exposedThetaList, hkm] using ha
      subst a
      exact le_rfl
    · by_cases hmk : m < k
      · have hx : a ∈ exposedThetaList m x := by simpa [exposedThetaList, hkm, hmk] using ha
        exact (ih hx).trans (theta_argument_size_lt r k x).le
      · simp [exposedThetaList, hkm, hmk] at ha

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Effective
