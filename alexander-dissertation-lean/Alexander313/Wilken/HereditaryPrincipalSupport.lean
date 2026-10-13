import Alexander313.Wilken.RelativeTermPrincipalSupport
import Alexander313.Wilken.HereditaryThetaSupport

/-!
# Primitive-recursive full-depth support and actual hereditary caller bounds

The finite syntax fold reconstructs every written term and computes its full
principal list and literal parameter list. Same-level theta nodes retain their
root and their recursively computed argument list. Raw auxiliary outputs do
not certify malformed codes. Hereditary original checks and normality are kept
in every semantic caller theorem; real values are transported from the actual
finite source family. Parameter payloads remain locally atomic, and no claim
equates weak hereditary normality with the stronger source Par convention.
All terms remain uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.PrincipalSupport

namespace Codes

abbrev State := RelativeTerm Nat × (List (RelativeTerm Nat) × List Nat)

def parameterState (_ : Nat) (p : Nat) : State := (.parameter p, ([], [p]))

def sumState (a b : State) : State := (.sum a.1 b.1, (a.2.1 ++ b.2.1, a.2.2 ++ b.2.2))

def thetaState (m k : Nat) (a : State) : State :=
  let t := RelativeTerm.theta k a.1
  (t, (cond (decide (m ≤ k)) (cond (k == m) (t :: a.2.1) a.2.1) [], a.2.2))

theorem parameterState_primrec : Primrec₂ parameterState :=
  ((parameter_primrec.comp Primrec.snd).pair ((Primrec.const []).pair
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have ht : Primrec (fun p : State × State => RelativeTerm.sum p.1.1 p.2.1) :=
    sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have ha : Primrec (fun p : State × State => p.1.2) := Primrec.snd.comp Primrec.fst
  have hb : Primrec (fun p : State × State => p.2.2) := Primrec.snd.comp Primrec.snd
  have hps := Primrec.list_append.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)
  have hpar := Primrec.list_append.comp (Primrec.snd.comp ha) (Primrec.snd.comp hb)
  exact (ht.pair (hps.pair hpar)).to₂

theorem thetaState_primrec : Primrec (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × (Nat × State) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × (Nat × State) => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht := theta_primrec.comp hk (Primrec.fst.comp ha)
  have hps := Primrec.fst.comp (Primrec.snd.comp ha)
  have hpar := Primrec.snd.comp (Primrec.snd.comp ha)
  have hsame := Primrec.beq.comp hk Primrec.fst
  have hopen := (Primrec.nat_le.comp Primrec.fst hk).decide
  have hcons := Primrec.list_cons.comp ht hps
  exact ht.pair ((hopen.cond (hsame.cond hcons hps) (Primrec.const [])).pair hpar)

def state (m : Nat) (t : RelativeTerm Nat) : State :=
  ValueFold.term parameterState sumState thetaState m t

def stateCode (m c : Nat) : State :=
  ValueFold.code parameterState sumState thetaState (.parameter 0, ([], [])) m c

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState sumState thetaState (.parameter 0, ([], []))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (.parameter 0, ([], []))
    parameterState_primrec sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (m : Nat) (t : RelativeTerm Nat) : stateCode m t.code = state m t :=
  ValueFold.code_term parameterState sumState thetaState (.parameter 0, ([], [])) m t

@[simp] theorem state_eq (m : Nat) (t : RelativeTerm Nat) : state m t = (t, (principalList m t, parameterList t)) := by
  induction t with
  | parameter p => rfl
  | sum a b iha ihb =>
    change sumState (state m a) (state m b) = _
    rw [iha, ihb]
    rfl
  | theta k a ih =>
    change thetaState m k (state m a) = _
    rw [ih]
    by_cases hmk : m ≤ k <;> by_cases hkm : k = m <;>
      simp [thetaState, principalList, parameterList, Bool.beq_eq_decide_eq, hmk, hkm]

end Codes

theorem principalList_primrec : Primrec₂ (principalList (Parameter := Nat)) := by
  have h := (Primrec.fst.comp Primrec.snd).comp₂ Codes.state_primrec
  simpa only [Codes.state_eq] using h

theorem parameterList_primrec : Primrec (parameterList (Parameter := Nat)) := by
  have h := (Primrec.snd.comp Primrec.snd).comp
    (Codes.state_primrec.comp (Primrec.const 0) Primrec.id)
  exact h.of_eq (fun t => by simp only [Codes.state_eq, id_eq])

def listCode (m c : Nat) : List Nat := (Codes.stateCode m c).2.1.map RelativeTerm.code

theorem listCode_primrec : Primrec₂ listCode := by
  have hl : Primrec (fun p : Nat × Nat => (Codes.stateCode p.1 p.2).2.1) :=
    (Primrec.fst.comp Primrec.snd).comp Codes.stateCode_primrec
  exact (Primrec.list_map hl (RelativeTerm.code_primrec.comp Primrec.snd).to₂).to₂

@[simp] theorem listCode_code (m : Nat) (t : RelativeTerm Nat) :
    listCode m t.code = (principalList m t).map RelativeTerm.code := by
  simp only [listCode, Codes.stateCode_code, Codes.state_eq]

def parameterCodeList (c : Nat) : List Nat := (Codes.stateCode 0 c).2.2

theorem parameterCodeList_primrec : Primrec parameterCodeList :=
  (Primrec.snd.comp Primrec.snd).comp (Codes.stateCode_primrec.comp (Primrec.const 0) Primrec.id)

@[simp] theorem parameterCodeList_code (t : RelativeTerm Nat) : parameterCodeList t.code = parameterList t := by
  simp only [parameterCodeList, Codes.stateCode_code, Codes.state_eq]

end Alexander313.Wilken.RelativeTerm.PrincipalSupport

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalSupport

abbrev principalList := RelativeTerm.PrincipalSupport.principalList (Parameter := Nat)
abbrev parameterList := RelativeTerm.PrincipalSupport.parameterList (Parameter := Nat)
abbrev listCode := RelativeTerm.PrincipalSupport.listCode
abbrev parameterCodeList := RelativeTerm.PrincipalSupport.parameterCodeList

theorem listCode_primrec : Primrec₂ listCode := RelativeTerm.PrincipalSupport.listCode_primrec

@[simp] theorem listCode_code (m : Nat) (t : RelativeTerm Nat) :
    listCode m t.code = (principalList m t).map RelativeTerm.code := RelativeTerm.PrincipalSupport.listCode_code m t

theorem principalList_root (m : Nat) (a : RelativeTerm Nat) :
    .theta m a ∈ principalList m (.theta m a) := RelativeTerm.PrincipalSupport.principalList_root m a

theorem principalList_shape (m : Nat) (t s : RelativeTerm Nat)
    (hs : s ∈ principalList m t) : ∃ a, s = .theta m a := RelativeTerm.PrincipalSupport.principalList_shape m t s hs

theorem principalList_normal {r : Nat} {t s : RelativeTerm Nat} (hn : Theta.Normal r t)
    (m : Nat) (hs : s ∈ principalList m t) : Theta.Normal r s := by
  revert hn hs
  induction t with
  | parameter p => intro hn hs; simp only [principalList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro hn hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha hn.sum_left hs
    · exact ihb hn.sum_right hs
  | theta k a ih =>
    intro hn hs
    by_cases hmk : m ≤ k
    · by_cases hkm : k = m
      · simp only [principalList, RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_pos hkm] at hs
        rcases List.mem_cons.mp hs with he | hs
        · subst s; exact hn
        · exact ih ((Theta.normal_theta r k a).mp hn) hs
      · apply ih ((Theta.normal_theta r k a).mp hn)
        simpa only [principalList, RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_neg hkm] using hs
    · simp only [principalList, RelativeTerm.PrincipalSupport.principalList, if_neg hmk, List.not_mem_nil] at hs

theorem principalList_payloads {r : Nat} {t s : RelativeTerm Nat} (ht : Payloads r t)
    (m : Nat) (hs : s ∈ principalList m t) : Payloads r s := by
  revert ht hs
  induction t with
  | parameter p => intro ht hs; simp only [principalList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2 hs
  | theta k a ih =>
    intro ht hs
    by_cases hmk : m ≤ k
    · by_cases hkm : k = m
      · simp only [principalList, RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_pos hkm] at hs
        rcases List.mem_cons.mp hs with he | hs
        · subst s; exact ht
        · exact ih ht hs
      · apply ih ht
        simpa only [principalList, RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_neg hkm] using hs
    · simp only [principalList, RelativeTerm.PrincipalSupport.principalList, if_neg hmk, List.not_mem_nil] at hs

theorem principalList_admitted {r n : Nat} {t s : RelativeTerm Nat}
    (ht : admissible r n t) (m : Nat) (hs : s ∈ principalList m t) : admissible r n s :=
  ⟨principalList_payloads ht.1 m hs, RelativeTerm.PrincipalSupport.principalList_admissible ht.2 m hs⟩

theorem principalList_node {r : Nat} {t s : RelativeTerm Nat} (ht : check r t = true)
    (hn : Theta.Normal r t) {m : Nat} (hs : s ∈ principalList m t) :
    check r s = true ∧ Theta.Normal r s := by
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r t).mp ht
  exact ⟨Theta.admitted_checked (principalList_admitted ha m hs), principalList_normal hn m hs⟩

theorem principalList_argument_lt (r m : Nat) (a s : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r a) (hs : s ∈ principalList m a) :
    denote r s < denote r (.theta m a) := by
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r (.theta m a)).mp ht
  have haa := Theta.admitted_theta_argument ha
  rw [denote_eq_finite r n s (principalList_admitted haa m hs).2,
    denote_eq_finite r n (.theta m a) ha.2]
  exact RelativeTerm.PrincipalSupport.principalList_argument_lt (finiteBase r) (finiteBase_pos r)
    (parameters r) n m a s ha.2 (hn.finite haa) hs

theorem principalList_theta_value_le (r : Nat) (a s : RelativeTerm Nat)
    (ht : check r (.theta 0 a) = true) (hn : Theta.Normal r (.theta 0 a))
    (hs : s ∈ principalList 0 (.theta 0 a)) : denote r s ≤ denote r (.theta 0 a) := by
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r (.theta 0 a)).mp ht
  rw [denote_eq_finite r n s (principalList_admitted ha 0 hs).2,
    denote_eq_finite r n (.theta 0 a) ha.2]
  exact RelativeTerm.PrincipalSupport.principalList_theta_value_le (finiteBase r) (finiteBase_pos r)
    (parameters r) n 0 a s ha.2
      (((Theta.normal_theta r 0 a).mp hn).finite (Theta.admitted_theta_argument ha)) hs

end Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalSupport
