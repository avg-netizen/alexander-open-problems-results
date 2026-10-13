import Alexander313.Wilken.RelativeTermNormalSupport

/-!
# Primitive-recursive extraction of the actual exposed theta nodes

The fold reconstructs the literal current term and retains exactly the
theta-m nodes exposed at cutoff m+1. It performs only constructor/level
tests and list operations. Typed correspondence connects its actual output
codes to the finite source-support fidelity theorem, without a semantic
normality checker or ordinal comparison oracle. Malformed raw codes have
auxiliary fold outputs; this extraction does not admit them as notations.
-/

namespace Alexander313.Wilken.RelativeTerm

variable {Parameter : Type}

def exposedThetaList (m : Nat) : RelativeTerm Parameter → List (RelativeTerm Parameter)
  | .parameter _ => []
  | .sum a b => exposedThetaList m a ++ exposedThetaList m b
  | .theta k a => if k = m then [.theta k a] else
      if m < k then exposedThetaList m a else []

@[simp] theorem exposedThetaList_toFinset [DecidableEq Parameter] (m : Nat)
    (t : RelativeTerm Parameter) : (exposedThetaList m t).toFinset = exposedTheta m t := by
  induction t with
  | parameter p => simp [exposedThetaList, exposedTheta]
  | sum a b iha ihb => simp [exposedThetaList, exposedTheta, iha, ihb]
  | theta k a ih =>
    by_cases hkm : k = m <;> by_cases hmk : m < k <;>
      simp [exposedThetaList, exposedTheta, hkm, hmk, ih]

theorem mem_exposedThetaList_iff [DecidableEq Parameter] (m : Nat)
    (t s : RelativeTerm Parameter) : s ∈ exposedThetaList m t ↔ s ∈ exposedTheta m t := by
  rw [← exposedThetaList_toFinset]
  exact List.mem_toFinset.symm

namespace ExposedThetaCodes

abbrev State := RelativeTerm Nat × List (RelativeTerm Nat)

def parameterState (_ : Nat) (p : Nat) : State := (.parameter p, [])

def sumState (a b : State) : State := (.sum a.1 b.1, a.2 ++ b.2)

def thetaState (m k : Nat) (a : State) : State :=
  let t := RelativeTerm.theta k a.1
  (t, cond (k == m) [t] (cond (decide (m < k)) a.2 []))

theorem parameterState_primrec : Primrec₂ parameterState :=
  ((parameter_primrec.comp Primrec.snd).pair (Primrec.const [])).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have ht : Primrec (fun p : State × State => RelativeTerm.sum p.1.1 p.2.1) :=
    sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hl : Primrec (fun p : State × State => p.1.2 ++ p.2.2) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  exact (ht.pair hl).to₂

theorem thetaState_primrec :
    Primrec (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × (Nat × State) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × (Nat × State) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : Nat × (Nat × State) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ht := theta_primrec.comp hk ha
  have he := Primrec.beq.comp hk Primrec.fst
  have hg := (Primrec.nat_lt.comp Primrec.fst hk).decide
  have hone := Primrec.list_cons.comp ht (Primrec.const [])
  exact ht.pair (he.cond hone (hg.cond hl (Primrec.const [])))

def state (m : Nat) (t : RelativeTerm Nat) : State :=
  ValueFold.term parameterState sumState thetaState m t

def stateCode (m c : Nat) : State :=
  ValueFold.code parameterState sumState thetaState (.parameter 0, []) m c

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState sumState thetaState (.parameter 0, [])
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (.parameter 0, [])
    parameterState_primrec sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (m : Nat) (t : RelativeTerm Nat) :
    stateCode m t.code = state m t :=
  ValueFold.code_term parameterState sumState thetaState (.parameter 0, []) m t

@[simp] theorem state_eq (m : Nat) (t : RelativeTerm Nat) :
    state m t = (t, exposedThetaList m t) := by
  induction t with
  | parameter p => rfl
  | sum a b iha ihb =>
    change sumState (state m a) (state m b) = _
    rw [iha, ihb]
    rfl
  | theta k a ih =>
    change thetaState m k (state m a) = _
    rw [ih]
    by_cases hkm : k = m <;> by_cases hmk : m < k <;>
      simp [thetaState, exposedThetaList, Bool.beq_eq_decide_eq, hkm, hmk]

end ExposedThetaCodes

theorem exposedThetaList_primrec :
    Primrec₂ (exposedThetaList (Parameter := Nat)) := by
  have h := Primrec.snd.comp₂ ExposedThetaCodes.state_primrec
  simpa only [ExposedThetaCodes.state_eq] using h

def exposedThetaCodeList (m c : Nat) : List Nat :=
  (ExposedThetaCodes.stateCode m c).2.map RelativeTerm.code

theorem exposedThetaCodeList_primrec : Primrec₂ exposedThetaCodeList := by
  have hl : Primrec (fun p : Nat × Nat => (ExposedThetaCodes.stateCode p.1 p.2).2) :=
    Primrec.snd.comp ExposedThetaCodes.stateCode_primrec
  exact (Primrec.list_map hl (RelativeTerm.code_primrec.comp Primrec.snd).to₂).to₂

@[simp] theorem exposedThetaCodeList_code (m : Nat) (t : RelativeTerm Nat) :
    exposedThetaCodeList m t.code = (exposedThetaList m t).map RelativeTerm.code := by
  simp only [exposedThetaCodeList, ExposedThetaCodes.stateCode_code, ExposedThetaCodes.state_eq]

theorem mem_exposedThetaCodeList_iff (m : Nat) (t : RelativeTerm Nat) (c : Nat) :
    c ∈ exposedThetaCodeList m t.code ↔
      ∃ s ∈ exposedTheta m t, s.code = c := by
  rw [exposedThetaCodeList_code, List.mem_map]
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, (mem_exposedThetaList_iff m t s).mp hs, he⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, (mem_exposedThetaList_iff m t s).mpr hs, he⟩

end Alexander313.Wilken.RelativeTerm
