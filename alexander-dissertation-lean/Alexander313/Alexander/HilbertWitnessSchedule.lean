import Alexander313.Alexander.HilbertWitnessStages
import Alexander313.Alexander.HilbertWitnessLimit
import Alexander313.Alexander.HilbertHenkinTruth
import Alexander313.Alexander.NativeSyntaxCoding
import Alexander313.Alexander.NativeRelationCoding

/-!
# A literal dovetail schedule for the actual finite witness languages

The stage languages depend only on the original language, not on the witness
choices. Their function/relation alphabets are encoded explicitly. The native
formula-list encoding then enumerates actual unary matrices, with a closed
falsum matrix as the fallback for invalid codes.

At time `pair s k`, the schedule visits code k from language stage s. The first
unpair coordinate is always at most the current time, so the chosen matrix can
be lifted by actual successive constant-language inclusions. Every matrix from
every finite stage is visited. This is a constructed schedule rather than a
fairness assumption. Actual finite symbol support proves that every matrix
of the common limit language is covered. Each scheduled witness is admitted
by the constructed union, proving its full syntactic witness property.

The enumeration is used for a classical completeness construction; no claim
of primitive recursiveness of these generic language encoders is made.
-/

namespace Alexander313.FirstOrderCalculus.WitnessSchedule

universe u v w

open WitnessStages

def constantFunctionsEncode {L : FirstOrder.Language.{u, v}} {C : Type w} :
    (Σ n, (ConstantExtension.language L C).Functions n) →
      (Σ n, L.Functions n) ⊕ C
  | ⟨n, .inl f⟩ => .inl ⟨n, f⟩
  | ⟨_, .inr (.constant c)⟩ => .inr c

def constantFunctionsDecode {L : FirstOrder.Language.{u, v}} {C : Type w} :
    ((Σ n, L.Functions n) ⊕ C) →
      Option (Σ n, (ConstantExtension.language L C).Functions n)
  | .inl ⟨n, f⟩ => some ⟨n, .inl f⟩
  | .inr c => some ⟨0, .inr (.constant c)⟩

@[simp] theorem constantFunctionsDecode_encode
    {L : FirstOrder.Language.{u, v}} {C : Type w}
    (f : Σ n, (ConstantExtension.language L C).Functions n) :
    constantFunctionsDecode (constantFunctionsEncode f) = some f := by
  rcases f with ⟨n, f⟩
  cases f with
  | inl f => rfl
  | inr c => cases c; rfl

def constantFunctionsEncodable {L : FirstOrder.Language.{u, v}} {C : Type w}
    [Encodable (Σ n, L.Functions n)] [Encodable C] :
    Encodable (Σ n, (ConstantExtension.language L C).Functions n) :=
  Encodable.ofLeftInjection constantFunctionsEncode constantFunctionsDecode
    constantFunctionsDecode_encode

variable {L : FirstOrder.Language.{u, v}}

def stageFunctionsEncodable [Encodable (Σ n, L.Functions n)] :
    (s : Nat) → Encodable (Σ n, (stageLanguage L s).Functions n)
  | 0 => inferInstanceAs (Encodable (Σ n, L.Functions n))
  | s + 1 => by
    letI := stageFunctionsEncodable s
    exact constantFunctionsEncodable

def stageRelationsEncodable [Encodable (Σ n, L.Relations n)] :
    (s : Nat) → Encodable (Σ n, (stageLanguage L s).Relations n)
  | 0 => inferInstanceAs (Encodable (Σ n, L.Relations n))
  | s + 1 => stageRelationsEncodable s

def choiceLabel {K : FirstOrder.Language.{u, v}} (c : UnaryChoice K) :
    Nat × K.Formula Nat := (c.name, c.matrix)

noncomputable def choiceOfLabel {K : FirstOrder.Language.{u, v}}
    (p : Nat × K.Formula Nat) : Option (UnaryChoice K) := by
  classical
  exact if h : p.2.freeVarFinset ⊆ {p.1} then some ⟨p.1, p.2, h⟩ else none

@[simp] theorem choiceOfLabel_label {K : FirstOrder.Language.{u, v}}
    (c : UnaryChoice K) : choiceOfLabel (choiceLabel c) = some c := by
  classical
  cases c with
  | mk x φ h => simp [choiceOfLabel, choiceLabel, h]

noncomputable def choiceEncodable {K : FirstOrder.Language.{u, v}}
    [Encodable (Σ n, K.Functions n)] [Encodable (Σ n, K.Relations n)] :
    Encodable (UnaryChoice K) := by
  letI := NativeSyntaxCoding.formulaEncodable (L := K) (α := Nat)
  exact Encodable.ofLeftInjection choiceLabel choiceOfLabel choiceOfLabel_label

def fallback (K : FirstOrder.Language.{u, v}) : UnaryChoice K :=
  ⟨0, ⊥, by simp⟩

def successor {K : FirstOrder.Language.{u, v}} (c : UnaryChoice K) :
    UnaryChoice (ConstantExtension.language K Unit) :=
  ⟨c.name, ConstantExtension.embed c.matrix, by
    simpa only [ConstantExtension.embed, SymbolMap.formulaMap_freeVarFinset] using c.support⟩

@[simp] theorem successor_name {K : FirstOrder.Language.{u, v}}
    (c : UnaryChoice K) : (successor c).name = c.name := rfl

@[simp] theorem successor_matrix {K : FirstOrder.Language.{u, v}}
    (c : UnaryChoice K) : (successor c).matrix = ConstantExtension.embed c.matrix := rfl

def lift {s : Nat} (c : UnaryChoice (stageLanguage L s)) :
    (r : Nat) → UnaryChoice (stageLanguage L (s + r))
  | 0 => c
  | r + 1 => successor (lift c r)

@[simp] theorem lift_name {s : Nat} (c : UnaryChoice (stageLanguage L s))
    (r : Nat) : (lift c r).name = c.name := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

def liftTo {s : Nat} (c : UnaryChoice (stageLanguage L s))
    (t : Nat) (h : s ≤ t) : UnaryChoice (stageLanguage L t) := by
  have e : s + (t - s) = t := by omega
  exact e ▸ lift c (t - s)

theorem name_cast {s t : Nat} (e : s = t)
    (c : UnaryChoice (stageLanguage L s)) :
    (e ▸ c : UnaryChoice (stageLanguage L t)).name = c.name := by
  subst t
  rfl

theorem limit_matrix_cast {s t : Nat} (e : s = t)
    (c : UnaryChoice (stageLanguage L s)) :
    (WitnessLimit.toLimit t).formulaMap
        (e ▸ c : UnaryChoice (stageLanguage L t)).matrix =
      (WitnessLimit.toLimit s).formulaMap c.matrix := by
  subst t
  rfl

theorem lift_limit_matrix {s : Nat} (c : UnaryChoice (stageLanguage L s))
    (r : Nat) :
    (WitnessLimit.toLimit (s + r)).formulaMap (lift c r).matrix =
      (WitnessLimit.toLimit s).formulaMap c.matrix := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (WitnessLimit.toLimit ((s + r) + 1)).formulaMap
      (ConstantExtension.embed (C := Unit) (lift c r).matrix) = _
    rw [WitnessLimit.toLimit_succ_formulaMap_embed, ih]

@[simp] theorem liftTo_name {s : Nat} (c : UnaryChoice (stageLanguage L s))
    (t : Nat) (h : s ≤ t) : (liftTo c t h).name = c.name := by
  simp only [liftTo, name_cast, lift_name]

theorem liftTo_limit_matrix {s : Nat} (c : UnaryChoice (stageLanguage L s))
    (t : Nat) (h : s ≤ t) :
    (WitnessLimit.toLimit t).formulaMap (liftTo c t h).matrix =
      (WitnessLimit.toLimit s).formulaMap c.matrix := by
  simp only [liftTo, limit_matrix_cast, lift_limit_matrix]

section Enumeration

variable [Encodable (Σ n, L.Functions n)] [Encodable (Σ n, L.Relations n)]

noncomputable def stageChoiceEncodable (s : Nat) :
    Encodable (UnaryChoice (stageLanguage L s)) := by
  letI := stageFunctionsEncodable (L := L) s
  letI := stageRelationsEncodable (L := L) s
  exact choiceEncodable

noncomputable def choiceCode {s : Nat} (c : UnaryChoice (stageLanguage L s)) : Nat := by
  letI := stageChoiceEncodable (L := L) s
  exact Encodable.encode c

noncomputable def enumerate (s k : Nat) : UnaryChoice (stageLanguage L s) := by
  letI := stageChoiceEncodable (L := L) s
  exact (Encodable.decode k).getD (fallback _)

@[simp] theorem enumerate_code {s : Nat} (c : UnaryChoice (stageLanguage L s)) :
    enumerate s (choiceCode c) = c := by
  letI := stageChoiceEncodable (L := L) s
  simp [enumerate, choiceCode, Encodable.encodek]

noncomputable def choices (t : Nat) : UnaryChoice (stageLanguage L t) :=
  liftTo (enumerate t.unpair.1 t.unpair.2) t (Nat.unpair_left_le t)

noncomputable def visitTime {s : Nat} (c : UnaryChoice (stageLanguage L s)) : Nat :=
  Nat.pair s (choiceCode c)

theorem stage_le_visitTime {s : Nat} (c : UnaryChoice (stageLanguage L s)) :
    s ≤ visitTime c := by
  simpa only [visitTime, Nat.unpair_pair] using Nat.unpair_left_le (visitTime c)

theorem choices_visitTime {s : Nat} (c : UnaryChoice (stageLanguage L s)) :
    choices (visitTime c) = liftTo c (visitTime c) (stage_le_visitTime c) := by
  have he : (visitTime c).unpair = (s, choiceCode c) := Nat.unpair_pair s (choiceCode c)
  have hg (p : Nat × Nat) (hp : p.1 ≤ visitTime c) (he : p = (s, choiceCode c)) :
      liftTo (enumerate p.1 p.2) (visitTime c) hp =
        liftTo c (visitTime c) (stage_le_visitTime c) := by
    subst p
    simp only [enumerate_code]
  exact hg (visitTime c).unpair (Nat.unpair_left_le (visitTime c)) he

/-- Every actual finite-stage matrix appears after actual language inclusion.
    The support proof and stage bound are constructed, not an assumed schedule. -/
theorem covers {s : Nat} (c : UnaryChoice (stageLanguage L s)) :
    ∃ t, ∃ h : s ≤ t, choices t = liftTo c t h :=
  ⟨visitTime c, stage_le_visitTime c, choices_visitTime c⟩

/-- Actual finite symbol support, followed by the constructed dovetail,
    proves coverage of every unary matrix of the whole common language. -/
theorem covers_limit (c : UnaryChoice (WitnessLimit.language L)) :
    ∃ t, (choices (L := L) t).name = c.name ∧
      (WitnessLimit.toLimit t).formulaMap (choices (L := L) t).matrix = c.matrix := by
  obtain ⟨s, d, hname, hmatrix⟩ := WitnessLimit.unaryChoice_preimage c
  obtain ⟨t, hst, hc⟩ := covers d
  refine ⟨t, ?_, ?_⟩
  · rw [hc, liftTo_name, hname]
  · rw [hc, liftTo_limit_matrix, hmatrix]

/-- The actual dovetail and actual consistent witness-stage union provide
    every literal Henkin witness; no witness or fairness contract is supplied. -/
theorem theory_hasWitnesses (T : L.Theory) :
    HilbertHenkinTruth.HasWitnesses (WitnessLimit.theory T (choices (L := L))) := by
  intro x φ hφ
  obtain ⟨t, hname, hmatrix⟩ := covers_limit (⟨x, φ, hφ⟩ : UnaryChoice (WitnessLimit.language L))
  refine ⟨ConstantExtension.constant t, ?_⟩
  erw [WitnessLimit.closedTerm_embed_constant (L := L)]
  simpa only [hname, hmatrix] using
    WitnessLimit.witness_derivation T (choices (L := L)) t

end Enumeration

end Alexander313.FirstOrderCalculus.WitnessSchedule
