import Alexander313.Carlson.FiniteReflection
import Alexander313.Carlson.FiniteLifting
import Alexander313.Carlson.GeneratingRules
import Mathlib.Tactic.DeriveEncodable

/-!
# Executable certificates for finite generating derivations

A certificate is an untrusted finite tree of Boolean relation tables, maps,
and rule tags. Its checker verifies every finite side condition of the five
generating rules. No validity proof or ordinal covering is stored in the tree.
Minimality in the lifting clause is checked by finite exhaustive search.

Soundness connects accepted certificates to `Str.GeneratingRule` and
`Str.ExactlyGenerates`; completeness reconstructs an accepted certificate
from any derivation on the fixed finite ambient order `Fin n`. Restricting
an accepted chain also certifies `Str.Generates`.

The certificates have executable natural-number encodings. The final
recognizers reject decoding failures and check the claimed endpoints, so
their existential acceptance characterizes the three semantic relations
on represented finite structures. These results concern a fixed finite
ambient order. They do not yet identify derivations on arbitrary rational
labels with derivations inside one finite ambient order, or construct the
fair sequence and its ordinal core.
-/

namespace Alexander313.Carlson

deriving instance Encodable for Lvl

namespace Finite

mutual

/-- Finite data for one of the five generating-rule clauses. Side conditions
are checked separately; malformed trees are representable and rejected. -/
inductive RuleCertificate (n : ℕ) where
  | arithmetic (P Q : PatternCode n)
  | downward (P : PatternCode n) (k : Lvl) (a b : Fin n)
      (X N : Finset (Fin n)) (g : Fin n → Fin n)
  | upward (rule : RuleCertificate n) (a b : Fin n)
      (N : Finset (Fin n)) (g : Fin n → Fin n)
  | finiteRestriction (chain : ChainCertificate n) (Q : PatternCode n) (a : Fin n)
  | lifting (rule : RuleCertificate n) (Q Qplus : PatternCode n)
      (h f : Fin n → Fin n)
  deriving Encodable

/-- A finite chain, with the common endpoint of each concatenation checked
explicitly rather than supplied as a proof in the data. -/
inductive ChainCertificate (n : ℕ) where
  | refl (P : PatternCode n)
  | tail (chain : ChainCertificate n) (rule : RuleCertificate n)
  deriving Encodable

end

variable {n : ℕ}

mutual

def RuleCertificate.source : RuleCertificate n → PatternCode n
  | .arithmetic P _ => P
  | .downward P _ _ _ _ _ _ => P
  | .upward d _ _ _ _ => d.source
  | .finiteRestriction c _ _ => c.source
  | .lifting _ Q _ _ _ => Q

def ChainCertificate.source : ChainCertificate n → PatternCode n
  | .refl P => P
  | .tail c _ => c.source

end

mutual

def RuleCertificate.target : RuleCertificate n → PatternCode n
  | .arithmetic _ Q => Q
  | .downward P k a b _ N g => P.downward k a b N g
  | .upward d a b N g => d.source.upward d.target a b N g
  | .finiteRestriction _ Q _ => Q
  | .lifting _ _ Qplus _ _ => Qplus

def ChainCertificate.target : ChainCertificate n → PatternCode n
  | .refl P => P
  | .tail _ d => d.target

end

mutual

/-- Total executable verification of a finite generating-rule tree. -/
def RuleCertificate.check : RuleCertificate n → Bool
  | .arithmetic P Q =>
      decide (P.toStr.IsPattern ∧ Str.IsSub P.toStr Q.toStr ∧ Q.U = P.U)
  | .downward P k a b X N g => decide (Str.DownData P.toStr k a b X N g)
  | .upward d a b N g =>
      d.check && decide (Str.UpData d.source.toStr d.target.toStr a b N g)
  | .finiteRestriction c Q a =>
      c.check && decide (Str.IsSub Q.toStr c.target.toStr ∧
        Str.ExtensionAt c.source.toStr Q.toStr a)
  | .lifting d Q Qplus h f =>
      d.check && decide (Str.ContinuousEmbedding d.source.toStr Q.toStr h ∧
        PatternLifting d.source.toStr d.target.toStr Q.toStr Qplus.toStr h f ∧
        PatternLifting.IsMinimal d.source.toStr d.target.toStr Q.toStr Qplus.toStr h)

/-- Total executable verification of a chain, including its joins. -/
def ChainCertificate.check : ChainCertificate n → Bool
  | .refl P => decide P.toStr.IsPattern
  | .tail c d => c.check && d.check && decide (c.target = d.source)

end

theorem RuleCertificate.sound (d : RuleCertificate n) :
    d.check = true → Str.GeneratingRule d.source.toStr d.target.toStr := by
  induction d using RuleCertificate.rec
    (motive_2 := fun c => c.check = true →
      Str.ExactlyGenerates c.source.toStr c.target.toStr)
  · intro h
    have h' := of_decide_eq_true h
    exact .arithmetic h'.1 h'.2.1 h'.2.2
  · rename_i P k a b X N g
    intro h
    have D : Str.DownData P.toStr k a b X N g := of_decide_eq_true h
    simpa only [source, target, PatternCode.toStr_downward] using
      (Str.GeneratingRule.downward D)
  · rename_i d a b N g ih
    intro h
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa only [source, target, PatternCode.toStr_upward] using
      (Str.GeneratingRule.upward (ih h.1) h.2)
  · rename_i c Q a ih
    intro h
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .finiteRestriction (ih h.1) h.2.1 h.2.2
  · rename_i d Q Qplus h f ih
    intro hc
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact .lifting (ih hc.1) hc.2.1 hc.2.2.1 hc.2.2.2
  · rename_i P h
    exact .refl (of_decide_eq_true h)
  · rename_i c d hc hd h
    simp only [ChainCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hjoin := congrArg PatternCode.toStr h.2
    have hstep := hd h.1.2
    rw [← hjoin] at hstep
    exact .tail (hc h.1.1) hstep

theorem ChainCertificate.sound (c : ChainCertificate n) :
    c.check = true → Str.ExactlyGenerates c.source.toStr c.target.toStr := by
  induction c using ChainCertificate.rec (motive_1 := fun _ => True)
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · intro h
    exact .refl (of_decide_eq_true h)
  · rename_i c d hc _
    intro h
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hjoin := congrArg PatternCode.toStr h.2
    have hstep := d.sound h.1.2
    rw [← hjoin] at hstep
    exact .tail (hc h.1.1) hstep

/-- Every semantic derivation on `Fin n` has a verified finite certificate.
Encoding arbitrary logical relations occurs only in this existence proof. -/
theorem RuleCertificate.complete {P Q : Str (Fin n)} (d : Str.GeneratingRule P Q) :
    ∃ c : RuleCertificate n, c.check = true ∧ c.source.toStr = P ∧ c.target.toStr = Q := by
  classical
  induction d using Str.GeneratingRule.rec
    (motive_2 := fun P Q _ => ∃ c : ChainCertificate n,
      c.check = true ∧ c.source.toStr = P ∧ c.target.toStr = Q)
  · rename_i P Q hP hsub hU
    refine ⟨.arithmetic (PatternCode.encode P) (PatternCode.encode Q), ?_, ?_, ?_⟩
    · simpa only [check, PatternCode.toStr_encode, PatternCode.encode_U,
        decide_eq_true_eq] using And.intro hP (And.intro hsub hU)
    · exact PatternCode.toStr_encode P
    · exact PatternCode.toStr_encode Q
  · rename_i P k a b X N g D
    refine ⟨.downward (PatternCode.encode P) k a b X N g, ?_, ?_, ?_⟩
    · simpa only [check, PatternCode.toStr_encode, decide_eq_true_eq] using D
    · exact PatternCode.toStr_encode P
    · simp only [target, PatternCode.toStr_downward, PatternCode.toStr_encode]
  · rename_i P Q a b N g d D ih
    obtain ⟨c, hc, hs, ht⟩ := ih
    refine ⟨.upward c a b N g, ?_, hs, ?_⟩
    · simp only [check, hc, hs, ht, Bool.true_and, decide_eq_true_eq]
      exact D
    · simp only [target, PatternCode.toStr_upward, hs, ht]
  · rename_i P Q R a c hsub hAt ih
    obtain ⟨c, hc, hs, ht⟩ := ih
    refine ⟨.finiteRestriction c (PatternCode.encode Q) a, ?_, hs, ?_⟩
    · simp only [check, hc, hs, ht, PatternCode.toStr_encode, Bool.true_and,
        decide_eq_true_eq]
      exact ⟨hsub, hAt⟩
    · exact PatternCode.toStr_encode Q
  · rename_i P Pplus Q Qplus h f d he L hM ih
    obtain ⟨c, hc, hs, ht⟩ := ih
    refine ⟨.lifting c (PatternCode.encode Q) (PatternCode.encode Qplus) h f, ?_, ?_, ?_⟩
    · simp only [check, hc, hs, ht, PatternCode.toStr_encode, Bool.true_and,
        decide_eq_true_eq]
      exact ⟨he, L, hM⟩
    · exact PatternCode.toStr_encode Q
    · exact PatternCode.toStr_encode Qplus
  · rename_i P hP
    refine ⟨.refl (PatternCode.encode P), ?_, ?_, ?_⟩
    · simpa only [ChainCertificate.check, PatternCode.toStr_encode,
        decide_eq_true_eq] using hP
    · exact PatternCode.toStr_encode P
    · exact PatternCode.toStr_encode P
  · rename_i P Q R c d ihc ihd
    obtain ⟨c, hc, hs, ht⟩ := ihc
    obtain ⟨d, hd, hs', ht'⟩ := ihd
    refine ⟨.tail c d, ?_, hs, ht'⟩
    simp only [ChainCertificate.check, hc, hd, Bool.true_and, decide_eq_true_eq]
    have h := congrArg PatternCode.encode (ht.trans hs'.symm)
    simpa only [PatternCode.encode_toStr] using h

theorem ChainCertificate.complete {P Q : Str (Fin n)} (d : Str.ExactlyGenerates P Q) :
    ∃ c : ChainCertificate n, c.check = true ∧ c.source.toStr = P ∧ c.target.toStr = Q := by
  classical
  induction d using Str.ExactlyGenerates.rec (motive_1 := fun _ _ _ => True)
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · rename_i P hP
    refine ⟨.refl (PatternCode.encode P), ?_, ?_, ?_⟩
    · simpa only [check, PatternCode.toStr_encode, decide_eq_true_eq] using hP
    · exact PatternCode.toStr_encode P
    · exact PatternCode.toStr_encode P
  · rename_i P Q R c d ih _
    obtain ⟨c, hc, hs, ht⟩ := ih
    obtain ⟨d, hd, hs', ht'⟩ := RuleCertificate.complete d
    refine ⟨.tail c d, ?_, hs, ht'⟩
    simp only [check, hc, hd, Bool.true_and, decide_eq_true_eq]
    have h := congrArg PatternCode.encode (ht.trans hs'.symm)
    simpa only [PatternCode.encode_toStr] using h

/-- A certificate for generation by restriction of a finite chain. -/
structure GenerationCertificate (n : ℕ) where
  chain : ChainCertificate n
  target : PatternCode n
  deriving Encodable

def GenerationCertificate.source (c : GenerationCertificate n) : PatternCode n := c.chain.source

def GenerationCertificate.check (c : GenerationCertificate n) : Bool :=
  c.chain.check && decide (Str.IsSub c.target.toStr c.chain.target.toStr ∧
    c.source.U ⊆ c.target.U)

theorem GenerationCertificate.sound (c : GenerationCertificate n) (h : c.check = true) :
    Str.Generates c.source.toStr c.target.toStr := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨c.chain.target.toStr, c.chain.sound h.1, h.2.1, h.2.2⟩

theorem GenerationCertificate.complete {P Q : Str (Fin n)} (d : Str.Generates P Q) :
    ∃ c : GenerationCertificate n,
      c.check = true ∧ c.source.toStr = P ∧ c.target.toStr = Q := by
  classical
  obtain ⟨R, chain, hsub, hU⟩ := d
  obtain ⟨c, hc, hs, ht⟩ := ChainCertificate.complete chain
  refine ⟨⟨c, PatternCode.encode Q⟩, ?_, hs, PatternCode.toStr_encode Q⟩
  simp only [check, hc, ht, PatternCode.toStr_encode, Bool.true_and, decide_eq_true_eq]
  refine ⟨hsub, ?_⟩
  change c.source.toStr.U ⊆ Q.U
  rwa [hs]

end Finite
end Alexander313.Carlson
