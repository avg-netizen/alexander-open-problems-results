import Alexander313.Wilken.SourceOneRootScalarCollapseSupport

/-!
# Complete executing relative scalar at the original source one

The exact domain is the genuine original high root and original admitted
Normal argument at its actual theta sort. No scalar branch or selected
endpoint is excluded. Every zero branch and positive suffix caller is
proved from original source0 syntax. No native base-one substitution.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar

open ThetaCourse

abbrev Query := Nat × (Nat × Nat)

def inputCheck (b k c : Nat) : Bool := rootCheck b &&
  (argumentCheck c && decide ((rawTree c).outerSort ≤ k + 2))

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2) := by
  have hk := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (argumentCheck_primrec.comp hc)
      ((Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp hc))
        (Primrec.nat_add.comp hk (Primrec.const 2))).decide))

/-- The complete original domain, without any selected return endpoint. -/
theorem inputCheck_exact (b k c : Nat) : inputCheck b k c = true ↔
    rootCheck b = true ∧ argumentCheck c = true ∧ (rawTree c).outerSort ≤ k + 2 := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def collapseCode (b k c : Nat) : Nat := cond (inputCheck b k c)
  (cond (decide (k = 0)) (zeroCode b c) (nodeCode k c)) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2) := by
  have hk := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact inputCheck_primrec.cond
    (((Primrec.eq.comp hk (Primrec.const 0)).decide).cond
      (zeroCode_primrec.comp Primrec.fst hc)
      (BoundedPublicReturn.nodeCode_primrec.comp hk hc)) (Primrec.const 0)

/-- Every genuine scalar caller executes a finite original source-one
accepted Normal code at the SAME relative-collapse value. -/
theorem collapseCode_spec (b k c : Nat) (hi : inputCheck b k c = true) :
    argumentCheck (collapseCode b k c) = true ∧
      interpretation 0 (collapseCode b k c) =
        globalCollapse (interpretation 0 b) k (interpretation 0 c) := by
  have h := (inputCheck_exact b k c).mp hi
  by_cases hk : k = 0
  · subst k
    have hs := zeroCode_spec b c h.1 h.2.1 (by simpa only [Nat.zero_add] using h.2.2)
    simpa only [collapseCode, hi, decide_true, Bool.cond_true] using And.intro hs.1 hs.2.2
  · have hs := positive_nodeCode_spec b k c h.1 (Nat.pos_of_ne_zero hk) h.2.1 h.2.2
    simpa only [collapseCode, hi, decide_eq_false hk, Bool.cond_true, Bool.cond_false] using hs

theorem collapseCode_zero_low (b c : Nat) (hi : inputCheck b 0 c = true) :
    lowCheckCode 0 (collapseCode b 0 c) = true := by
  have h := (inputCheck_exact b 0 c).mp hi
  have hs := zeroCode_spec b c h.1 h.2.1 (by simpa only [Nat.zero_add] using h.2.2)
  simpa only [collapseCode, hi, decide_true, Bool.cond_true] using hs.2.1

theorem collapseCode_sort (b k c : Nat) (hi : inputCheck b k c = true) :
    (rawTree (collapseCode b k c)).outerSort ≤ k + 1 := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨t, he, ht⟩ := (lowCheckCode_iff 0 _).mp (collapseCode_zero_low b c hi)
    have hs := of_decide_eq_true (Bool.and_eq_true.mp ht).2
    simpa only [← he, rawTree_code, Nat.zero_add] using hs
  · simp only [collapseCode, hi, decide_eq_false hk, Bool.cond_true, Bool.cond_false,
      nodeCode, BoundedPublicReturn.nodeCode, rawTree_code, outerSort, le_refl]

theorem collapseCode_rejected (b k c : Nat) (hi : inputCheck b k c = false) :
    collapseCode b k c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

def execute (b k c : Nat) : Part Nat := cond (inputCheck b k c) (Part.some (collapseCode b k c)) Part.none

theorem execute_partrec : Partrec (fun p : Query => execute p.1 p.2.1 p.2.2) :=
  Partrec.cond inputCheck_primrec.to_comp collapseCode_primrec.to_comp.partrec Partrec.none

theorem execute_dom (b k c : Nat) : (execute b k c).Dom ↔ inputCheck b k c = true := by
  cases hi : inputCheck b k c <;> simp [execute, hi]

theorem execute_graph (b k c out : Nat) : out ∈ execute b k c ↔
    inputCheck b k c = true ∧ out = collapseCode b k c := by
  cases hi : inputCheck b k c <;> simp [execute, hi]

theorem execute_spec (b k c out : Nat) (ho : out ∈ execute b k c) :
    argumentCheck out = true ∧ interpretation 0 out =
      globalCollapse (interpretation 0 b) k (interpretation 0 c) := by
  obtain ⟨hi, rfl⟩ := (execute_graph b k c out).mp ho
  exact collapseCode_spec b k c hi

def graphBool (b k c out : Nat) : Bool := inputCheck b k c && (out == collapseCode b k c)

theorem graphBool_primrec : Primrec
    (fun p : Query × Nat => graphBool p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (collapseCode_primrec.comp Primrec.fst))

theorem graphBool_exact (b k c out : Nat) : graphBool b k c out = true ↔ out ∈ execute b k c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar
