import Alexander313.SourceColumns

/-! # An actual empty numerical column

The machine searches a constantly false primitive-recursive predicate. Its
domain is empty, and its literal encoded index has no W instances. This is
used to verify mechanicalness when the recorded outer source head is a ghost.
No arithmetic truth or program-domain contract is assumed. Uncompiled.
-/

namespace Alexander313.EmptyColumn

def evaluation (_ : Nat) : Part Nat :=
  Nat.rfind (fun _ : Nat => Part.some false)

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind (Primrec.const false : Primrec (fun _ : Nat × Nat => false)).to_comp.partrec.to₂

theorem evaluation_no_domain (n : Nat) : ¬ (evaluation n).Dom := by
  simp [evaluation, Nat.rfind_dom]

theorem program_exists : ∃ p : Program, ∀ n, ¬ p.domain n := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun n => ?_⟩
  simpa only [Program.domain, hp] using evaluation_no_domain n

noncomputable def program : Program := Classical.choose program_exists

theorem program_no_domain (n : Nat) : ¬ program.domain n :=
  Classical.choose_spec program_exists n

noncomputable def index : Nat := Encodable.encode program

theorem not_W (n : Nat) : ¬ W index n := by
  have hdecode : Nat.Partrec.Code.ofNatCode index = program :=
    Denumerable.ofNat_encode program
  rw [W, hdecode]
  exact program_no_domain n

end Alexander313.EmptyColumn
