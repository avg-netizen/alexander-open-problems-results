import Alexander313.Carlson.ComputableAmalgamation
import Alexander313.Carlson.PrimitiveAmalgamationCertificates

/-!
# An actual partial-recursive machine for terminating amalgamation search

The machine searches the same original decoder/verifier as `leastCode`.
Its behavior is specified on the pinned existing finite-family encoding;
on every family of pure patterns it halts at exactly the computed least code.
-/

namespace Alexander313.Carlson.Finite.PartialAmalgamationSearch

open AmalgamationCertificate PrimitiveAmalgamationCertificates

variable {n : ℕ}

def search (P : Fin n → RationalPresentation) : Part ℕ :=
  Nat.rfind (fun code => Part.some (checkCode P code))

theorem search_partrec : Partrec (search (n := n)) :=
  Partrec.rfind checkCode_primrec.to_comp.partrec₂

theorem search_eq_leastCode (P : Fin n → RationalPresentation)
    (hP : ∀ i, (P i).toStr.IsPattern) :
    search P = Part.some (ComputableAmalgamation.leastCode P hP) := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  refine ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    exact (ComputableAmalgamation.leastCode_check P hP).symm
  · intro m hm
    simp only [Part.mem_some_iff]
    have hn : checkCode P m ≠ true := Nat.find_min (AmalgamationCertificate.exists_code P hP) hm
    cases hb : checkCode P m with
    | false => rfl
    | true => exact (hn hb).elim

theorem search_program (n : ℕ) : ∃ machine : Nat.Partrec.Code,
    ∀ P : Fin n → RationalPresentation,
      machine.eval (familyCode P) = search P := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp (search_partrec (n := n))
  refine ⟨machine, fun P => ?_⟩
  rw [hm]
  change (Part.bind (Part.ofOption (@Encodable.decode (Fin n → RationalPresentation)
    Primcodable.finArrow.toEncodable (@Encodable.encode _ Primcodable.finArrow.toEncodable P)))
    (fun Q => (search Q).map Encodable.encode)) = search P
  rw [@Encodable.encodek _ Primcodable.finArrow.toEncodable P]
  simp only [Part.ofOption, Part.bind_some]
  exact Part.ext (fun _ => by simp)

/-- One machine halts on every pure-pattern family and returns the same
least accepted code as the executable total search, including the empty family. -/
theorem terminating_search_program (n : ℕ) : ∃ machine : Nat.Partrec.Code,
    ∀ (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern),
      machine.eval (familyCode P) = Part.some (ComputableAmalgamation.leastCode P hP) := by
  obtain ⟨machine, hm⟩ := search_program n
  exact ⟨machine, fun P hP => (hm P).trans (search_eq_leastCode P hP)⟩

end Alexander313.Carlson.Finite.PartialAmalgamationSearch
