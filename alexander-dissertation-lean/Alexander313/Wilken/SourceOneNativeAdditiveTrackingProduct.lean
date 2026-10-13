import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFactor
import Alexander313.Wilken.HereditaryMultiplication

/-!
# Actual original source-one principal-product replacement

The unchanged original source-zero codes execute the real public ordinal
multiplication procedure. Actual multiplicative closure of finiteBase1
derives the original return bound, so genuine source-zero lowering returns
Normal LOW syntax for the product. The printed small replacement is that
literal singleton. No Native base-one checker, assigned product or supplied
return bound is used. Raised replacements, covering fidelity and the full
insertion assignment remain separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Product

open MultiplicativePrincipalArithmetic

theorem original_boundary_mul_closed : Ordinal.IsPrincipal (· * ·) (finiteBase 1) := by
  have he := finiteBase_succ_omegaPower_eq_self 0
  simpa only [he] using Ordinal.isPrincipal_mul_omega0_opow_opow (finiteBase 1)

def execute (head factor : Nat) : Part Nat :=
  (Multiplication.multiply (Factor.publicCode head) (Factor.publicCode factor)).map
    (SourceZeta.Transport.returnCode 0)

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.map
    (Multiplication.multiply_partrec.comp
      (Factor.publicCode_primrec.comp Primrec.fst).to_comp
      (Factor.publicCode_primrec.comp Primrec.snd).to_comp)
    (SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0) Primrec.snd).to_comp.to₂).to₂

theorem execute_domain (head factor : Nat) : (execute head factor).Dom ↔
    lowCheckCode 0 head = true ∧ lowCheckCode 0 factor = true := by
  change (Multiplication.multiply (Factor.publicCode head) (Factor.publicCode factor)).Dom ↔ _
  simpa only [Factor.publicCode, unionCheck_pair] using
    Multiplication.multiply_domain (Factor.publicCode head) (Factor.publicCode factor)

theorem execute_returns (head factor : Nat)
    (hh : lowCheckCode 0 head = true) (hf : lowCheckCode 0 factor = true) :
    ∃ out, out ∈ execute head factor :=
  Part.dom_iff_mem.mp ((execute_domain head factor).mpr ⟨hh, hf⟩)

/-- Both input bounds and the original return caller are derived from
the actual original LOW guards; the product is the executed ordinal one. -/
theorem execute_spec (head factor out : Nat) (ho : out ∈ execute head factor) :
    lowCheckCode 0 head = true ∧ lowCheckCode 0 factor = true ∧
      Theta.acceptedLowCode 0 out = true ∧
      interpretation 0 out = interpretation 0 head * interpretation 0 factor := by
  have hi := (execute_domain head factor).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  obtain ⟨public, hp, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := Multiplication.multiply_value _ _ public hp
  have hv : unionInterpretation public = interpretation 0 head * interpretation 0 factor := by
    simpa only [Factor.publicCode, unionInterpretation_pair] using hs.2.2.2
  have hh : interpretation 0 head < finiteBase 1 :=
    (lt_nextBase_iff_code 0 _).mpr ⟨head, hi.1, rfl⟩
  have hf : interpretation 0 factor < finiteBase 1 :=
    (lt_nextBase_iff_code 0 _).mpr ⟨factor, hi.2, rfl⟩
  have hb : unionInterpretation public < finiteBase 1 := by
    rw [hv]
    exact original_boundary_mul_closed hh hf
  have hr := SourceZeta.Transport.returnCode_spec 0 public hs.2.2.1 hb
  exact ⟨hi.1, hi.2, hr.1, hr.2.trans hv⟩

def smallReplacement (head factor : Nat) : Part (List Nat) :=
  (execute head factor).map fun d => [d]

theorem smallReplacement_partrec : Partrec₂ smallReplacement :=
  (Partrec.map execute_partrec
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to_comp.to₂).to₂

theorem smallReplacement_returns (head factor : Nat)
    (hh : lowCheckCode 0 head = true) (hf : lowCheckCode 0 factor = true) :
    ∃ word, word ∈ smallReplacement head factor := by
  obtain ⟨out, ho⟩ := execute_returns head factor hh hf
  exact ⟨[out], Part.mem_map _ ho⟩

/-- Every actual small replacement is the original-source singleton
whose value is the literal product of the original written inputs. -/
theorem smallReplacement_spec (head factor : Nat) (word : List Nat)
    (hw : word ∈ smallReplacement head factor) :
    ∃ d, word = [d] ∧ Theta.acceptedLowCode 0 d = true ∧
      interpretation 0 d = interpretation 0 head * interpretation 0 factor := by
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hs := execute_spec head factor d hd
  exact ⟨d, rfl, hs.2.2.1, hs.2.2.2⟩

/-- The genuine original positive head and last-factor M>1 derive the
positive additive-principal caller for the singleton product itself. -/
theorem smallReplacement_principal (head factor : Nat) (word : List Nat)
    (hw : word ∈ smallReplacement head factor)
    (hh : 0 < interpretation 0 head)
    (hf : IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : 1 < interpretation 0 factor) :
    ∃ d, word = [d] ∧ SourceLocalization.RootAdapter.inputCheck d = true ∧
      interpretation 0 d = interpretation 0 head * interpretation 0 factor := by
  obtain ⟨d, he, hd, hv⟩ := smallReplacement_spec head factor word hw
  have hp := Ordinal.isPrincipal_add_mul_of_isPrincipal_add (interpretation 0 head)
    (ne_of_gt hb) hf.2.1
  have hle : 1 ≤ interpretation 0 d := by
    rw [hv]
    exact hb.le.trans (Ordinal.le_mul_right (interpretation 0 factor) hh)
  exact ⟨d, he, (SourceLocalization.RootAdapter.inputCheck_exact d).mpr
    ⟨((Theta.acceptedLowCode_iff 0 d).mp hd).1, hle, by rw [hv]; exact hp⟩, hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Product
