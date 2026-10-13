import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFactorSupport

/-!
# Actual original source-one factor-removal branch of Definition3.20

The original RAW LOW positive non-M principal executes the real public
principal logarithm. Its finite MNF prefix and last factor return through
actual bounded source-zero lowering. The original input bounds derive
both return domains; generic MNF arithmetic derives the original source
interval and strict factor-count descent. The source-one non-M singleton
case is impossible. Later insertion branches remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Factor

open FactorSupport
open Alexander313.Wilken.MultiplicativeNormalForm
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

abbrev Output := Nat × Nat

def inputCheck (c : Nat) : Bool := SourceLocalization.RootAdapter.inputCheck c &&
  !SourceMultiplicativePrincipal.inputCheck c

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp SourceLocalization.RootAdapter.inputCheck_primrec
    (Primrec.not.comp SourceMultiplicativePrincipal.inputCheck_primrec)

theorem inputCheck_exact (c : Nat) : inputCheck c = true ↔
    lowCheckCode 0 c = true ∧ 1 ≤ interpretation 0 c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 c) ∧
        ¬IsMultiplicativePrincipal (interpretation 0 c) := by
  rw [inputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨ha, hm⟩
    have hs := (SourceLocalization.RootAdapter.inputCheck_exact c).mp ha
    refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
    intro hc
    have ht := (SourceMultiplicativePrincipal.inputCheck_exact c).mpr ⟨hs.1, hs.2.1, hc⟩
    simpa only [ht, Bool.not_true, Bool.false_eq_true] using hm
  · rintro ⟨hl, hb, hp, hm⟩
    refine ⟨(SourceLocalization.RootAdapter.inputCheck_exact c).mpr ⟨hl, hb, hp⟩, ?_⟩
    have hf : SourceMultiplicativePrincipal.inputCheck c = false := Bool.eq_false_of_not_eq_true
      (fun ht => hm ((SourceMultiplicativePrincipal.inputCheck_exact c).mp ht).2.2)
    simp only [hf, Bool.not_false]

theorem original_one_lt (c : Nat) (hc : inputCheck c = true) : 1 < interpretation 0 c := by
  have hs := (inputCheck_exact c).mp hc
  apply lt_of_le_of_ne hs.2.1
  intro he
  apply hs.2.2.2
  rw [← he]
  exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩

/-- At tau=1 every non-M caller is in the genuine factor branch;
the printed non-M singleton cutoff cannot hold. -/
theorem original_split_cutoff (c : Nat) (hc : inputCheck c = true) :
    (1 : Ordinal.{0}) ^ Ordinal.omega0 < interpretation 0 c := by
  simpa only [Ordinal.one_opow] using original_one_lt c hc

def publicCode (c : Nat) : Nat := Nat.pair 0 c

theorem publicCode_primrec : Primrec publicCode := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem publicCode_principal (c : Nat) (hc : inputCheck c = true) :
    Principal.unionPrincipalCheck (publicCode c) = true := by
  have hs := (inputCheck_exact c).mp hc
  apply (Principal.unionPrincipalCheck_exact _).mpr
  exact ⟨by simpa only [publicCode, unionCheck_pair] using hs.1,
    by simpa only [publicCode, unionInterpretation_pair] using Order.one_le_iff_pos.mp hs.2.1,
    by simpa only [publicCode, unionInterpretation_pair] using hs.2.2.1⟩

def execute (c : Nat) : Part Output := cond (inputCheck c)
  ((PrincipalLogarithm.logarithm (publicCode c)).map fun d => (prefixCode d, lastCode d)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (Partrec.map (PrincipalLogarithm.logarithm_partrec.comp publicCode_primrec.to_comp)
      ((prefixCode_primrec.comp Primrec.snd).pair
        (lastCode_primrec.comp Primrec.snd)).to_comp.to₂) Partrec.none

theorem execute_domain (c : Nat) : (execute c).Dom ↔ inputCheck c = true := by
  cases hc : inputCheck c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hd := (PrincipalLogarithm.logarithm_domain _).mpr (publicCode_principal c hc)
    rw [execute, hc, Bool.cond_true]
    change (PrincipalLogarithm.logarithm (publicCode c)).Dom ↔ true = true
    exact ⟨fun _ => rfl, fun _ => hd⟩

/-- Both finite returns and the exact printed source NF split are derived
from the unchanged original check-zero non-M principal guard. -/
theorem execute_spec (c : Nat) (out : Output) (ho : out ∈ execute c) :
    inputCheck c = true ∧ Theta.acceptedLowCode 0 out.1 = true ∧
      Theta.acceptedLowCode 0 out.2 = true ∧
      SourceLocalization.RootAdapter.inputCheck out.1 = true ∧
      1 ≤ interpretation 0 out.1 ∧ interpretation 0 out.1 < interpretation 0 c ∧
      IsMultiplicativePrincipal (interpretation 0 out.2) ∧ 1 < interpretation 0 out.2 ∧
      interpretation 0 c = interpretation 0 out.1 * interpretation 0 out.2 ∧
      interpretation 0 out.2 = lf (interpretation 0 c) ∧
      (canonicalMNF (interpretation 0 out.1)).length < (canonicalMNF (interpretation 0 c)).length := by
  have hc := (execute_domain c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hi := (inputCheck_exact c).mp hc
  have hpos := Order.one_le_iff_pos.mp hi.2.1
  have hbound : interpretation 0 c < finiteBase 1 := (lt_nextBase_iff_code 0 _).mpr ⟨c, hi.1, rfl⟩
  rw [execute, hc, Bool.cond_true] at ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hlog := PrincipalLogarithm.logarithm_value (publicCode c) d hd
  have hdcheck := Canonical.check_original hlog.2.2.2.1
  have hpow : Ordinal.omega0 ^ unionInterpretation d = interpretation 0 c := by
    simpa only [publicCode, unionInterpretation_pair] using hlog.2.2.2.2
  have hword : omegaFactors (unionInterpretation d) = canonicalMNF (interpretation 0 c) := by
    rw [← hpow, canonicalMNF_omegaPower]
  have hp := prefixPublicCode_spec d hdcheck
  have hl := lastPublicCode_spec d hdcheck
  rw [hword] at hp hl
  have hone : IsMultiplicativePrincipal (1 : Ordinal.{0}) :=
    ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
  have hs := MultiplicativeFactorRemoval.source_prefix_last_interval hone hpos hi.2.2.1
    hi.2.1 hi.2.2.2
  have hpbound : unionInterpretation (prefixPublicCode d) < finiteBase 1 := by
    rw [hp.2]
    exact hs.2.1.trans_lt hbound
  have hne : canonicalMNF (interpretation 0 c) ≠ [] := by
    intro he
    have hn := MultiplicativeFactorRemoval.nonmultiplicative_prefix_nonempty hpos hi.2.2.1 hi.2.2.2
    exact hn (by simp only [he, factorPrefix, List.reverse_nil, List.tail_nil])
  have hlastle : lf (interpretation 0 c) ≤ interpretation 0 c := by
    have hx := canonicalMNF_reduced (interpretation 0 c)
    have hle := MultiplicativeFactorRemoval.factorProduct_mem_le
      (canonicalMNF (interpretation 0 c)) (fun a ha => (hx.1.1 a ha).1)
      (lf (interpretation 0 c)) (lastFactor_mem _ hne)
    rwa [factorProduct_canonicalMNF hpos hi.2.2.1] at hle
  have hlbound : unionInterpretation (lastPublicCode d) < finiteBase 1 := by
    rw [hl.2]
    exact hlastle.trans_lt hbound
  have hpr := SourceZeta.Transport.returnCode_spec 0 _ hp.1 hpbound
  have hlr := SourceZeta.Transport.returnCode_spec 0 _ hl.1 hlbound
  have hpv : interpretation 0 (prefixCode d) = factorProduct (factorPrefix (canonicalMNF (interpretation 0 c))) :=
    hpr.2.trans hp.2
  have hlv : interpretation 0 (lastCode d) = lf (interpretation 0 c) := hlr.2.trans hl.2
  have hred := MultiplicativeFactorRemoval.factorPrefix_reduced _ (canonicalMNF_reduced (interpretation 0 c))
  have hprincipal := isMNF_product_principal hred.1
  have hcaller : SourceLocalization.RootAdapter.inputCheck (prefixCode d) = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact _).mpr
      ⟨((Theta.acceptedLowCode_iff 0 _).mp hpr.1).1, by rw [hpv]; exact hs.1,
        by rw [hpv]; exact hprincipal.2⟩
  refine ⟨hc, hpr.1, hlr.1, hcaller, ?_, ?_, ?_, ?_, ?_, hlv, ?_⟩
  · rw [hpv]; exact hs.1
  · rw [hpv]; exact hs.2.1
  · rw [hlv]; exact hs.2.2.1
  · rw [hlv]; exact hs.2.2.2.1
  · rw [hpv, hlv]; exact hs.2.2.2.2
  · rw [hpv]
    exact MultiplicativeFactorRemoval.source_prefix_factor_count_lt hpos hi.2.2.1 hi.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Factor
