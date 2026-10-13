import Alexander313.Wilken.HereditarySourceZeta
import Alexander313.Wilken.HereditaryBoundedLowering
import Alexander313.Wilken.HereditaryThetaEmbeddings

/-!
# Same-base zeta invariance and an executing original-level return

Actual collapse injection recovers argument value from the value of an
original literal theta-zero root. The source zeta formula therefore agrees
on different admitted spellings at the same public base. Canonical union
outputs agree literally; the raw normalizer's argument transport retains
the original raw formula. No support-set or normal-spelling uniqueness is
assumed.

The returned canonical union code is converted to a native code at the
original public level by the actual finite embedding or bounded lowering
algorithm. The proved zeta bound supplies every lowering caller condition.
The complete native graph uses an actual canonical round trip and a literal
conversion test. Finite conversion and graph tests are PR; zeta execution
remains partial recursive. Base one is included. No cross-base zeta
invariance or base-transformation theorem is asserted. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceZeta.Transport

open ThetaCourse

theorem normal_raw_input (r c : Nat) (hc : inputCheck r c = true) :
    rawInputCheck r c = true := by
  obtain ⟨a, rfl, ha, _⟩ := (inputCheck_exact r c).mp hc
  exact (rawInputCheck_exact r _).mpr ⟨a, rfl, ha⟩

/-- The same-base injection is applied to actual originally admitted
arguments with their derived theta caller sorts. -/
theorem argument_value_injective (r c v : Nat)
    (hc : rawInputCheck r c = true) (hv : rawInputCheck r v = true)
    (he : interpretation r c = interpretation r v) :
    interpretation r (argumentCode c) = interpretation r (argumentCode v) := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact r c).mp hc
  obtain ⟨b, rfl, hb⟩ := (rawInputCheck_exact r v).mp hv
  have haa := SourceFixedPoint.checked_theta_argument r 0 a ha
  have hbb := SourceFixedPoint.checked_theta_argument r 0 b hb
  let alpha := SourceFixedPoint.sourceOrdinal r 0 a haa
  let beta := SourceFixedPoint.sourceOrdinal r 0 b hbb
  have hsorta : alpha.val < omegaSequence (finiteBase r) 2 :=
    SourceFixedPoint.checked_theta_sort r 0 a ha
  have hsortb : beta.val < omegaSequence (finiteBase r) 2 :=
    SourceFixedPoint.checked_theta_sort r 0 b hb
  have hcollapse : globalCollapse (finiteBase r) 0 alpha.val =
      globalCollapse (finiteBase r) 0 beta.val := by
    simpa only [interpretation_code, denote, RelativeTerm.eval] using he
  have hab := (globalCollapse_eq_iff (finiteBase r) (finiteBase_pos r)
    0 alpha beta hsorta hsortb).mp hcollapse
  simpa only [argumentCode, Localization.argumentCode_theta, interpretation_code] using hab

theorem sourceValue_raw_invariant (r c v : Nat)
    (hc : rawInputCheck r c = true) (hv : rawInputCheck r v = true)
    (he : interpretation r c = interpretation r v) : sourceValue r c = sourceValue r v :=
  sourceValue_argument_congr r c v (argument_value_injective r c v hc hv he)

theorem sourceValue_invariant (r c v : Nat)
    (hc : inputCheck r c = true) (hv : inputCheck r v = true)
    (he : interpretation r c = interpretation r v) : sourceValue r c = sourceValue r v :=
  sourceValue_raw_invariant r c v (normal_raw_input r c hc) (normal_raw_input r v hv) he

theorem zeta_output_invariant (r c v q w : Nat)
    (hq : q ∈ zeta r c) (hw : w ∈ zeta r v)
    (he : interpretation r c = interpretation r v) : q = w := by
  have hs := zeta_value r c q hq
  have ht := zeta_value r v w hw
  exact Canonical.check_value_injective q w hs.2.1 ht.2.1
    (hs.2.2.trans ((sourceValue_invariant r c v hs.1 ht.1 he).trans ht.2.2.symm))

theorem rawZeta_output_invariant (r c v q w : Nat)
    (hq : q ∈ rawZeta r c) (hw : w ∈ rawZeta r v)
    (he : interpretation r c = interpretation r v) : q = w := by
  have hs := rawZeta_value r c q hq
  have ht := rawZeta_value r v w hw
  exact Canonical.check_value_injective q w hs.2.1 ht.2.1
    (hs.2.2.trans ((sourceValue_raw_invariant r c v hs.1 ht.1 he).trans ht.2.2.symm))

theorem raw_normal_output (r c q w : Nat) (hq : q ∈ rawZeta r c)
    (hw : w ∈ zeta r (Theta.Normalization.normalizeCode r c)) : q = w := by
  have hc := (rawZeta_value r c q hq).1
  have hm : q ∈ zeta r (Theta.Normalization.normalizeCode r c) := by
    simpa only [rawZeta, hc, Bool.cond_true] using hq
  exact Part.mem_unique hm hw

/-- This total finite kernel is meaningful on a canonical union code below
the requested level's endpoint. It executes embedding or genuine lowering. -/
def returnCode (r q : Nat) : Nat := cond (decide (q.unpair.1 ≤ r))
  (BaseArithmetic.embedCode (r - q.unpair.1) q.unpair.2)
  (BoundedLowering.lowerCode r q.unpair.1 q.unpair.2)

theorem returnCode_primrec : Primrec₂ returnCode := by
  have hr := Primrec.fst
  have hp := Primrec.unpair.comp Primrec.snd
  have hs := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  exact ((Primrec.nat_le.comp hs hr).decide.cond
    (BaseArithmetic.embedCode_primrec.comp (Primrec.nat_sub.comp hr hs) hc)
    (BoundedLowering.lowerCode_primrec.comp (hr.pair (hs.pair hc)))).to₂

theorem returnCode_spec (r q : Nat) (hq : Canonical.check q = true)
    (hb : unionInterpretation q < finiteBase (r + 1)) :
    Theta.acceptedLowCode r (returnCode r q) = true ∧
      interpretation r (returnCode r q) = unionInterpretation q := by
  have hlow : lowCheckCode q.unpair.1 q.unpair.2 = true := Canonical.check_original hq
  have hn := Canonical.check_normal hq
  by_cases hs : q.unpair.1 ≤ r
  · have hlevel : q.unpair.1 + (r - q.unpair.1) = r := by omega
    have he := Theta.embed_old_checked q.unpair.1 (r - q.unpair.1) q.unpair.2 hlow
    have hnormal := Theta.embed_normal q.unpair.1 (r - q.unpair.1) q.unpair.2 hn
    have hv := Theta.embed_original_value q.unpair.1 (r - q.unpair.1) q.unpair.2
    simp only [returnCode, hs, decide_true, Bool.cond_true]
    refine ⟨(Theta.acceptedLowCode_iff r _).mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [hlevel] using he
    · simpa only [hlevel, rawTree] using hnormal
    · simpa only [hlevel, unionInterpretation] using hv
  · have hc : checkCode q.unpair.1 q.unpair.2 = true :=
      (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hlow)).1
    have hg := (BoundedLowering.checkInput_exact r q.unpair.1 q.unpair.2).mpr
      ⟨Nat.le_of_lt (Nat.lt_of_not_ge hs), hc, hb⟩
    simpa only [returnCode, hs, decide_false, Bool.cond_false, unionInterpretation] using
      BoundedLowering.lowerCode_spec r q.unpair.1 q.unpair.2 hg

theorem raw_root_low (r c : Nat) (hc : rawInputCheck r c = true) : lowCheckCode r c = true := by
  obtain ⟨a, rfl, ha⟩ := (rawInputCheck_exact r c).mp hc
  simp only [lowCheckCode_code, lowCheck, ha, outerSort, Nat.zero_add,
    Nat.le_refl, decide_true, Bool.true_and]

theorem raw_root_bound (r c : Nat) (hc : rawInputCheck r c = true) :
    interpretation r c < finiteBase (r + 1) :=
  (lt_nextBase_iff_code r _).mpr ⟨c, raw_root_low r c hc, rfl⟩

theorem zeta_return_bound (r c q : Nat) (hq : q ∈ zeta r c) :
    unionInterpretation q < finiteBase (r + 1) :=
  (zeta_bound r c q hq).trans
    (raw_root_bound r c (normal_raw_input r c (zeta_value r c q hq).1))

theorem rawZeta_return_bound (r c q : Nat) (hq : q ∈ rawZeta r c) :
    unionInterpretation q < finiteBase (r + 1) :=
  (rawZeta_bound r c q hq).trans (raw_root_bound r c (rawZeta_value r c q hq).1)

def zetaAt (r c : Nat) : Part Nat := (zeta r c).map (returnCode r)

theorem zetaAt_partrec : Partrec₂ zetaAt :=
  (Partrec.map zeta_partrec
    (returnCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂).to₂

theorem zetaAt_domain (r c : Nat) : (zetaAt r c).Dom ↔ inputCheck r c = true :=
  zeta_domain r c

theorem zetaAt_spec (r c d : Nat) (hd : d ∈ zetaAt r c) :
    inputCheck r c = true ∧ Theta.acceptedLowCode r d = true ∧
      interpretation r d = sourceValue r c ∧ interpretation r d < interpretation r c := by
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
  have hs := zeta_value r c q hq
  have ht := returnCode_spec r q hs.2.1 (zeta_return_bound r c q hq)
  exact ⟨hs.1, ht.1, ht.2.trans hs.2.2, ht.2.trans_lt (zeta_bound r c q hq)⟩

def rawZetaAt (r c : Nat) : Part Nat := (rawZeta r c).map (returnCode r)

theorem rawZetaAt_partrec : Partrec₂ rawZetaAt :=
  (Partrec.map rawZeta_partrec
    (returnCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂).to₂

theorem rawZetaAt_domain (r c : Nat) : (rawZetaAt r c).Dom ↔ rawInputCheck r c = true :=
  rawZeta_domain r c

theorem rawZetaAt_spec (r c d : Nat) (hd : d ∈ rawZetaAt r c) :
    rawInputCheck r c = true ∧ Theta.acceptedLowCode r d = true ∧
      interpretation r d = sourceValue r c ∧ interpretation r d < interpretation r c := by
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
  have hs := rawZeta_value r c q hq
  have ht := returnCode_spec r q hs.2.1 (rawZeta_return_bound r c q hq)
  exact ⟨hs.1, ht.1, ht.2.trans hs.2.2, ht.2.trans_lt (rawZeta_bound r c q hq)⟩

theorem zetaAt_returns (r c : Nat) (hc : inputCheck r c = true) :
    ∃ d, d ∈ zetaAt r c := Part.dom_iff_mem.mp ((zetaAt_domain r c).mpr hc)

theorem rawZetaAt_returns (r c : Nat) (hc : rawInputCheck r c = true) :
    ∃ d, d ∈ rawZetaAt r c := Part.dom_iff_mem.mp ((rawZetaAt_domain r c).mpr hc)

theorem zetaAt_invariant (r c v d e : Nat) (hd : d ∈ zetaAt r c) (he : e ∈ zetaAt r v)
    (hv : interpretation r c = interpretation r v) : d = e := by
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp he
  rw [zeta_output_invariant r c v q w hq hw hv]

theorem rawZetaAt_invariant (r c v d e : Nat) (hd : d ∈ rawZetaAt r c) (he : e ∈ rawZetaAt r v)
    (hv : interpretation r c = interpretation r v) : d = e := by
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp he
  rw [rawZeta_output_invariant r c v q w hq hw hv]

theorem rawZetaAt_normal_output (r c d e : Nat) (hd : d ∈ rawZetaAt r c)
    (he : e ∈ zetaAt r (Theta.Normalization.normalizeCode r c)) : d = e := by
  obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp he
  rw [raw_normal_output r c q w hq hw]

/-- Canonicalizing the actual native output supplies a finite inverse
certificate; this is executed canonicalization, not a chosen representative. -/
def canonicalOutput (r d : Nat) : Nat := Canonical.canonicalize (Nat.pair r d)

theorem canonicalOutput_primrec : Primrec₂ canonicalOutput :=
  (Canonical.Effective.canonicalize_primrec.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).to₂

theorem canonicalOutput_spec (r d : Nat) (hd : Theta.acceptedLowCode r d = true) :
    Canonical.check (canonicalOutput r d) = true ∧
      unionInterpretation (canonicalOutput r d) = interpretation r d := by
  have hl := ((Theta.acceptedLowCode_iff r d).mp hd).1
  have hq : unionCheck (Nat.pair r d) = true := by simpa only [unionCheck_pair] using hl
  exact ⟨Canonical.canonicalize_check _ hq, by
    simpa only [canonicalOutput, unionInterpretation_pair] using Canonical.canonicalize_value _ hq⟩

theorem canonicalOutput_return (r q : Nat) (hq : Canonical.check q = true)
    (hb : unionInterpretation q < finiteBase (r + 1)) :
    canonicalOutput r (returnCode r q) = q := by
  have hs := returnCode_spec r q hq hb
  have ht := canonicalOutput_spec r _ hs.1
  exact Canonical.check_value_injective _ _ ht.1 hq (ht.2.trans hs.2)

def graph (r c d : Nat) : Bool := Theta.acceptedLowCode r d &&
  ((d == returnCode r (canonicalOutput r d)) && SourceZeta.graph r c (canonicalOutput r d))

theorem graph_primrec : Primrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have hq := canonicalOutput_primrec.comp hr hd
  exact Primrec.and.comp (Theta.Effective.acceptedLowCode_primrec.comp hr hd)
    (Primrec.and.comp (Primrec.beq.comp hd (returnCode_primrec.comp hr hq))
      (SourceZeta.graph_primrec.comp (hr.pair (hc.pair hq))))

theorem zetaAt_graph_iff (r c d : Nat) : d ∈ zetaAt r c ↔ graph r c d = true := by
  constructor
  · intro hd
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
    have hs := zeta_value r c q hq
    have hb := zeta_return_bound r c q hq
    have ht := returnCode_spec r q hs.2.1 hb
    have he := canonicalOutput_return r q hs.2.1 hb
    simp only [graph, ht.1, he, beq_self_eq_true, Bool.true_and]
    exact (zeta_graph_iff r c q).mp hq
  · intro hg
    obtain ⟨_, hd, hq⟩ := (by simpa only [graph, Bool.and_eq_true, beq_iff_eq] using hg :
      Theta.acceptedLowCode r d = true ∧ d = returnCode r (canonicalOutput r d) ∧
        SourceZeta.graph r c (canonicalOutput r d) = true)
    exact (Part.mem_map_iff (returnCode r)).mpr
      ⟨canonicalOutput r d, (zeta_graph_iff r c _).mpr hq, hd.symm⟩

def rawGraph (r c d : Nat) : Bool := Theta.acceptedLowCode r d &&
  ((d == returnCode r (canonicalOutput r d)) && SourceZeta.rawGraph r c (canonicalOutput r d))

theorem rawGraph_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawGraph p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have hq := canonicalOutput_primrec.comp hr hd
  exact Primrec.and.comp (Theta.Effective.acceptedLowCode_primrec.comp hr hd)
    (Primrec.and.comp (Primrec.beq.comp hd (returnCode_primrec.comp hr hq))
      (SourceZeta.rawGraph_primrec.comp (hr.pair (hc.pair hq))))

theorem rawZetaAt_graph_iff (r c d : Nat) : d ∈ rawZetaAt r c ↔ rawGraph r c d = true := by
  constructor
  · intro hd
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff (returnCode r)).mp hd
    have hs := rawZeta_value r c q hq
    have hb := rawZeta_return_bound r c q hq
    have ht := returnCode_spec r q hs.2.1 hb
    have he := canonicalOutput_return r q hs.2.1 hb
    simp only [rawGraph, ht.1, he, beq_self_eq_true, Bool.true_and]
    exact (rawZeta_graph_iff r c q).mp hq
  · intro hg
    obtain ⟨_, hd, hq⟩ := (by simpa only [rawGraph, Bool.and_eq_true, beq_iff_eq] using hg :
      Theta.acceptedLowCode r d = true ∧ d = returnCode r (canonicalOutput r d) ∧
        SourceZeta.rawGraph r c (canonicalOutput r d) = true)
    exact (Part.mem_map_iff (returnCode r)).mpr
      ⟨canonicalOutput r d, (rawZeta_graph_iff r c _).mpr hq, hd.symm⟩

theorem graph_spec (r c d : Nat) (hd : graph r c d = true) :
    inputCheck r c = true ∧ Theta.acceptedLowCode r d = true ∧
      interpretation r d = sourceValue r c ∧ interpretation r d < interpretation r c :=
  zetaAt_spec r c d ((zetaAt_graph_iff r c d).mpr hd)

theorem rawGraph_spec (r c d : Nat) (hd : rawGraph r c d = true) :
    rawInputCheck r c = true ∧ Theta.acceptedLowCode r d = true ∧
      interpretation r d = sourceValue r c ∧ interpretation r d < interpretation r c :=
  rawZetaAt_spec r c d ((rawZetaAt_graph_iff r c d).mpr hd)

theorem graph_unique (r c : Nat) (hc : inputCheck r c = true) : ∃! d, graph r c d = true := by
  obtain ⟨d, hd⟩ := zetaAt_returns r c hc
  exact ⟨d, (zetaAt_graph_iff r c d).mp hd,
    fun e he => Part.mem_unique ((zetaAt_graph_iff r c e).mpr he) hd⟩

theorem rawGraph_unique (r c : Nat) (hc : rawInputCheck r c = true) : ∃! d, rawGraph r c d = true := by
  obtain ⟨d, hd⟩ := rawZetaAt_returns r c hc
  exact ⟨d, (rawZetaAt_graph_iff r c d).mp hd,
    fun e he => Part.mem_unique ((rawZetaAt_graph_iff r c e).mpr he) hd⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceZeta.Transport
