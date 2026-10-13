import Alexander313.Wilken.HereditaryPublicMtsCoveringSupport

/-!
# Actual localization supplies the least-table covering premises

Marked public values have the independently computed native FIRST below
the original public mu. Every real localization prefix derives an eligible
earlier root or entry from the actual native covered table. A passing
earlier entry has the same FIRST after its genuine OWN-context mu column
is established. Thus the chronological least table covers every marked
row; no reachability, covering or predecessor is supplied. The separate
outside-cut reach barrier and whole alpha-infinity domain remain open.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Covering

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open FirstSupport
open CoveringSupport (Covering)

def Marked (gamma code : Nat) : Prop :=
  ∃ current : Nat, SourceLocalization.Node gamma current ∧
    UniformPublicReturn.publicCode gamma current = code ∧
      firstValue gamma current ≤ SkPublicRecurrence.muValue gamma

theorem marked_first (gamma current : Nat) (hn : SourceLocalization.Node gamma current)
    (hm : Marked gamma (UniformPublicReturn.publicCode gamma current)) :
    firstValue gamma current ≤ SkPublicRecurrence.muValue gamma := by
  obtain ⟨other, ho, he, hb⟩ := hm
  have hv : interpretation gamma other = interpretation gamma current :=
    (node_public_spec gamma other ho).2.symm.trans
      ((congrArg unionInterpretation he).trans (node_public_spec gamma current hn).2)
  rw [← firstValue_eq_of_value gamma other current
    ((SourceLocalization.inputCheck_exact gamma other).mpr ho)
    ((SourceLocalization.inputCheck_exact gamma current).mpr hn) hv]
  exact hb

theorem base_public (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    UniformPublicReturn.publicCode gamma (SourceLocalization.baseRaw gamma) = gamma := by
  have hc := node_public_spec gamma (SourceLocalization.baseRaw gamma)
    (SourceLocalization.baseRaw_node gamma (gamma_baseCheck gamma beta hi))
  have hg := ((MuPublicDictionary.Support.inputCheck_image gamma).mp
    ((inputCheck_exact gamma beta).mp hi).1).1
  exact Canonical.check_value_injective _ _ hc.1 hg
    (hc.2.trans (SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi)))

private theorem endpoint_append_singleton (xs : List Nat) (d : Nat) :
    SourceLocalization.endpoint (xs ++ [d]) = d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => exact ih

/-- A real tail node strictly below the actual endpoint lies in the
proper prefix, so its original HIGH guard is a conclusion. -/
theorem tail_high (gamma root current : Nat)
    (hi : SourceLocalization.inputCheck gamma root = true)
    (hc : current ∈ (SourceLocalization.nativePath gamma root).tail)
    (hlt : interpretation gamma current < interpretation gamma root) :
    Mu.inputCheck gamma current = true := by
  obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head gamma root
  have hm : current ∈ tail := by simpa only [ht, List.tail_cons] using hc
  have hn : tail ≠ [] := by intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨last, hs, hrev⟩ := FinePredecessor.stripLast_split tail hn
  have he : interpretation gamma last = interpretation gamma root := by
    have hv := SourceLocalization.nativePath_end gamma root hi
    have hp : SourceLocalization.nativePath gamma root =
        (SourceLocalization.baseRaw gamma :: FinePredecessor.stripLast tail) ++ [last] := by
      exact ht.trans (congrArg (List.cons (SourceLocalization.baseRaw gamma)) hs)
    simpa only [hp, endpoint_append_singleton] using hv
  have hproper : current ∈ FinePredecessor.stripLast tail := by
    rw [hs] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hm
    · have hc : current = last := List.mem_singleton.mp hm
      exact False.elim (hlt.ne ((congrArg (interpretation gamma) hc).trans he))
  exact (SourceLocalization.Properties.nativePath_proper_prefix_spec gamma root hi current
    (by simpa only [ht, List.tail_cons] using hproper)).1

theorem tail_strict_base (gamma beta d current : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hc : current ∈ (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail) :
    unionInterpretation gamma < interpretation gamma current := by
  obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
  have hp := SourceLocalization.nativePath_source gamma _ (nativeRoot_spec gamma beta d hi hd).1
  rw [ht] at hp
  have hm : current ∈ tail := by simpa only [ht, List.tail_cons] using hc
  have hv := SourceLocalization.sourcePath_head_lt_tail hp current hm
  simpa only [SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi)] using hv

theorem earlier_in_prefix (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (before : List Nat) (current : Nat) (after : List Nat)
    (hs : (localization gamma d).tail = before ++ current :: after)
    (hm : Marked gamma current) :
    ∃ a ∈ gamma :: before, PublicTrackingSequences.adjacencyCheck a current = true := by
  have hmap : ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
      (UniformPublicReturn.publicCode gamma) = before ++ current :: after := by
    simpa only [localization, List.map_tail] using hs
  obtain ⟨nativeBefore, rest, htail, hbefore, hrest⟩ := List.map_eq_append_iff.mp hmap
  obtain ⟨nativeCurrent, nativeAfter, hrest', hcurrent, hafter⟩ := List.map_eq_cons_iff.mp hrest
  have htail' : (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail =
      nativeBefore ++ nativeCurrent :: nativeAfter := by rw [htail, hrest']
  have hmem : nativeCurrent ∈ (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail := by
    rw [htail']
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hnode := SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1
    nativeCurrent (List.mem_of_mem_tail hmem)
  have hmarked : Marked gamma (UniformPublicReturn.publicCode gamma nativeCurrent) :=
    hcurrent.symm ▸ hm
  have hcut := (localization_bounded gamma beta d hi hd nativeCurrent
    (List.mem_of_mem_tail hmem)).trans_lt ((inputCheck_exact gamma beta).mp hi).2.2.2.2.2
  obtain ⟨a, ha, hedge⟩ := earlier_eligible gamma nativeCurrent
    ((inputCheck_exact gamma beta).mp hi).1 hnode
    (tail_strict_base gamma beta d nativeCurrent hi hd hmem) hcut
    (marked_first gamma nativeCurrent hnode hmarked)
  have hedge' : PublicTrackingSequences.adjacencyCheck a current = true := by
    simpa only [hcurrent] using hedge
  rcases ha with rfl | ⟨previous, hp, ha, hfirst⟩
  · exact ⟨gamma, List.mem_cons_self, hedge'⟩
  · obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
    have hfull : SourceLocalization.nativePath gamma (nativeRoot gamma d) =
        (SourceLocalization.baseRaw gamma :: nativeBefore) ++ nativeCurrent :: nativeAfter := by
      have htailEq : tail = nativeBefore ++ nativeCurrent :: nativeAfter := by
        simpa only [ht, List.tail_cons] using htail'
      simp only [ht, htailEq, List.cons_append]
    have hprefix := Localization.publicPath_prefix gamma (nativeRoot gamma d)
      (nativeRoot_spec gamma beta d hi hd).1
      (SourceLocalization.baseRaw gamma :: nativeBefore) nativeCurrent nativeAfter hfull
    have hpublicPath : Localization.publicPath gamma nativeCurrent = gamma :: (before ++ [current]) := by
      simpa only [List.cons_append, List.map_cons, List.map_append, List.map_singleton,
        base_public gamma beta hi, hbefore, hcurrent] using hprefix.symm
    have hpTail : previous ∈ (SourceLocalization.nativePath gamma nativeCurrent).tail :=
      FinePredecessor.stripLast_mem _ _ hp
    have hpublicMem : UniformPublicReturn.publicCode gamma previous ∈ before ++ [current] := by
      have hx : UniformPublicReturn.publicCode gamma previous ∈
          (Localization.publicPath gamma nativeCurrent).tail := by
        rw [Localization.publicPath, ← List.map_tail]
        exact List.mem_map.mpr ⟨previous, hpTail, rfl⟩
      simpa only [hpublicPath, List.tail_cons] using hx
    have hbeforeMem : UniformPublicReturn.publicCode gamma previous ∈ before := by
      rcases List.mem_append.mp hpublicMem with hx | hx
      · exact hx
      · have he := List.mem_singleton.mp hx
        have hpnode := SourceLocalization.nativePath_nodes gamma nativeCurrent
          ((SourceLocalization.inputCheck_exact gamma nativeCurrent).mpr hnode)
          previous (List.mem_of_mem_tail hpTail)
        have hv : interpretation gamma previous = interpretation gamma nativeCurrent :=
          (node_public_spec gamma previous hpnode).2.symm.trans
            ((congrArg unionInterpretation he).trans
              ((congrArg unionInterpretation hcurrent).symm.trans (node_public_spec gamma nativeCurrent hnode).2))
        exact False.elim ((SourceAdditiveTracking.ProperPrefix.properPrefix_lt_root gamma nativeCurrent
          ((SourceLocalization.inputCheck_exact gamma nativeCurrent).mpr hnode) previous hp).ne hv)
    exact ⟨a, List.mem_cons.mpr (Or.inr (ha.symm ▸ hbeforeMem)), hedge'⟩

theorem passing_predecessor_marked (gamma beta d a current : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ha : a ∈ gamma :: (localization gamma d).tail)
    (hc : current ∈ (localization gamma d).tail)
    (hm : Marked gamma current)
    (hedge : PublicTrackingSequences.adjacencyCheck a current = true) :
    a = gamma ∨ Marked gamma a := by
  rcases List.mem_cons.mp ha with ha | ha
  · exact Or.inl ha
  · have ha' : a ∈ ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
        (UniformPublicReturn.publicCode gamma) := by simpa only [localization, List.map_tail] using ha
    have hc' : current ∈ ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
        (UniformPublicReturn.publicCode gamma) := by simpa only [localization, List.map_tail] using hc
    obtain ⟨previous, hp, hpa⟩ := List.mem_map.mp ha'
    obtain ⟨next, hn, hnc⟩ := List.mem_map.mp hc'
    have hinput := (nativeRoot_spec gamma beta d hi hd).1
    have hpnode := SourceLocalization.nativePath_nodes gamma _ hinput previous (List.mem_of_mem_tail hp)
    have hnnode := SourceLocalization.nativePath_nodes gamma _ hinput next (List.mem_of_mem_tail hn)
    have hs := (Support.eligible_exact a current).mp hedge
    have hstrict : interpretation gamma previous < interpretation gamma next := by
      rw [← (node_public_spec gamma previous hpnode).2, ← (node_public_spec gamma next hnnode).2,
        hpa, hnc]
      exact hs.2.2.1
    have hbound := localization_bounded gamma beta d hi hd next (List.mem_of_mem_tail hn)
    have hhigh := tail_high gamma (nativeRoot gamma d) previous hinput hp
      ((hstrict.trans_le hbound).trans_eq (nativeRoot_spec gamma beta d hi hd).2.symm)
    have hpCut := (localization_bounded gamma beta d hi hd previous
      (List.mem_of_mem_tail hp)).trans_lt ((inputCheck_exact gamma beta).mp hi).2.2.2.2.2
    have he := public_edge_first_eq gamma previous next ((inputCheck_exact gamma beta).mp hi).1
      hhigh hnnode hpCut (by simpa only [hpa, hnc] using hedge)
    have hb := marked_first gamma next hnnode (hnc.symm ▸ hm)
    exact Or.inr ⟨previous, hpnode, hpa, he.le.trans hb⟩

/-- Every marked row of the ACTUAL executing localization table is a
genuine covering. All pure table premises have been proved from source. -/
theorem localization_rows_covering (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ∀ e ∈ Support.table gamma (localization gamma d).tail,
      e.1 = gamma ∨ Marked gamma e.1 → Covering gamma e.1 e.2 := by
  apply CoveringSupport.table_covering gamma (localization gamma d).tail (Marked gamma)
    ((inputCheck_exact gamma beta).mp hi).1
  · intro c hc he
    have hm : c ∈ ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
        (UniformPublicReturn.publicCode gamma) := by simpa only [localization, List.map_tail] using hc
    obtain ⟨current, hm, hp⟩ := List.mem_map.mp hm
    have hn := SourceLocalization.nativePath_nodes gamma _ (nativeRoot_spec gamma beta d hi hd).1
      current (List.mem_of_mem_tail hm)
    have hv : interpretation gamma current = unionInterpretation gamma :=
      (node_public_spec gamma current hn).2.symm.trans (congrArg unionInterpretation (hp.trans he))
    exact (tail_strict_base gamma beta d current hi hd hm).ne hv.symm
  · exact earlier_in_prefix gamma beta d hi hd
  · exact passing_predecessor_marked gamma beta d hi hd

/-- The real last localization entry has the original target VALUE. Its
canonical public return is therefore the original target code, even when
the selected native spelling differs from the parsed native root. -/
theorem localization_tail_last (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    ∃ before : List Nat, (localization gamma d).tail = before ++ [beta] := by
  obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
  have hr := (nativeRoot_spec gamma beta d hi hd).1
  have hn : tail ≠ [] := by
    intro he
    have hv := SourceLocalization.nativePath_end gamma (nativeRoot gamma d) hr
    have heq : unionInterpretation gamma = unionInterpretation beta := by
      simpa only [ht, he, SourceLocalization.endpoint,
        SourceLocalization.baseRaw_value gamma (gamma_baseCheck gamma beta hi),
        (nativeRoot_spec gamma beta d hi hd).2] using hv
    exact hlt.ne heq
  obtain ⟨last, hs, hrev⟩ := FinePredecessor.stripLast_split tail hn
  have hp : SourceLocalization.nativePath gamma (nativeRoot gamma d) =
      (SourceLocalization.baseRaw gamma :: FinePredecessor.stripLast tail) ++ [last] := by
    exact ht.trans (congrArg (List.cons (SourceLocalization.baseRaw gamma)) hs)
  have hl : last ∈ SourceLocalization.nativePath gamma (nativeRoot gamma d) := by
    rw [hp]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hlast := node_public_spec gamma last (SourceLocalization.nativePath_nodes gamma _ hr last hl)
  have hv : interpretation gamma last = unionInterpretation beta := by
    have hv := SourceLocalization.nativePath_end gamma (nativeRoot gamma d) hr
    have hv' : interpretation gamma last = interpretation gamma (nativeRoot gamma d) := by
      simpa only [hp, endpoint_append_singleton] using hv
    exact hv'.trans (nativeRoot_spec gamma beta d hi hd).2
  have hcode : UniformPublicReturn.publicCode gamma last = beta :=
    Canonical.check_value_injective _ _ hlast.1 ((inputCheck_exact gamma beta).mp hi).2.1
      (hlast.2.trans hv)
  refine ⟨(FinePredecessor.stripLast tail).map (UniformPublicReturn.publicCode gamma), ?_⟩
  rw [localization, hp, List.map_append, List.map_singleton, List.map_cons,
    List.tail_cons, hcode]

/-- On the actual FIRST cut, the independently executed least table
produces a genuine covering to its original canonical target. -/
theorem search_word_covering (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hfirst : firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma) :
    Covering gamma beta (Support.word gamma (localization gamma d).tail) := by
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp
    (nativeRoot_spec gamma beta d hi hd).1
  have hp := node_public_spec gamma (nativeRoot gamma d) hn
  have hcode : UniformPublicReturn.publicCode gamma (nativeRoot gamma d) = beta :=
    Canonical.check_value_injective _ _ hp.1 ((inputCheck_exact gamma beta).mp hi).2.1
      (hp.2.trans (nativeRoot_spec gamma beta d hi hd).2)
  have hm : Marked gamma beta := ⟨nativeRoot gamma d, hn, hcode, hfirst⟩
  obtain ⟨before, hlast⟩ := localization_tail_last gamma beta d hi hd hlt
  have hrow : (beta, Support.word gamma (localization gamma d).tail) ∈
      Support.table gamma (localization gamma d).tail := by
    rw [hlast, Support.table_append_singleton, Support.word_append]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  exact localization_rows_covering gamma beta d hi hd _ hrow (Or.inr hm)

/-- Actual execution inherits the covering proved for any actual search
whose native FIRST satisfies the cut. Search output equality is obtained
from real Part membership, not from a representative or covering premise. -/
theorem execute_covering (gamma beta d : Nat) (out : List Nat)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : out ∈ execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hfirst : firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma) :
    Covering gamma beta out := by
  have hi := (execute_spec gamma beta out ho).1
  have hw : Support.word gamma (localization gamma d).tail ∈ execute gamma beta := by
    simpa only [execute, hi, Bool.cond_true] using
      Part.mem_map (fun e => Support.word gamma (localization gamma e).tail) hd
  have he := Part.mem_unique hw ho
  exact he ▸ search_word_covering gamma beta d hi hd hlt hfirst

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Covering
