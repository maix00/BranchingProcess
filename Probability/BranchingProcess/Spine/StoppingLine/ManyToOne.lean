/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.AdaptedPayoff
public import Probability.BranchingProcess.Spine.StoppingLine.Mass
public import Probability.Process.Tree.Line.Basic

/-!
# Many-to-one at generation-observable random lines

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.StoppingLine`:

* `spineHit L` is the event that a distinguished node belongs to the line
  evaluated on the same tree after erasing roles.
* `measurableSet_spineHit` proves measurability of that entrance event.
* `lintegral_mass_eq` proves `E[W_L] = P_spine(spineHit L)` for a
  generation-observable random line; optionality is not assumed.
* `lintegral_mass_le_one` gives `E[W_L] ≤ 1`.
* `lintegral_mass_eq_one_iff` characterizes preservation of expectation
  by almost-sure spine entrance: `E[W_L] = 1 ↔ P_spine(spineHit L) = 1`.

The original process has any measurable state space and countable child slots.
The measurable weight is mean harmonic on its finite positive region; the root
lies there. Weights retain the existing ancestral eligibility guard.
Line-mass corollaries require only a random antichain and generation-observable
membership. Optionality relative to a separately supplied line past is unnecessary. No bounded depth, path coverage, moment or uniform-integrability
assumption is imposed.

This generalizes Lemma 14.1 of J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*
(2004), §14, Lemma 14.1, pp. 577–578, DOI 10.1239/aap/1086957585.
The line formulas specialize `Spine.lintegral_adaptedPayoff_eq`; they do not
maintain a second fixed-address density proof. The same canonical original and distinguished trees are used.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.StoppingLine

open Classical MeasureTheory Combinatorics.UlamHarris Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S]

/-- Entrance of the realized distinguished ray into the line on its untyped tree. -/
def spineHit {h : S → ℝ≥0∞}
    (L : (List ι → Option S) → Set (Unit × List ι)) :
    Set (List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) :=
  {t | ∃ u, ((), u) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
    (t u).any Sum.isRight = true}

variable [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

/-- Generation-by-generation many-to-one, with a payoff known at each node's
whole generation (Biggins–Kyprianou (2004), proof of Lemma 14.1). -/
private lemma lintegral_linePayoff
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hsimple : ∀ u : List ι,
      MeasurableSet[State.treeFiltration u.length] {t | ((), u) ∈ L t})
    (g : (u : List ι) →
      (Π k : Finset.Iic u.length, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞)
    (hg : ∀ u, Measurable (g u)) :
    (∫⁻ t, ∑' u : List ι, if ((), u) ∈ L t then
      addressWeight h u.length u.get (State.treeHistory u.length t) *
        g u (State.treeHistory u.length t) else 0 ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, ∑' u : List ι,
      if ((), u) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
        (t u).any Sum.isRight = true then g u (untypedHistory u.length t) else 0
      ∂treeKernel Q hh harmonic (some (Sum.inr s)) := by
  let F (u : List ι) (t : List ι → Option S) :=
    if ((), u) ∈ L t then g u (State.treeHistory u.length t) else 0
  have hF (u : List ι) : Measurable[State.treeFiltration u.length] (F u) :=
    ((hg u).comp (Measurable.of_comap_le le_rfl)).ite (hsimple u) measurable_const
  have hi := lintegral_adaptedPayoff_eq Q hh harmonic s F hF
  refine (lintegral_congr fun t => ?_).trans (hi.trans (lintegral_congr fun t => ?_))
  · apply tsum_congr
    intro u
    by_cases ht : ((), u) ∈ L t <;> simp [F, ht]
  · apply tsum_congr
    intro u
    by_cases ht : ((), u) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) <;>
      by_cases htag : (t u).any Sum.isRight = true <;> simp [F, ht, htag]; rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The actual distinguished-line entrance event is measurable. -/
theorem measurableSet_spineHit {h : S → ℝ≥0∞}
    {L : (List ι → Option S) → Set (Unit × List ι)} (hL : Tree.IsRandomLine L) :
    MeasurableSet (spineHit (h := h) L) := by
  have he : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun v => (t v).map (Sum.elim id Subtype.val)) := by
    have hm := measurable_option_map (measurable_id.sumElim
      (measurable_subtype_coe : Measurable (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S)))
    fun_prop
  have ht : Measurable (fun o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      o.any Sum.isRight) := measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hm := MeasurableSet.iUnion fun u =>
    ((hL.measurableSet_mem ((), u)).preimage he).inter
      ((measurableSet_singleton true).preimage (ht.comp (measurable_pi_apply u)))
  convert hm using 1
  ext t
  simp only [spineHit, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]

omit [MeasurableSpace S] [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] in
private lemma sum_line_spine_indicator {h : S → ℝ≥0∞}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : ∀ t, RootIndexed.IsLine (L t))
    (t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (hf : ∃ f, distinguishedNodes t = Set.range (lineagePrefix f)) :
    (∑' u : List ι, if ((), u) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
        (t u).any Sum.isRight = true then (1 : ℝ≥0∞) else 0) =
      (spineHit L).indicator (fun _ => 1) t := by
  obtain ⟨f, hf⟩ := hf
  by_cases ht : t ∈ spineHit L
  · obtain ⟨u, hu, htagu⟩ := ht
    rw [Set.indicator_of_mem (show t ∈ spineHit L from ⟨u, hu, htagu⟩)]
    rw [tsum_eq_single u]
    · exact ite_eq_left ⟨hu, htagu⟩
    · intro v hv
      apply ite_eq_right
      rintro ⟨hvmem, htagv⟩
      have huc : u ∈ distinguishedNodes t := htagu
      have hvc : v ∈ distinguishedNodes t := htagv
      rw [hf] at huc hvc
      obtain ⟨n, rfl⟩ := huc
      obtain ⟨m, rfl⟩ := hvc
      apply hv
      rcases le_total m n with hmn | hnm
      · exact congrArg Prod.snd ((hL _).eq hvmem hu ⟨rfl, lineagePrefix_prefix f hmn⟩)
      · exact (congrArg Prod.snd ((hL _).eq hu hvmem ⟨rfl, lineagePrefix_prefix f hnm⟩)).symm
  · rw [Set.indicator_of_notMem ht]
    have hz (u : List ι) : (if ((), u) ∈ L (fun v =>
        (t v).map (Sum.elim id Subtype.val)) ∧ (t u).any Sum.isRight = true
        then (1 : ℝ≥0∞) else 0) = 0 := ite_eq_right (fun hu => ht ⟨u, hu⟩)
    simp only [hz, tsum_zero]

/-- Biggins–Kyprianou (2004), Lemma 14.1: the expected normalized line mass
is the probability that the same canonical distinguished ray meets the line. -/
theorem lintegral_mass_eq
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsRandomLine L)
    (hsimple : ∀ u : List ι,
      MeasurableSet[State.treeFiltration u.length] {t | ((), u) ∈ L t}) :
    (∫⁻ t, mass h L t ∂State.treeKernel Q (some s.1)) =
      (treeKernel Q hh harmonic (some (Sum.inr s))) (spineHit L) := by
  have hi := lintegral_linePayoff Q hh harmonic s hsimple
    (fun _ _ => 1) (fun _ => measurable_const)
  simp only [mul_one] at hi
  change (∫⁻ t, mass h L t ∂State.treeKernel Q (some s.1)) = _ at hi
  refine hi.trans ?_
  rw [← lintegral_indicator_one (measurableSet_spineHit hL)]
  apply lintegral_congr_ae
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  exact sum_line_spine_indicator hL.isLine t ⟨ht.choose, ht.choose_spec.1.2⟩

/-- A generation-observable random line has normalized expected mass at most one. -/
theorem lintegral_mass_le_one
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsRandomLine L)
    (hsimple : ∀ u : List ι,
      MeasurableSet[State.treeFiltration u.length] {t | ((), u) ∈ L t}) :
    (∫⁻ t, mass h L t ∂State.treeKernel Q (some s.1)) ≤ 1 := by
  rw [lintegral_mass_eq Q hh harmonic s hL hsimple]
  exact prob_le_one

/-- Expected line mass is preserved exactly when the distinguished ray hits
almost surely (Biggins–Kyprianou (2004), Lemma 14.1). -/
theorem lintegral_mass_eq_one_iff
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsRandomLine L)
    (hsimple : ∀ u : List ι,
      MeasurableSet[State.treeFiltration u.length] {t | ((), u) ∈ L t}) :
    (∫⁻ t, mass h L t ∂State.treeKernel Q (some s.1)) = 1 ↔
      (treeKernel Q hh harmonic (some (Sum.inr s))) (spineHit L) = 1 := by
  rw [lintegral_mass_eq Q hh harmonic s hL hsimple]

end ProbabilityTheory.BranchingProcess.Spine.StoppingLine
