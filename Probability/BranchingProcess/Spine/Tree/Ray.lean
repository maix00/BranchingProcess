/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Construction
public import Probability.BranchingProcess.State.Support
public import Combinatorics.UlamHarris.Ray

/-!
# The unique realized distinguished ray

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `distinguishedNodes t` is the carrier of nodes whose optional state has the
  distinguished tag: `C(t) = {u | t(u) = some (inr s) for some s}`.
* `ae_treeKernel_unique_spine` proves
  `∃! f, IsRay C(t) f ∧ C(t) = range (lineagePrefix f)` almost surely when the root is
  distinguished, the offspring kernel is Markov, and its mean weight is
  harmonic on the finite positive-weight domain. Each prefix is an actual
  distinguished node, so the ray is realized and infinite.

This formalizes the nonextinction and unique spine in Zhan Shi,
*Branching Random Walks* (2015), Chapter 4, §4.4, the construction after
(4.8) and the paragraph before Theorem 4.3,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
It uses the already constructed canonical state tree; existence of a ray
alone does not assert the tree-density or conditional spinal decomposition.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open scoped ENNReal

/-- Nodes carrying a distinguished state, rather than an absent or normal state. -/
def distinguishedNodes {ι S T : Type*} (t : List ι → Option (S ⊕ T)) : Set (List ι) :=
  {u | (t u).any Sum.isRight = true}

private theorem measurable_distinguished {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] : Measurable (fun o : Option (S ⊕ T) => o.any Sum.isRight) :=
  measurable_option_elim false
    (show Measurable (Sum.isRight : S ⊕ T → Bool) from
      measurable_const.sumElim measurable_const)

private theorem measurableSet_unique_distinguished {ι S T : Type*} [Countable ι]
    [MeasurableSpace S] [MeasurableSpace T] :
    MeasurableSet {ξ : Step ι (S ⊕ T) | ∃! i, (ξ i).any Sum.isRight = true} := by
  classical
  have hB (i : ι) : MeasurableSet {ξ : Step ι (S ⊕ T) |
      (ξ i).any Sum.isRight = true} :=
    (MeasurableSet.singleton true).preimage
      (measurable_distinguished.comp (measurable_pi_apply i))
  change MeasurableSet {ξ : Step ι (S ⊕ T) | ∃ i,
    (ξ i).any Sum.isRight = true ∧ ∀ j, (ξ j).any Sum.isRight = true → j = i}
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  rw [Set.ofPred_and]
  apply (hB i).inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hij : j = i
  · simp [hij]
  · convert (hB j).compl using 1
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hij, imp_false]

/-- The canonical normal/distinguished tree has exactly one realized infinite spine. -/
theorem ae_treeKernel_unique_spine {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)),
      ∃! f, IsRay (distinguishedNodes t) f ∧
        distinguishedNodes t = Set.range (lineagePrefix f) := by
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  let R (o : Option E) (ξ : Step ι E) : Prop :=
    (o.any Sum.isRight = true → ∃! i, (ξ i).any Sum.isRight = true) ∧
      (o.any Sum.isRight ≠ true → ∀ i, (ξ i).any Sum.isRight ≠ true)
  have hD : MeasurableSet {o : Option E | o.any Sum.isRight = true} :=
    (MeasurableSet.singleton true).preimage measurable_distinguished
  have hU : MeasurableSet {ξ : Step ι E | ∃! i, (ξ i).any Sum.isRight = true} :=
    measurableSet_unique_distinguished
  have hN : MeasurableSet {ξ : Step ι E | ∀ i, (ξ i).any Sum.isRight ≠ true} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      ((MeasurableSet.singleton true).preimage
        (measurable_distinguished.comp (measurable_pi_apply i))).compl
  have hR : MeasurableSet {p : Option E × Step ι E | R p.1 p.2} := by
    have hr := ((hD.preimage measurable_fst).compl.union (hU.preimage measurable_snd)).inter
      ((hD.preimage measurable_fst).union (hN.preimage measurable_snd))
    convert hr using 1
    ext p
    simp only [R, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
      Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  let : IsMarkovKernel (reproductionKernel Q h) :=
    reproductionKernel_isMarkovKernel Q hh harmonic
  have hstep : ∀ o, ∀ᵐ ξ ∂(Kernel.optionElim
      (Measure.dirac (fun _ : ι => (none : Option E))) (reproductionKernel Q h)) o, R o ξ := by
    intro o
    cases o with
    | none =>
      rw [Kernel.optionElim_none]
      apply (ae_dirac_iff (hR.preimage (measurable_const.prodMk measurable_id))).mpr
      simp [R]
    | some o =>
      rw [Kernel.optionElim_some]
      cases o with
      | inl a =>
        rw [reproductionKernel_normal]
        apply (ae_map_iff (Step.map_measurable measurable_inl).aemeasurable
          (hR.preimage (measurable_const.prodMk measurable_id))).mpr
        exact Filter.Eventually.of_forall fun ξ => by
          constructor
          · simp
          · intro _ i
            cases he : ξ i <;> simp [Step.map, he]
      | inr a =>
        have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
          (hh (MeasurableSet.singleton 0).compl).inter
            (hh (MeasurableSet.singleton ∞).compl)
        rw [reproductionKernel_distinguished Q hh]
        apply (ae_map_iff (Step.distinguishChild_measurable hP).aemeasurable
          (hR.preimage (measurable_const.prodMk measurable_id))).mpr
        filter_upwards [ae_biasedFamilyChild_eligible Q hh a.1 a.2.1 a.2.2
          (harmonic a.1 a.2.1 a.2.2)] with p hp
        obtain ⟨t, ht, htz, htt⟩ := hp
        have hu := Step.distinguishChild_unique (fun s => h s ≠ 0 ∧ h s ≠ ∞)
          p.1 p.2 ht ⟨htz, htt⟩
        constructor
        · intro _
          convert hu using 1
          ext i
          cases he : Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2 i with
          | none => simp [he]
          | some v => cases v <;> simp [he]
        · simp
  have hlocal := State.ae_treeKernel_reproduction (reproductionKernel Q h)
    (some (Sum.inr s)) R hR hstep
  have hr : ∀ᵐ o ∂(treeKernel Q hh harmonic (some (Sum.inr s))).map (fun t => t []),
      o.any Sum.isRight = true := by
    rw [treeKernel_root]
    exact (ae_dirac_iff hD).mpr rfl
  have hroot := ae_of_ae_map
    (measurable_pi_apply ([] : List ι)).aemeasurable hr
  filter_upwards [hlocal, hroot] with t ht htroot
  have hchild : ∀ u ∈ distinguishedNodes t, ∃! i, u ++ [i] ∈ distinguishedNodes t :=
    fun u hu => (ht u).1 hu
  obtain ⟨f, hf, huniq⟩ := existsUnique_isRay_of_unique_child
    (distinguishedNodes t) htroot hchild
  refine ⟨f, ⟨hf, hf.eq_range_of_unique_child hchild ?_⟩, fun g hg => huniq g hg.1⟩
  intro u i hui
  by_contra hu
  exact ((ht u).2 hu i) hui

end ProbabilityTheory.BranchingProcess.Spine

end
