/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Tree
public import Probability.BranchingProcess.Spine.Observation
public import Probability.BranchingProcess.State.Support
public import Combinatorics.UlamHarris.Ray

/-!
# The unique realized spine under a locally normalized family bias

## Public declarations

* `ProbabilityTheory.BranchingProcess.Spine.LocalBias.ae_treeKernel_unique_spine`
  proves that the distinguished nodes of the canonical biased tree form one
  realized infinite ray. Only the local normalization and support conditions
  of `IsAdmissible` are used, with a distinguished eligible initial state.

This is the unique-spine argument in Zhan Shi, *Branching Random Walks*
(2015), §4.4 before Theorem 4.3, DOI 10.1007/978-3-319-25372-5,
with the harmonic weight replaced by a normalized local family bias.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem measurable_distinguished {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] : Measurable (fun o : Option (S ⊕ T) => o.any Sum.isRight) :=
  measurable_option_elim false
    (show Measurable (Sum.isRight : S ⊕ T → Bool) from
      measurable_const.sumElim measurable_const)

/-- The canonical normal/distinguished tree has exactly one realized infinite spine. -/
theorem ae_treeKernel_unique_spine {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) :
    ∀ᵐ t ∂treeKernel Q B hB (some (Sum.inr s)),
      ∃! f, IsRay (distinguishedNodes t) f ∧
        distinguishedNodes t = Set.range (lineagePrefix f) := by
  let E := S ⊕ B.domain
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
  let : IsMarkovKernel (reproductionKernel Q B) :=
    reproductionKernel_isMarkovKernel Q B hB
  have hstep : ∀ o, ∀ᵐ ξ ∂(Kernel.optionElim
      (Measure.dirac (fun _ : ι => (none : Option E))) (reproductionKernel Q B)) o, R o ξ := by
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
        have hP : MeasurableSet B.domain := hB.measurableSet_domain
        rw [reproductionKernel_distinguished Q B hB.measurableSet_domain]
        apply (ae_map_iff (Step.distinguishChild_measurable (P := B.domain.Mem) hP).aemeasurable
          (hR.preimage (measurable_const.prodMk measurable_id))).mpr
        filter_upwards [ae_familyChildKernel_eligible Q B hB a.1 a.2] with p hp
        obtain ⟨t, ht, htD⟩ := hp
        have hu := Step.distinguishChild_unique B.domain.Mem
          p.1 p.2 ht htD
        constructor
        · intro _
          convert hu using 1
          ext i
          cases he : Step.distinguishChild B.domain.Mem p.1 p.2 i with
          | none => simp [he]
          | some v => cases v <;> simp [he]
        · simp
  have hlocal := State.ae_treeKernel_reproduction (reproductionKernel Q B)
    (some (Sum.inr s)) R hR hstep
  have hr : ∀ᵐ o ∂(treeKernel Q B hB (some (Sum.inr s))).map (fun t => t []),
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

end ProbabilityTheory.BranchingProcess.Spine.LocalBias

end
