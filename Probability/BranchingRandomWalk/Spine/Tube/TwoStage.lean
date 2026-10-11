/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.SecondMoment

/-!
# Two-stage tube success from the branching field

The first child whose increment enters a prescribed window is chosen by its
least slot index. Its descendant field is independent of the root step. This
gives an exact product formula for success in two consecutive tube windows.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- A step has a surviving child whose potential belongs to `I`. -/
def hasPotentialChildIn {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (ξ : Step ℕ X) : Prop :=
  ∃ i, survive ξ i ∧ ξ.potentialValue' φ i ∈ I

theorem measurableSet_hasPotentialChildIn {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I) :
    MeasurableSet {ξ : Step ℕ X | hasPotentialChildIn φ I ξ} := by
  rw [show {ξ : Step ℕ X | hasPotentialChildIn φ I ξ} =
      ⋃ i : ℕ, {ξ | survive ξ i ∧ ξ.potentialValue' φ i ∈ I} by
    ext ξ
    simp [hasPotentialChildIn]]
  apply MeasurableSet.iUnion
  intro i
  exact (survive_measurableSet i).inter
    (hI.preimage (Step.potentialValue'_measurable φ i))

/-- The first slot whose surviving child increment lies in `I`. -/
def firstPotentialChildIn {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (i : ℕ) (ξ : Step ℕ X) : Prop :=
  survive ξ i ∧ ξ.potentialValue' φ i ∈ I ∧
    ∀ j < i, ¬ (survive ξ j ∧ ξ.potentialValue' φ j ∈ I)

theorem measurableSet_firstPotentialChildIn {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I) (i : ℕ) :
    MeasurableSet {ξ : Step ℕ X | firstPotentialChildIn φ I i ξ} := by
  have hgood (j : ℕ) : MeasurableSet
      {ξ : Step ℕ X | survive ξ j ∧ ξ.potentialValue' φ j ∈ I} :=
    (survive_measurableSet j).inter
      (hI.preimage (Step.potentialValue'_measurable φ j))
  have hprior : MeasurableSet
      {ξ : Step ℕ X | ∀ j < i,
        ¬ (survive ξ j ∧ ξ.potentialValue' φ j ∈ I)} := by
    rw [show {ξ : Step ℕ X | ∀ j < i,
        ¬ (survive ξ j ∧ ξ.potentialValue' φ j ∈ I)} =
        ⋂ j : {j : ℕ // j < i},
          {ξ : Step ℕ X | ¬ (survive ξ j.1 ∧
            ξ.potentialValue' φ j.1 ∈ I)} by
      ext ξ
      simp]
    exact MeasurableSet.iInter fun j => (hgood j.1).compl
  have hvalue : MeasurableSet
      {ξ : Step ℕ X | ξ.potentialValue' φ i ∈ I} := by
    change MeasurableSet
      ((fun ξ : Step ℕ X => ξ.potentialValue' φ i) ⁻¹' I)
    exact hI.preimage (Step.potentialValue'_measurable φ i)
  simpa only [firstPotentialChildIn, Set.ofPred_and] using
    (survive_measurableSet i).inter
      (hvalue.inter hprior)

/-- The event that the least first-window child has a child in the second
window one generation later. -/
def twoStageTubeEvent {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I J : Set ℝ) : Set (StepField ℕ X) :=
  {ω | ∃ i : ℕ,
    firstPotentialChildIn φ I i (ω []) ∧
      hasPotentialChildIn φ J ((subtreeStepField [i] ω) [])}

theorem measurableSet_twoStageTubeEvent {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I J : Set ℝ)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    MeasurableSet (twoStageTubeEvent φ I J) := by
  rw [show twoStageTubeEvent φ I J =
      ⋃ i : ℕ, {ω : StepField ℕ X |
        firstPotentialChildIn φ I i (ω []) ∧
          hasPotentialChildIn φ J ((subtreeStepField [i] ω) [])} by
    ext ω
    simp [twoStageTubeEvent]]
  apply MeasurableSet.iUnion
  intro i
  have hfirst : MeasurableSet
      {ω : StepField ℕ X | firstPotentialChildIn φ I i (ω [])} :=
    (measurableSet_firstPotentialChildIn φ I hI i).preimage
      (measurable_pi_apply ([] : TreeNode ℕ))
  have hnext : MeasurableSet
      {ω : StepField ℕ X |
        hasPotentialChildIn φ J ((subtreeStepField [i] ω) [])} := by
    exact (measurableSet_hasPotentialChildIn φ J hJ).preimage
      ((measurable_pi_apply ([] : TreeNode ℕ)).comp
        (subtreeStepField_measurable [i]))
  exact hfirst.inter hnext

/-- The disjoint cells given by the least successful first-window slot
partition the one-step entry event. -/
theorem hasPotentialChildIn_eq_iUnion_firstPotentialChildIn
    {X : Type*} [MeasurableSpace X] (φ : Potential X) (I : Set ℝ)
    (ξ : Step ℕ X) :
    hasPotentialChildIn φ I ξ ↔
      ∃ i : ℕ, firstPotentialChildIn φ I i ξ := by
  classical
  constructor
  · rintro ⟨i, hi, hxi⟩
    let hex : ∃ k, survive ξ k ∧ ξ.potentialValue' φ k ∈ I :=
      ⟨i, hi, hxi⟩
    let i₀ := Nat.find hex
    have hs : survive ξ i₀ ∧ ξ.potentialValue' φ i₀ ∈ I := by
      simpa [i₀] using Nat.find_spec hex
    refine ⟨i₀, hs.1, hs.2, ?_⟩
    intro j hji hj
    apply Nat.find_min hex
    · simpa [i₀] using hji
    · exact hj
  · rintro ⟨i, hi, hxi, _⟩
    exact ⟨i, hi, hxi⟩

theorem firstPotentialChildIn_pairwise_disjoint
    {X : Type*} [MeasurableSpace X] (φ : Potential X) (I : Set ℝ) :
    Pairwise fun i j : ℕ =>
      Disjoint {ξ : Step ℕ X | firstPotentialChildIn φ I i ξ}
        {ξ | firstPotentialChildIn φ I j ξ} := by
  intro i j hij
  rw [Set.disjoint_left]
  intro ξ hi hj
  rcases hi with ⟨hi₁, hi₂, hi₃⟩
  rcases hj with ⟨hj₁, hj₂, hj₃⟩
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact (hj₃ i hij' ⟨hi₁, hi₂⟩).elim
  · exact (hi₃ j hji' ⟨hj₁, hj₂⟩).elim

theorem measure_twoStageTubeEvent_eq_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I J : Set ℝ)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    (stepFieldLaw μ) (twoStageTubeEvent φ I J) =
      μ {ξ | hasPotentialChildIn φ I ξ} *
        (stepFieldLaw μ) {ω | hasPotentialChildIn φ J (ω [])} := by
  let first (i : ℕ) : Set (Step ℕ X) :=
    {ξ | firstPotentialChildIn φ I i ξ}
  let next : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ J (ω [])}
  let cell (i : ℕ) : Set (StepField ℕ X) :=
    {ω | first i (ω []) ∧ next (subtreeStepField [i] ω)}
  have hcell_meas (i : ℕ) : MeasurableSet (cell i) := by
    change MeasurableSet
      ({ω : StepField ℕ X | firstPotentialChildIn φ I i (ω [])} ∩
        {ω | hasPotentialChildIn φ J ((subtreeStepField [i] ω) [])})
    exact
      ((measurableSet_firstPotentialChildIn φ I hI i).preimage
        (measurable_pi_apply ([] : TreeNode ℕ))).inter
      ((measurableSet_hasPotentialChildIn φ J hJ).preimage
        ((measurable_pi_apply ([] : TreeNode ℕ)).comp
          (subtreeStepField_measurable [i])))
  have hcell_pair : Pairwise fun i j : ℕ => Disjoint (cell i) (cell j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact (Set.disjoint_left.mp
      (firstPotentialChildIn_pairwise_disjoint φ I hij)) hi.1 hj.1
  have hunion : twoStageTubeEvent φ I J = ⋃ i, cell i := by
    ext ω
    simp only [twoStageTubeEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      cell, first, next]
    apply exists_congr
    intro i
    rfl
  have hpair (i : ℕ) :
      (stepFieldLaw μ) (cell i) = μ (first i) * (stepFieldLaw μ) next := by
    let pairMap : StepField ℕ X → Step ℕ X × StepField ℕ X :=
      fun ω => (ω ([] : TreeNode ℕ), subtreeStepField [i] ω)
    have hmap : Measurable pairMap :=
      (measurable_pi_apply ([] : TreeNode ℕ)).prodMk
        (subtreeStepField_measurable [i])
    have hrectangle : MeasurableSet (first i ×ˢ next) :=
      (measurableSet_firstPotentialChildIn φ I hI i).prod
        (by
          change MeasurableSet
            {ω : StepField ℕ X | hasPotentialChildIn φ J (ω [])}
          exact (measurableSet_hasPotentialChildIn φ J hJ).preimage
            (measurable_pi_apply ([] : TreeNode ℕ)))
    have hpre : cell i = pairMap ⁻¹' (first i ×ˢ next) := by
      ext ω
      change (firstPotentialChildIn φ I i (ω []) ∧
        hasPotentialChildIn φ J ((subtreeStepField [i] ω) [])) ↔
        (pairMap ω) ∈ first i ×ˢ next
      simp [pairMap, first, next]
    rw [hpre, ← Measure.map_apply hmap hrectangle]
    calc
      (Measure.map pairMap (stepFieldLaw μ)) (first i ×ˢ next) =
          (μ.prod (stepFieldLaw μ)) (first i ×ˢ next) := by
        simpa [pairMap] using congrArg
          (fun ν : Measure (Step ℕ X × StepField ℕ X) => ν (first i ×ˢ next))
            (root_subtreeStepField_joint_law μ i)
      _ = μ (first i) * (stepFieldLaw μ) next :=
        Measure.prod_prod (first i) next
  have hfirst : μ (⋃ i, first i) = ∑' i, μ (first i) :=
    measure_iUnion
      (firstPotentialChildIn_pairwise_disjoint φ I)
      (fun i => measurableSet_firstPotentialChildIn φ I hI i)
  have hfirst_union : (⋃ i, first i) = {ξ | hasPotentialChildIn φ I ξ} := by
    ext ξ
    simp only [Set.mem_iUnion, first, Set.mem_ofPred_eq]
    exact (hasPotentialChildIn_eq_iUnion_firstPotentialChildIn φ I ξ).symm
  rw [hunion, measure_iUnion hcell_pair hcell_meas]
  simp_rw [hpair]
  calc
    (∑' i, μ (first i) * (stepFieldLaw μ) next) =
        (∑' i, μ (first i)) * (stepFieldLaw μ) next :=
      ENNReal.tsum_mul_right
    _ = μ (⋃ i, first i) * (stepFieldLaw μ) next := by rw [← hfirst]
    _ = μ {ξ | hasPotentialChildIn φ I ξ} *
        (stepFieldLaw μ) {ω | hasPotentialChildIn φ J (ω [])} := by
      rw [hfirst_union]

/-- If both windows have positive tilted mass, then a two-generation path
enters the first window and its selected first child has a descendant
increment in the second window with positive probability. -/
theorem measure_twoStageTubeEvent_pos_of_tiltedWindows_pos
    {X : Type*} [MeasurableSpace X] [Countable ℕ]
    (φ : Potential X) (I J : Set ℝ) (aI aJ : ℝ)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hIlower : ∀ x ∈ I, aI ≤ x) (hJlower : ∀ x ∈ J, aJ ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hIpositive : 0 < tiltedPotentialLaw φ (-1) μ I)
    (hJpositive : 0 < tiltedPotentialLaw φ (-1) μ J) :
    0 < (stepFieldLaw μ) (twoStageTubeEvent φ I J) := by
  have hfirst : 0 < μ {ξ | hasPotentialChildIn φ I ξ} :=
    measure_hasPotentialChildIn_pos_of_tiltedWindow_pos
      φ I aI hI hIlower μ hIpositive
  have hnextStep : 0 < μ {ξ | hasPotentialChildIn φ J ξ} :=
    measure_hasPotentialChildIn_pos_of_tiltedWindow_pos
      φ J aJ hJ hJlower μ hJpositive
  have hrootLaw : (stepFieldLaw μ).map
      (fun ω : StepField ℕ X => ω ([] : TreeNode ℕ)) = μ :=
    stepFieldLaw_coordinate μ ([] : TreeNode ℕ)
  have hstepEvent : MeasurableSet
      {ξ : Step ℕ X | hasPotentialChildIn φ J ξ} :=
    measurableSet_hasPotentialChildIn φ J hJ
  have hnext : 0 < (stepFieldLaw μ)
      {ω : StepField ℕ X | hasPotentialChildIn φ J (ω [])} := by
    rw [show {ω : StepField ℕ X | hasPotentialChildIn φ J (ω [])} =
        (fun ω : StepField ℕ X => ω ([] : TreeNode ℕ)) ⁻¹'
          {ξ : Step ℕ X | hasPotentialChildIn φ J ξ} by rfl,
      ← Measure.map_apply (measurable_pi_apply ([] : TreeNode ℕ)) hstepEvent,
      hrootLaw]
    exact hnextStep
  rw [measure_twoStageTubeEvent_eq_mul φ I J hI hJ μ]
  exact ENNReal.mul_pos (ne_of_gt hfirst) (ne_of_gt hnext)

end ProbabilityTheory.BranchingRandomWalk.Spine
