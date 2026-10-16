/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Basic
/-!
# Independence of the hit positions and fresh descendants

The particles' positions at the first capacity hit are measurable from the
stopped past.  The descendant field rooted at those particles therefore
factorizes from any event determined by the hit positions, with the ordinary
exact-`N` field law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem measurableSet_smallInitialPopulationHitInitialPosition_preimage_at
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (A : Set (Fin N → ℝ)) (hA : MeasurableSet A) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      ((smallInitialPopulationHitInitialPosition m N hm ⁻¹' A) ∩
        {field | smallInitialPopulationCapacityTime m N field = n}) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  letI : MeasurableSpace (FiniteRootStepField m ℕ ℝ) := F n
  let roots := smallInitialPopulationRootsAt m N n hm
  let positionAt (r : Fin N → RootIndexed.TreeNode (Fin m) ℕ) :
      FiniteRootStepField m ℕ ℝ → Fin N → ℝ := fun field i =>
    RootIndexed.positionAtGeneration (fun _ : Fin m => (0 : ℝ)) id n
      (r i).1 (r i).2 field
  have hroots : Measurable[F n] roots :=
    measurable_smallInitialPopulationRootsAt m N n hm
  have hpositionAt (r : Fin N → RootIndexed.TreeNode (Fin m) ℕ) :
      Measurable[F n] (positionAt r) := by
    apply measurable_pi_iff.mpr
    intro i
    exact RootIndexed.positionAtGeneration_measurable
      (fun _ : Fin m => (0 : ℝ)) id measurable_id n (r i).1 (r i).2
  have hhitEq (field : FiniteRootStepField m ℕ ℝ)
      (htime : smallInitialPopulationCapacityTime m N field = n) :
      smallInitialPopulationHitInitialPosition m N hm field =
        positionAt (roots field) field := by
    funext i
    rw [smallInitialPopulationHitInitialPosition_eq_at_time
      m N n hm field htime i]
    rw [smallInitialPopulationHitRoots_eq_at_time
      m N n hm field htime]
  have hdecomp :
      ((smallInitialPopulationHitInitialPosition m N hm ⁻¹' A) ∩
        {field | smallInitialPopulationCapacityTime m N field = n}) =
      ⋃ r : Fin N → RootIndexed.TreeNode (Fin m) ℕ,
        {field | roots field = r} ∩ (positionAt r ⁻¹' A) ∩
          {field | smallInitialPopulationCapacityTime m N field = n} := by
    ext field
    constructor
    · rintro ⟨hAfield, htime⟩
      refine Set.mem_iUnion.mpr ⟨roots field, ?_⟩
      refine ⟨⟨rfl, ?_⟩, htime⟩
      change positionAt (roots field) field ∈ A
      rw [← hhitEq field htime]
      exact hAfield
    · intro h
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp h
      rcases hr with ⟨⟨hr, hpos⟩, htime⟩
      have hrootPosition : positionAt (roots field) field = positionAt r field := by
        rw [hr]
      change positionAt r field ∈ A at hpos
      rw [← hrootPosition, ← hhitEq field htime] at hpos
      exact ⟨hpos, htime⟩
  rw [hdecomp]
  apply MeasurableSet.iUnion
  intro r
  have hr : MeasurableSet[F n] {field | roots field = r} :=
    hroots (measurableSet_singleton r)
  exact (hr.inter (hpositionAt r hA)).inter
    ((smallInitialPopulationCapacityTime_isStoppingTime m N).measurableSet_eq n)

/-- The hit-time position vector is measurable from the sigma algebra at its
stopping time. -/
theorem measurableSet_smallInitialPopulationHitInitialPosition_preimage
    (m N : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (A : Set (Fin N → ℝ)) (hA : MeasurableSet A) :
    MeasurableSet[(smallInitialPopulationCapacityTime_isStoppingTime
      m N).measurableSpace]
      (smallInitialPopulationHitInitialPosition m N hm ⁻¹' A) := by
  classical
  let τ := smallInitialPopulationCapacityTime m N
  let hτ := smallInitialPopulationCapacityTime_isStoppingTime m N
  let initial := smallInitialPopulationHitInitialPosition m N hm
  let zeroPosition : Fin N → ℝ := fun _ => 0
  have htop : MeasurableSet[hτ.measurableSpace] {field | τ field = ⊤} :=
    hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
  have hdecomp :
      (initial ⁻¹' A) =
        (⋃ n : ℕ, (initial ⁻¹' A) ∩
          {field | τ field = (n : WithTop ℕ)}) ∪
        (if zeroPosition ∈ A then {field | τ field = ⊤} else ∅) := by
    ext field
    by_cases htopField : τ field = ⊤
    · have hinitial : initial field = zeroPosition := by
        funext i
        simp [τ, initial, zeroPosition, smallInitialPopulationHitInitialPosition,
          smallInitialPopulationHitRoots, htopField,
          RootIndexed.selectedSubtreeInitialPosition,
          RootIndexed.subtreeInitialPosition, RootIndexed.position]
      simp [htopField, hinitial]
    · obtain ⟨n, htime⟩ := WithTop.ne_top_iff_exists.mp htopField
      have htime' : τ field = (n : WithTop ℕ) := htime.symm
      change (initial field ∈ A) ↔
        field ∈ (⋃ k : ℕ, (initial ⁻¹' A) ∩
          {field | τ field = (k : WithTop ℕ)}) ∪
          (if zeroPosition ∈ A then {field | τ field = ⊤} else ∅)
      constructor
      · intro hAfield
        exact Or.inl (Set.mem_iUnion.mpr ⟨n, ⟨hAfield, htime'⟩⟩)
      · rintro (hunion | htop')
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hunion
          exact hk.1
        · by_cases hz : zeroPosition ∈ A
          · have htop' : τ field = ⊤ := by simpa [hz] using htop'
            exact (htopField htop').elim
          · simp [hz] at htop'
  rw [hdecomp]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro n
    exact (hτ.measurableSet_inter_eq_iff (initial ⁻¹' A) n).2
      (measurableSet_smallInitialPopulationHitInitialPosition_preimage_at
        m N n hm A hA)
  · by_cases hz : zeroPosition ∈ A
    · simpa [hz] using htop
    · simp [hz]

/-- On the finite-hit event, a measurable event of the initial positions
factorizes from every measurable event of the hit-subtree field.  The
almost-sure finiteness of the capacity time removes the finite-hit restriction
and gives the unconditional product formula. -/
theorem smallInitialPopulationHitInitialPosition_freshField_factorization
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ)
    (A : Set (Fin N → ℝ)) (hA : MeasurableSet A)
    (B : Set (RootIndexed.StepField (Fin N) ℕ ℝ)) (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      ((smallInitialPopulationHitInitialPosition m N hm ⁻¹' A) ∩
        (smallInitialPopulationHitSubtreeField m N hm ⁻¹' B)) =
      finiteRootStepFieldLaw μ m
        (smallInitialPopulationHitInitialPosition m N hm ⁻¹' A) *
      finiteRootStepFieldLaw μ N B := by
  let P := finiteRootStepFieldLaw μ m
  let Q := finiteRootStepFieldLaw μ N
  let τ := smallInitialPopulationCapacityTime m N
  let initial := smallInitialPopulationHitInitialPosition m N hm
  let fresh := smallInitialPopulationHitSubtreeField m N hm
  have hfinite : ∀ᵐ field ∂P, τ field ≠ ⊤ := by
    simpa [P, τ] using ae_smallInitialPopulationCapacityTime_ne_top
      m N hm hmN μ hboundary hnonempty hsupercritical
  have hAStopped : MeasurableSet[
      (smallInitialPopulationCapacityTime_isStoppingTime m N).measurableSpace]
      (initial ⁻¹' A) := by
    exact measurableSet_smallInitialPopulationHitInitialPosition_preimage
      m N hm A hA
  have hfactor := smallInitialPopulationHitRoots_factorization_on_finite
    m N hm μ (initial ⁻¹' A) B hAStopped hB
  have hfactor' :
      P (((initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) ∩ fresh ⁻¹' B)) =
        P (initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) * Q B := by
    change P (((initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) ∩
      RootIndexed.selectedSubtreeStepFieldVector
        (smallInitialPopulationHitRoots m N hm) ⁻¹' B)) =
        P (initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) * Q B
    exact hfactor
  have hleft :
      P ((initial ⁻¹' A) ∩ fresh ⁻¹' B) =
        P (((initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) ∩ fresh ⁻¹' B)) := by
    apply measure_congr
    filter_upwards [hfinite] with field hfield
    simp [hfield, and_assoc]
  have hright :
      P (initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) = P (initial ⁻¹' A) := by
    apply measure_congr
    filter_upwards [hfinite] with field hfield
    simp [hfield, and_assoc]
  calc
    P ((initial ⁻¹' A) ∩ fresh ⁻¹' B) =
        P (((initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) ∩ fresh ⁻¹' B)) := hleft
    _ = P (initial ⁻¹' A ∩ {field | τ field ≠ ⊤}) * Q B := hfactor'
    _ = P (initial ⁻¹' A) * Q B := by rw [hright]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
