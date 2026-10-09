/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.GenerationManyToOne
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
public import Probability.BranchingRandomWalk.Step.Law
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# First-passage input for the `a = 1` left-tail argument

This file proves the one-generation estimate needed when a lineage first
crosses a lower level.  The proof is the raw many-to-one identity followed by
the pointwise exponential weight bound.  It does not assume a polynomial
left-tail estimate for the selected population.

The estimate is only one ingredient of (4.16): passing from a randomly
selected generation to its descendant subtrees and proving the no-large-drop
small-deviation bound are separate steps.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- A finite history has no downward drawdown larger than `delta`. -/
def historyHasNoLargeDrop {n : ℕ} (delta : ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  ∀ i j : Fin (n + 1), (i : ℕ) ≤ j →
    history i - history j ≤ delta

/-- The finite-history event used in Aïdékon--Hu's no-large-drop estimate:
the path has no drawdown larger than `delta` and its endpoint is at most
`threshold`. -/
def historyNoLargeDropAndEndpointBelow {n : ℕ} (delta threshold : ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  historyHasNoLargeDrop delta history ∧
    history ⟨n, Nat.lt_succ_self n⟩ ≤ threshold

theorem measurableSet_historyHasNoLargeDrop {n : ℕ} (delta : ℝ) :
    MeasurableSet {history : Fin (n + 1) → ℝ |
      historyHasNoLargeDrop delta history} := by
  rw [show {history : Fin (n + 1) → ℝ |
      historyHasNoLargeDrop delta history} =
    ⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1),
      {history | (i : ℕ) ≤ j → history i - history j ≤ delta} by
    ext history
    simp [historyHasNoLargeDrop]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    by_cases hij : (i : ℕ) ≤ j
    · have hdiff : Measurable
          (fun history : Fin (n + 1) → ℝ => history i - history j) :=
        (measurable_pi_apply i).sub (measurable_pi_apply j)
      have hmeas : MeasurableSet
          {history : Fin (n + 1) → ℝ | history i - history j ≤ delta} :=
        measurableSet_Iic.preimage hdiff
      simpa only [hij, true_implies] using hmeas
    · simp [hij]

theorem measurableSet_historyNoLargeDropAndEndpointBelow {n : ℕ}
    (delta threshold : ℝ) :
    MeasurableSet {history : Fin (n + 1) → ℝ |
      historyNoLargeDropAndEndpointBelow delta threshold history} := by
  exact (measurableSet_historyHasNoLargeDrop delta).inter
    (measurableSet_Iic.preimage
      (measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))

/-- Indicator of the no-large-drop and endpoint event on a finite history. -/
noncomputable def noLargeDropEndpointTest {n : ℕ} (delta threshold : ℝ) :
    (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
  {history | historyNoLargeDropAndEndpointBelow delta threshold history}.indicator
    fun _ => 1

theorem noLargeDropEndpointTest_measurable {n : ℕ} (delta threshold : ℝ) :
    Measurable (noLargeDropEndpointTest (n := n) delta threshold) :=
  measurable_const.indicator
    (measurableSet_historyNoLargeDropAndEndpointBelow delta threshold)

/-- There is a surviving generation-`n` vertex whose path has no large
drawdown and ends below `threshold`.  This is a single-root event. -/
def hasNoLargeDropEndpointBelow {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (delta threshold : ℝ) :
    Set (StepField ι X) :=
  {ω | ∃ u : TreeNode ι, u.length = n ∧ surviveAlong ω [] u ∧
    historyNoLargeDropAndEndpointBelow delta threshold
      (Spine.pathHistory φ n 0 ω u)}

theorem measurableSet_hasNoLargeDropEndpointBelow
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (delta threshold : ℝ) :
    MeasurableSet (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
      φ n delta threshold) := by
  rw [show hasNoLargeDropEndpointBelow (ι := ι) (X := X)
      φ n delta threshold =
      ⋃ u : TreeNode ι,
        {ω | u.length = n ∧ surviveAlong ω [] u ∧
          historyNoLargeDropAndEndpointBelow delta threshold
            (Spine.pathHistory φ n 0 ω u)} by
    ext ω
    simp [hasNoLargeDropEndpointBelow]]
  apply MeasurableSet.iUnion
  intro u
  have hsurvive : MeasurableSet {ω : StepField ι X |
      surviveAlong ω [] u} := Spine.measurableSet_surviveAlong (X := X) [] u
  have hpath : MeasurableSet {ω : StepField ι X |
      historyNoLargeDropAndEndpointBelow delta threshold
        (Spine.pathHistory φ n 0 ω u)} :=
    (measurableSet_historyNoLargeDropAndEndpointBelow delta threshold).preimage
      (Spine.pathHistory_measurable φ n 0 u)
  have hlength : MeasurableSet
      {ω : StepField ι X | u.length = n} := by
    by_cases hu : u.length = n <;> simp [hu]
  rw [show {ω : StepField ι X |
      u.length = n ∧ surviveAlong ω [] u ∧
        historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory φ n 0 ω u)} =
      {ω | u.length = n} ∩ {ω | surviveAlong ω [] u} ∩
        {ω | historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory φ n 0 ω u)} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]]
  exact (hlength.inter hsurvive).inter hpath

/-- The corresponding path event on the spine increment space. -/
def spineNoLargeDropEndpointBelowEvent (n : ℕ) (delta threshold : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | historyNoLargeDropAndEndpointBelow delta threshold
    (ProbabilityTheory.RandomWalk.history n 0 increment)}

theorem measurableSet_spineNoLargeDropEndpointBelowEvent
    (n : ℕ) (delta threshold : ℝ) :
    MeasurableSet (spineNoLargeDropEndpointBelowEvent n delta threshold) :=
  (measurableSet_historyNoLargeDropAndEndpointBelow delta threshold).preimage
    (ProbabilityTheory.RandomWalk.history_measurable n 0)

/-- Many-to-one reduces the probability of an admissible low endpoint in a
single-root branching walk to the corresponding spine path probability.  The
factor `exp threshold` comes from the unweighted many-to-one exponential
weight.  This is the exact BRW-to-spine reduction used in the second term of
the proof of (4.16); the sharp no-large-drop estimate for the spine event is a
separate random-walk theorem. -/
theorem measure_hasNoLargeDropEndpointBelow_le_exp_mul_spineProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (delta threshold : ℝ) :
    (stepFieldLaw μ) (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
        φ n delta threshold) ≤
      ENNReal.ofReal (Real.exp threshold) *
        (tiltedIncrementFieldLaw φ μ)
          (spineNoLargeDropEndpointBelowEvent n delta threshold) := by
  let f : (Fin (n + 1) → ℝ) → ℝ≥0∞ := noLargeDropEndpointTest delta threshold
  have hf : Measurable f := noLargeDropEndpointTest_measurable delta threshold
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  letI := htilted
  have hpathCount : ∀ ω : StepField ι X,
      (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
        φ n delta threshold).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ≤ Spine.pathGeneration φ n f 0 ω := by
    intro ω
    by_cases hω : ω ∈ hasNoLargeDropEndpointBelow φ n delta threshold
    · obtain ⟨u, hu, hsurvive, hhistory⟩ := hω
      have hmem : ω ∈ hasNoLargeDropEndpointBelow φ n delta threshold :=
        ⟨u, hu, hsurvive, hhistory⟩
      have hterm : Spine.pathGenerationTerm φ n f 0 u ω = 1 := by
        simp [Spine.pathGenerationTerm, Set.indicator, hu, hsurvive,
          f, noLargeDropEndpointTest, hhistory]
      have hleft :
          (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
            φ n delta threshold).indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
        simp [Set.indicator, hmem]
      rw [hleft]
      rw [Spine.pathGeneration]
      calc
        (1 : ℝ≥0∞) = Spine.pathGenerationTerm φ n f 0 u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ι, Spine.pathGenerationTerm φ n f 0 p ω :=
          ENNReal.le_tsum (f := fun p => Spine.pathGenerationTerm φ n f 0 p ω) u
    · simp [Set.indicator, hω]
  have hmeasure : MeasurableSet
    (hasNoLargeDropEndpointBelow (ι := ι) (X := X) φ n delta threshold) :=
    measurableSet_hasNoLargeDropEndpointBelow (ι := ι) (X := X)
      φ n delta threshold
  have hhistoryMeas : MeasurableSet
      (spineNoLargeDropEndpointBelowEvent n delta threshold) :=
    measurableSet_spineNoLargeDropEndpointBelowEvent n delta threshold
  have hendpoint (increment : ℕ → ℝ)
      (hevent : increment ∈ spineNoLargeDropEndpointBelowEvent
        n delta threshold) :
      AdditivePath.displacement n increment ≤ threshold := by
    have h := hevent.2
    have hlast := ProbabilityTheory.RandomWalk.history_last n 0 increment
    rw [hlast, AdditivePath.fromIncrements_apply] at h
    simpa using h
  have hhistory_eq (increment : ℕ → ℝ) :
      ProbabilityTheory.RandomWalk.history n 0 increment =
        fun k : Fin (n + 1) => AdditivePath.displacement (k : ℕ) increment := by
    funext k
    simp [ProbabilityTheory.RandomWalk.history_eq_fromIncrements]
  calc
    (stepFieldLaw μ) (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
        φ n delta threshold) =
        ∫⁻ ω, (hasNoLargeDropEndpointBelow (ι := ι) (X := X)
          φ n delta threshold).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂stepFieldLaw μ := by
            rw [lintegral_indicator_const hmeasure]
            simp
    _ ≤ ∫⁻ ω, Spine.pathGeneration φ n f 0 ω ∂stepFieldLaw μ :=
      lintegral_mono hpathCount
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            f (ProbabilityTheory.RandomWalk.history n 0 increment)
          ∂tiltedIncrementFieldLaw φ μ :=
      Spine.pathManyToOneCore φ μ hboundary n hf 0
    _ ≤ ∫⁻ increment,
          ENNReal.ofReal (Real.exp threshold) *
            (spineNoLargeDropEndpointBelowEvent n delta threshold).indicator
              (fun _ => (1 : ℝ≥0∞)) increment
          ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      by_cases hevent : increment ∈
          spineNoLargeDropEndpointBelowEvent n delta threshold
      · have hexp : ENNReal.ofReal
            (Real.exp (AdditivePath.displacement n increment)) ≤
            ENNReal.ofReal (Real.exp threshold) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hendpoint increment hevent))
        have hcondition : historyNoLargeDropAndEndpointBelow delta threshold
            (fun k : Fin (n + 1) => AdditivePath.displacement (k : ℕ) increment) := by
          change historyNoLargeDropAndEndpointBelow delta threshold
            (ProbabilityTheory.RandomWalk.history n 0 increment) at hevent
          simpa only [hhistory_eq] using hevent
        have htest : f (ProbabilityTheory.RandomWalk.history n 0 increment) = 1 := by
          simp [f, noLargeDropEndpointTest, hcondition]
        have hright :
            (spineNoLargeDropEndpointBelowEvent n delta threshold).indicator
              (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        calc
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
              f (ProbabilityTheory.RandomWalk.history n 0 increment) =
              ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) := by
                rw [htest]
                simp
          _ ≤ ENNReal.ofReal (Real.exp threshold) := hexp
          _ = ENNReal.ofReal (Real.exp threshold) *
              (spineNoLargeDropEndpointBelowEvent n delta threshold).indicator
                (fun _ => (1 : ℝ≥0∞)) increment := by
                  rw [hright]
                  simp
      · have hcondition : ¬ historyNoLargeDropAndEndpointBelow delta threshold
            (fun k : Fin (n + 1) => AdditivePath.displacement (k : ℕ) increment) := by
          intro h
          apply hevent
          change historyNoLargeDropAndEndpointBelow delta threshold
            (ProbabilityTheory.RandomWalk.history n 0 increment)
          simpa only [hhistory_eq] using h
        have htest : f (ProbabilityTheory.RandomWalk.history n 0 increment) = 0 := by
          simp [f, noLargeDropEndpointTest, hcondition]
        have hright :
            (spineNoLargeDropEndpointBelowEvent n delta threshold).indicator
              (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            f (ProbabilityTheory.RandomWalk.history n 0 increment) ≤
          ENNReal.ofReal (Real.exp threshold) *
            (spineNoLargeDropEndpointBelowEvent n delta threshold).indicator
              (fun _ => (1 : ℝ≥0∞)) increment
        rw [htest, hright]
        simp
    _ = ENNReal.ofReal (Real.exp threshold) *
          (tiltedIncrementFieldLaw φ μ)
            (spineNoLargeDropEndpointBelowEvent n delta threshold) := by
      rw [lintegral_const_mul _ (measurable_const.indicator hhistoryMeas)]
      rw [lintegral_indicator_const hhistoryMeas]
      simp

/-- Indicator of the event that a real endpoint is at most `threshold`. -/
noncomputable def endpointBelowTest (threshold : ℝ) : ℝ → ℝ≥0∞ :=
  {x | x ≤ threshold}.indicator fun _ => 1

theorem endpointBelowTest_measurable (threshold : ℝ) :
    Measurable (endpointBelowTest threshold) := by
  exact measurable_const.indicator measurableSet_Iic

/-- There is a surviving vertex at generation `n` whose position is below a
specified level.  The set is measurable because the address type is
countable and every fixed ancestral path is measurable. -/
def hasEndpointBelow {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (threshold : ℝ) :
    Set (StepField ι X) :=
  {ω | ∃ u : TreeNode ι, u.length = n ∧ surviveAlong ω [] u ∧
    Spine.pathPotential φ ω u ≤ threshold}

theorem measurableSet_hasEndpointBelow
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (threshold : ℝ) :
    MeasurableSet (hasEndpointBelow (ι := ι) (X := X) φ n threshold) := by
  rw [show hasEndpointBelow (ι := ι) (X := X) φ n threshold =
      ⋃ u : TreeNode ι,
        {ω | u.length = n ∧ surviveAlong ω [] u ∧
          Spine.pathPotential φ ω u ≤ threshold} by
    ext ω
    simp [hasEndpointBelow]]
  apply MeasurableSet.iUnion
  intro u
  have hsurvive : MeasurableSet {ω : StepField ι X |
      surviveAlong ω [] u} := Spine.measurableSet_surviveAlong (X := X) [] u
  have hposition : MeasurableSet {ω : StepField ι X |
      Spine.pathPotential φ ω u ≤ threshold} :=
    measurableSet_Iic.preimage (Spine.pathPotential_measurable φ [] u)
  have hlength : MeasurableSet {ω : StepField ι X | u.length = n} := by
    by_cases hu : u.length = n <;> simp [hu]
  rw [show {ω : StepField ι X |
      u.length = n ∧ surviveAlong ω [] u ∧
        Spine.pathPotential φ ω u ≤ threshold} =
      {ω | u.length = n} ∩ {ω | surviveAlong ω [] u} ∩
        {ω | Spine.pathPotential φ ω u ≤ threshold} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]]
  exact (hlength.inter hsurvive).inter hposition

/-- At a fixed generation, the probability that any descendant has crossed
below a level is bounded by the exponential of that level.  This is a direct
consequence of the many-to-one identity and requires only boundary
normalization; no offspring moment assumption is used. -/
theorem measure_hasEndpointBelow_le_exp
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (threshold : ℝ) :
    (stepFieldLaw μ) (hasEndpointBelow (ι := ι) (X := X) φ n threshold) ≤
      ENNReal.ofReal (Real.exp threshold) := by
  let f : ℝ → ℝ≥0∞ := endpointBelowTest threshold
  have hf : Measurable f := endpointBelowTest_measurable threshold
  have hboundary' : HasBoundaryNormalization
      (φ.comp (id : X → X) measurable_id) μ := by
    simpa [Potential.comp] using hboundary
  have hmany := Spine.generationManyToOne
    (d := (id : X → X)) measurable_id (potential := φ) μ hboundary'
    hf n 0
  letI : IsProbabilityMeasure
      (Spine.tiltedIncrementFieldLaw
        (φ.comp (id : X → X) measurable_id) μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability
      (φ.comp (id : X → X) measurable_id) μ hboundary'
  have hpathCount : ∀ ω : StepField ι X,
      (hasEndpointBelow (ι := ι) (X := X) φ n threshold).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ≤
        Spine.generationEndpoint φ n f 0 ω := by
    intro ω
    by_cases hω : ω ∈ hasEndpointBelow φ n threshold
    · obtain ⟨u, hu, hsurvive, hposition⟩ := hω
      have hmem : ω ∈ hasEndpointBelow (ι := ι) (X := X) φ n threshold :=
        ⟨u, hu, hsurvive, hposition⟩
      have hterm : Spine.generationTerm φ n f 0 u ω = 1 := by
        simp [Spine.generationTerm, Set.indicator, hu, hsurvive,
          f, endpointBelowTest, hposition]
      have hleft :
          (hasEndpointBelow (ι := ι) (X := X) φ n threshold).indicator
            (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
        simp [Set.indicator, hmem]
      rw [hleft]
      rw [Spine.generationEndpoint]
      calc
        (1 : ℝ≥0∞) = Spine.generationTerm φ n f 0 u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ι, Spine.generationTerm φ n f 0 p ω :=
          ENNReal.le_tsum (f := fun p => Spine.generationTerm φ n f 0 p ω) u
    · simp [Set.indicator, hω]
  calc
    (stepFieldLaw μ) (hasEndpointBelow φ n threshold) =
        ∫⁻ ω, (hasEndpointBelow φ n threshold).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂stepFieldLaw μ := by
            rw [lintegral_indicator_const
              (measurableSet_hasEndpointBelow (ι := ι) (X := X)
                φ n threshold)]
            simp
    _ ≤ ∫⁻ ω, Spine.generationEndpoint φ n f 0 ω ∂stepFieldLaw μ :=
      lintegral_mono hpathCount
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp
            (AdditivePath.displacement n increment)) *
            f (AdditivePath.displacement n increment)
          ∂Spine.tiltedIncrementFieldLaw
            (φ.comp (id : X → X) measurable_id) μ := by
      simpa [Potential.comp] using hmany
    _ ≤ ∫⁻ _ : (ℕ → ℝ), ENNReal.ofReal (Real.exp threshold)
          ∂Spine.tiltedIncrementFieldLaw
            (φ.comp (id : X → X) measurable_id) μ := by
      apply lintegral_mono
      intro increment
      by_cases hposition : AdditivePath.displacement n increment ≤ threshold
      · simp [f, endpointBelowTest, hposition]
        exact ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr hposition)
      · simp [f, endpointBelowTest, hposition]
    _ = ENNReal.ofReal (Real.exp threshold) := by simp

/-- A finite-horizon union of below-level endpoint events is measurable. -/
def hasEndpointBelowByHorizon {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (horizon : ℕ) (threshold : ℝ) :
    Set (StepField ι X) :=
  ⋃ n : Fin (horizon + 1), hasEndpointBelow φ n threshold

theorem measurableSet_hasEndpointBelowByHorizon
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (horizon : ℕ) (threshold : ℝ) :
    MeasurableSet (hasEndpointBelowByHorizon (ι := ι) (X := X)
      φ horizon threshold) := by
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_hasEndpointBelow (ι := ι) (X := X) φ n threshold

/-- The probability that a single-root BRW has any descendant below the
threshold by a finite horizon is at most the horizon length times the
one-generation exponential bound.  This is the first-passage estimate used
for the large-drop exceptional event after branching at a selected
generation. -/
theorem measure_hasEndpointBelowByHorizon_le_sum_exp
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (horizon : ℕ) (threshold : ℝ) :
    (stepFieldLaw μ) (hasEndpointBelowByHorizon (ι := ι) (X := X)
      φ horizon threshold) ≤
      ∑ n : Fin (horizon + 1), ENNReal.ofReal (Real.exp threshold) := by
  rw [hasEndpointBelowByHorizon]
  calc
    (stepFieldLaw μ) (⋃ n : Fin (horizon + 1),
        hasEndpointBelow φ n threshold) ≤
        ∑ n : Fin (horizon + 1),
          (stepFieldLaw μ) (hasEndpointBelow φ n threshold) :=
      measure_iUnion_fintype_le (stepFieldLaw μ) _
    _ ≤ ∑ n : Fin (horizon + 1), ENNReal.ofReal (Real.exp threshold) := by
      apply Finset.sum_le_sum
      intro n hn
      exact measure_hasEndpointBelow_le_exp φ μ hboundary n threshold

end ProbabilityTheory.BranchingRandomWalk.Analytic

end
