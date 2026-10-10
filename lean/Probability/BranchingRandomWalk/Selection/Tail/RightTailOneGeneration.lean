/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.Tail.TwoStageTube
import Probability.BranchingRandomWalk.Selection.Tail.PathManyToOne
import Probability.Distributions.Moments.Signs
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees

/-!
# A one-generation upper-tail bound from the offspring law

The cross-child moment assumption gives a quantitative lower bound for a
one-step tube hit. Independent initial roots then give an upper bound for the
probability that no root produces such a child. This is a finite-horizon
consequence of the model assumptions; the longer corridor estimates needed
for (4.15) are separate.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Histories that stay in a fixed-width affine corridor, including the
initial root coordinate. -/
def affineCorridorHistory (n : ℕ) (lower drift width : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | ∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
    history k ≤ lower + drift * (k.val : ℝ) + width}

/-- The corridor window at its first positive time coordinate. -/
def affineCorridorFirstWindow (lower drift width : ℝ) : Set ℝ :=
  {y | lower + drift ≤ y ∧ y ≤ lower + drift + width}

/-- The affine corridor used in Lemma 4.5, with its terminal endpoint
restricted by the additional cutoff. -/
def affineCorridorHistoryEndpointCutoff (n : ℕ) (lower drift width endpointUpper : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | history ∈ affineCorridorHistory n lower drift width ∧
    history ⟨n + 1, by omega⟩ ≤ endpointUpper}

theorem measurableSet_affineCorridorHistory
    (n : ℕ) (lower drift width : ℝ) :
    MeasurableSet (affineCorridorHistory n lower drift width) := by
  rw [show affineCorridorHistory n lower drift width =
      ⋂ k : Fin (n + 2), {history | lower + drift * (k.val : ℝ) ≤ history k ∧
        history k ≤ lower + drift * (k.val : ℝ) + width} by
        ext history
        simp [affineCorridorHistory]]
  apply MeasurableSet.iInter
  intro k
  exact MeasurableSet.inter
    (measurableSet_le measurable_const (measurable_pi_apply k))
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem affineCorridorHistory_firstWindow
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width := by
  have hcoord := h ⟨1, by omega⟩
  simpa [affineCorridorHistory, affineCorridorFirstWindow] using hcoord

theorem affineCorridorHistory_terminalUpper
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨n + 1, by omega⟩ ≤
      lower + drift * ((n + 1 : ℕ) : ℝ) + width := by
  have hcoord := (h ⟨n + 1, by omega⟩).2
  simpa [affineCorridorHistory] using hcoord

theorem measurableSet_affineCorridorHistoryEndpointCutoff
    (n : ℕ) (lower drift width endpointUpper : ℝ) :
    MeasurableSet
      (affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) := by
  rw [show affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper =
      affineCorridorHistory n lower drift width ∩
        {history | history ⟨n + 1, by omega⟩ ≤ endpointUpper} by
        ext history
        simp [affineCorridorHistoryEndpointCutoff]]
  exact (measurableSet_affineCorridorHistory n lower drift width).inter
    (measurableSet_le
      (measurable_pi_apply (⟨n + 1, by omega⟩ : Fin (n + 2)))
      measurable_const)

theorem affineCorridorHistoryEndpointCutoff_firstWindow
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width :=
  affineCorridorHistory_firstWindow n lower drift width history h.1

theorem affineCorridorHistoryEndpointCutoff_terminalUpper
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨n + 1, by omega⟩ ≤ endpointUpper := h.2

/-- The one-child generation-`n` corridor count after a fixed root
reproduction step. -/
noncomputable def pathGenerationChildObservable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (x : ℝ) (i : ℕ) (ξ : Step ℕ X) (η : StepField ℕ X) : ℝ≥0∞ :=
  survivingPotentialTest φ
    (fun y => Spine.pathGeneration φ n
      (fun tail => F (prependHistory x tail)) (x + y) η) ξ i

theorem pathGenerationChildObservable_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (x : ℝ) (i : ℕ) :
    Measurable (Function.uncurry
      (pathGenerationChildObservable φ n F x i)) := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  unfold pathGenerationChildObservable survivingPotentialTest
  exact ((Spine.pathGeneration_joint_measurable φ n htailTest).comp
    (((measurable_const.add
      ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
        measurable_snd)).ite
    ((survive_measurableSet i).preimage measurable_fst)
    measurable_const

/-- The conditional first moment of one child continuation is the spine
many-to-one integral, provided that child is present. -/
theorem lintegral_pathGenerationChildObservable_eq_manyToOne
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ) =
      survivingPotentialTest φ
        (fun y => ∫⁻ increment,
          ENNReal.ofReal (Real.exp
            (AdditivePath.displacement n increment)) *
            F (prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ) ξ i := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  have hmean (y : ℝ) :
      (∫⁻ η, Spine.pathGeneration φ n tailTest (x + y) η
        ∂stepFieldLaw μ) =
        ∫⁻ increment,
          ENNReal.ofReal (Real.exp
            (AdditivePath.displacement n increment)) *
            F (prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ := by
    simpa [tailTest] using
      (Spine.pathManyToOneCore φ μ hboundary n htailTest (x + y))
  classical
  by_cases hi : survive ξ i
  · simp [pathGenerationChildObservable, survivingPotentialTest,
      tailTest, hi, hmean]
  · simp [pathGenerationChildObservable, survivingPotentialTest, hi]

/-- The terminal cutoff in Lemma 4.5 bounds a child's continuation moment by
the exponential terminal weight times the corresponding spine corridor
probability. -/
theorem lintegral_pathGenerationChildObservable_le_endpoint_weight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
      survivingPotentialTest φ
        (fun y => ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                corridor}) ξ i := by
  classical
  rw [lintegral_pathGenerationChildObservable_eq_manyToOne
    φ μ hboundary n (corridor.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hcorridor) x i ξ]
  by_cases hi : survive ξ i
  · simp only [survivingPotentialTest, if_pos hi]
    let y : ℝ := ξ.potentialValue' φ i
    let E : Set (ℕ → ℝ) := {increment | prependHistory x
      (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈ corridor}
    have hE : MeasurableSet E :=
      hcorridor.preimage ((prependHistory_joint_measurable n).comp
        (measurable_const.prodMk
          (ProbabilityTheory.RandomWalk.history_measurable n (x + y))))
    have hterminalPath (increment : ℕ → ℝ) (hevent : increment ∈ E) :
        AdditivePath.displacement n increment ≤ terminalUpper - (x + y) := by
      have h := hterminal
        (prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment)) hevent
      have hindex :
          (⟨n + 1, by omega⟩ : Fin (n + 2)) =
            Fin.succ ⟨n, Nat.lt_succ_self n⟩ := by
        apply Fin.ext
        rfl
      rw [hindex, prependHistory_succ, ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements_apply] at h
      linarith
    have htailBound :
        (∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            (corridor.indicator fun _ => (1 : ℝ≥0∞))
              (prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
          (tiltedIncrementFieldLaw φ μ) E := by
      calc
        _ ≤ ∫⁻ increment,
            ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
              E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            ∂tiltedIncrementFieldLaw φ μ := by
          apply lintegral_mono
          intro increment
          by_cases hevent : increment ∈ E
          · have hweight :
                ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) ≤
                  ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) :=
              ENNReal.ofReal_le_ofReal
                (Real.exp_le_exp.mpr (hterminalPath increment hevent))
            change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
                corridor.indicator (fun _ => (1 : ℝ≥0∞))
                  (prependHistory x
                    (ProbabilityTheory.RandomWalk.history n (x + y) increment)) ≤
              ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
                E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            have hcorridorMem : prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor := by
              simpa [E] using hevent
            simp only [Set.indicator_of_mem hcorridorMem,
              Set.indicator_of_mem hevent]
            simpa using hweight
          · have hcorridorNot :
                prependHistory x
                  (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∉
                    corridor := hevent
            change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
                corridor.indicator (fun _ => (1 : ℝ≥0∞))
                  (prependHistory x
                    (ProbabilityTheory.RandomWalk.history n (x + y) increment)) ≤
              ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
                E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            simp only [Set.indicator_of_notMem hcorridorNot,
              Set.indicator_of_notMem hevent]
            simp
        _ = ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ) E := by
          rw [lintegral_const_mul _ (measurable_const.indicator hE)]
          rw [lintegral_indicator_const hE]
          simp
    simpa [y, E] using htailBound
  · simp [survivingPotentialTest, hi]

/-- A continuation corridor must contain the child's position at its first
time coordinate. Thus a probability bound only for starts in the first
window extends to all starts: outside the window the continuation event is
empty. -/
theorem shiftedCorridorProbability_le_of_firstWindow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (x : ℝ) (corridor : Set (Fin (n + 2) → ℝ))
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ y : ℝ,
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q := by
  intro y
  by_cases hy : x + y ∈ window
  · exact hprob y hy
  · have hempty : {increment | prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          corridor} = ∅ := by
      ext increment
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hmem
      have hwindow := hfirst _ hmem
      have hindex : (⟨1, by omega⟩ : Fin (n + 2)) =
          Fin.succ (⟨0, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hindex, prependHistory_succ] at hwindow
      have hwindow' : x + y ∈ window := by simpa using hwindow
      exact hy hwindow'
    rw [hempty]
    simp

/-- If every shifted spine corridor has probability at most `q`, the child
continuation mean is bounded by the endpoint factor, `q`, and the child's
realized exponential weight. This is the input for the cross-child part of
the MRCA estimate. -/
theorem lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (q : ℝ≥0∞)
    (hprob : ∀ y : ℝ,
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
          realizedPotentialWeight φ (-1) ξ i := by
  have hendpoint := lintegral_pathGenerationChildObservable_le_endpoint_weight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal i ξ
  by_cases hi : survive ξ i
  · let y : ℝ := ξ.potentialValue' φ i
    have hrealExp : Real.exp (terminalUpper - (x + y)) =
        Real.exp (terminalUpper - x) * Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfactor :
        ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) =
          ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (-y)) := by
      rw [hrealExp, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have hmean : survivingPotentialTest φ
        (fun z => ENNReal.ofReal (Real.exp (terminalUpper - (x + z))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + z) increment) ∈
                corridor}) ξ i =
          ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor} := by
      simp [survivingPotentialTest, hi, y]
    calc
      _ ≤ survivingPotentialTest φ
          (fun z => ENNReal.ofReal (Real.exp (terminalUpper - (x + z))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + z) increment) ∈
                  corridor}) ξ i := hendpoint
      _ = ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor} := hmean
      _ ≤ ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (-y)) * q := by
          rw [hfactor]
          gcongr
          exact hprob y
      _ = ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
            realizedPotentialWeight φ (-1) ξ i := by
          simp [realizedPotentialWeight, hi, y]
          ac_rfl
  · simpa [survivingPotentialTest, realizedPotentialWeight, hi] using
      hendpoint

/-- The child moment estimate in Lemma 4.5 only needs the uniform corridor
probability for child positions that lie in the tube at the first time step. -/
theorem lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
          realizedPotentialWeight φ (-1) ξ i := by
  exact lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal q
    (shiftedCorridorProbability_le_of_firstWindow φ μ n x corridor window q
      hfirst hprob) i ξ

/-- If each child continuation mean is bounded by a common factor times its
realized exponential weight, then the ordered off-diagonal pair sum is
bounded by the cross-child weight. -/
theorem ennreal_tsum_offDiagonal_mul_le_crossChildWeight_of_childMomentBound
    {X : Type*} [MeasurableSpace X] [Countable ℕ]
    (φ : Potential X) (ξ : Step ℕ X) (K : ℝ≥0∞)
    (m : ℕ → ℝ≥0∞)
    (hm : ∀ i, m i ≤ K * realizedPotentialWeight φ (-1) ξ i) :
    (∑' i, ∑' j, if i ≠ j then m i * m j else 0) ≤
      K ^ 2 * crossChildWeight φ ξ := by
  classical
  have hzero (i : ℕ) (hi : ¬ survive ξ i) : m i = 0 := by
    apply le_antisymm
    · have h := hm i
      simpa [realizedPotentialWeight, hi] using h
    · exact bot_le
  have hpair (i j : ℕ) :
      (if i ≠ j then m i * m j else 0) ≤
        K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) := by
    by_cases hij : i ≠ j
    · by_cases hi : survive ξ i
      · by_cases hj : survive ξ j
        · have hweight :
              realizedPotentialWeight φ (-1) ξ i *
                  realizedPotentialWeight φ (-1) ξ j =
                ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
            rw [show realizedPotentialWeight φ (-1) ξ i =
                ENNReal.ofReal (Real.exp (-ξ.potentialValue' φ i)) by
                  simp [realizedPotentialWeight, hi],
              show realizedPotentialWeight φ (-1) ξ j =
                ENNReal.ofReal (Real.exp (-ξ.potentialValue' φ j)) by
                  simp [realizedPotentialWeight, hj]]
            have hexp : Real.exp (-ξ.potentialValue' φ i) *
                Real.exp (-ξ.potentialValue' φ j) =
              Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [← ENNReal.ofReal_mul
              (Real.exp_nonneg (-ξ.potentialValue' φ i)), hexp]
          have hproducts :
              m i * m j ≤
                (K * realizedPotentialWeight φ (-1) ξ i) *
                  (K * realizedPotentialWeight φ (-1) ξ j) :=
            mul_le_mul (hm i) (hm j) (by positivity) (by positivity)
          have hfactor :
              (K * realizedPotentialWeight φ (-1) ξ i) *
                  (K * realizedPotentialWeight φ (-1) ξ j) =
                K ^ 2 * ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
            calc
              _ = (K * K) *
                  (realizedPotentialWeight φ (-1) ξ i *
                    realizedPotentialWeight φ (-1) ξ j) := by ac_rfl
              _ = K ^ 2 * ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
                rw [pow_two, hweight]
          simpa [hij, hi, hj] using hproducts.trans_eq hfactor
        · simp [hij, hj, hzero j hj]
      · simp [hij, hi, hzero i hi]
    · simp [hij]
  have hinner (i : ℕ) :
      (∑' j, if i ≠ j then m i * m j else 0) ≤
        ∑' j, K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) :=
    ENNReal.tsum_le_tsum (fun j => hpair i j)
  calc
    (∑' i, ∑' j, if i ≠ j then m i * m j else 0) ≤
        ∑' i, ∑' j, K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) := ENNReal.tsum_le_tsum hinner
    _ = K ^ 2 * crossChildWeight φ ξ := by
      let fLeft : ℕ → ℕ → ℝ≥0∞ := fun i j => by
        letI : Decidable (i = j) := instDecidableEqNat i j
        letI : Decidable (i ≠ j) := instDecidableNot
        letI : Decidable (survive ξ i) := Classical.propDecidable _
        letI : Decidable (survive ξ j) := Classical.propDecidable _
        exact if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
        else 0
      let fRight : ℕ → ℕ → ℝ≥0∞ := fun i j => by
        letI : Decidable (i = j) := Classical.propDecidable _
        letI : Decidable (i ≠ j) := instDecidableNot
        letI : Decidable (survive ξ i) := Classical.propDecidable _
        letI : Decidable (survive ξ j) := Classical.propDecidable _
        exact if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
        else 0
      have hsumLeft : (∑' i, ∑' j, K ^ 2 * fLeft i j) =
          K ^ 2 * (∑' i, ∑' j, fLeft i j) := by
        calc
          (∑' i, ∑' j, K ^ 2 * fLeft i j) =
              ∑' i, K ^ 2 * (∑' j, fLeft i j) := by
            apply tsum_congr
            intro i
            exact ENNReal.tsum_mul_left
          _ = K ^ 2 * (∑' i, ∑' j, fLeft i j) := ENNReal.tsum_mul_left
      have hpairEq : (∑' i, ∑' j, fLeft i j) =
          ∑' i, ∑' j, fRight i j := by
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        by_cases h : i ≠ j ∧ survive ξ i ∧ survive ξ j <;>
          simp [fLeft, fRight, h]
      have hcross : (∑' i, ∑' j, fRight i j) =
          crossChildWeight φ ξ := by
        unfold crossChildWeight
        rfl
      change (∑' i, ∑' j, K ^ 2 * fLeft i j) =
        K ^ 2 * crossChildWeight φ ξ
      calc
        _ = K ^ 2 * (∑' i, ∑' j, fLeft i j) := hsumLeft
        _ = K ^ 2 * (∑' i, ∑' j, fRight i j) := by rw [hpairEq]
        _ = K ^ 2 * crossChildWeight φ ξ := by rw [hcross]

/-- The root's ordered off-diagonal continuation terms are controlled by the
cross-child exponential weight once the shifted spine corridor probabilities
have a uniform bound. This is the fixed-ancestor estimate in Lemma 4.5. -/
theorem pathGenerationChildMean_offDiagonal_le_crossChildWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (ξ : Step ℕ X) :
    (∑' i, ∑' j, if i ≠ j then
      (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂stepFieldLaw μ) *
      (∫⁻ ζ, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
        ∂stepFieldLaw μ)
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossChildWeight φ ξ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (terminalUpper - x)) * q
  let m : ℕ → ℝ≥0∞ := fun i =>
    ∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ
  have hm (i : ℕ) : m i ≤ K * realizedPotentialWeight φ (-1) ξ i := by
    simpa [m, K] using
      lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob i ξ
  simpa [K, m] using
    ennreal_tsum_offDiagonal_mul_le_crossChildWeight_of_childMomentBound
      φ ξ K m hm

/-- Integrating the fixed-ancestor off-diagonal estimate over the root step
gives the expected cross-child contribution in the MRCA decomposition. -/
theorem lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    (∑' i, ∑' j, if i ≠ j then
      ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂stepFieldLaw μ) *
        (∫⁻ ζ, pathGenerationChildObservable φ n
          (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
          ∂stepFieldLaw μ) ∂μ
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator fun _ => (1 : ℝ≥0∞)
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [F] using pathGenerationChildObservable_measurable
      φ n (corridor.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hcorridor) x i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hoffInner (i : ℕ) :
      Measurable (fun ξ => ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ξ => ∑' i, ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ξ, ∑' j, offTerm i j ξ ∂μ) =
        ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ) =
        ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hoffInnerIntegral i
    · intro i
      exact (hoffInner i).aemeasurable
  have hoffTermIntegral (i j : ℕ) :
      (∫⁻ ξ, offTerm i j ξ ∂μ) =
        if i ≠ j then ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0 := by
    by_cases hij : i ≠ j
    · simp [offTerm, hij]
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hsum :
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) =
        ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := by
    calc
      _ = ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        rw [hoffTermIntegral]
      _ = ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := hoffIntegral.symm
  have hpointwise (ξ : Step ℕ X) :
      (∑' i, ∑' j, offTerm i j ξ) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossChildWeight φ ξ := by
    simpa [offTerm, childMean, F] using
      pathGenerationChildMean_offDiagonal_le_crossChildWeight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob ξ
  have hbound := calc
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) ≤
          ∫⁻ ξ, (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
            crossChildWeight φ ξ ∂μ := by
        rw [hsum]
        exact lintegral_mono hpointwise
      _ = (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
        rw [lintegral_const_mul _ (crossChildWeight_measurable φ)]
  simpa [F, childMean] using hbound

/-- Integrating an observable of the root step and a fixed child's subtree
uses their product law. -/
theorem lintegral_root_subtreeFunction_eq
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i : ι) (H : Step ι X × StepField ι X → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
      ∂stepFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ := by
  let pair : StepField ι X → Step ι X × StepField ι X := fun ω =>
    (ω [], subtreeStepField [i] ω)
  have hpair : Measurable pair :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk
      (subtreeStepField_measurable [i])
  calc
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
        ∂stepFieldLaw μ) = ∫⁻ z, H z ∂(stepFieldLaw μ).map pair := by
      exact (lintegral_map hH hpair).symm
    _ = ∫⁻ z, H z ∂μ.prod (stepFieldLaw μ) := by
      rw [root_subtreeStepField_joint_law μ i]
    _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ :=
      lintegral_prod H hH.aemeasurable

/-- Paley--Zygmund for an ENNReal-valued nonnegative observable, in the
support-event form used for the number of corridor paths. -/
theorem measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, X ω ∂μ) = mean)
    (hsecond : (∫⁻ ω, X ω ^ 2 ∂μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤ μ {ω | X ω ≠ 0} := by
  let A : Set Ω := {ω | X ω ≠ 0}
  let indicator : Ω → ℝ≥0∞ := A.indicator fun _ => 1
  have hA : MeasurableSet A := by
    change MeasurableSet (X ⁻¹' ({0}ᶜ))
    exact (measurableSet_singleton 0).compl.preimage hX
  have hindicator : Measurable indicator := measurable_const.indicator hA
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    convert Real.HolderConjugate.conjExponent
      (show 1 < (2 : ℝ) by norm_num) using 1 <;>
      norm_num [Real.conjExponent]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h22
    hindicator.aemeasurable hX.aemeasurable
  have hindicator_sq : (fun ω => indicator ω ^ (2 : ℝ)) = indicator := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [indicator, hω]
  have hindicator_integral :
      (∫⁻ ω, indicator ω ^ (2 : ℝ) ∂μ) = μ A := by
    rw [hindicator_sq]
    exact lintegral_indicator_one hA
  have hX_on_A : ∀ ω, indicator ω * X ω = X ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [indicator, hω]
    · have hzero : X ω = 0 := by
        by_contra hne
        exact hω hne
      simp [indicator, hω, hzero]
  have hHolder' :
      mean ≤ (μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ) := by
    calc
      mean = ∫⁻ ω, indicator ω * X ω ∂μ := by
        rw [lintegral_congr fun ω => hX_on_A ω, hmean]
      _ ≤ (∫⁻ ω, indicator ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hHolder
      _ ≤ (μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ) := by
        rw [hindicator_integral]
        gcongr
        simpa [pow_two] using hsecond
  have hroot (x : ℝ≥0∞) :
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) =
          (x ^ (1 / 2 : ℝ)) ^ 2 := by rw [pow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
      _ = x := by
        have hhalf : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [hhalf, ENNReal.rpow_one]
  have hsq : mean ^ 2 ≤ μ A * second := by
    have hmul := mul_le_mul hHolder' hHolder' (by positivity) (by positivity)
    calc
      mean ^ 2 = mean * mean := by rw [pow_two]
      _ ≤ ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) ^ 2 := by
        simpa [pow_two] using hmul
      _ = μ A * second := by
        rw [pow_two]
        calc
          ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) *
              ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) =
            ((μ A) ^ (1 / 2 : ℝ) * (μ A) ^ (1 / 2 : ℝ)) *
              (second ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) := by ac_rfl
          _ = μ A * second := by rw [hroot, hroot]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl hsecond_pos.ne') (Or.inl hsecond_top)).2
  simpa [mul_comm] using hsq

/-- The square of a generation-`n + 1` corridor count expands into ordered
pairs of first-generation child subtrees. This is the first split in the
most-recent-common-ancestor decomposition of the paper's second moment. -/
theorem pathGeneration_succ_sq_eq_childPairSum
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ι X) :
    let childCount : ι → ℝ≥0∞ := fun i =>
      survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i
    Spine.pathGeneration φ (n + 1) F x ω ^ 2 =
      ∑' p : ι × ι, childCount p.1 * childCount p.2 := by
  dsimp only
  let childCount : ι → ℝ≥0∞ := fun i =>
    survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n
        (fun tail => F (prependHistory x tail)) (x + y)
        (subtreeStepField [i] ω)) (ω []) i
  rw [Spine.pathGeneration_succ]
  change (∑' i : ι, childCount i) ^ 2 =
    ∑' p : ι × ι, childCount p.1 * childCount p.2
  rw [pow_two]
  calc
    (∑' i : ι, childCount i) * (∑' i : ι, childCount i) =
        ∑' i : ι, childCount i * (∑' j : ι, childCount j) := by
      rw [← ENNReal.tsum_mul_right]
    _ = ∑' i : ι, ∑' j : ι, childCount i * childCount j := by
      apply tsum_congr
      intro i
      rw [← ENNReal.tsum_mul_left]
    _ = ∑' p : ι × ι, childCount p.1 * childCount p.2 :=
      ENNReal.tsum_prod.symm

/-- Split an ordered pair sum into pairs that stay in the same child subtree
and pairs whose paths separate at the first generation. -/
theorem ennreal_tsum_pair_eq_diagonal_add_offDiagonal
    {ι : Type*} [Countable ι] [DecidableEq ι] (f : ι → ℝ≥0∞) :
    (∑' p : ι × ι, f p.1 * f p.2) =
      (∑' i, f i ^ 2) +
        ∑' i, ∑' j, if i ≠ j then f i * f j else 0 := by
  classical
  have hsplit (i j : ι) :
      f i * f j =
        (if i = j then f i * f j else 0) +
          (if i ≠ j then f i * f j else 0) := by
    by_cases h : i = j <;> simp [h]
  have hdiag (i : ι) :
      (∑' j, if i = j then f i * f j else 0) = f i ^ 2 := by
    rw [tsum_eq_single i]
    · simp [pow_two]
    · intro j hj
      simp [Ne.symm hj]
  calc
    (∑' p : ι × ι, f p.1 * f p.2) =
        ∑' i, ∑' j, f i * f j :=
      ENNReal.tsum_prod (f := fun i j => f i * f j)
    _ =
        ∑' i, ((∑' j, if i = j then f i * f j else 0) +
          ∑' j, if i ≠ j then f i * f j else 0) := by
      apply tsum_congr
      intro i
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro j
      exact hsplit i j
    _ = (∑' i, ∑' j, if i = j then f i * f j else 0) +
        ∑' i, ∑' j, if i ≠ j then f i * f j else 0 := ENNReal.tsum_add
    _ = (∑' i, f i ^ 2) +
        ∑' i, ∑' j, if i ≠ j then f i * f j else 0 := by
      congr 1
      apply tsum_congr
      intro i
      exact hdiag i

/-- The generation-`n + 1` corridor count square separates into pairs that
remain in one child subtree and pairs whose paths diverge at the root. -/
theorem pathGeneration_succ_sq_eq_diagonal_add_offDiagonal
    {ι X : Type*} [Countable ι] [DecidableEq ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ι X) :
    let childCount : ι → ℝ≥0∞ := fun i =>
      survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i
    Spine.pathGeneration φ (n + 1) F x ω ^ 2 =
      (∑' i, childCount i ^ 2) +
        ∑' i, ∑' j, if i ≠ j then childCount i * childCount j else 0 := by
  classical
  let childCount : ι → ℝ≥0∞ := fun i =>
    survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n
        (fun tail => F (prependHistory x tail)) (x + y)
        (subtreeStepField [i] ω)) (ω []) i
  change Spine.pathGeneration φ (n + 1) F x ω ^ 2 =
    (∑' i, childCount i ^ 2) +
      ∑' i, ∑' j, if i ≠ j then childCount i * childCount j else 0
  calc
    Spine.pathGeneration φ (n + 1) F x ω ^ 2 =
        ∑' p : ι × ι, childCount p.1 * childCount p.2 := by
          exact pathGeneration_succ_sq_eq_childPairSum φ n F x ω
    _ = (∑' i, childCount i ^ 2) +
        ∑' i, ∑' j, if i ≠ j then childCount i * childCount j else 0 :=
      ennreal_tsum_pair_eq_diagonal_add_offDiagonal childCount

/-- The descendant fields of two distinct first-generation children have the
product law. This is the subtree-independence input for the off-diagonal
terms in the paper's second-moment decomposition. -/
theorem distinct_child_subtreeFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (stepFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
      (stepFieldLaw μ).prod (stepFieldLaw μ) := by
  classical
  let roots : Bool → TreeNode ι := fun b => if b then [i] else [j]
  have hlen : ∀ b, (roots b).length = 1 := by
    intro b
    cases b <;> simp [roots]
  have hinj : Function.Injective roots := by
    intro b c h
    cases b <;> cases c <;> simp_all [roots]
  let pairEval : (Bool → StepField ι X) → StepField ι X × StepField ι X :=
    fun fields => (fields true, fields false)
  have hcomp :
      (fun ω : StepField ι X =>
        (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
      pairEval ∘
        ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots := by
    funext ω
    simp [pairEval, roots,
      ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector]
  have hvector :=
    ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_law
      μ roots hlen hinj
  have hpair := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => stepFieldLaw μ) (i := true) (j := false) (by decide)
  calc
    (stepFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
        ((stepFieldLaw μ).map
          (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots)).map
            pairEval := by
      rw [Measure.map_map (by fun_prop)
        (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable roots)]
      rw [hcomp]
    _ = (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ)).map pairEval := by
      rw [hvector]
    _ = (stepFieldLaw μ).prod (stepFieldLaw μ) := by
      simpa [pairEval] using hpair

/-- The root reproduction step is independent of the two descendant fields
below distinct children; their full joint law is the corresponding triple
product. This is the branching-property law used to average a split pair. -/
theorem root_two_distinct_childFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
      μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
  classical
  let roots : Bool → TreeNode ι := fun b => if b then [i] else [j]
  let vector : StepField ι X → Bool → StepField ι X :=
    ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots
  let rootVector : StepField ι X → Step ι X × (Bool → StepField ι X) :=
    fun ω => (ω [], vector ω)
  let evalPair : (Bool → StepField ι X) → StepField ι X × StepField ι X :=
    fun fields => (fields true, fields false)
  let regroup : Step ι X × (Bool → StepField ι X) →
      Step ι X × (StepField ι X × StepField ι X) :=
    fun p => (p.1, evalPair p.2)
  have hvectorMeas : Measurable vector :=
    ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable roots
  have hrootVectorMeas : Measurable rootVector :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk hvectorMeas
  have hevalPair : Measurable evalPair :=
    (measurable_pi_apply true).prodMk (measurable_pi_apply false)
  have hregroupMeas : Measurable regroup :=
    measurable_fst.prodMk (hevalPair.comp measurable_snd)
  have hlen : ∀ b, (roots b).length = 1 := by
    intro b
    cases b <;> simp [roots]
  have hinj : Function.Injective roots := by
    intro b c h
    cases b <;> cases c <;> simp_all [roots]
  have hvector :=
    ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_law
      μ roots hlen hinj
  have hrootPast : Measurable[generationFiltration
      (M := Step ι X) 1]
      (fun ω : StepField ι X => ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : StepField ι X => ω ([] : TreeNode ι)) vector
      (stepFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_independent
        μ roots hlen) hrootPast.comap_le
  have hrootVector :
      (stepFieldLaw μ).map rootVector =
        μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ)) := by
    unfold rootVector vector
    rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable
        roots).aemeasurable,
      stepFieldLaw_coordinate μ ([] : TreeNode ι), hvector]
  have hinfinitePi := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => stepFieldLaw μ) (i := true) (j := false) (by decide)
  have hregroup :
      (μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))).map regroup =
        μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
    change (μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))).map
      (Prod.map id evalPair) = _
    have hprod := Measure.map_prod_map μ
      (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))
      measurable_id hevalPair
    rw [← hprod, Measure.map_id, hinfinitePi]
  have hcomp :
      (fun ω : StepField ι X => (ω ([] : TreeNode ι),
        (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
      regroup ∘ rootVector := by
    funext ω
    simp [regroup, rootVector, vector, evalPair, roots,
      ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector]
  calc
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
        (stepFieldLaw μ).map (regroup ∘ rootVector) := by rw [hcomp]
    _ = ((stepFieldLaw μ).map rootVector).map regroup :=
      (Measure.map_map hregroupMeas hrootVectorMeas).symm
    _ = μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
      rw [hrootVector, hregroup]

/-- Conditional on the root reproduction step, the two descendant observables
from distinct children factor under their independent subtree fields. -/
theorem lintegral_root_product_distinct_child_subtrees
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (F G : Step ι X → StepField ι X → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F))
    (hG : Measurable (Function.uncurry G)) :
    (∫⁻ ω, F (ω []) (subtreeStepField [i] ω) *
      G (ω []) (subtreeStepField [j] ω) ∂stepFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, F ξ η ∂stepFieldLaw μ) *
        (∫⁻ ζ, G ξ ζ ∂stepFieldLaw μ) ∂μ := by
  let triple : StepField ι X → Step ι X ×
      (StepField ι X × StepField ι X) := fun ω =>
    (ω [], (subtreeStepField [i] ω, subtreeStepField [j] ω))
  let H : Step ι X × (StepField ι X × StepField ι X) → ℝ≥0∞ :=
    fun p => F p.1 p.2.1 * G p.1 p.2.2
  have hTriple : Measurable triple :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk
      ((subtreeStepField_measurable [i]).prodMk
        (subtreeStepField_measurable [j]))
  have hH : Measurable H := by
    exact (hF.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hG.comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc
    (∫⁻ ω, F (ω []) (subtreeStepField [i] ω) *
        G (ω []) (subtreeStepField [j] ω) ∂stepFieldLaw μ) =
        ∫⁻ p, H p ∂(stepFieldLaw μ).map triple := by
      exact (lintegral_map hH hTriple).symm
    _ = ∫⁻ p, H p ∂μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
      rw [root_two_distinct_childFields_joint_law μ i j hij]
    _ = ∫⁻ ξ, (∫⁻ η, F ξ η ∂stepFieldLaw μ) *
          (∫⁻ ζ, G ξ ζ ∂stepFieldLaw μ) ∂μ := by
      rw [lintegral_prod H hH.aemeasurable]
      apply lintegral_congr
      intro ξ
      change (∫⁻ p, F ξ p.1 * G ξ p.2 ∂
        (stepFieldLaw μ).prod (stepFieldLaw μ)) = _
      exact lintegral_prod_mul
        (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
        (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Specialization of the split-pair factorization to the path counts in the
first-generation decomposition. This is the off-diagonal term for the
generation-`n + 1` second moment. -/
theorem lintegral_pathGeneration_childProduct_eq
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i j : ℕ) (hij : i ≠ j) :
    (∫⁻ ω, survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i *
      survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [j] ω)) (ω []) j ∂stepFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i
          ∂stepFieldLaw μ) *
        (∫⁻ ζ, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) ζ) ξ j
          ∂stepFieldLaw μ) ∂μ := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  let childObservable (k : ℕ) : Step ℕ X → StepField ℕ X → ℝ≥0∞ :=
    fun ξ η => survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n tailTest (x + y) η) ξ k
  have hchildObservable (k : ℕ) :
      Measurable (Function.uncurry (childObservable k)) := by
    unfold childObservable survivingPotentialTest
    exact ((Spine.pathGeneration_joint_measurable φ n htailTest).comp
      (((measurable_const.add
        ((Step.potentialValue'_measurable φ k).comp measurable_fst))).prodMk
          measurable_snd)).ite
      ((survive_measurableSet k).preimage measurable_fst)
      measurable_const
  have hfactor := lintegral_root_product_distinct_child_subtrees
    μ i j hij (childObservable i) (childObservable j)
    (hchildObservable i) (hchildObservable j)
  simpa [tailTest, childObservable] using hfactor

/-- The diagonal term in the generation-`n + 1` second moment is the root-step
average of the squared generation-`n` child count. -/
theorem lintegral_pathGeneration_childSquare_eq
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i : ℕ) :
    (∫⁻ ω, (survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i) ^ 2 ∂stepFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, (survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i) ^ 2
        ∂stepFieldLaw μ ∂μ := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  let childObservable : Step ℕ X → StepField ℕ X → ℝ≥0∞ := fun ξ η =>
    survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n tailTest (x + y) η) ξ i
  have hchildObservable :
      Measurable (Function.uncurry childObservable) := by
    unfold childObservable survivingPotentialTest
    exact ((Spine.pathGeneration_joint_measurable φ n htailTest).comp
      (((measurable_const.add
        ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
          measurable_snd)).ite
      ((survive_measurableSet i).preimage measurable_fst)
      measurable_const
  have hsquare : Measurable (fun p : Step ℕ X × StepField ℕ X =>
      childObservable p.1 p.2 ^ 2) := by
    exact hchildObservable.pow_const 2
  have hfactor := lintegral_root_subtreeFunction_eq μ i
    (fun p : Step ℕ X × StepField ℕ X => childObservable p.1 p.2 ^ 2)
    hsquare
  simpa [tailTest, childObservable] using hfactor

/-- Exact first-generation second-moment recursion for a corridor path
count. The diagonal term keeps a single child subtree; distinct children
factor into the product of their conditional first moments. -/
theorem lintegral_pathGeneration_succ_sq_eq_childPairRecursion
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
      ∂stepFieldLaw μ) =
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n F x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
      ∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
              ∂stepFieldLaw μ) *
          (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
              ∂stepFieldLaw μ) ∂μ else 0 := by
  let childCount : ℕ → StepField ℕ X → ℝ≥0∞ := fun i ω =>
    pathGenerationChildObservable φ n F x i (ω [])
      (subtreeStepField [i] ω)
  have hchildCount (i : ℕ) : Measurable (childCount i) := by
    unfold childCount
    exact (pathGenerationChildObservable_measurable φ n F hF x i).comp
      ((measurable_pi_apply ([] : TreeNode ℕ)).prodMk
        (subtreeStepField_measurable [i]))
  have hdiagSum : Measurable (fun ω => ∑' i, (childCount i ω) ^ 2) := by
    apply Measurable.tsum
    intro i
    exact (hchildCount i).pow_const 2
  have hoffTerm (i j : ℕ) :
      Measurable (fun ω => if i ≠ j then childCount i ω * childCount j ω else 0) := by
    by_cases hij : i ≠ j
    · simp only [if_pos hij]
      change Measurable (childCount i * childCount j)
      exact (hchildCount i).mul (hchildCount j)
    · simp [hij]
  have hoffInner (i : ℕ) :
      Measurable (fun ω => ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ω => ∑' i, ∑' j, if i ≠ j then
      childCount i ω * childCount j ω else 0) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  have hdiagIntegral :
      (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂stepFieldLaw μ) =
        ∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro i
    exact ((hchildCount i).pow_const 2).aemeasurable
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ω, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ) =
        ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ) =
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hoffInnerIntegral i
    · intro i
      exact (hoffInner i).aemeasurable
  have hpoint (ω : StepField ℕ X) :
      (Spine.pathGeneration φ (n + 1) F x ω) ^ 2 =
        (∑' i, (childCount i ω) ^ 2) +
          ∑' i, ∑' j, if i ≠ j then
            childCount i ω * childCount j ω else 0 := by
    simpa [childCount, pathGenerationChildObservable] using
      (pathGeneration_succ_sq_eq_diagonal_add_offDiagonal φ n F x ω)
  calc
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
        ∂stepFieldLaw μ) =
        ∫⁻ ω, (∑' i, (childCount i ω) ^ 2) +
          (∑' i, ∑' j, if i ≠ j then
            childCount i ω * childCount j ω else 0) ∂stepFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact hpoint ω
    _ = (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂stepFieldLaw μ) +
        ∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
      rw [lintegral_add_left' hdiagSum.aemeasurable]
    _ = (∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂stepFieldLaw μ) +
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
      rw [hdiagIntegral, hoffIntegral]
    _ = (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        ∑' i, ∑' j, if i ≠ j then
          ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
                ∂stepFieldLaw μ) *
            (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
                ∂stepFieldLaw μ) ∂μ else 0 := by
      congr 1
      · apply tsum_congr
        intro i
        simpa [childCount, pathGenerationChildObservable] using
          (lintegral_pathGeneration_childSquare_eq φ μ n F hF x i)
      · apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        by_cases hij : i ≠ j
        · simpa [childCount, pathGenerationChildObservable, hij] using
            (lintegral_pathGeneration_childProduct_eq φ μ n F hF x i j hij)
        · simp [hij]

/-- One generation of the paper's second-moment recursion, with the
off-diagonal MRCA contribution bounded by the cross-child exponential moment.
The diagonal term remains as the next recursive second moment. -/
theorem lintegral_pathGeneration_succ_sq_le_diagonal_add_crossWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x ω) ^ 2
      ∂stepFieldLaw μ) ≤
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator fun _ => (1 : ℝ≥0∞)
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hrec := lintegral_pathGeneration_succ_sq_eq_childPairRecursion
    φ μ n F hF x
  have hcross := lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal
    window q hfirst hprob
  calc
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
        ∂stepFieldLaw μ) =
        (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        ∑' i, ∑' j, if i ≠ j then
          ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
                ∂stepFieldLaw μ) *
            (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
                ∂stepFieldLaw μ) ∂μ else 0 := hrec
    _ ≤ (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
      apply add_le_add_right
      simpa [F] using hcross

/-- The first-generation second-moment recursion for the paper's affine tube
with a terminal endpoint cutoff. A probability estimate for the uncut tube
also bounds its endpoint-restricted version by monotonicity. -/
theorem lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x lower drift width endpointUpper : ℝ)
    (q : ℝ≥0∞)
    (hprob : ∀ y : ℝ,
      x + y ∈ affineCorridorFirstWindow lower drift width →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            affineCorridorHistory n lower drift width} ≤ q) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
        fun _ => (1 : ℝ≥0∞)) x ω) ^ 2 ∂stepFieldLaw μ) ≤
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
            fun _ => (1 : ℝ≥0∞)) x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (endpointUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let window := affineCorridorFirstWindow lower drift width
  have hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window := by
    intro history hhistory
    exact affineCorridorHistoryEndpointCutoff_firstWindow
      n lower drift width endpointUpper history hhistory
  have hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ endpointUpper := by
    intro history hhistory
    exact affineCorridorHistoryEndpointCutoff_terminalUpper
      n lower drift width endpointUpper history hhistory
  have hprobCut : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q := by
    intro y hy
    apply le_trans (measure_mono ?_) (hprob y hy)
    intro increment hincrement
    exact hincrement.1
  exact lintegral_pathGeneration_succ_sq_le_diagonal_add_crossWeight
    φ μ hboundary n x endpointUpper corridor
    (measurableSet_affineCorridorHistoryEndpointCutoff
      n lower drift width endpointUpper)
    hterminal window q hfirst hprobCut

/-- Integrals of products of observables in distinct child subtrees factor.
This is the analytic form of the off-diagonal branching property. -/
theorem lintegral_mul_distinct_child_subtrees_eq_product
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (f g : StepField ι X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
      ∂stepFieldLaw μ) =
      (∫⁻ ω, f ω ∂stepFieldLaw μ) * ∫⁻ ω, g ω ∂stepFieldLaw μ := by
  let pair : StepField ι X → StepField ι X × StepField ι X := fun ω =>
    (subtreeStepField [i] ω, subtreeStepField [j] ω)
  have hpair : Measurable pair :=
    (subtreeStepField_measurable [i]).prodMk
      (subtreeStepField_measurable [j])
  have hproduct : Measurable (fun p : StepField ι X × StepField ι X =>
      f p.1 * g p.2) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
        ∂stepFieldLaw μ) =
        ∫⁻ p, f p.1 * g p.2 ∂(stepFieldLaw μ).map pair := by
      exact (lintegral_map hproduct hpair).symm
    _ = (∫⁻ ω, f ω ∂stepFieldLaw μ) *
          ∫⁻ ω, g ω ∂stepFieldLaw μ := by
      rw [show pair = fun ω : StepField ι X =>
        (subtreeStepField [i] ω, subtreeStepField [j] ω) from rfl,
        distinct_child_subtreeFields_joint_law μ i j hij]
      exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable

/-- A corridor contains a surviving generation-`n` path exactly when the
unweighted corridor path count is nonzero. -/
theorem pathGeneration_ne_zero_iff_hasPathHistoryIn
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (initial : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (ω : StepField ℕ X) :
    Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ≠ 0 ↔
      ω ∈ hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
  classical
  constructor
  · intro hcount
    by_contra hpath
    have hterms (u : TreeNode ℕ) :
        Spine.pathGenerationTerm φ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 0 := by
      by_cases hu : u.length = n
      · by_cases hs : surviveAlong ω [] u
        · have hnot : Spine.pathHistory φ n initial ω u ∉ corridor := by
            intro hmem
            exact hpath ⟨u, hu, hs, hmem⟩
          simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hnot]
        · simp [Spine.pathGenerationTerm, hu, hs]
      · simp [Spine.pathGenerationTerm, hu]
    have hzero : Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω = 0 := by
      unfold Spine.pathGeneration
      rw [ENNReal.tsum_eq_zero]
      exact hterms
    exact hcount hzero
  · rintro ⟨u, hu, hs, hcorridor⟩
    have hterm : Spine.pathGenerationTerm φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 1 := by
      simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hcorridor]
    have hle : 1 ≤ Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω := by
      unfold Spine.pathGeneration
      calc
        1 = Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ℕ, Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω :=
          ENNReal.le_tsum (f := fun p => Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω) u
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)

/-- Paley--Zygmund converts first and second moment estimates for the
generation-`n` corridor path count into a lower bound on one-root tube
success. This is the probability step used in the paper's long-corridor
estimate. -/
theorem measure_hasPathHistoryIn_ge_of_pathGeneration_moments
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) := by
  let Xcount : StepField ℕ X → ℝ≥0∞ := fun ω =>
    Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
  have hX : Measurable Xcount := Spine.pathGeneration_measurable φ n
    (measurable_const.indicator hcorridor) initial
  have hPZ := measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    (stepFieldLaw μ) Xcount hX mean second hmean hsecond
    hsecond_pos hsecond_top
  have hsupport : {ω : StepField ℕ X | Xcount ω ≠ 0} =
      hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
    ext ω
    exact pathGeneration_ne_zero_iff_hasPathHistoryIn
      φ n initial corridor ω
  simpa [Xcount, hsupport] using hPZ

/-- Quantitative one-step Paley--Zygmund estimate for offspring entering a
bounded-below position window. -/
theorem measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I) :
    (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ≤
      μ {ξ | hasPotentialChildIn φ I ξ} := by
  let p : ℝ≥0∞ := tiltedPotentialLaw φ (-1) μ I
  let c : ℝ≥0∞ := ∫⁻ ξ, crossChildWeight φ ξ ∂μ
  let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a)) * p + c
  have htilted : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  have hp : 0 < p := hpositive
  have hp_top : p ≠ ∞ := measure_ne_top (tiltedPotentialLaw φ (-1) μ) I
  have hc_top : c ≠ ∞ := hcross
  have hcoef_pos : 0 < ENNReal.ofReal (Real.exp (-a)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hd_pos : 0 < d := by
    dsimp [d, p, c]
    exact lt_of_lt_of_le
      (ENNReal.mul_pos (ne_of_gt hcoef_pos) (ne_of_gt hpositive))
      (le_add_right le_rfl)
  have hd_top : d ≠ ∞ := by
    dsimp [d, p, c]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top, hc_top⟩
  have hq := tiltedWindowProbability_le_sqrt_success_mul_secondMoment
    φ I a hI hlower μ
  have hroot (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [pow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
      _ = x := by
        have hhalf : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [hhalf, ENNReal.rpow_one]
  have hmul :
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
        ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ)) =
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    calc
      _ = ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ)) *
          (d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ)) := by ac_rfl
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
        rw [hroot, hroot]
  have hsq : p ^ 2 ≤
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    have hsquare := mul_le_mul hq hq (by positivity) (by positivity)
    calc
      p ^ 2 = p * p := by rw [pow_two]
      _ ≤ (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
          ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            d ^ (1 / 2 : ℝ)) := by
          simpa [p, d, mul_assoc] using hsquare
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := hmul
  have hq : p ^ 2 / d ≤ μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl hd_pos.ne') (Or.inl hd_top)).2
    simpa [mul_comm] using hsq
  have hsuccess :
      μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} =
        μ {ξ | hasPotentialChildIn φ I ξ} := by
    congr 1
    ext ξ
    exact (weightedOffspringWindowMass_ne_zero_iff φ I ξ)
  simpa [p, d, hsuccess] using hq

/-- Under the finite-root product law, the probability that every initial root
fails to produce a child in `I` is the `m`th power of the one-root failure
probability. -/
theorem measure_noRootHasPotentialChildIn_eq_pow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ)
        {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])}) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  have hE : MeasurableSet E := by
    exact (measurableSet_hasPotentialChildIn φ I hI).preimage
      (measurable_pi_apply ([] : TreeNode ℕ))
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (stepFieldLaw μ) Eᶜ := by
    rw [← Measure.map_apply (measurable_pi_apply r) hE.compl]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have hfactor :=
    (finiteRootStepFieldLaw_roots_independent μ m).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun _ : Fin m => Eᶜ)
      (by intro r hr; exact hE.compl)
  have hset :
      (⋂ r ∈ Finset.univ,
          (fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} := by
    ext field
    simp [E]
  rw [hset] at hfactor
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hprod :
      (∏ r ∈ Finset.univ,
          (finiteRootStepFieldLaw μ m)
            ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  rw [hnot] at hfactor
  exact hfactor

/-- The independent initial roots all miss a measurable one-root event with
probability equal to the one-root failure probability raised to the number of
roots.  The event may inspect the entire pre-sampled descendant field of a
root, so this is the independence interface needed for multi-generation tube
success events as well as one-generation hits. -/
theorem measure_allRootsAvoidStepFieldEvent_eq_pow
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (stepFieldLaw μ) Eᶜ := by
    rw [← Measure.map_apply (measurable_pi_apply r) hE.compl]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have hfactor :=
    (finiteRootStepFieldLaw_roots_independent μ m).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun _ : Fin m => Eᶜ)
      (by intro r hr; exact hE.compl)
  have hset :
      (⋂ r ∈ Finset.univ,
        (fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        {field : FiniteRootStepField m ℕ X | ∀ r : Fin m, field r ∉ E} := by
    ext field
    simp
  rw [hset] at hfactor
  have hprod :
      (∏ r ∈ Finset.univ,
        (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  exact hfactor

/-- If one initial root has probability at least `p` of a measurable event
in its whole descendant field, then the chance that all `m` independent
roots miss the event is at most `exp (-m * p)`. -/
theorem measure_allRootsAvoidStepFieldEvent_le_exp
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ) E).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  let q : ℝ≥0∞ := (stepFieldLaw μ) E
  have hqtop : q ≠ ∞ := measure_ne_top _ _
  have hpq : ENNReal.ofReal p ≤ q := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal q.toReal :=
        ENNReal.ofReal_le_ofReal hprob
      _ = q := ENNReal.ofReal_toReal hqtop
  have hfailure :
      (stepFieldLaw μ) Eᶜ ≤ 1 - ENNReal.ofReal p := by
    have hcompl := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := ENNReal.ofReal p) (s := E)
      (by simpa [q] using hpq) hE
    exact hcompl
  have hbase :
      1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    simpa using (ENNReal.ofReal_sub 1 hp).symm
  have hexp : (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
    calc
      (1 - p) ^ m ≤ (Real.exp (-p)) ^ m :=
        pow_le_pow_left₀ (sub_nonneg.mpr hp_one) (Real.one_sub_le_exp_neg p) m
      _ = Real.exp (-(m : ℝ) * p) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hpow :
      (ENNReal.ofReal (1 - p)) ^ m ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
    calc
      (ENNReal.ofReal (1 - p)) ^ m = ENNReal.ofReal ((1 - p) ^ m) :=
        (ENNReal.ofReal_pow (sub_nonneg.mpr hp_one) m).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) :=
        ENNReal.ofReal_le_ofReal hexp
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m :=
        measure_allRootsAvoidStepFieldEvent_eq_pow μ E hE m
    _ ≤ (1 - ENNReal.ofReal p) ^ m :=
      pow_le_pow_left₀ (by positivity) hfailure m
    _ = (ENNReal.ofReal (1 - p)) ^ m := by rw [hbase]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := hpow

/-- Exponential extinction bound for independent roots when success means
that the root's branching field contains a surviving generation-`n` path in
a prescribed measurable history corridor. -/
theorem measure_allRootsAvoidPathHistoryIn_le_exp
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ)
      (hasPathHistoryIn (ι := ℕ) φ n initial corridor)).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  exact measure_allRootsAvoidStepFieldEvent_le_exp μ _
    (measurableSet_hasPathHistoryIn φ n initial corridor hcorridor)
    m p hp hp_one hprob

/-- Combining the path-count Paley--Zygmund bound with independent roots:
first and second moment estimates for one root give an exponential bound on
the probability that every initial root misses the corridor. -/
theorem measure_allRootsAvoidPathHistoryIn_le_exp_of_pathGeneration_moments
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp
        (-(m : ℝ) * (mean ^ 2 / second).toReal)) := by
  let E : Set (StepField ℕ X) :=
    hasPathHistoryIn (ι := ℕ) φ n initial corridor
  let q : ℝ≥0∞ := mean ^ 2 / second
  have hE : MeasurableSet E :=
    measurableSet_hasPathHistoryIn φ n initial corridor hcorridor
  have hsuccess : q ≤ (stepFieldLaw μ) E := by
    dsimp [q, E]
    exact measure_hasPathHistoryIn_ge_of_pathGeneration_moments
      φ μ n initial corridor hcorridor mean second hmean hsecond
      hsecond_pos hsecond_top
  have hqtop : q ≠ ∞ := ne_top_of_le_ne_top
    (measure_ne_top (stepFieldLaw μ) E) hsuccess
  have hqle : q ≤ 1 := by
    calc
      q ≤ (stepFieldLaw μ) E := hsuccess
      _ ≤ (stepFieldLaw μ) Set.univ := measure_mono (Set.subset_univ E)
      _ = 1 := measure_univ
  have hprob : q.toReal ≤ ((stepFieldLaw μ) E).toReal :=
    ENNReal.toReal_mono (measure_ne_top (stepFieldLaw μ) E) hsuccess
  have hp_one : q.toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hqtop ENNReal.one_ne_top).2 hqle
  have hroots := measure_allRootsAvoidStepFieldEvent_le_exp
    μ E hE m q.toReal ENNReal.toReal_nonneg hp_one hprob
  simpa [E, q] using hroots

/-- A one-generation upper bound for all-root failure.  Its one-root success
probability is bounded below from the actual offspring law by the
second-moment estimate. -/
theorem measure_noRootHasPotentialChildIn_le_secondMomentPower
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I)
    (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  let A : Set (Step ℕ X) := {ξ | hasPotentialChildIn φ I ξ}
  have hA : MeasurableSet A := measurableSet_hasPotentialChildIn φ I hI
  have hE : MeasurableSet E := by
    exact hA.preimage (measurable_pi_apply ([] : TreeNode ℕ))
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hmap : (stepFieldLaw μ) E = μ A := by
    rw [show E = (fun ω : StepField ℕ X => ω []) ⁻¹' A by rfl]
    rw [← Measure.map_apply (measurable_pi_apply ([] : TreeNode ℕ)) hA]
    rw [stepFieldLaw_coordinate μ []]
  have hhit := measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    φ I a hI hlower μ hboundary hcross hpositive
  have hprob :
      (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≤ μ A := by
    simpa [A] using hhit
  have hmiss :
      (stepFieldLaw μ) Eᶜ ≤
        1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
          (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
            ∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
    have hmiss' := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := μ A) (s := E)
      (by rw [hmap]) hE
    exact hmiss'.trans (tsub_le_tsub_left hprob 1)
  have hformula := measure_noRootHasPotentialChildIn_eq_pow φ I hI μ m
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
        rw [hformula]
        rw [← hnot]
    _ ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m :=
      pow_le_pow_left₀ (by positivity) hmiss m

/-- First-moment bound for the number of surviving particles whose complete
ancestral history lies in a measurable corridor. This is the form of the
many-to-one estimate used with Markov's inequality for a killed population. -/
theorem lintegral_pathGeneration_le_exp_mul_spineProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
      corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage
      (ProbabilityTheory.RandomWalk.history_measurable n initial)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hterminalPath (increment : ℕ → ℝ) (hevent : increment ∈ spineEvent) :
      AdditivePath.displacement n increment ≤ terminalUpper - initial := by
    have h := hterminal
      (ProbabilityTheory.RandomWalk.history n initial increment)
      (by simpa [spineEvent] using hevent)
    rw [ProbabilityTheory.RandomWalk.history_last,
      AdditivePath.fromIncrements_apply] at h
    linarith
  calc
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (ProbabilityTheory.RandomWalk.history n initial increment)
          ∂tiltedIncrementFieldLaw φ μ :=
      Spine.pathManyToOneCore φ μ hboundary n hF initial
    _ ≤ ∫⁻ increment,
          ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
          ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      change ENNReal.ofReal
          (Real.exp (AdditivePath.displacement n increment)) *
          F (ProbabilityTheory.RandomWalk.history n initial increment) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
          spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
      by_cases hevent : increment ∈ spineEvent
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor := by
          simpa [spineEvent] using hevent
        have hexp : ENNReal.ofReal
              (Real.exp (AdditivePath.displacement n increment)) ≤
            ENNReal.ofReal (Real.exp (terminalUpper - initial)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hterminalPath increment hevent))
        have hFval :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 1 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 1
          rw [Set.indicator_of_mem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        rw [hFval, hindicator]
        simpa using hexp
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∉
            corridor := by
          intro h
          exact hevent (by simpa [spineEvent] using h)
        have hFzero :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 0 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 0
          rw [Set.indicator_of_notMem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        rw [hFzero, hindicator]
        simp
    _ = ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [lintegral_const_mul _ (measurable_const.indicator hspineEvent)]
      rw [lintegral_indicator_const hspineEvent]
      simp

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail
