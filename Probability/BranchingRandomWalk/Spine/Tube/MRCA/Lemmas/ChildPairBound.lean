/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Assumptions.CrossWeight
import Probability.BranchingRandomWalk.Assumptions.Structural
import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess

/-!
# Proof lemmas for cross-child continuation bounds

## Internal proof declarations


This proof-support module provides the two cross-module estimates needed by
`MRCA/ChildPairBound.lean`. First, if every shifted spine corridor event has
probability at most $q$ on the specified first-step window, then a child's
continuation mean is at most
$e^{u-x}q$ times its realized exponential weight. Second, if each child mean
is at most $K$ times that weight, the ordered off-diagonal sum is at most
$K^2$ times the cross-child exponential weight.

These steps support the root-split estimate in Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (master's thesis,
Fudan University, 2026), Chapter 4, Lemma 4.5. The intermediate conditional
observable calculations are private to this proof chain.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The conditional first moment of one child continuation is the spine
many-to-one integral, provided that child is present. -/
private lemma lintegral_pathGenerationChildObservable_eq_manyToOne
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂offspringFieldLaw μ) =
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
        ∂offspringFieldLaw μ) =
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

/-- The terminal cutoff in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 4, Lemma 4.5, bounds a child's continuation moment by the
exponential terminal weight times the corresponding spine corridor
probability. -/
private lemma lintegral_pathGenerationChildObservable_le_endpoint_weight
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
      ∂offspringFieldLaw μ) ≤
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
  · simp only [survivingPotentialTest, ite_eq_left hi]
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
private lemma shiftedCorridorProbability_le_of_firstWindow
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
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
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
private lemma lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
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
      ∂offspringFieldLaw μ) ≤
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

/-- The child moment estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.5, needs the uniform corridor
probability only for child positions that lie in the tube at the first time
step. -/
lemma lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
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
      ∂offspringFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
          realizedPotentialWeight φ (-1) ξ i := by
  exact lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal q
    (shiftedCorridorProbability_le_of_firstWindow φ μ n x corridor window q
      hfirst hprob) i ξ

/-- If each child continuation mean is bounded by a common factor times its
realized exponential weight, then the ordered off-diagonal pair sum is
bounded by the cross-child weight. -/
lemma ennreal_tsum_offDiagonal_mul_le_crossPotentialWeight_of_childMomentBound
    {X : Type*} [MeasurableSpace X] [Countable ℕ]
    (φ : Potential X) (ξ : Step ℕ X) (K : ℝ≥0∞)
    (m : ℕ → ℝ≥0∞)
    (hm : ∀ i, m i ≤ K * realizedPotentialWeight φ (-1) ξ i) :
    (∑' i, ∑' j, if i ≠ j then m i * m j else 0) ≤
      K ^ 2 * crossPotentialWeight φ (-1) ξ := by
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
    _ = K ^ 2 * crossPotentialWeight φ (-1) ξ := by
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
          crossPotentialWeight φ (-1) ξ := by
        rw [← crossPotentialWeight_real_neg_one_eq_sum φ ξ]
      change (∑' i, ∑' j, K ^ 2 * fLeft i j) =
        K ^ 2 * crossPotentialWeight φ (-1) ξ
      calc
        _ = K ^ 2 * (∑' i, ∑' j, fLeft i j) := hsumLeft
        _ = K ^ 2 * (∑' i, ∑' j, fRight i j) := by rw [hpairEq]
        _ = K ^ 2 * crossPotentialWeight φ (-1) ξ := by rw [hcross]

end ProbabilityTheory.BranchingRandomWalk.Spine
