/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Decomposition
/-!
# Quantitative terminal failure decomposition

The predictable-root estimate bounds the second term in the terminal failure
decomposition by its explicit independent-subtree exponential.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

@[expose] public section

/-- For the varying first and second stage horizons, terminal
extinction is bounded by the low-root probability plus the explicit
second-stage all-failure exponential. The remaining work is to bound the
first term and combine this killed-process estimate with the capacity event. -/
theorem eventually_measure_rightTailPositiveAKilledTerminalEmpty_le
    (m K : ℕ) (hKm : K ≤ m)
    (ell ellN : ℕ → ℕ) (logN : ℕ → ℝ) (b v c κ : ℝ)
    (hEll : ∀ n, 0 < ell n) (hEllN : ∀ n, ell n ≤ ellN n)
    (hstart : ∀ n, 0 ≤ b * logN n)
    (hD : Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ)) atTop atTop)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma : ℝ}
    (hν : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (hκ : 0 ≤ κ) (hc : 0 < c) (hv : 0 < v)
    (hκv : κ / c ^ 2 < v)
    (hterminal : κ / c ^ 2 ≤ 2 * v / 5)
    (hentranceWidth : (5 * (κ / c ^ 2) + v) / 2 ≤ c)
    (hK : 0 < K) :
    let P : ℕ → RestartedPopulation m := fun n =>
      rightTailPositiveAKilledPopulation m (ell n) (ellN n) (logN n) b v c κ
    let hP : ∀ n, (P n).FiniteSlices := fun n =>
      rightTailPositiveAKilledPopulation_finiteSlices
        m (ell n) (ellN n) (logN n) b v c κ
    let A : ℕ → Set (RestartedField m) :=
      fun n => rightTailSecondStageEnoughRoots (K := K) P hP ell n
    ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          {field | ¬ ((P n) (ellN n) field).Nonempty} ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K : ℝ) *
                (rightTailPositiveASecondStagePZMean μ
                  (ellN n - ell n) κ c v).toReal / 4))) := by
  classical
  dsimp
  let P : ℕ → RestartedPopulation m := fun n =>
    rightTailPositiveAKilledPopulation m (ell n) (ellN n) (logN n) b v c κ
  let hP : ∀ n, (P n).FiniteSlices := fun n =>
    rightTailPositiveAKilledPopulation_finiteSlices
      m (ell n) (ellN n) (logN n) b v c κ
  let D : ℕ → ℕ := fun n => ellN n - ell n
  let A : ℕ → Set (RestartedField m) :=
    fun n => rightTailSecondStageEnoughRoots (K := K)
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  let chosen : ℕ → RestartedField m → Fin K → RootIndexed.TreeNode (Fin m) ℕ :=
    fun n => rightTailSecondStageRoots hKm
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  have havoid :=
    eventually_measure_rightTailSecondStageEnoughRoots_allAvoid_le
      (hKm := hKm) P hP (D := D) (generation := ell) hD μ
      hboundary hcross hν hsigma hκ hc hv hκv hterminal hentranceWidth hK
  obtain ⟨_entryQ, _hentryQ, _C, _hC, _bridgeQ, _hbridgeQ, _amplitude,
      _hamplitude, havoid⟩ := havoid
  filter_upwards [havoid] with n havoidN
  have hdecomp :=
    measure_rightTailPositiveAKilledTerminalEmpty_le
      m K (ell n) (ellN n) hKm (logN n) b v c κ
      (hEll n) (hEllN n) (hstart n) μ hboundary
  have havoid' :
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
            rightTailPositiveASecondStageFailureEvent K (D n) κ c v) ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
          ENNReal.ofReal (Real.exp
            (-((K : ℝ) *
              (rightTailPositiveASecondStagePZMean μ (D n) κ c v).toReal /
                4))) := by
    have hAeq :
        rightTailSecondStageEnoughRoots (K := K) P hP ell n = A n := by
      simp [A, rightTailSecondStageEnoughRoots]
    have hchoeq :
        rightTailSecondStageRoots hKm P hP ell n = chosen n := by
      funext field i
      simp [chosen, rightTailSecondStageRoots]
    rw [hAeq, hchoeq] at havoidN
    simpa [D] using havoidN
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        {field | ¬ ((P n) (ellN n) field).Nonempty} ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ)
            (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
              rightTailPositiveASecondStageFailureEvent K (D n) κ c v) := by
          simpa [P, hP, A, chosen, D, rightTailPositiveAKilledPopulation,
            rightTailSecondStageEnoughRoots, rightTailSecondStageRoots] using hdecomp
    _ ≤ (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K : ℝ) *
                (rightTailPositiveASecondStagePZMean μ (D n) κ c v).toReal /
                  4))) := by
            gcongr

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
