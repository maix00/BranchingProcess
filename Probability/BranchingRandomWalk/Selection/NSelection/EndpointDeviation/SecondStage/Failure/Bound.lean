/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Selection
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Lemmas.AllAvoid
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Lemmas.Decomposition
/-!
# Quantitative terminal failure decomposition

## Public declarations

In the namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`,
`eventually_measure_positiveAKilledTerminalEmpty_le` combines the
terminal-failure decomposition with the second-stage all-avoid estimate. Under
the hypotheses in the theorem, eventually
\[
\mathbb P(\text{terminal killed population empty})
\le \mathbb P(A_n^c)+\mathbb P(A_n)
   \exp\!\left(-\frac{K}{4}\,
   \operatorname{toReal}(\operatorname{PZMean}(D_n,\kappa,c,v))\right),
\]
where `Aₙ` is the event that at least `K` roots reach the second-stage
starting generation and `Dₙ` is the second-stage duration. The hypotheses
include `D n → ∞`, finite cross weight, boundary normalization, centered
second moment with positive variance, and the parameter inequalities used by
the entrance and bridge estimates.

The predictable-root estimate bounds the second term in the terminal failure
decomposition by its explicit independent-subtree exponential.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

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
theorem eventually_measure_positiveAKilledTerminalEmpty_le
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
      positiveAKilledPopulation m (ell n) (ellN n) (logN n) b v c κ
    let hP : ∀ n, (P n).FiniteSlices := fun n =>
      positiveAKilledPopulation_finiteSlices
        m (ell n) (ellN n) (logN n) b v c κ
    let A : ℕ → Set (RestartedField m) :=
      fun n => secondStageEnoughRoots (K := K) P hP ell n
    ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          {field | ¬ ((P n) (ellN n) field).Nonempty} ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K : ℝ) *
                (positiveASecondStagePZMean μ
                  (ellN n - ell n) κ c v).toReal / 4))) := by
  classical
  dsimp
  let P : ℕ → RestartedPopulation m := fun n =>
    positiveAKilledPopulation m (ell n) (ellN n) (logN n) b v c κ
  let hP : ∀ n, (P n).FiniteSlices := fun n =>
    positiveAKilledPopulation_finiteSlices
      m (ell n) (ellN n) (logN n) b v c κ
  let D : ℕ → ℕ := fun n => ellN n - ell n
  let A : ℕ → Set (RestartedField m) :=
    fun n => secondStageEnoughRoots (K := K)
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  let chosen : ℕ → RestartedField m → Fin K → RootIndexed.TreeNode (Fin m) ℕ :=
    fun n => secondStageRoots hKm
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  have havoid :=
    eventually_measure_secondStageEnoughRoots_allAvoid_le
      (m := m) (K := fun _ => K) (hKm := fun _ => hKm)
      P hP (D := D) (generation := ell) hD μ
      hboundary hcross hν hsigma hκ hc hv hκv hterminal hentranceWidth
      (Filter.Eventually.of_forall fun _ => hK)
  obtain ⟨_entryQ, _hentryQ, _C, _hC, _bridgeQ, _hbridgeQ, _amplitude,
      _hamplitude, havoid⟩ := havoid
  filter_upwards [havoid] with n havoidN
  have hdecomp :=
    measure_positiveAKilledTerminalEmpty_le
      m K (ell n) (ellN n) hKm (logN n) b v c κ
      (hEll n) (hEllN n) (hstart n) μ hboundary
  have havoid' :
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
            positiveASecondStageFailureEvent K (D n) κ c v) ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
          ENNReal.ofReal (Real.exp
            (-((K : ℝ) *
              (positiveASecondStagePZMean μ (D n) κ c v).toReal /
                4))) := by
    have hAeq :
        secondStageEnoughRoots (K := K) P hP ell n = A n := by
      simp [A, secondStageEnoughRoots]
    have hchoeq :
        secondStageRoots hKm P hP ell n = chosen n := by
      funext field i
      simp [chosen, secondStageRoots]
    rw [hAeq, hchoeq] at havoidN
    simpa [D] using havoidN
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        {field | ¬ ((P n) (ellN n) field).Nonempty} ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ)
            (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
              positiveASecondStageFailureEvent K (D n) κ c v) := by
          simpa [P, hP, A, chosen, D, positiveAKilledPopulation,
            secondStageEnoughRoots, secondStageRoots] using hdecomp
    _ ≤ (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K : ℝ) *
                (positiveASecondStagePZMean μ (D n) κ c v).toReal /
                  4))) := by
            gcongr

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
