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
`eventually_measure_positiveASelectedBRWTerminalEmpty_le` combines the
terminal-failure decomposition with the second-stage all-avoid estimate. Under
the hypotheses in the theorem, eventually
\[
\mathbb P(\text{terminal selected BRW population empty})
\le \mathbb P(A_n^c)+\mathbb P(A_n)
   \exp\!\left(-\frac{K_n}{4}\,
   \operatorname{toReal}(\operatorname{PZMean}(D_n,\kappa,c,v))\right),
\]
where (K_n=K(n)), `Aₙ` is the event that at least `K n` roots reach the
second-stage starting generation, and (D_n=ell_N(n)-ell(n)). The hypotheses
include (K_n\le m) for every (n), eventual positivity of (K_n),
`D n → ∞`, finite cross weight, boundary normalization, centered second
moment with positive variance, and the parameter inequalities used by the
entrance and bridge estimates.

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
first term and combine this selected-process estimate with the capacity event. -/
theorem eventually_measure_positiveASelectedBRWTerminalEmpty_le
    (m : ℕ) (K : ℕ → ℕ) (hKm : ∀ n, K n ≤ m)
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
    (hK : ∀ᶠ n : ℕ in atTop, 0 < K n) :
    let P : ℕ → RestartedPopulation m := fun n =>
      positiveASelectedBRWPopulation m (ell n) (ellN n) (logN n) b v c κ
    let hP : ∀ n, (P n).FiniteSlices := fun n =>
      positiveASelectedBRWPopulation_finiteSlices
        m (ell n) (ellN n) (logN n) b v c κ
    let A : ℕ → Set (RestartedField m) :=
      fun n => secondStageEnoughRoots (K := K n) P hP ell n
    ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          {field | ¬ ((P n) (ellN n) field).Nonempty} ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K n : ℝ) *
                (positiveASecondStagePZMean μ
                  (ellN n - ell n) κ c v).toReal / 4))) := by
  classical
  dsimp
  let P : ℕ → RestartedPopulation m := fun n =>
    positiveASelectedBRWPopulation m (ell n) (ellN n) (logN n) b v c κ
  let hP : ∀ n, (P n).FiniteSlices := fun n =>
    positiveASelectedBRWPopulation_finiteSlices
      m (ell n) (ellN n) (logN n) b v c κ
  let D : ℕ → ℕ := fun n => ellN n - ell n
  let A : ℕ → Set (RestartedField m) :=
    fun n => secondStageEnoughRoots (K := K n)
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  let chosen : ∀ n, RestartedField m → Fin (K n) →
      RootIndexed.TreeNode (Fin m) ℕ :=
    fun n => secondStageRoots (hKm n)
      (fun _ : ℕ => P n) (fun _ : ℕ => hP n) (fun _ => ell n) 0
  have havoid :=
    eventually_measure_secondStageEnoughRoots_allAvoid_le
      (m := m) (K := K) (hKm := hKm)
      P hP (D := D) (generation := ell) hD μ
      hboundary hcross hν hsigma hκ hc hv hκv hterminal hentranceWidth
      hK
  obtain ⟨_entryQ, _hentryQ, _C, _hC, _bridgeQ, _hbridgeQ, _amplitude,
      _hamplitude, havoid⟩ := havoid
  filter_upwards [havoid] with n havoidN
  have hdecomp :=
    measure_positiveASelectedBRWTerminalEmpty_le
      m (K n) (ell n) (ellN n) (hKm n) (logN n) b v c κ
      (hEll n) (hEllN n) (hstart n) μ hboundary
  have havoid' :
      (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
            positiveASecondStageFailureEvent (K n) (D n) κ c v) ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
          ENNReal.ofReal (Real.exp
            (-((K n : ℝ) *
              (positiveASecondStagePZMean μ (D n) κ c v).toReal /
                4))) := by
    have hAeq :
        secondStageEnoughRoots (K := K n) P hP ell n = A n := by
      simp [A, secondStageEnoughRoots]
    have hchoeq :
        secondStageRoots (hKm n) P hP ell n = chosen n := by
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
              positiveASecondStageFailureEvent (K n) (D n) κ c v) := by
          simpa [P, hP, A, chosen, D, positiveASelectedBRWPopulation,
            secondStageEnoughRoots, secondStageRoots] using hdecomp
    _ ≤ (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n)ᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ) (A n) *
            ENNReal.ofReal (Real.exp
              (-((K n : ℝ) *
                (positiveASecondStagePZMean μ (D n) κ c v).toReal /
                  4))) := by
            gcongr

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
