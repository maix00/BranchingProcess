/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Bound
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.LowCountPower
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Lemmas.PZAssembly
/-!
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAKilledEnoughRootEvent`:
  the event that the first-stage killed population at its cutoff contains at
  least `K` particles.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_measure_rightTailPositiveAKilledEnoughRoots_compl_le_exp_neg_power`:
  if `δ < a - b - 2 * v - 3 * ε`, the probability that this population
  contains fewer than `floor (N n ^ δ)` particles is eventually at most
  `exp (-N n ^ δ)`.

# First-stage lower bound for the selected root count

The first-stage PZ budget bounds the probability that the killed slice has
fewer than floor(N^δ) particles. This is the low-root term in the terminal
failure decomposition.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

@[expose] public section

/-- The event that the first-stage killed slice contains at least K
particles. -/
noncomputable def rightTailPositiveAKilledEnoughRootEvent
    (m K ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (RestartedField m) :=
  let P := rightTailPositiveAKilledPopulation m ell ellN logN b v c κ
  let hP : P.FiniteSlices :=
    rightTailPositiveAKilledPopulation_finiteSlices m ell ellN logN b v c κ
  rightTailSecondStageEnoughRoots (K := K)
    (fun _ : ℕ => P) (fun _ : ℕ => hP) (fun _ => ell) 0

/-- Under the first-stage PZ power budget, the probability that the killed
population at the first cutoff has fewer than floor(N^δ) particles is at most
exp(-N^δ), with δ < a - b - 2v - 3ε. -/
theorem eventually_measure_rightTailPositiveAKilledEnoughRoots_compl_le_exp_neg_power
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma a b v epsilon delta c κ : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hvb : v < b)
    (hepsilon : 0 < epsilon)
    (hbudget : delta < a - b - 2 * v - 3 * epsilon)
    (ellN : ℕ → ℕ)
    (hTree : ∀ n, MeasurableSpace
      (RootIndexed.TreeNode
        (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
    let K : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ delta)
    let ell : ℕ → ℕ := rightTailPositiveAFirstCutoff N
    let L : ℕ → ℝ := logarithmOfSampleSize N
    ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := Fin (m n)) μ)
        (@rightTailPositiveAKilledEnoughRootEvent
          (m n) (K n) (ell n) (ellN n) (L n) b v c κ (hTree n))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
  classical
  dsimp
  let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
  let K : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ delta)
  let ell : ℕ → ℕ := rightTailPositiveAFirstCutoff N
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let pzMean (n : ℕ) : ℝ≥0∞ :=
    let corridor := affineCorridorThrough (ell n) (-b * L n) 0
      (b * L n) ((-b + v) * L n)
    let spineEvent := {increment : ℕ → ℝ |
      RandomWalk.history (ell n) 0 increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (-b * L n)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let upperMean := ENNReal.ofReal (Real.exp ((-b + v) * L n)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let q : ℕ → ℝ≥0∞ := fun _ => 1
    let pairBound := ∑ j : Fin (ell n),
      ENNReal.ofReal (Real.exp 0) *
        (ENNReal.ofReal (Real.exp (2 * ((-b + v) * L n))) *
          q (ell n - j.val - 1) ^ 2) *
        (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (0 - (-b * L n))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * L n) 0 (b * L n)})
    lowerMean ^ 2 / (upperMean + pairBound)
  let populationLow (n : ℕ) : Set (RootIndexed.StepField (Fin (m n)) ℕ ℝ) :=
    let initial := RootIndexed.initialPopulation (α := ℕ)
      (Finset.univ : Finset (Fin (m n)))
    let window := rightTailPositiveARestartedWindow
      (ell n) (ellN n) (L n) b v c κ
    let upper := rightTailPositiveAWindowUpper
      (ell n) (ellN n) (L n) b v c κ
    let populationFinite :=
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
        (fun _ : Fin (m n) => 0) id measurable_id initial
        (by simp [initial, RootIndexed.mem_initialPopulation_iff])
        (ell n) window
        (measurableSet_rightTailPositiveARestartedWindow
          (ell n) (ellN n) (L n) b v c κ)
        upper (rightTailPositiveARestartedWindow_subset_Iic_upper
          (ell n) (ellN n) (L n) b v c κ)
    {field |
      ((populationFinite.toFinset (ell n) field).card : ℝ) ≤
        (m n : ℝ) * (pzMean n).toReal / 4}
  have hPZ :=
    eventually_rightTailPositiveA_pzMean_toReal_ge_power_of_centeredSecondMoment
      hN μ hboundary hcross ν hν hνMoment hsigma hb hv hvb hepsilon
  have hthreshold := eventually_floorPowerOfSampleSize_mul_ennreal_toReal_ge
    (N := N) (a := a) (r := -b - 2 * v - 3 * epsilon) (δ := delta)
    hN ha (by linarith [hbudget]) pzMean (by
      filter_upwards [hPZ] with n hn
      simpa [pzMean, ell, L, logarithmOfSampleSize] using hn)
  have hlow :=
    eventually_rightTailPositiveA_populationLowCount_le_exp_neg_power
      hN μ hboundary hcross ν hν hνMoment hsigma ha hb hv hvb hepsilon
      hbudget (c := c) (κ := κ) ellN
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < (N n : ℝ) := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  filter_upwards [hthreshold, hlow, hNpos] with n hthresholdN hlowN hNposN
  letI : MeasurableSpace (RootIndexed.TreeNode (Fin (m n)) ℕ) := hTree n
  have hKReal : (K n : ℝ) ≤ (N n : ℝ) ^ delta := by
    dsimp [K]
    exact Nat.floor_le (Real.rpow_nonneg hNposN.le _)
  have hKThreshold :
      (K n : ℝ) ≤
        (m n : ℝ) * (pzMean n).toReal / 4 :=
    hKReal.trans hthresholdN
  let enough := rightTailPositiveAKilledEnoughRootEvent
    (m n) (K n) (ell n) (ellN n) (L n) b v c κ
  have hsubset : enoughᶜ ⊆ populationLow n := by
    intro field hfield
    have hcard : ¬ K n ≤
        (((rightTailPositiveAKilledPopulation_finiteSlices
            (m n) (ell n) (ellN n) (L n) b v c κ).toFinset
              (ell n) field).card) := by
      simpa [enough, rightTailPositiveAKilledEnoughRootEvent,
        rightTailSecondStageEnoughRoots] using hfield
    have hcardLt : (((rightTailPositiveAKilledPopulation_finiteSlices
          (m n) (ell n) (ellN n) (L n) b v c κ).toFinset
            (ell n) field).card : ℝ) < (K n : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hcard
    exact le_of_lt (hcardLt.trans_le hKThreshold)
  have hlowN' :
      (finiteRootStepFieldLaw μ (m n)) (populationLow n) ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
    exact hlowN
  calc
    (RootIndexed.stepFieldLaw (Root := Fin (m n)) μ) enoughᶜ ≤
        (RootIndexed.stepFieldLaw (Root := Fin (m n)) μ) (populationLow n) :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
      simpa [finiteRootStepFieldLaw] using hlowN'

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
