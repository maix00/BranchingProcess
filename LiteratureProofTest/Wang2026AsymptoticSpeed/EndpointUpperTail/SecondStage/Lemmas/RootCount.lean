/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales

import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Population
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Roots.Population
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.Population.Lemmas.Embedding
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.Logarithmic.Survival
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.IndependentEventCount
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.FirstStage.Cutoff
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.Population.RestartedWindow
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales
import Analysis.Asymptotics.Power.FloorProduct

import Probability.BranchingRandomWalk.Assumptions.CrossWeight
import Probability.BranchingRandomWalk.Spine.Tilted.Law
import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

/-!
# First-stage lower bound for the selected root count

## Internal proof declarations

Under the first-stage budget \(\delta<a-b+v-3\varepsilon\), if
\(K_n=\lfloor N_n^\delta\rfloor\), the probability that the selected BRW slice has
fewer than \(K_n\) roots is eventually exponentially small:

\[
\forall^\infty n,\qquad
\mathbb P\!\left(
  |P_{\ell_n}|<\lfloor N_n^\delta\rfloor\right)
\le \exp(-N_n^\delta).
\]

* `LiteratureProofTest.Wang2026AsymptoticSpeed.SecondStage.Lemmas.eventually_enoughRoots_compl_le_exp_neg_power`:
  if `δ < a - b + v - 3 * ε`, the probability that this population
  contains fewer than `floor (N n ^ δ)` particles is eventually at most
  `exp (-N n ^ δ)`.

The logarithmic survival rate and Chernoff bound control the probability that the selected BRW slice has
fewer than floor(N^δ) particles. This is the low-root term in the terminal
failure decomposition. The proof uses Lemma 3.8, equation (3.10), of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), followed by the independent-root Chernoff estimate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace LiteratureProofTest.Wang2026AsymptoticSpeed.SecondStage.Lemmas

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)

section

/-- By Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.8, equation
(3.10), and the independent-root Chernoff bound, the probability that the selected
population at the first cutoff has fewer than floor(N^δ) particles is at most
exp(-N^δ), with δ < a - b + v - 3ε. -/
lemma eventually_enoughRoots_compl_le_exp_neg_power
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma a b v epsilon delta c κ : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (ha : 0 < a) (hv : 0 < v) (hvb : v < b)
    (hepsilon : 0 < epsilon)
    (hbudget : delta < a - b + v - 3 * epsilon)
    (ellN : ℕ → ℕ)
    (hTree : ∀ n, MeasurableSpace
      (RootIndexed.TreeNode
        (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
    let K : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ delta)
    let ell : ℕ → ℕ := positiveAFirstStageCutoff N
    let L : ℕ → ℝ := logarithmOfSampleSize N
    ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := Fin (m n)) μ)
        (@positiveASelectedBRWEnoughRootEvent
          (m n) (K n) (ell n) (ellN n) (L n) b v c κ (hTree n))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
  classical
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  let K (n : ℕ) := Nat.floor ((N n : ℝ) ^ delta)
  let ell := positiveAFirstStageCutoff N
  let L := logarithmOfSampleSize N
  let E (n : ℕ) := hasPathHistoryIn (ι := ℕ) realPotential (ell n) 0
    (affineCorridorThrough (ell n) (-b * L n) 0 (b * L n) ((-b + v) * L n))
  let p (n : ℕ) := (offspringFieldLaw μ).real (E n)
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_hasPathHistoryIn realPotential (ell n) 0 _
      (measurableSet_affineCorridorThrough ..)
  have hrate : Tendsto (fun n => Real.log (p n) / L n) atTop (𝓝 (v - b)) := by
    have h := (LogarithmicCorridor.tendsto_log_survival_div_log
      realPotential μ hboundary hcross (by simpa [hν] using hνMoment)
      hsigma hv hvb).comp hN
    simpa [Function.comp_def, p, E, ell, positiveAFirstStageCutoff, L, logarithmOfSampleSize,
      show -b + v = v - b by ring] using h
  have hNReal : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hNReal
  have hpower : ∀ᶠ n in atTop, (N n : ℝ) ^ (v - b - epsilon) ≤ p n := by
    filter_upwards [hL.eventually_gt_atTop 0,
      hrate.eventually (Ioo_mem_nhds (show v - b - epsilon < v - b by linarith)
        (show v - b < 0 by linarith)), hN.eventually_gt_atTop 0]
      with n hLn hn hNn
    have hpn : 0 < p n := by
      refine lt_of_le_of_ne ENNReal.toReal_nonneg ?_
      intro hz
      have hh := hn.2
      rw [← hz, Real.log_zero, zero_div] at hh
      exact (lt_irrefl _ hh)
    have hlog : (v - b - epsilon) * L n < Real.log (p n) :=
      (lt_div_iff₀ hLn).mp hn.1
    rw [Real.rpow_def_of_pos (show 0 < (N n : ℝ) by exact_mod_cast hNn)]
    apply le_of_lt
    calc
      Real.exp (Real.log (N n : ℝ) * (v - b - epsilon)) =
          Real.exp ((v - b - epsilon) * L n) := by dsimp [L, logarithmOfSampleSize]; congr 1; ring
      _ < Real.exp (Real.log (p n)) := Real.exp_lt_exp.mpr hlog
      _ = p n := Real.exp_log hpn
  have hthresholdRaw := Asymptotics.eventually_floor_rpow_mul_ge
    (x := fun n => (N n : ℝ)) (y := p) hNReal
    (a := a) (r := v - b - epsilon) (δ := delta) (C := 4)
    ha (by linarith [hbudget]) hpower
  have hthreshold : ∀ᶠ n in atTop, (N n : ℝ) ^ delta ≤ (m n : ℝ) * p n / 4 := by
    filter_upwards [hthresholdRaw] with n hn
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by simpa [m, mul_comm] using hn)
  have hmPos : ∀ᶠ n in atTop, 0 < m n := by
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    apply Nat.floor_pos.mpr
    exact Real.one_le_rpow (by exact_mod_cast hn) ha.le
  filter_upwards [hthreshold, hmPos] with n hthresholdN hm
  let _ : MeasurableSpace (RootIndexed.TreeNode (Fin (m n)) ℕ) := hTree n
  let P := positiveASelectedBRWPopulation (m n) (ell n) (ellN n) (L n) b v c κ
  let slices := positiveASelectedBRWPopulation_finiteSlices
    (m n) (ell n) (ellN n) (L n) b v c κ
  let roots := positiveASuccessfulRoots (m n) (ell n) (L n) b v
  have hcountEq (field : FiniteRootStepField (m n) ℕ ℝ) :
      (∑ r : Fin (m n), (E n).indicator (fun _ => (1 : ℝ)) (field r)) =
        (roots field).card := by
    simp [roots, positiveASuccessfulRoots, E, Set.indicator]
  have hEmbedding := ae_positiveA_successfulRoots_card_le_selectedBRWPopulation
    (m n) (ell n) (ellN n) (L n) b v c κ μ hboundary
  have hKle : (K n : ℝ) ≤ (m n : ℝ) * p n / 4 :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hthresholdN
  let enough := positiveASelectedBRWEnoughRootEvent
    (m n) (K n) (ell n) (ellN n) (L n) b v c κ
  have hsubset : ∀ᵐ field ∂finiteRootStepFieldLaw μ (m n),
      field ∈ enoughᶜ →
        (∑ r : Fin (m n), (E n).indicator (fun _ => (1 : ℝ)) (field r)) ≤
          (m n : ℝ) * p n / 4 := by
    filter_upwards [hEmbedding] with field hembed
    intro hfield
    have hnot : ¬ K n ≤ (slices.toFinset (ell n) field).card := by
      simpa [enough, positiveASelectedBRWEnoughRootEvent, secondStageEnoughRoots,
        slices, P] using hfield
    rw [hcountEq]
    have hrootCard : (roots field).card ≤ (slices.toFinset (ell n) field).card := hembed
    have hlt : ((roots field).card : ℝ) < (K n : ℝ) := by
      exact_mod_cast hrootCard.trans_lt (Nat.lt_of_not_ge hnot)
    exact hlt.le.trans hKle
  have hcount := RootIndexed.measure_finiteRootEventCount_le_quarter_mean μ (E n) (hE n) (m n) hm
  have hexp : ENNReal.ofReal (Real.exp (-((m n : ℝ) * p n / 4))) ≤
      ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hthresholdN))
  calc
    (RootIndexed.stepFieldLaw (Root := Fin (m n)) μ) enoughᶜ ≤
        (finiteRootStepFieldLaw μ (m n))
          {field | (∑ r : Fin (m n), (E n).indicator (fun _ => (1 : ℝ)) (field r)) ≤
            (m n : ℝ) * p n / 4} := measure_mono_ae hsubset
    _ ≤ ENNReal.ofReal (Real.exp (-((m n : ℝ) * p n / 4))) := hcount
    _ ≤ ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := hexp

end

end LiteratureProofTest.Wang2026AsymptoticSpeed.SecondStage.Lemmas
