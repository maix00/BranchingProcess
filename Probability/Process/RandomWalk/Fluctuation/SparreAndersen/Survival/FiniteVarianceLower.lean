/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Signs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.Pi
public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Sequence.IID.Basic
import Analysis.Asymptotics.Power.SequenceLowerPower
import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.Lemmas.FiniteVarianceLower
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.Recurrence
import Probability.Process.RandomWalk.Fluctuation.FiniteVarianceSignLimit

/-!
# Finite-variance survival lower bound

## Public declarations

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.exists_nonnegativeSurvivalProbability_ge_power_of_centeredSecondMoment`:
  for centered increments of variance $\sigma^2>0$ and
  $0<\gamma<1/2$, there is $C>0$ such that
  $\mathbb P(S_1,\ldots,S_n\ge0)\ge C(n+1)^{\gamma-1}$
  for every $n$.

The proof uses the coefficient recurrence in equation (2.2) of Section 2 of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events in
the binomial random walk: Will the drunken sailor hit the sober man?*,
*Journal of Statistical Physics* 96 (1999), 963–1019, DOI
10.1023/A:1004636216365, arXiv:cond-mat/9905252. Their Appendix A,
equations (A.7)--(A.8), derives the generating-function identity behind the
recurrence. The proof combines the finite recurrence with the Gaussian
endpoint-sign limit and a prefix-sum induction.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk


/-- A positive centered finite-variance walk has a polynomial lower bound
for survival through each finite horizon. -/
theorem exists_nonnegativeSurvivalProbability_ge_power_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) {γ : ℝ} (hγ : 0 < γ) (hγhalf : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative n increment}).toReal := by
  let F : ℕ → ℝ := fun n => (Measure.pi (fun _ : Fin n => ν)).real
    {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t}
  let P : ℕ → ℝ := fun n => (Measure.pi (fun _ : Fin n => ν)).real
    {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)}
  let β : ℝ := (γ + 1 / 2) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hγβ : γ < β := by dsimp [β]; linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hF0 : F 0 = 1 := finiteSurvivalProbability_zero ν
  have hFpos (n : ℕ) : 0 < F n := by
    rw [show F n = ((iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment}).toReal from
      finiteSurvivalProbability_eq_infinite ν n]
    exact ENNReal.toReal_pos
      (survivalProbability_pos_of_positiveIncrement
        ν (hν.measure_Ioi_zero_pos hsigma) n).ne'
      (measure_ne_top _ _)
  have hPnonneg (n : ℕ) : 0 ≤ P n := ENNReal.toReal_nonneg
  have hPlimit : Tendsto P atTop (nhds (1 / 2 : ℝ)) := by
    have h := tendsto_nonnegativePartialSumProbability_half ν hν hsigma
    have hreal := (ENNReal.tendsto_toReal (by norm_num :
      (1 / 2 : ℝ≥0∞) ≠ ⊤)).comp h
    have hhalf : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    simpa only [Function.comp_def, hhalf,
      ← finiteEndpointProbability_eq_infinite ν] using hreal
  have hβhalf : β < 1 / 2 := by dsimp [β]; linarith
  have hPβ : ∀ᶠ n : ℕ in atTop, β ≤ P n := by
    exact (hPlimit.eventually (eventually_gt_nhds hβhalf)).mono
      (by intro n hn; exact hn.le)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hPβ
  let N := max 1 N₀
  have hN : 1 ≤ N := le_max_left _ _
  have hPβall : ∀ n, N ≤ n → β ≤ P n := by
    intro n hn
    exact hN₀ n (le_trans (le_max_right _ _) hn)
  have hrec : ∀ n : ℕ, 0 < n →
      P n = (n : ℝ) * F n -
        ∑ r : Fin (n - 1), F (r.val + 1) * P (n - (r.val + 1)) := by
    intro n hn
    exact measureReal_nonnegative_endpoint_recurrence ν hn
  have hconv : ∀ n : ℕ, 0 < n →
      (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val) :=
    fun n hn => recurrence_to_convolution F P hF0 hrec hn
  obtain ⟨C, hC, hbound⟩ := Asymptotics.lower_power_of_prefix
    F hFpos hβ hγ hγβ hγ1 N hN
      (fun n hn => prefix_bound_of_convolution F P
        (fun k => (hFpos k).le) hPnonneg hβ.le N hN
        hPβall hconv n hn)
  refine ⟨C, hC, ?_⟩
  intro n
  have h := hbound n
  change C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤ F n at h
  rw [show F n = ((iidSequenceLaw ν)
    {increment | SurvivesNonnegative n increment}).toReal from
      finiteSurvivalProbability_eq_infinite ν n] at h
  exact h

end ProbabilityTheory.RandomWalk

end
