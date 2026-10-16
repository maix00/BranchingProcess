/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Continuous
public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Process.RandomWalk.Fluctuation.DescendingLocalTime
public import Probability.Process.Brownian.Reflection.Path.NonnegativeUnitPath
public import Probability.Process.Brownian.Construction.Existence
public import Probability.Distributions.Moments.Real

/-!
# Finiteness of the first descending ladder time

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.tendsto_survivalProbability_zero_of_centeredUnitSecondMoment`:
  for centered, unit-variance increments,
  $\mathbb P(S_j\ge0\text{ for }1\le j\le n)\to0$.
- `ProbabilityTheory.RandomWalk.measure_firstDescendingLadderTime_eq_top_zero_of_centeredSecondMoment`:
  for every centered variance $\sigma^2>0$,
  $\mathbb P(T^-_1=\infty)=0$.

The proof combines Donsker's functional central limit theorem with the
zero probability of a nonnegative Brownian path on $[0,1]$. This supplies
the almost-sure finiteness premise for the first ladder-time law in
Francesco Caravenna and Loïc Chaumont, *Invariance principles for random
walks conditioned to stay positive*, Lemma 2.1, DOI 10.1214/07-AIHP119.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- The nonnegative polygonal path event is exactly finite-horizon survival
when its normalization scale is positive. -/
private lemma normalizedPath_nonnegative_iff_survives
    (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) :
    normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n increment ∈
      {f : C(unitInterval, ℝ) | ∀ t, 0 ≤ f t} ↔
      SurvivesNonnegative n increment := by
  have hscale : 0 < (Real.sqrt n)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hrange :
      normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n increment ∈
        {f : C(unitInterval, ℝ) | ∀ t, 0 ≤ f t} ↔
      Set.range (normalizedLinearContinuousPathIcc
        (fun n => Real.sqrt n) n increment) ⊆ Set.Ici 0 := by
    constructor
    · intro h x ⟨t, ht⟩
      rw [← ht]
      exact h t
    · intro h t
      exact h ⟨t, rfl⟩
  rw [hrange, normalizedLinearContinuousPathIcc_range_subset_iff
    (fun n => Real.sqrt n) hn (convex_Ici (0 : ℝ))
      (Set.mem_Ici.mpr le_rfl)]
  constructor
  · intro h k
    exact (mul_nonneg_iff_of_pos_left hscale).mp (h k)
  · intro h k
    exact (mul_nonneg_iff_of_pos_left hscale).mpr (h k)

/-- A centered unit-variance random walk survives above zero with
probability tending to zero. -/
theorem tendsto_survivalProbability_zero_of_centeredUnitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    Tendsto (fun n : ℕ => (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment}) atTop (nhds 0) := by
  obtain ⟨Q, B, hB, hmeasurable, hcontinuous⟩ := exists_brownianReal
  letI : IsProbabilityMeasure
      (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) := Q.property
  let F : Set C(unitInterval, ℝ) := {f | ∀ t, 0 ≤ f t}
  have hclosed : IsClosed F := isClosed_nonnegativeUnitPaths
  have hDonsker :=
    tendstoInDistribution_normalizedLinearContinuousPath_brownian
      ν hcentered hsecondMoment hB.toIsPreBrownianReal
        hcontinuous hmeasurable
  have hlimsup := hDonsker.limsup_measure_map_le_of_isClosed hclosed
  have hzero : (Q : Measure _).map
      (continuousunitIntervalPath B hcontinuous) F = 0 :=
    hB.measure_nonnegativeUnitPath_eq_zero hcontinuous hmeasurable
  rw [hzero] at hlimsup
  have heq : (fun n : ℕ => (iidSequenceLaw ν)
        {increment | SurvivesNonnegative n increment}) =ᶠ[atTop]
      (fun n : ℕ => ((iidSequenceLaw ν).map
        (normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n)) F) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Measure.map_apply
      (measurable_normalizedLinearContinuousPathIcc _ _) hclosed.measurableSet]
    apply congrArg
    ext increment
    exact (normalizedPath_nonnegative_iff_survives n hn increment).symm
  have hlimsupSurv : atTop.limsup (fun n : ℕ =>
      (iidSequenceLaw ν)
        {increment | SurvivesNonnegative n increment}) ≤ 0 := by
    simpa only [limsup_congr heq] using hlimsup
  exact tendsto_of_le_liminf_of_limsup_le bot_le hlimsupSurv

/-- A vanishing finite-horizon survival probability makes the first strict
descending ladder time finite almost surely. -/
private lemma measure_firstDescendingLadderTime_eq_top_zero_of_tendsto_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsurvival : Tendsto (fun n : ℕ => (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment}) atTop (nhds 0)) :
    iidSequenceLaw ν {increment |
      strictDescendingLadderTime increment 1 = ⊤} = 0 := by
  have hle : ∀ n : ℕ,
      iidSequenceLaw ν {increment |
        strictDescendingLadderTime increment 1 = ⊤} ≤
      iidSequenceLaw ν {increment | SurvivesNonnegative n increment} := by
    intro n
    apply measure_mono
    intro increment htop
    change strictDescendingLadderTime increment 1 = ⊤ at htop
    exact (survivesNonnegative_iff_firstDescendingLadderTime_gt
      increment n).2 (htop ▸ WithTop.coe_lt_top n)
  exact le_antisymm (ge_of_tendsto hsurvival
    (Filter.Eventually.of_forall hle)) bot_le

/-- Positive scaling of the increments preserves the finite-horizon
nonnegative survival probability. -/
private lemma measure_survival_map_div
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hsigma : 0 < sigma) (n : ℕ) :
    iidSequenceLaw (ν.map fun x => x / sigma)
      {increment | SurvivesNonnegative n increment} =
    iidSequenceLaw ν
      {increment | SurvivesNonnegative n increment} := by
  let T : (ℕ → ℝ) → (ℕ → ℝ) := fun x j => x j / sigma
  have hT : Measurable T :=
    Measurable.of_eval fun j =>
      (measurable_id.div_const sigma).comp (measurable_pi_apply j)
  have hiid : (iidSequenceLaw ν).map T =
      iidSequenceLaw (ν.map fun x => x / sigma) := by
    simpa only [T] using iidSequenceLaw_map_coordinatewise ν
      (fun x => x / sigma) (measurable_id.div_const sigma)
  rw [← hiid, Measure.map_apply hT (measurableSet_survivesNonnegative n)]
  apply congrArg
  ext increment
  have hdisp (k : ℕ) :
      AdditivePath.displacement k (T increment) =
        AdditivePath.displacement k increment / sigma := by
    simp [T, AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  change SurvivesNonnegative n (T increment) ↔
    SurvivesNonnegative n increment
  constructor
  · intro h k
    have hk := h k
    rw [hdisp] at hk
    rw [div_eq_mul_inv] at hk
    exact (mul_nonneg_iff_of_pos_right (inv_pos.mpr hsigma)).mp hk
  · intro h k
    rw [hdisp]
    exact div_nonneg (h k) hsigma.le

/-- Every centered random walk with a finite positive variance has a
finite first strict descending ladder time almost surely. -/
theorem measure_firstDescendingLadderTime_eq_top_zero_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    iidSequenceLaw ν {increment |
      strictDescendingLadderTime increment 1 = ⊤} = 0 := by
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  have hunit :=
    tendsto_survivalProbability_zero_of_centeredUnitSecondMoment
      νunit hνunit.1 hνunit.2
  have hsurvival : Tendsto (fun n : ℕ => (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment}) atTop (nhds 0) := by
    simpa only [νunit, measure_survival_map_div ν hsigma] using hunit
  exact measure_firstDescendingLadderTime_eq_top_zero_of_tendsto_survival
    ν hsurvival

end ProbabilityTheory.RandomWalk

end
