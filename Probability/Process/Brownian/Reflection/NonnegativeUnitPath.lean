/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassagePrinciple
public import Probability.Process.Path.UnitInterval
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Brownian paths leave the nonnegative half-line immediately

The public theorems in this file are:

- `ProbabilityTheory.isClosed_nonnegativeUnitPaths`:
  $\{f\in C([0,1],\mathbb R):f(t)\ge0\text{ for all }t\}$ is closed.
- `ProbabilityTheory.IsBrownianReal.measure_nonnegativeUnitPath_eq_zero`:
  a Brownian path started at zero belongs to this set with probability zero.

The probability statement follows from the reflection-principle calculation
in S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, Theorem 2.1, arXiv:1810.01783. It is the
Brownian input for the almost-sure finiteness of the first descending ladder
time under Donsker convergence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Nonnegative continuous paths on the unit interval form a closed set. -/
theorem isClosed_nonnegativeUnitPaths :
    IsClosed {f : C(unitInterval, ℝ) | ∀ t, 0 ≤ f t} := by
  rw [show {f : C(unitInterval, ℝ) | ∀ t, 0 ≤ f t} =
      ⋂ t : unitInterval, {f | f t ∈ Set.Ici 0} by
    ext f
    simp]
  exact isClosed_iInter fun t =>
    isClosed_Ici.preimage (continuous_eval_const t)

/-- A Brownian path started at zero has a negative value before time one
almost surely. -/
theorem IsBrownianReal.measure_nonnegativeUnitPath_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    P.map (continuousunitIntervalPath B hcontinuous)
      {f : C(unitInterval, ℝ) | ∀ t, 0 ≤ f t} = 0 := by
  let pathB := hB.continuousPathMap hmeasurable
  have hminMap : ∀ᵐ f ∂P.map pathB, runningMinimum f 1 < 0 := by
    have hset : MeasurableSet
        {f : C(ℝ≥0, ℝ) | runningMinimum f 1 < 0} :=
      (measurable_runningMinimum 1) measurableSet_Iio
    exact (mem_ae_iff_prob_eq_one hset).mpr
      (hB.measure_runningMinimum_lt_zero hmeasurable (by norm_num))
  have hmin : ∀ᵐ ω ∂P, runningMinimum (pathB ω) 1 < 0 :=
    ae_of_ae_map (hB.measurable_continuousPathMap hmeasurable).aemeasurable
      hminMap
  have hpath := hB.continuousPathMap_ae_eq hmeasurable
  have hnot : ∀ᵐ ω ∂P,
      ¬ ∀ t : unitInterval, 0 ≤ B (UnitInterval.toNNReal t) ω := by
    filter_upwards [hmin, hpath] with ω hminω hpathω hnonneg
    obtain ⟨u, hu, hvalue⟩ := exists_runningMinimum_eq (pathB ω) 1
    obtain ⟨t, ht⟩ :=
      UnitInterval.exists_mul_eq 1 u (by norm_num) hu.2
    have htime : UnitInterval.toNNReal t = u := by simpa using ht
    have hneg : B (UnitInterval.toNNReal t) ω < 0 := by
      rw [htime, ← hpathω u, hvalue]
      exact hminω
    exact (not_le.mpr hneg) (hnonneg t)
  rw [Measure.map_apply
    (measurable_continuousunitIntervalPath B hcontinuous hmeasurable)
    isClosed_nonnegativeUnitPaths.measurableSet]
  simpa only [Set.preimage, Set.mem_ofPred_eq,
    continuousunitIntervalPath_apply, not_not] using (ae_iff).mp hnot

end ProbabilityTheory

end
