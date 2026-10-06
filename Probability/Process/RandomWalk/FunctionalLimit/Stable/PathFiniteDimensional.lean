/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.FiniteDimensional
public import Probability.Process.RandomWalk.Path.Scaling

/-!
# Finite-dimensional limits of stable random-walk paths

The endpoint-vector stable domain-of-attraction theorem also gives convergence
of the normalized step path at any finite grid whose integer block endpoints
agree with the path's floor-time evaluations. The block-scale and centering
limits are explicit inputs, just as in the endpoint theorem.
-/

open Filter MeasureTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Finite-dimensional convergence of the normalized right-continuous step
path, obtained by identifying its values with the cumulative endpoints of a
finite block decomposition. The block decomposition and all asymptotic scale
and centering hypotheses are part of the statement, so this result does not
silently assume positive block durations or negligible centering.
-/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_of_stableClock
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hX : HasStableClockIncrements α μ unitIntervalClock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : Monotone grid) (hgridStart : grid 0 = ⊥)
    (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds ((unitIntervalClock (grid j.succ) -
          unitIntervalClock (grid j.castSucc)) ^ (1 / α))))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds 0))
    (hposition : ∀ (n : ℕ) (j : Fin (blocks + 1)),
      AdditivePath.blockStart (length n) j.val =
        ⌊(n : ℝ) * (grid j : ℝ)⌋₊) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        normalizedStepPath spatialScale n increments (grid j : ℝ))
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  have hendpoints := tendstoInDistribution_endpoints_of_stableClock
    hDOA hX blocks grid hgrid hgridStart length spatialScale hblock hspatial
    hratio hcenter
  apply hendpoints.congr
  · intro n
    filter_upwards with increments
    funext j
    simp only [normalizedStepPath, hposition]
    rw [div_eq_mul_inv, mul_comm]
  · exact Filter.Eventually.of_forall fun _ => rfl

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
