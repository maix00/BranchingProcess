/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Levy.Cutoff
public import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Basic
import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Endpoint
import Probability.RandomMeasure.Poisson.Intensity.Support
import Probability.RandomMeasure.Poisson.Intensity.TimeMark

/-!
# Endpoint identity for a Lévy cutoff path

At the final observation time, the path defined through the small- and
large-jump cutoff bands agrees almost surely with the sum of the two full
realized Poisson integrals.

## Public declarations

- `ProbabilityTheory.ae_poissonEntrancePath_cutoff_top_eq_integral` states
  that the path at `⊤` equals the sum of its small- and large-jump integrals
  almost surely for each fixed cutoff. The generic support-based identity is
  owned by `Probability.RandomMeasure.Poisson.JumpPath.Entrance.Endpoint`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The fixed-cutoff path used in the entrance construction has the full
small-plus-large jump sum as its unit-time endpoint almost surely. -/
theorem ae_poissonEntrancePath_cutoff_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) Pb) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) ⊤ ω =
        (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  exact ae_poissonEntrancePath_top_eq_integral hds hdb
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_smallJumpBand n))
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_largeJumpBand n))
    (unitTime_prod_restrict_carrier ν (smallJumpBand n) (measurableSet_smallJumpBand n))
    (unitTime_prod_restrict_carrier ν (largeJumpBand n) (measurableSet_largeJumpBand n))

end ProbabilityTheory
