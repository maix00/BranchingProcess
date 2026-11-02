/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Jump.PoissonConfiguration.Increment
public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
import Probability.Process.Stable.JumpModel.EndpointLaw
import Probability.Distributions.Stable.LevyMeasure.Cutoff.Variation
import Probability.RandomMeasure.Poisson.Intensity.LevyCutoff

/-!
# Increment law of the finite-variation stable jump model

## Public declarations

- `IsStrictlyAlphaStable.law_poissonEntrancePath_cutoff_increment`: for
  $0<\alpha<1$ and $0\le s\le t\le1$, the cutoff Poisson entrance path
  $X^{(n)}$ satisfies
  \[
    \operatorname{Law}(X^{(n)}_t-X^{(n)}_s)
      =(x\mapsto |(s,t]|^{\frac{1}{\alpha}}x)_*\mu.
  \]
  The two Poisson point families have the small- and large-jump cutoff
  intensities of the Lévy measure representing $\mu$.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- On each deterministic interval `[s,t]` in the unit interval, the cutoff
Poisson entrance path has the prescribed stable increment law with clock mass
`volume (Ioc s t)`. -/
theorem IsStrictlyAlphaStable.law_poissonEntrancePath_cutoff_increment
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb)
    (s t : unitInterval) (hst : s ≤ t) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω -
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) s ω) =
      μ.map (fun x => (((volume : Measure unitInterval) (Set.Ioc s t)).toReal ^
        (1 / α)) * x) := by
  have hsfirst := T.isLevyMeasure.integrable_unitTime_smallJumpMark n
    (h.levyMeasure_smallJumpMoment_lt_top T hT hα)
  rw [Measure.map_congr (ae_poissonEntrancePath_cutoff_sub_eq_timeWindow
    n hds hdb hsfirst (T.isLevyMeasure.measure_largeJumpBand_lt_top n) s t hst)]
  simpa only [Set.mem_Ioc] using
    (h.law_timeWindow_split_poissonRandomMeasures T hT hα n hds hdb
      (Set.Ioc s t) measurableSet_Ioc)

end ProbabilityTheory
