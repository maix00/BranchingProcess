/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Process.Path.Representation.Cadlag
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
import Probability.Distributions.Gaussian.Interval
import Probability.Process.Stable.SmallDeviation.EscapeRate.Gaussian
import Probability.Process.Stable.Brownian.Basic
import Probability.Process.Stable.Brownian.PathLaw
import Probability.Process.Stable.Levy
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# The standard Brownian path-law escape constant

## Public declarations

- `ProbabilityTheory.Process.Brownian.SmallDeviation.Range.exists_brownian_pathLaw_escapeRate_eq_neg_pi_sq_div_eight`:
  the canonical càdlàg path law of standard Brownian motion has exponent-two
  escape constant $C=-\pi^2/8$, and its full-width coefficient is
  $4C=-\pi^2/2$.

The path law is built from the rational-coordinate càdlàg version associated
with `IsBrownianReal`. The construction handles the measurable exceptional
set; the statement uses almost-sure continuity rather than requiring every
sample path to be continuous. The constants are the Gaussian specialization
of Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.Process.Brownian.SmallDeviation.Range

/-- Standard Brownian motion on its canonical càdlàg path law has escape
constant `-π² / 8` and full-width coefficient `-π² / 2`. -/
theorem exists_brownian_pathLaw_escapeRate_eq_neg_pi_sq_div_eight
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B Q) :
    ∃ C, HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      (Process.Path.Cadlag.pathLaw Q
        (fun t ω => B (unitInterval.toNNReal t) ω)
        (fun t => hB.toIsPreBrownianReal.aemeasurable
          (unitInterval.toNNReal t))) C ∧
      C = -(Real.pi ^ 2) / 8 ∧
      C * 2 ^ (2 : ℝ) = -(Real.pi ^ 2) / 2 := by
  have hP : IsStableClockProcessLaw 2 (gaussianReal 0 1) unitInterval.clock
      (Process.Path.Cadlag.pathLaw Q
        (fun t ω => B (unitInterval.toNNReal t) ω)
        (fun t => hB.toIsPreBrownianReal.aemeasurable
          (unitInterval.toNNReal t))) := by
    simpa [IsStableLevyProcess.unitIntervalPathLaw,
      IsLevyProcess.unitIntervalPathLaw, Process.Path.Cadlag.pathLaw] using
      hB.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw
  have hX := hB.isStableLevyProcess
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  obtain ⟨C, hEscape⟩ :=
    hP.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨C, hEscape,
    HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight hEscape hX,
    HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
      hEscape hX⟩

end ProbabilityTheory.Process.Brownian.SmallDeviation.Range

end
