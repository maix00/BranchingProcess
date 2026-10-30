/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

/-!
# Scaling horizontal-tube logarithmic rates

## Public declarations

Let $\nu$ be a probability law, $\sigma>0$, and let $(x_n)$ and $(t_n)$ be
arbitrary real and natural-number sequences. If the standardized law
$\nu_\sigma=\nu\circ(x\mapsto x/\sigma)^{-1}$ satisfies
\[
 \frac{(x_n/\sigma)^2}{t_n}
 \log\!\left(\mathbb P_{\nu_\sigma}
   \{S_j\in[-a x_n/\sigma,(1-a)x_n/\sigma]:1\le j\le t_n\}\right)
 \longrightarrow C,
\]
then
\[
 \frac{x_n^2}{t_n}
 \log\!\left(\mathbb P_{\nu}
   \{S_j\in[-a x_n,(1-a)x_n]:1\le j\le t_n\}\right)
 \longrightarrow \sigma^2 C.
\]
This follows from `horizontalTubeProbability_map_div`; no moment or scale
assumption is required.

The public theorem is
`ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.tendsto_scaledLogProbability_of_map_div`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- A logarithmic tube-probability limit for increments divided by `sigma`
transfers to the original increment law, with the rate multiplied by
`sigma ^ 2`. -/
theorem tendsto_scaledLogProbability_of_map_div
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a sigma constant : ℝ) (hsigma : 0 < sigma)
    (scale : ℕ → ℝ) (time : ℕ → ℕ)
    (hlimit : Tendsto (fun n =>
      (scale n / sigma) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (iidSequenceLaw (ν.map fun x => x / sigma))
          a (scale n / sigma) (time n)).toReal)
      atTop (nhds constant)) :
    Tendsto (fun n =>
      scale n ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (iidSequenceLaw ν) a (scale n) (time n)).toReal)
      atTop (nhds (sigma ^ 2 * constant)) := by
  have hconstant : Tendsto (fun _ : ℕ => sigma ^ 2) atTop
      (nhds (sigma ^ 2)) := tendsto_const_nhds
  have hscaled := hconstant.mul hlimit
  convert hscaled using 1
  · funext n
    rw [horizontalTubeProbability_map_div ν a (scale n) (time n) hsigma]
    field_simp [hsigma.ne']

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
