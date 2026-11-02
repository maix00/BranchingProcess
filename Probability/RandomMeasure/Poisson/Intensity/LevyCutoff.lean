/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Intensity.TimeMark
public import MeasureTheory.Measure.Levy.Cutoff

/-!
# Integrable marks under a finite-variation Lévy cutoff

Finite first absolute moment of the truncated Lévy measure implies Bochner
integrability of the jump-size coordinate under unit-time product intensity.

## Public declarations

* `IsLevyMeasure.integrable_unitTime_smallJumpMark` proves integrability of
  the mark coordinate on each restricted reciprocal small-jump band whenever
  the truncated first absolute moment is finite.

Writing `\nu` for the Lévy measure and `\lambda_{[0,1]}` for unit-time
Lebesgue measure, if the truncated first absolute moment is finite, the mark
coordinate is integrable on every small-jump band. There the absolute mark
agrees with its truncation:

\[\begin{aligned}
\int_{[0,1]\times\mathrm{smallJumpBand}(n)}|x|\,d(\lambda_{[0,1]}\otimes\nu)(t,x)
&=\int_{\mathrm{smallJumpBand}(n)}|x|\,d\nu(x)\\
&=\int_{\mathrm{smallJumpBand}(n)}\min(1,|x|)\,d\nu(x)\\
&\le\int_{\mathbb R}\min(1,|x|)\,d\nu(x)<\infty.
\end{aligned}\]

Thus the mark-coordinate map `(t,x) ↦ x` is integrable under
`\lambda_{[0,1]}\otimes(\nu|_{\mathrm{smallJumpBand}(n)})`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A finite truncated first absolute moment makes the jump-size coordinate
integrable under unit-time product intensity restricted to any small-jump
band. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integrable_unitTime_smallJumpMark
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (n : ℕ)
    (hfinite :
      (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) < ⊤) :
    Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n))) := by
  let : SigmaFinite ν := hν.sigmaFinite
  let : SigmaFinite (ν.restrict (smallJumpBand n)) := inferInstance
  refine ⟨(by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs]
  rw [lintegral_unitTime_prod_mark
    (ν.restrict (smallJumpBand n))
    (fun x => ENNReal.ofReal |x|) (by fun_prop)]
  calc
    (∫⁻ x in smallJumpBand n, ENNReal.ofReal |x| ∂ν) =
        ∫⁻ x in smallJumpBand n, ENNReal.ofReal (min 1 |x|) ∂ν :=
      lintegral_smallJumpBand_abs_eq_min ν n
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν := setLIntegral_le_lintegral _ _
    _ < ⊤ := hfinite

end ProbabilityTheory

end
