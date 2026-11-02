/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import MeasureTheory.Measure.Levy.Cutoff
import Probability.RandomMeasure.Poisson.Intensity.TimeMark

/-!
# Intensity conditions for a one-jump entrance

A finite truncated first moment and a positive mark window away from zero
produce one cutoff satisfying all quantitative intensity conditions needed
for the independent small/large Poisson model.

Assume $\int \min(1,|x|)\,\nu(dx)<\infty$ and
$\nu(\mathrm{largeJumpBand}(n))<\infty$ for every $n$. For a measurable
$J$ with $\nu(J)>0$ and $|x|\ge\delta$ for $x\in J$, where
$\delta,\rho>0$, let $dt$ be Lebesgue measure on $[0,1]$. Then some $n$
satisfies
$$
\int_{[0,1]\times\mathrm{smallJumpBand}(n)} |x|\,dt\,\nu(dx)<\rho,
\qquad
0<\bigl(dt\otimes(\nu\!\restriction_{\mathrm{largeJumpBand}(n)})\bigr)
  ([0,1]\times J),
\qquad
\bigl(dt\otimes(\nu\!\restriction_{\mathrm{largeJumpBand}(n)})\bigr)
  ([0,1]\times\mathrm{largeJumpBand}(n))<\infty.
$$

## Public declarations

* `ProbabilityTheory.exists_unitTime_cutoff_intensities` chooses one cutoff
  for which the small-jump first-moment integral is below $\rho$, the target
  large-mark window has positive product intensity, and the total large-jump
  intensity is finite.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem exists_unitTime_cutoff_intensities
    (ν : Measure ℝ) [SigmaFinite ν]
    (hfinite : (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) ≠ ⊤)
    (hlarge : ∀ n, ν (largeJumpBand n) < ⊤)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJpos : 0 < ν J)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hJaway : ∀ x ∈ J, δ ≤ |x|) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (ν.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) (Set.univ ×ˢ J) ∧
      ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  obtain ⟨n, hn, hrad⟩ :=
    exists_smallJumpBand_lintegral_lt_and_radius_lt
      ν hfinite ρ δ hρ hδ
  have hJsub : J ⊆ largeJumpBand n := by
    intro x hx
    exact le_trans hrad.le (hJaway x hx)
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [lintegral_unitTime_prod_mark
      (ν.restrict (smallJumpBand n))
      (fun x => ENNReal.ofReal |x|) (by fun_prop)]
    exact hn
  · rw [unitTime_prod_restrict_markWindow ν hJ hJsub]
    exact hJpos
  · have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact hlarge n

end ProbabilityTheory
