/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs

/-!
# Tilted scaled measures of a convolution semigroup

For a convolution semigroup `S` with members `μ_t`, this module defines the
finite-scale measure
\[
  \widetilde{\mu}_t(dx)=\min(1,x^2)\,t^{-1}\mu_t(dx),
  \qquad t>0.
\]
It is the canonical finite-measure object used to extract the Lévy measure.

## Public declarations

* `ProbabilityTheory.ConvolutionSemigroup.tiltedScaledMeasure S t` is
  `withDensity (min(1,x²))` applied to the scaled member `t⁻¹ μ_t`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory
namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- The scaled measure `t⁻¹ · μ_t` tilted by the density `min 1 x²`. -/
noncomputable def tiltedScaledMeasure (t : {t : ℝ // 0 < t}) : Measure ℝ :=
  (S.scaledMeasure t).withDensity (fun x => ENNReal.ofReal (min 1 (x ^ 2)))

end ConvolutionSemigroup
end ProbabilityTheory

end
