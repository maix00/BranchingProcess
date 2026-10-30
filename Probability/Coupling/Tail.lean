/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Coupling.Order

/-!
# Tail comparison through a coupling

An almost-sure order between two real-valued observables transfers upper-tail
probability bounds through the corresponding coupling.

## Public declarations

* `ProbabilityTheory.Coupling.measure_ge_le_of_ae_le`: if
  `g(p.2) ≤ f(p.1)` almost surely under a coupling, then for every
  `threshold : ℝ`,
  \[
  \nu\{y\mid threshold\le g(y)\}
  \le \mu\{x\mid threshold\le f(x)\}.
  \]
-/

open MeasureTheory

namespace ProbabilityTheory.Coupling

/-- If the second observable is almost surely at most the first, its upper
tail probability is at most the first observable's upper tail probability. -/
theorem measure_ge_le_of_ae_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (κ : ProbabilityTheory.Coupling μ ν)
    (f : X → ℝ) (g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (horder : ∀ᵐ p ∂κ.joint, g p.2 ≤ f p.1)
    (threshold : ℝ) :
    ν {y | threshold ≤ g y} ≤ μ {x | threshold ≤ f x} := by
  change ν (g ⁻¹' Set.Ici threshold) ≤ μ (f ⁻¹' Set.Ici threshold)
  exact measure_preimage_le_of_ae_le
    (s := Set.Ici threshold) (isUpperSet_Ici threshold) measurableSet_Ici
    κ f g hf hg horder

end ProbabilityTheory.Coupling
