import Probability.Process.Stable.Basic
import Mathlib.Topology.UnitInterval

/-!
# The escape rate of the unit tube of a stable Lévy process

Лемма 1 I of the original paper states that a strictly stable Lévy process leaves its unit tube `𝔘` at an
exponential rate: `a ^ α * ln P (ξ (·) ∈ a𝔘) → C` as `a ↓ 0`, with `C ∈ (−∞, 0)` depending on the law `μ`
alone. This is the constant `C` that scales every statement of the small-deviation theorem — (15), (16) and
Лемма 4 all carry it — and the existence of the limit is the content of Лемма 1, which is not formalized here:
the predicate below records what is being asserted, so that the theorems can be stated with it as a hypothesis.

The tube is the family `stableProcessTube a` of paths of amplitude at most `a`. The paper writes the unit tube
as `𝔘` and scales it, and its companion family `𝔍_a` consists of the paths whose oscillation `sup − inf` is at
most `2a`; either normalization fixes the same constant once the tube is fixed, and the amplitude family is
used here because it needs no boundedness argument on a càdlàg path.
-/

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory

/-- The tube of paths of `D(0, 1)` of amplitude at most `a`: the paths whose values stay in `[-a, a]`. -/
def stableProcessTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {f | ∀ t, |f t| ≤ a}

/-- The paper's constant `C` of Лемма 1 I, stated for an abstract tube probability: it is the limit of
`a ^ α * log P (ξ (·) ∈ a𝔘)` as `a ↓ 0` along the tubes of the stable process. -/
def IsStableEscapeRate (α C : ℝ) (tubeProbability : ℝ → ℝ) : Prop :=
  Tendsto (fun a => a ^ α * Real.log (tubeProbability a)) (𝓝[>] (0 : ℝ)) (𝓝 C)

/-- Лемма 1 I for a stable Lévy process: the probabilities of its amplitude tubes decay at rate `C`, that is
`a ^ α * log P (ξ (·) ∈ tube a) → C` as `a ↓ 0`. -/
def HasStableProcessEscapeRate (α : ℝ) (μ : Measure ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) (C : ℝ) : Prop :=
  IsStableLevyProcessLaw α μ P ∧
    IsStableEscapeRate α C fun a => (P (stableProcessTube a)).toReal

namespace HasStableProcessEscapeRate

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)} {C : ℝ}

/-- A process whose tubes decay at rate `C` is a stable Lévy process. -/
theorem isStableLevyProcessLaw (h : HasStableProcessEscapeRate α μ P C) :
    IsStableLevyProcessLaw α μ P := h.1

/-- The defining limit of the escape rate: `a ^ α * log P (ξ (·) ∈ tube a) → C` as `a ↓ 0`. -/
theorem tendsto (h : HasStableProcessEscapeRate α μ P C) :
    Tendsto (fun a => a ^ α * Real.log ((P (stableProcessTube a)).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2

end HasStableProcessEscapeRate

end ProbabilityTheory
