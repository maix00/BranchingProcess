import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.BlockScale
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Horizontal
import Probability.BranchingRandomWalk.Walk.Law

/-!
# One-block corridors for the stable Mogulskii route

The one-block step of Mogulskii's stable proof estimates the probability that the increment path stays in a
corridor of normalized width `w` over a block of length asymptotic to a constant multiple of `a n ^ α`. The
block event is the horizontal tube of the increment path at the stable block length, and the small-deviation
rate `a n ^ α / (n * L* (a n))` is the normalization that turns a per-block constant `C * c / w ^ α` into the
corridor rate of the theorem.

For `α < 2` the limit process has jumps, so the estimate has to go through the stable Lévy process and the
Skorokhod `J₁` topology; the killed-interval spectral expansion used for the Gaussian case is not available
here and is not used. For `α = 2` the stable block length is literally the diffusive block length, which is
the link by which the Gaussian specialization reuses the spectral estimates.

The stable-process estimate itself is not proved here: this module fixes the block event, its probability and
the deterministic properties that the partition and two-sided bound arguments consume.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-! ## The block length at `α = 2` is the diffusive one -/

/-- At `α = 2` the stable block length is the diffusive block length. This is the
link by which the Gaussian specialization reuses the spectral estimates. -/
@[simp] theorem stableBlockLength_two (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 constant scale n = diffusiveBlockLength constant scale n := by
  simp [stableBlockLength, diffusiveBlockLength]

/-! ## The block corridor events -/

/-- The stable block corridor: the increment path stays in the open corridor of
normalized width `width` with lower offset `a`, over a block of length
`stableBlockLength α constant normalization n`. -/
def stableBlockTube (α constant a width : ℝ) (normalization : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InOpenHorizontalTube a width (stableBlockLength α constant normalization n) increment}

/-- The closed variant of `stableBlockTube`, used by the upper bounds. -/
def stableClosedBlockTube (α constant a width : ℝ) (normalization : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InHorizontalTube a width (stableBlockLength α constant normalization n) increment}

/-- The probability of the stable block corridor under the i.i.d. increment law. -/
noncomputable def stableBlockCorridorProbability (ν : Measure ℝ)
    (α constant a width : ℝ) (normalization : ℕ → ℝ) (n : ℕ) : ENNReal :=
  independentIncrementLaw ν (stableBlockTube α constant a width normalization n)

/-- The closed block corridor is a measurable event. -/
theorem measurableSet_stableClosedBlockTube (a width : ℝ) (n : ℕ) :
    MeasurableSet (stableClosedBlockTube α constant a width normalization n) :=
  measurableSet_inHorizontalTube a width _

/-- The narrower open corridor is contained in the wider one with the same
offset. This is the monotonicity the two-sided bound of the theorem uses when
comparing `f + ε`, `g - ε` with `f`, `g`. -/
theorem stableBlockTube_mono_width {α constant a w w' : ℝ} {normalization : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockTube α constant a w' normalization n ⊆
      stableBlockTube α constant a w normalization n := by
  intro increment h k
  have hk := h k
  exact ⟨by nlinarith [hk.1], by nlinarith [hk.2]⟩

/-- Monotonicity of the block corridor probability in the corridor width. -/
theorem stableBlockCorridorProbability_mono_width (ν : Measure ℝ)
    {α constant a w w' : ℝ} {normalization : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockCorridorProbability ν α constant a w' normalization n ≤
      stableBlockCorridorProbability ν α constant a w normalization n :=
  measure_mono (stableBlockTube_mono_width (α := α) (constant := constant)
    (normalization := normalization) ha0 ha1 hww)

end ProbabilityTheory.RandomWalk
