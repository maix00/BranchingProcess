module

public import Probability.Process.Stable.PathLaw
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.Endpoint
public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Path-space formulation of the stable-process escape rate

This file defines the càdlàg path-space events and specification predicate for
the escape rate. The process-level limits corresponding to Lemma 1 (18)--(20),
including their common finite negative constant, are proved on the original
sample space in `Probability.Process.Stable.SmallDeviation.EscapeRate`. The
bridge from that process result to this path-space packaging remains separate.
The path law on `unitInterval` is a finite-horizon restriction, not a full
Lévy-process object.

The set `J_a` in Lemma 1(I) consists of paths starting at zero whose range
has diameter less than `2 * a`. This is translation invariant in space: the
range need not lie in `(-a, a)`. We encode the strict diameter bound with a
positive uniform margin below `2 * a`; that is an open event in the Skorokhod
`J₁` topology.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The strict range-diameter tube of width `2 * a` from Lemma 1(I), encoded
by a positive uniform margin below that diameter. -/
def stableProcessRangeTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.oscillationInOpenTube (2 * a)

/-- The path event `a J₁` from Lemma 1(I), including the process's zero
starting value. -/
def stableProcessTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeTubeStartingAtZero a

/-- Initial evaluation is continuous in `J₁`, and the range condition is the open Skorokhod corridor. -/
theorem measurableSet_stableProcessTube (a : ℝ) :
    MeasurableSet (stableProcessTube a) := by
  exact Skorokhod.measurableSet_rangeTubeStartingAtZero a

/-- For a process law started at zero almost surely, adding the explicit
starting-value condition to the source's range tube does not change its
probability. -/
theorem measure_stableProcessTube_eq_rangeTube
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P) (a : ℝ) :
    P (stableProcessTube a) = P (stableProcessRangeTube a) := by
  have heq : stableProcessTube a =ᵐ[P] stableProcessRangeTube a := by
    filter_upwards [hP.ae_start_eq_zero] with f hf
    simp [stableProcessTube, Skorokhod.rangeTubeStartingAtZero,
      stableProcessRangeTube, hf]
  exact measure_congr heq

/-- The paper's constant `C` of Lemma 1 I, stated as the limit of
`a ^ α * log P(stableProcessTube a)` as `a ↓ 0`. -/
def IsStableEscapeRate (α C : ℝ) (tubeProbability : ℝ → ℝ) : Prop :=
  C < 0 ∧
    (∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < tubeProbability a) ∧
    Tendsto (fun a => a ^ α * Real.log (tubeProbability a))
      (𝓝[>] (0 : ℝ)) (𝓝 C)

namespace IsStableEscapeRate

variable {α C : ℝ} {tubeProbability : ℝ → ℝ}

theorem negative (h : IsStableEscapeRate α C tubeProbability) : C < 0 := h.1

theorem eventually_tubeProbability_pos (h : IsStableEscapeRate α C tubeProbability) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < tubeProbability a := h.2.1

theorem tendsto (h : IsStableEscapeRate α C tubeProbability) :
    Tendsto (fun a => a ^ α * Real.log (tubeProbability a))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.2

end IsStableEscapeRate

/-- Lemma 1 I for a stable process path law: the probabilities of its strict range-diameter tubes decay at rate `C`,
that is `a ^ α * log P(stableProcessTube a) → C` as `a ↓ 0`. -/
def HasStableProcessEscapeRate (α : ℝ) (μ : Measure ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) (C : ℝ) [IsProbabilityMeasure P] : Prop :=
  IsStableClockProcessLaw α μ unitIntervalClock P ∧
    IsStableEscapeRate α C fun a => (P (stableProcessTube a)).toReal

namespace HasStableProcessEscapeRate

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)} {C : ℝ}
variable [IsProbabilityMeasure P]

/-- The path law underlying the finite-horizon tube estimate. -/
theorem isStableClockProcessLaw (h : HasStableProcessEscapeRate α μ P C) :
    IsStableClockProcessLaw α μ unitIntervalClock P := h.1

/-- The defining limit of the escape rate: `a ^ α * log P (ξ (·) ∈ tube a) → C` as `a ↓ 0`. -/
theorem tendsto (h : HasStableProcessEscapeRate α μ P C) :
    Tendsto (fun a => a ^ α * Real.log ((P (stableProcessTube a)).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.tendsto

/-- The range-tube event has positive probability for all sufficiently small
positive widths. This is part of the finite escape-rate statement: `ENNReal.toReal`
must not turn a zero probability into the real number zero before taking a
logarithm. -/
theorem eventually_tubeProbability_pos (h : HasStableProcessEscapeRate α μ P C) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < (P (stableProcessTube a)).toReal :=
  h.2.eventually_tubeProbability_pos

/-- The escape exponent is strictly negative, as in Lemma 1 I. -/
theorem negative (h : HasStableProcessEscapeRate α μ P C) : C < 0 := h.2.negative

end HasStableProcessEscapeRate

end ProbabilityTheory
