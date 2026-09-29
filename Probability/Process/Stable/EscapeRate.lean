module

public import Probability.Process.Stable.Basic
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Corridor
public import Topology.Cadlag.Skorokhod.Endpoint

/-!
# The escape rate of a finite-horizon stable process tube

Лемма 1 I of the original paper states that a strictly stable process leaves its unit tube `𝔘` at an
exponential rate: `a ^ α * ln P (ξ (·) ∈ a𝔘) → C` as `a ↓ 0`, with `C ∈ (−∞, 0)` depending on the law `μ`
alone. This is the constant `C` that scales every statement of the small-deviation theorem — (15), (16) and
Лемма 4 all carry it — and existence of the limit is the content of Лемма 1, which is not formalized here.
The path law on `unitInterval` is a finite-horizon restriction, not a full Lévy-process object.

The tube in Lemma 1(I) is the scaled open unit-interval tube: paths starting at zero whose range stays strictly
inside `(-a, a)`.  The path-space corridor API expresses this strict range condition with a positive uniform margin,
which is open and measurable in the Skorokhod `J₁` topology. It replaces the earlier closed pointwise
amplitude condition, which did not match the cited lemma.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The identity clock on the compact time horizon `[0,1]`.  The tube estimate uses this finite-horizon clock instance. -/
def unitIntervalClock : unitInterval → ℝ := fun t => (t : ℝ)

theorem monotone_unitIntervalClock : Monotone unitIntervalClock := by
  intro s t hst
  exact hst

theorem unitIntervalClock_bot : unitIntervalClock ⊥ = 0 := by
  simp [unitIntervalClock]

/-- The scaled open unit-interval tube from Lemma 1(I): paths starting at zero whose range stays strictly
inside `(-a, a)`. -/
def stableProcessTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0} ∩ Skorokhod.rangeInOpenInterval (-a) a

/-- Initial evaluation is continuous in `J₁`, and the range condition is the open Skorokhod corridor. -/
theorem measurableSet_stableProcessTube (a : ℝ) :
    MeasurableSet (stableProcessTube a) := by
  exact MeasurableSet.inter
    (MeasurableSet.preimage (measurableSet_singleton 0)
      Skorokhod.continuous_apply_bot.measurable)
    (Skorokhod.measurableSet_rangeInOpenInterval (-a) a)

/-- The paper's constant `C` of Lemma 1 I, stated as the limit of
`a ^ α * log P(stableProcessTube a)` as `a ↓ 0`. -/
def IsStableEscapeRate (α C : ℝ) (tubeProbability : ℝ → ℝ) : Prop :=
  C < 0 ∧
    Tendsto (fun a => a ^ α * Real.log (tubeProbability a))
      (𝓝[>] (0 : ℝ)) (𝓝 C)

/-- Lemma 1 I for a stable process path law: the probabilities of its strict symmetric tubes decay at rate `C`,
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
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.2

/-- The escape exponent is strictly negative, as in Lemma 1 I. -/
theorem negative (h : HasStableProcessEscapeRate α μ P C) : C < 0 := h.2.1

end HasStableProcessEscapeRate

end ProbabilityTheory
