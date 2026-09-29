import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.UnitInterval
import Probability.Distributions.Stable.Basic
import Topology.Cadlag.Skorokhod.TimeChange
import Topology.Cadlag.Skorokhod.Topology

/-!
# The law of a stable Lévy process

The original small-deviation theorem takes place on the paths of a strictly stable Lévy process `ξ(t)`: the
paper's (16) and Лемма 1 are statements about `ξ (·)`, and the constant `C` of Лемма 1 I is defined as
`a ^ a * ln P (ξ (·) ∈ a𝔘) → C` as `a ↓ 0`, along the unit tube `𝔘` of that process. This module supplies the
object those statements are about.

The pinned Mathlib tree has no stable Lévy-process construction. This file only specifies the proposed path
law; it does not prove that such a measure exists for every strictly stable `μ`. The law is represented on
the càdlàg paths of `D(0, 1)`, modeled here as `CadlagPath unitInterval ℝ`. Its finite-dimensional increment
condition says that paths start at `0` almost surely and that every finite increasing tuple of increments
is a measurable random vector with the product law of the strictly stable marginals `t ^ (1 / α) • μ`. This
is the usual finite-dimensional specification of independent stationary increments with stable scaling, on
the time interval needed by the small-deviation argument.

Before using this predicate as the process object in the proof, the development still has to verify the
measurability of coordinate evaluation for the chosen Skorokhod Borel space and establish an existence
theorem (or construct the canonical law). Those facts are not supplied by Mathlib or this predicate itself.
-/

open MeasureTheory Set

namespace ProbabilityTheory

/-- `P` is the law of a strictly `α`-stable Lévy process whose unit-time law is `μ`: `μ` is strictly
`α`-stable, `P`-almost every path starts at `0`, and for every increasing tuple of times in `[0, 1]` the
increments are independent, the increment over an interval of length `t` being distributed as
`t ^ (1 / α) • μ`. -/
def IsStableLevyProcessLaw (α : ℝ) (μ : Measure ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P] : Prop :=
  IsStrictlyAlphaStable α μ ∧
    P {f | f ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ = 0} = 1 ∧
      ∀ ⦃n : ℕ⦄ (t : Fin (n + 1) → ℝ) (hint : ∀ i, t i ∈ Icc (0 : ℝ) 1), Monotone t →
        AEMeasurable (fun f (i : Fin n) =>
            f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) P ∧
        (P.map fun f (i : Fin n) =>
            f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) =
          Measure.pi fun i : Fin n => μ.map fun x => (t i.succ - t i.castSucc) ^ (1 / α) * x

namespace IsStableLevyProcessLaw

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
variable [IsProbabilityMeasure P]

/-- The unit-time law of a stable Lévy process is strictly stable. -/
theorem strictlyStable (h : IsStableLevyProcessLaw α μ P) : IsStrictlyAlphaStable α μ := h.1

/-- The paths of a stable Lévy process start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableLevyProcessLaw α μ P) :
    P {f | f ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ = 0} = 1 := h.2.1

/-- The increments of a stable Lévy process over an increasing tuple of times in `[0, 1]` are independent,
and the increment over an interval of length `t` is distributed as `t ^ (1 / α) • μ`. -/
theorem aemeasurable_increments (h : IsStableLevyProcessLaw α μ P) ⦃n : ℕ⦄
    (t : Fin (n + 1) → ℝ) (hint : ∀ i, t i ∈ Icc (0 : ℝ) 1) (ht : Monotone t) :
    AEMeasurable (fun f (i : Fin n) =>
      f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) P :=
  (h.2.2 t hint ht).1

/-- The increments of a stable Lévy process over an increasing tuple of times in `[0, 1]` are independent,
and the increment over an interval of length `t` is distributed as `t ^ (1 / α) • μ`. -/
theorem map_increments (h : IsStableLevyProcessLaw α μ P) ⦃n : ℕ⦄ (t : Fin (n + 1) → ℝ)
    (hint : ∀ i, t i ∈ Icc (0 : ℝ) 1) (ht : Monotone t) :
    (P.map fun f (i : Fin n) =>
        f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) =
      Measure.pi fun i : Fin n => μ.map fun x => (t i.succ - t i.castSucc) ^ (1 / α) * x :=
  (h.2.2 t hint ht).2

end IsStableLevyProcessLaw

end ProbabilityTheory
