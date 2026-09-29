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

Mathlib has no α-stable Lévy process, so the process is not constructed here; it is *defined* by its law, in
the form in which the paper uses it, on the càdlàg paths of `D(0, 1)` that the library models as
`CadlagPath unitInterval ℝ`. `IsStableLevyProcessLaw α μ P` says that `P` is a law on such paths starting at
`0` whose increments over an increasing tuple of times are independent, the increment over an interval of
length `t` being distributed as the strictly stable law `μ` scaled by `t ^ (1 / α)`; the independence is the
product measure `Measure.pi` of the increment marginals, i.e. the finite-dimensional distribution of the
increments. Times are taken in `[0, 1]` with their membership proof, which keeps the statement free of any
order structure on the path's time type.

That scaling is exactly the self-similarity `ξ(t) =_d t ^ (1 / α) ξ(1)` which reduces the small-deviation
statements to a single scale, and it is what makes the constant of Лемма 1 I depend on the law `μ` alone.
-/

open MeasureTheory Set

namespace ProbabilityTheory

/-- `P` is the law of a strictly `α`-stable Lévy process whose unit-time law is `μ`: `μ` is strictly
`α`-stable, `P`-almost every path starts at `0`, and for every increasing tuple of times in `[0, 1]` the
increments are independent, the increment over an interval of length `t` being distributed as
`t ^ (1 / α) • μ`. -/
def IsStableLevyProcessLaw (α : ℝ) (μ : Measure ℝ) (P : Measure (CadlagPath unitInterval ℝ)) : Prop :=
  IsStrictlyAlphaStable α μ ∧
    P {f | f ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ = 0} = 1 ∧
      ∀ ⦃n : ℕ⦄ (t : Fin (n + 1) → ℝ) (hint : ∀ i, t i ∈ Icc (0 : ℝ) 1), Monotone t →
        (P.map fun f (i : Fin n) =>
            f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) =
          Measure.pi fun i : Fin n => μ.map fun x => (t i.succ - t i.castSucc) ^ (1 / α) * x

namespace IsStableLevyProcessLaw

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}

/-- The unit-time law of a stable Lévy process is strictly stable. -/
theorem strictlyStable (h : IsStableLevyProcessLaw α μ P) : IsStrictlyAlphaStable α μ := h.1

/-- The paths of a stable Lévy process start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableLevyProcessLaw α μ P) :
    P {f | f ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ = 0} = 1 := h.2.1

/-- The increments of a stable Lévy process over an increasing tuple of times in `[0, 1]` are independent,
and the increment over an interval of length `t` is distributed as `t ^ (1 / α) • μ`. -/
theorem map_increments (h : IsStableLevyProcessLaw α μ P) ⦃n : ℕ⦄ (t : Fin (n + 1) → ℝ)
    (hint : ∀ i, t i ∈ Icc (0 : ℝ) 1) (ht : Monotone t) :
    (P.map fun f (i : Fin n) =>
        f ⟨t i.succ, hint i.succ⟩ - f ⟨t i.castSucc, hint i.castSucc⟩) =
      Measure.pi fun i : Fin n => μ.map fun x => (t i.succ - t i.castSucc) ^ (1 / α) * x :=
  h.2.2 t hint ht

end IsStableLevyProcessLaw

end ProbabilityTheory
