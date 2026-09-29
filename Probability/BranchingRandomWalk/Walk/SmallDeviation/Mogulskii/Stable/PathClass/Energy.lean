module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.PathClass.Basic

/-!
# The `Hα` energy on `M₂` and finite unions

This file defines the source's corridor functional for extended-real step
boundaries and its finite-union minimum on `M₃`.  Infinite corridor width has
zero reciprocal-power cost.  The admissibility witness in `M₂` ensures that
the width is strictly positive at every interior time; the totalized density
also keeps the definition meaningful outside that domain.
-/

open MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- The reciprocal `α`-power of a corridor width. Infinite width contributes
zero. On finite positive widths this is exactly `(upper - lower) ^ (-α)` as in
the paper. The definition is total outside admissible corridors as well. -/
noncomputable def widthCost (α : ℝ) (upper lower : EReal) : ℝ≥0∞ :=
  if upper = ⊤ ∨ lower = ⊥ then 0
  else if 0 < upper.toReal - lower.toReal then
    ENNReal.ofReal ((upper.toReal - lower.toReal) ^ (-α))
  else 0

@[simp]
theorem widthCost_coe_sub (α upper lower : ℝ) (hwidth : 0 < upper - lower) :
    widthCost α (upper : EReal) (lower : EReal) =
      ENNReal.ofReal ((upper - lower) ^ (-α)) := by
  simp [widthCost, hwidth]

@[simp]
theorem widthCost_top (α : ℝ) (lower : EReal) :
    widthCost α ⊤ lower = 0 := by
  simp [widthCost]

@[simp]
theorem widthCost_bot (α : ℝ) (upper : EReal) :
    widthCost α upper ⊥ = 0 := by
  simp [widthCost]

/-- The `Hα` cost of an `M₂` corridor, integrated over the unit time interval.
The codomain is `ℝ≥0∞` so the integral is defined before finiteness is proved. -/
noncomputable def M2Corridor.energy (α : ℝ) (c : M2Corridor) : ℝ≥0∞ :=
  ∫⁻ t : unitInterval,
    widthCost α (StepBoundary.eval c.upper t) (StepBoundary.eval c.lower t) ∂volume

/-- A finite union of admissible corridors, with the source's strictly
positive minimum-energy condition from class `M₃`. -/
noncomputable def finiteMinimumEnergy (α : ℝ) (count : ℕ) (hcount : 0 < count)
    (pieces : Fin count → M2Corridor) : ℝ≥0∞ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin count)).Nonempty from
    ⟨⟨0, hcount⟩, by simp⟩) fun i => M2Corridor.energy α (pieces i)

structure M3 (α : ℝ) where
  count : ℕ
  count_pos : 0 < count
  pieces : Fin count → M2Corridor
  minimum_energy_pos : 0 < finiteMinimumEnergy α count count_pos pieces

/-- The union represented by an `M₃` datum. -/
def M3.toSet {α : ℝ} (G : M3 α) : Set (CadlagPath unitInterval ℝ) :=
  ⋃ i : Fin G.count, M2Corridor.toSet (G.pieces i)

/-- The `Hα` functional on `M₃`: the minimum of the component corridor
energies. -/
noncomputable def M3.energy {α : ℝ} (G : M3 α) : ℝ≥0∞ :=
  finiteMinimumEnergy α G.count G.count_pos G.pieces

theorem M3.energy_pos {α : ℝ} (G : M3 α) : 0 < G.energy :=
  G.minimum_energy_pos

/-- Membership in class `M₃` is represented by a finite union of `M₂`
corridors satisfying the positive-minimum condition. -/
def IsM₃ (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ A : M3 α, G = M3.toSet A

theorem isM₃_toSet (α : ℝ) (A : M3 α) : IsM₃ α (M3.toSet A) :=
  ⟨A, rfl⟩

end ProbabilityTheory.RandomWalk.Mogulskii
