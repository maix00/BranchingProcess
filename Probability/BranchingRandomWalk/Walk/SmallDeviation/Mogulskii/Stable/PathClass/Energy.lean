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

theorem widthCost_lt_top (α : ℝ) (upper lower : EReal) :
    widthCost α upper lower < ⊤ := by
  unfold widthCost
  split_ifs <;> simp [ENNReal.ofReal_lt_top]

/-- The `Hα` cost of an `M₂` corridor, integrated over the unit time interval.
The codomain is `ℝ≥0∞` so the integral is defined before finiteness is proved. -/
noncomputable def M2Corridor.energy (α : ℝ) (c : M2Corridor) : ℝ≥0∞ :=
  ∫⁻ t : unitInterval,
    widthCost α (StepBoundary.eval c.upper t) (StepBoundary.eval c.lower t) ∂volume

/-- A finite-step corridor has finite `Hα` energy. Its density takes only
finitely many finite values, one for each pair of step levels. -/
theorem M2Corridor.energy_lt_top (α : ℝ) (c : M2Corridor) :
    M2Corridor.energy α c < ⊤ := by
  let levelCosts : Finset ℝ≥0∞ :=
    (Finset.univ.product Finset.univ).image fun p =>
      widthCost α (c.upper.levels p.1) (c.lower.levels p.2)
  have hlevelCosts_lt_top : levelCosts.sup id < ⊤ := by
    rw [Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact widthCost_lt_top α _ _
  have hbound (t : unitInterval) :
      widthCost α (c.upper.eval t) (c.lower.eval t) ≤ levelCosts.sup id := by
    change id (widthCost α (c.upper.eval t) (c.lower.eval t)) ≤ levelCosts.sup id
    apply Finset.le_sup
    dsimp [levelCosts]
    apply Finset.mem_image.mpr
    refine ⟨(c.upper.levelIndex t, c.lower.levelIndex t), ?_, ?_⟩
    · simp
    · rfl
  calc
    M2Corridor.energy α c ≤ ∫⁻ _ : unitInterval, levelCosts.sup id ∂volume :=
      lintegral_mono hbound
    _ = levelCosts.sup id := by simp
    _ < ⊤ := hlevelCosts_lt_top

/-- A finite union of admissible corridors, with the source's strictly
positive minimum-energy condition from class `M₃`. -/
noncomputable def finiteMinimumEnergy (α : ℝ) (count : ℕ) (hcount : 0 < count)
    (pieces : Fin count → M2Corridor) : ℝ≥0∞ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin count)).Nonempty from
    ⟨⟨0, hcount⟩, by simp⟩) fun i => M2Corridor.energy α (pieces i)

theorem finiteMinimumEnergy_lt_top (α : ℝ) (count : ℕ) (hcount : 0 < count)
    (pieces : Fin count → M2Corridor) :
    finiteMinimumEnergy α count hcount pieces < ⊤ := by
  let i : Fin count := ⟨0, hcount⟩
  have hi : i ∈ (Finset.univ : Finset (Fin count)) := by simp
  have hmin : finiteMinimumEnergy α count hcount pieces ≤
      M2Corridor.energy α (pieces i) := by
    unfold finiteMinimumEnergy
    exact Finset.inf'_le _ hi
  exact hmin.trans_lt (M2Corridor.energy_lt_top α (pieces i))

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

theorem M3.energy_lt_top {α : ℝ} (G : M3 α) : G.energy < ⊤ :=
  finiteMinimumEnergy_lt_top α G.count G.count_pos G.pieces

/-- The real-valued `Hα` functional on `M₃`, obtained from its finite
extended-real minimum. -/
noncomputable def M3.hAlpha {α : ℝ} (G : M3 α) : ℝ := G.energy.toReal

theorem M3.hAlpha_pos {α : ℝ} (G : M3 α) : 0 < G.hAlpha :=
  ENNReal.toReal_pos (ne_of_gt G.energy_pos) G.energy_lt_top.ne

/-- Membership in class `M₃` is represented by a finite union of `M₂`
corridors satisfying the positive-minimum condition. -/
def IsM₃ (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ A : M3 α, G = M3.toSet A

theorem isM₃_toSet (α : ℝ) (A : M3 α) : IsM₃ α (M3.toSet A) :=
  ⟨A, rfl⟩

end ProbabilityTheory.RandomWalk.Mogulskii
