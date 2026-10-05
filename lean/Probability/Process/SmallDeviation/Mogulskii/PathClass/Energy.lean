/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Basic

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

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

private theorem lintegral_congr_off_top {f g : unitInterval → ℝ≥0∞}
    (hfg : ∀ t, t ≠ ⊤ → f t = g t) :
    ∫⁻ t : unitInterval, f t ∂volume = ∫⁻ t : unitInterval, g t ∂volume := by
  apply lintegral_congr_ae
  have hne : ∀ᵐ t : unitInterval ∂volume, t ≠ ⊤ :=
    (countable_singleton (⊤ : unitInterval)).ae_notMem volume
  filter_upwards [hne] with t ht
  exact hfg t ht

/-- A nonnegative integrand supported only at the right endpoint has zero
Lebesgue integral. This is the measure-theoretic reason a terminal boundary
knot changes no `Hα` energy. -/
private theorem lintegral_eq_zero_of_eq_zero_off_top {f : unitInterval → ℝ≥0∞}
    (hf : ∀ t, t ≠ ⊤ → f t = 0) :
    ∫⁻ t : unitInterval, f t ∂volume = 0 := by
  rw [lintegral_congr_off_top hf]
  simp

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

/-- The pair of upper and lower level indices active at a time. -/
noncomputable def M2Corridor.levelPairIndex (c : M2Corridor) (t : unitInterval) :=
  (c.upper.levelIndex t, c.lower.levelIndex t)

theorem M2Corridor.levelPairIndex_measurable (c : M2Corridor) :
    Measurable c.levelPairIndex :=
  c.upper.levelIndex_measurable.prodMk c.lower.levelIndex_measurable

/-- The level-pair map as a simple function. Its nonempty fibers are the
finite measurable cells on which the corridor width, and hence its energy
density, is constant. -/
noncomputable def M2Corridor.levelPairIndexSimple (c : M2Corridor) :
    SimpleFunc unitInterval (Fin (c.upper.knots.card + 1) ×
      Fin (c.lower.knots.card + 1)) := by
  classical
  refine SimpleFunc.mk c.levelPairIndex (fun p => ?_) ?_
  · exact c.levelPairIndex_measurable (measurableSet_singleton p)
  · apply Set.Finite.subset (Set.finite_univ :
      (Set.univ : Set (Fin (c.upper.knots.card + 1) ×
        Fin (c.lower.knots.card + 1))).Finite)
    rintro p ⟨t, rfl⟩
    exact Set.mem_univ _

/-- The energy is the finite sum over the measurable cells on which the
upper and lower step levels are fixed. Each coefficient is the Lebesgue
measure (time length) of its level-pair cell. This is an exact finite
partition form of the integral and does not require expanding the partition
into an ordered list of breakpoints. -/
theorem M2Corridor.energy_eq_finiteLevelCellSum (α : ℝ) (c : M2Corridor) :
    M2Corridor.energy α c =
      ∑ p ∈ c.levelPairIndexSimple.range,
        widthCost α (c.upper.levels p.1) (c.lower.levels p.2) *
          volume (c.levelPairIndex ⁻¹' {p}) := by
  classical
  let cost : Fin (c.upper.knots.card + 1) × Fin (c.lower.knots.card + 1) → ℝ≥0∞ :=
    fun p => widthCost α (c.upper.levels p.1) (c.lower.levels p.2)
  change (∫⁻ t : unitInterval,
      widthCost α (c.upper.eval t) (c.lower.eval t) ∂volume) = _
  change (∫⁻ t : unitInterval, cost (c.levelPairIndex t) ∂volume) = _
  calc
    _ = ∫⁻ t : unitInterval,
        (SimpleFunc.map cost c.levelPairIndexSimple) t ∂volume := by
      apply lintegral_congr
      intro t
      rw [SimpleFunc.coe_map]
      rfl
    _ = (SimpleFunc.map cost c.levelPairIndexSimple).lintegral volume :=
      SimpleFunc.lintegral_eq_lintegral _ _
    _ = _ := by rw [SimpleFunc.map_lintegral]; rfl

/-- On a constant-width corridor the energy is the width cost itself, since
the unit time interval has volume one. This is the one-cell case of the finite
partition formula. -/
theorem M2Corridor.energy_eq_widthCost_of_constant_values
    (α : ℝ) (c : M2Corridor) (upper lower : EReal)
    (hu : ∀ t, c.upper.eval t = upper)
    (hl : ∀ t, c.lower.eval t = lower) :
    M2Corridor.energy α c = widthCost α upper lower := by
  unfold M2Corridor.energy
  simp_rw [hu, hl]
  simp

/-- Changing the endpoint values of either step boundary does not change the
energy, provided the boundaries agree at all times before the endpoint. -/
theorem M2Corridor.energy_eq_of_boundaries_eq_off_top
    {α : ℝ} {c d : M2Corridor}
    (hu : ∀ t, t ≠ ⊤ → c.upper.eval t = d.upper.eval t)
    (hl : ∀ t, t ≠ ⊤ → c.lower.eval t = d.lower.eval t) :
    M2Corridor.energy α c = M2Corridor.energy α d := by
  change (∫⁻ t : unitInterval,
      widthCost α (c.upper.eval t) (c.lower.eval t) ∂volume) =
    ∫⁻ t : unitInterval,
      widthCost α (d.upper.eval t) (d.lower.eval t) ∂volume
  apply lintegral_congr_off_top
  intro t ht
  rw [hu t ht, hl t ht]

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

end ProbabilityTheory.Process.SmallDeviation.Mogulskii
