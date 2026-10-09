/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Basic
public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Boundary.Partition

/-!
# Increasing endpoint cores for an `M₂` step corridor

Trace separation supplies a common interior value at every knot. Choosing
small, strictly increasing core radii then makes each return window wider
than the preceding entrance core. This is the deterministic geometry needed
to concatenate endpoint-constrained segment events across boundary jumps.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The deterministic duration of a nondegenerate common partition cell. -/
noncomputable def commonPartitionCellLength (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) : ℝ :=
  (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ) -
    (StepBoundary.commonPartitionGrid upper lower i.val : ℝ)

/-- Every cell in the common partition has positive duration. -/
theorem commonPartitionCellLength_pos (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    0 < commonPartitionCellLength upper lower i := by
  unfold commonPartitionCellLength
  apply sub_pos.mpr
  exact_mod_cast StepBoundary.commonPartitionGrid_strictSucc
    upper lower i.val i.isLt

/-- A center in the common left/right trace strip at each knot. At time zero
the center is fixed to the pinned value `0`. -/
noncomputable def commonPartitionCoreCenter
    (upper lower : StepBoundary)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) : ℝ :=
  if i.val = 0 then 0 else
    Classical.choose (exists_mem_selValues_of_traceSeparated hsep
      (StepBoundary.commonPartitionGrid upper lower i.val))

theorem commonPartitionCoreCenter_mem
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreCenter upper lower hsep i ∈
      selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) := by
  classical
  by_cases hi : i.val = 0
  · have hi' : i = ⟨0, Nat.pos_of_ne_zero (by
        have hcard := Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
        omega)⟩ := Fin.ext hi
    rw [hi']
    change (0 : ℝ) ∈ selValues upper lower
      (StepBoundary.commonPartitionGrid upper lower 0)
    have hgrid : StepBoundary.commonPartitionGrid upper lower 0 = ⊥ := by
      have hmin : (StepBoundary.commonKnots upper lower).min'
          (StepBoundary.commonKnots_nonempty upper lower) = ⊥ := by
        apply le_antisymm
        · exact Finset.min'_le _ _
            (StepBoundary.bot_mem_commonKnots upper lower)
        · exact bot_le
      simpa only [StepBoundary.commonPartitionGrid, Nat.zero_min,
        Finset.orderEmbOfFin_zero] using hmin
    rw [hgrid]
    change max (lower.leftTrace ⊥) (lower.rightTrace ⊥) < (0 : EReal) ∧
      (0 : EReal) < min (upper.leftTrace ⊥) (upper.rightTrace ⊥)
    rw [StepBoundary.leftTrace_bot, StepBoundary.rightTrace_eq_eval,
      StepBoundary.leftTrace_bot, StepBoundary.rightTrace_eq_eval,
      max_self, min_self]
    exact hstart
  · have hspec := Classical.choose_spec
      (exists_mem_selValues_of_traceSeparated hsep
        (StepBoundary.commonPartitionGrid upper lower i.val))
    simpa [commonPartitionCoreCenter, hi] using hspec

/-- A positive neighborhood size around each knot center that stays within
both traces of both step boundaries. -/
noncomputable def commonPartitionCoreMargin
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) : ℝ :=
  Classical.choose (exists_pos_uniformMargin_selValues
    (commonPartitionCoreCenter_mem upper lower hstart hsep i))

theorem commonPartitionCoreMargin_pos
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    0 < commonPartitionCoreMargin upper lower hstart hsep i :=
  (Classical.choose_spec (exists_pos_uniformMargin_selValues
    (commonPartitionCoreCenter_mem upper lower hstart hsep i))).1

theorem commonPartitionCoreMargin_mem
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card)
    (y : ℝ)
    (hy : |y - commonPartitionCoreCenter upper lower hsep i| ≤
      commonPartitionCoreMargin upper lower hstart hsep i) :
    y ∈ selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) :=
  (Classical.choose_spec (exists_pos_uniformMargin_selValues
    (commonPartitionCoreCenter_mem upper lower hstart hsep i))).2 y hy

/-- A common positive increase in endpoint-core radius, chosen below every
trace-strip margin and divided by the number of knots. -/
noncomputable def commonPartitionCoreRadiusStep
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) : ℝ := by
  classical
  let cardPos : 0 < (StepBoundary.commonKnots upper lower).card :=
    Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
  have hne : (Finset.univ : Finset (Fin (StepBoundary.commonKnots upper lower).card)).Nonempty :=
    ⟨⟨0, cardPos⟩, Finset.mem_univ _⟩
  exact (Finset.univ.inf' hne
    (commonPartitionCoreMargin upper lower hstart hsep)) /
      (StepBoundary.commonKnots upper lower).card

theorem commonPartitionCoreRadiusStep_pos
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) :
    0 < commonPartitionCoreRadiusStep upper lower hstart hsep := by
  classical
  let cardPos : 0 < (StepBoundary.commonKnots upper lower).card :=
    Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
  have hne : (Finset.univ : Finset (Fin (StepBoundary.commonKnots upper lower).card)).Nonempty :=
    ⟨⟨0, cardPos⟩, Finset.mem_univ _⟩
  change 0 <
    (Finset.univ.inf' hne
      (commonPartitionCoreMargin upper lower hstart hsep)) /
        (StepBoundary.commonKnots upper lower).card
  apply div_pos
  · apply (Finset.lt_inf'_iff hne).2
    intro i hi
    exact commonPartitionCoreMargin_pos upper lower hstart hsep i
  · exact Nat.cast_pos.mpr
      (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))

/-- Endpoint-core radii increase linearly from the pinned initial value `0`.
Every radius remains within the corresponding common trace strip. -/
noncomputable def commonPartitionCoreRadius
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) : ℝ :=
  (i.val : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep

theorem commonPartitionCoreRadius_zero
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) :
    commonPartitionCoreRadius upper lower hstart hsep
      ⟨0, Nat.pos_of_ne_zero (by
        have hcard := Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
        omega)⟩ = 0 := by
  simp [commonPartitionCoreRadius]

private theorem commonPartitionCoreRadius_lt_margin
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreRadius upper lower hstart hsep i <
      commonPartitionCoreMargin upper lower hstart hsep i := by
  classical
  let cardPos : 0 < (StepBoundary.commonKnots upper lower).card :=
    Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
  have hne : (Finset.univ : Finset (Fin (StepBoundary.commonKnots upper lower).card)).Nonempty :=
    ⟨⟨0, cardPos⟩, Finset.mem_univ _⟩
  let cardR : ℝ := (StepBoundary.commonKnots upper lower).card
  let least := Finset.univ.inf'
    hne (commonPartitionCoreMargin upper lower hstart hsep)
  have hcardPos : 0 < cardR := by
    dsimp [cardR]
    exact Nat.cast_pos.mpr
      (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
  have hstepPos : 0 < commonPartitionCoreRadiusStep upper lower hstart hsep :=
    commonPartitionCoreRadiusStep_pos upper lower hstart hsep
  have hi : (i.val : ℝ) < cardR := by
    dsimp [cardR]
    exact_mod_cast i.isLt
  have hleast : least ≤ commonPartitionCoreMargin upper lower hstart hsep i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  calc
    commonPartitionCoreRadius upper lower hstart hsep i =
        (i.val : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep := rfl
    _ < cardR * commonPartitionCoreRadiusStep upper lower hstart hsep :=
      mul_lt_mul_of_pos_right hi hstepPos
    _ = least := by
      dsimp [cardR, least, commonPartitionCoreRadiusStep]
      field_simp [ne_of_gt (Nat.cast_pos.mpr
        (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)))]
    _ ≤ commonPartitionCoreMargin upper lower hstart hsep i := hleast

theorem commonPartitionCoreRadius_nonneg
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    0 ≤ commonPartitionCoreRadius upper lower hstart hsep i := by
  simp only [commonPartitionCoreRadius]
  exact mul_nonneg (Nat.cast_nonneg _) (commonPartitionCoreRadiusStep_pos
    upper lower hstart hsep).le

theorem commonPartitionCoreRadius_mem
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreCenter upper lower hsep i -
        commonPartitionCoreRadius upper lower hstart hsep i ∈
          selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) ∧
      commonPartitionCoreCenter upper lower hsep i +
        commonPartitionCoreRadius upper lower hstart hsep i ∈
          selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) := by
  have hradius : 0 ≤ commonPartitionCoreRadius upper lower hstart hsep i :=
    commonPartitionCoreRadius_nonneg upper lower hstart hsep i
  have hsmall := commonPartitionCoreRadius_lt_margin upper lower hstart hsep i
  constructor
  · apply commonPartitionCoreMargin_mem upper lower hstart hsep i
    rw [abs_of_nonpos (by linarith :
      commonPartitionCoreCenter upper lower hsep i -
        commonPartitionCoreRadius upper lower hstart hsep i -
        commonPartitionCoreCenter upper lower hsep i ≤ 0)]
    linarith
  · apply commonPartitionCoreMargin_mem upper lower hstart hsep i
    rw [abs_of_nonneg (by linarith : 0 ≤
      commonPartitionCoreCenter upper lower hsep i +
        commonPartitionCoreRadius upper lower hstart hsep i -
        commonPartitionCoreCenter upper lower hsep i)]
    linarith

/-- A smaller positive increment for the endpoint cores. The parameter `η`
lets the entire core system be made uniformly small while preserving strict
growth from the pinned initial radius. -/
noncomputable def commonPartitionCoreRadiusStepSmall
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) (η : ℝ) : ℝ :=
  min (η / (StepBoundary.commonKnots upper lower).card)
    (commonPartitionCoreRadiusStep upper lower hstart hsep)

theorem commonPartitionCoreRadiusStepSmall_pos
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) {η : ℝ} (hη : 0 < η) :
    0 < commonPartitionCoreRadiusStepSmall upper lower hstart hsep η := by
  change 0 < min (η / (StepBoundary.commonKnots upper lower).card)
    (commonPartitionCoreRadiusStep upper lower hstart hsep)
  exact lt_min (div_pos hη (Nat.cast_pos.mpr
      (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)))
    ) (commonPartitionCoreRadiusStep_pos upper lower hstart hsep)

/-- Endpoint-core radii with a user-specified uniform upper bound. -/
noncomputable def commonPartitionCoreRadiusSmall
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) (η : ℝ)
    (i : Fin (StepBoundary.commonKnots upper lower).card) : ℝ :=
  (i.val : ℝ) * commonPartitionCoreRadiusStepSmall upper lower hstart hsep η

theorem commonPartitionCoreRadiusSmall_nonneg
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) {η : ℝ} (hη : 0 < η)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    0 ≤ commonPartitionCoreRadiusSmall upper lower hstart hsep η i := by
  simp only [commonPartitionCoreRadiusSmall]
  exact mul_nonneg (Nat.cast_nonneg _)
    (commonPartitionCoreRadiusStepSmall_pos upper lower hstart hsep hη).le

theorem commonPartitionCoreRadiusSmall_le
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) (η : ℝ)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreRadiusSmall upper lower hstart hsep η i ≤
      commonPartitionCoreRadius upper lower hstart hsep i := by
  simp only [commonPartitionCoreRadiusSmall, commonPartitionCoreRadius]
  exact mul_le_mul_of_nonneg_left
    (min_le_right _ _) (Nat.cast_nonneg _)

theorem commonPartitionCoreRadiusSmall_lt_margin
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) (η : ℝ)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreRadiusSmall upper lower hstart hsep η i <
      commonPartitionCoreMargin upper lower hstart hsep i := by
  exact (commonPartitionCoreRadiusSmall_le upper lower hstart hsep η i).trans_lt
    (commonPartitionCoreRadius_lt_margin upper lower hstart hsep i)

theorem commonPartitionCoreRadiusSmall_mem
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) {η : ℝ} (hη : 0 < η)
    (i : Fin (StepBoundary.commonKnots upper lower).card) :
    commonPartitionCoreCenter upper lower hsep i -
        commonPartitionCoreRadiusSmall upper lower hstart hsep η i ∈
          selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) ∧
      commonPartitionCoreCenter upper lower hsep i +
        commonPartitionCoreRadiusSmall upper lower hstart hsep η i ∈
          selValues upper lower (StepBoundary.commonPartitionGrid upper lower i.val) := by
  have hradius := commonPartitionCoreRadiusSmall_nonneg upper lower hstart hsep hη i
  have hmargin := commonPartitionCoreRadiusSmall_lt_margin upper lower hstart hsep η i
  constructor
  · apply commonPartitionCoreMargin_mem upper lower hstart hsep i
    rw [abs_of_nonpos (by linarith :
      commonPartitionCoreCenter upper lower hsep i -
        commonPartitionCoreRadiusSmall upper lower hstart hsep η i -
        commonPartitionCoreCenter upper lower hsep i ≤ 0)]
    linarith
  · apply commonPartitionCoreMargin_mem upper lower hstart hsep i
    rw [abs_of_nonneg (by linarith : 0 ≤
      commonPartitionCoreCenter upper lower hsep i +
        commonPartitionCoreRadiusSmall upper lower hstart hsep η i -
        commonPartitionCoreCenter upper lower hsep i)]
    linarith

/-- Endpoint cores can be chosen with arbitrarily small radii, while keeping
the strict increase and trace containment needed by the return-kernel proof. -/
theorem exists_commonPartitionEndpointCores_small
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) {η : ℝ} (hη : 0 < η) :
    ∃ center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ,
      center ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      radius ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        radius ⟨i.val + 1, by
          have hcard := Nat.sub_add_cancel
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
          omega⟩ > radius ⟨i.val, by omega⟩) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card, radius j < η) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card, 0 ≤ radius j) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card,
        center j - radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val) ∧
        center j + radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val)) := by
  let center := commonPartitionCoreCenter upper lower hsep
  let radius := commonPartitionCoreRadiusSmall upper lower hstart hsep η
  refine ⟨center, radius, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [center, commonPartitionCoreCenter]
  · simp [radius, commonPartitionCoreRadiusSmall]
  · intro i
    have hcard := Nat.sub_add_cancel
      (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
    dsimp [radius, commonPartitionCoreRadiusSmall]
    push_cast
    change
      (i.val + 1 : ℝ) * commonPartitionCoreRadiusStepSmall upper lower hstart hsep η >
        (i.val : ℝ) * commonPartitionCoreRadiusStepSmall upper lower hstart hsep η
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val)
      (commonPartitionCoreRadiusStepSmall_pos upper lower hstart hsep hη)
  · intro j
    have hcardPos : 0 < (StepBoundary.commonKnots upper lower).card :=
      Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
    have hcardR : 0 < ((StepBoundary.commonKnots upper lower).card : ℝ) :=
      Nat.cast_pos.mpr hcardPos
    have hj : (j.val : ℝ) < (StepBoundary.commonKnots upper lower).card := by
      exact_mod_cast j.isLt
    have hstepPos := commonPartitionCoreRadiusStepSmall_pos
      upper lower hstart hsep hη
    have hstepLe := min_le_left
      (η / (StepBoundary.commonKnots upper lower).card)
      (commonPartitionCoreRadiusStep upper lower hstart hsep)
    calc
      radius j = (j.val : ℝ) *
          commonPartitionCoreRadiusStepSmall upper lower hstart hsep η := rfl
      _ < (StepBoundary.commonKnots upper lower).card *
          commonPartitionCoreRadiusStepSmall upper lower hstart hsep η :=
        mul_lt_mul_of_pos_right hj hstepPos
      _ ≤ (StepBoundary.commonKnots upper lower).card *
          (η / (StepBoundary.commonKnots upper lower).card) :=
        mul_le_mul_of_nonneg_left hstepLe hcardR.le
      _ = η := by field_simp [ne_of_gt hcardR]
  · intro j
    exact commonPartitionCoreRadiusSmall_nonneg upper lower hstart hsep hη j
  · intro j
    exact commonPartitionCoreRadiusSmall_mem upper lower hstart hsep hη j

/-- The selected cores expand strictly at each partition step, while both
ends of every core remain inside the common incoming/outgoing trace strip. -/
theorem exists_commonPartitionEndpointCores
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) :
    ∃ center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ,
      center ⟨0, Nat.pos_of_ne_zero (by
        have hcard := Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
        omega)⟩ = 0 ∧
      radius ⟨0, Nat.pos_of_ne_zero (by
        have hcard := Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
        omega)⟩ = 0 ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        radius ⟨i.val + 1, by
          have hcard := Nat.sub_add_cancel
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
          omega⟩ > radius ⟨i.val, by omega⟩) ∧
      (∀ i : Fin (StepBoundary.commonKnots upper lower).card,
        center i - radius i ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower i.val) ∧
        center i + radius i ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower i.val)) := by
  refine ⟨commonPartitionCoreCenter upper lower hsep,
    commonPartitionCoreRadius upper lower hstart hsep, ?_, ?_, ?_, ?_⟩
  · simp [commonPartitionCoreCenter]
  · exact commonPartitionCoreRadius_zero upper lower hstart hsep
  · intro i
    have hcard := Nat.sub_add_cancel
      (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
    dsimp [commonPartitionCoreRadius]
    push_cast
    change
      (i.val + 1 : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep >
        (i.val : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val)
      (commonPartitionCoreRadiusStep_pos upper lower hstart hsep)
  · intro i
    exact commonPartitionCoreRadius_mem upper lower hstart hsep i

/-- A local increment that stays in the corridor contracted by the current
endpoint core keeps the translated path in the original corridor. -/
theorem add_mem_corridor_of_core_and_increment
    {lower upper center radius start increment : ℝ}
    (hstartLower : center - radius ≤ start)
    (hstartUpper : start ≤ center + radius)
    (hincrementLower : lower + radius - center < increment)
    (hincrementUpper : increment < upper - radius - center) :
    lower < start + increment ∧ start + increment < upper := by
  constructor <;> linarith

/-- An endpoint increment in a sufficiently narrow band around the change of
core center sends every point of the old closed core strictly inside the new
core. The strict inequality on the band width handles the closed upper end
of the source's `Ioc` return window. -/
theorem add_mem_nextCore_of_endpointBand
    {center₀ center₁ radius₀ radius₁ bandRadius start increment : ℝ}
    (hstartLower : center₀ - radius₀ ≤ start)
    (hstartUpper : start ≤ center₀ + radius₀)
    (_hband : 0 < bandRadius)
    (hbandSmall : bandRadius < radius₁ - radius₀)
    (hincrementLower : center₁ - center₀ - bandRadius < increment)
    (hincrementUpper : increment ≤ center₁ - center₀ + bandRadius) :
    center₁ - radius₁ < start + increment ∧
      start + increment < center₁ + radius₁ := by
  constructor <;> linarith

/-- Successive cores that fit in the incoming finite corridor determine an
endpoint band which is both narrower than the increase in core radius and
strictly inside the corridor contracted by the current core. -/
theorem exists_endpointBand_in_contractedCorridor
    {lower upper center₀ center₁ radius₀ radius₁ : ℝ}
    (hradius : radius₀ < radius₁)
    (hnextLower : lower < center₁ - radius₁)
    (hnextUpper : center₁ + radius₁ < upper) :
    ∃ bandRadius : ℝ, 0 < bandRadius ∧
      bandRadius < radius₁ - radius₀ ∧
      lower + radius₀ - center₀ < center₁ - center₀ - bandRadius ∧
      center₁ - center₀ + bandRadius < upper - radius₀ - center₀ := by
  refine ⟨(radius₁ - radius₀) / 2, half_pos (sub_pos.mpr hradius), ?_, ?_⟩
  · linarith
  · constructor
    · have hdist : lower + radius₀ - center₀ <
          center₁ - center₀ - (radius₁ - radius₀) := by linarith
      linarith
    · have hdist : center₁ - center₀ + (radius₁ - radius₀) <
          upper - radius₀ - center₀ := by linarith
      linarith

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
