/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Corridor.Interpolation
public import Combinatorics.BranchingWalk.Walk.Path.Skorokhod
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Corridor membership of càdlàg walk paths

The positive-uniform-margin corridor in Skorokhod path space is identified
with the strict finite-grid tube event for a normalized random-walk path.
-/

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- Every value of the normalized step path is a grid-vertex value of its
polygonal interpolation. -/
theorem exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (t : unitInterval) :
    ∃ s : unitInterval,
      normalizedLinearContinuousPathIcc scale n increment s =
        normalizedStepCadlagPathIcc scale n increment t := by
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hkn : k ≤ n := natFloor_mul_le_of_mem_unitInterval n t
  let s : unitInterval :=
    ⟨(k : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by positivity)]
        exact_mod_cast hkn⟩
  refine ⟨s, ?_⟩
  rw [normalizedLinearContinuousPathIcc_apply]
  change normalizedLinearPath scale n increment ((k : ℝ) / n) =
    normalizedStepPath scale n increment t
  rw [normalizedLinearPath_grid scale hn hkn, normalizedStepPath]

/-- Membership of a normalized càdlàg step path in a constant open
Skorokhod corridor is equivalent to the corresponding strict grid
inequalities.  The interval may have arbitrary width as long as it contains
the time-zero position. -/
theorem normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenInterval lower upper ↔
      InOpenCorridorOnGrid scale n (fun _ ↦ lower) (fun _ ↦ upper)
        increment := by
  constructor
  · rintro ⟨margin, hmargin, hpath⟩ k
    let t : unitInterval :=
      ⟨((k.val + 1 : ℕ) : ℝ) / n, by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have ht := hpath t
    change lower + margin ≤ normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ∧
      normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ≤ upper - margin at ht
    dsimp only [InOpenCorridorOnGrid]
    rw [normalizedStepPath_grid scale hn] at ht ⊢
    constructor <;> linarith
  · intro hgrid
    have hlinear : normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInOpenInterval lower upper :=
      (normalizedLinearContinuousPathIcc_mem_rangeInOpenInterval_iff
        scale hn hlower hupper increment).2 hgrid
    obtain ⟨margin, hmargin, hpath⟩ :=
      (Skorokhod.ofContinuousMap_mem_rangeInOpenInterval_iff
        (lt_trans hlower hupper)
        (normalizedLinearContinuousPathIcc scale n increment)).2 hlinear
    refine ⟨margin, hmargin, fun t ↦ ?_⟩
    obtain ⟨s, hs⟩ :=
      exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
        scale hn increment t
    simpa [hs] using hpath s

/-- A centered open corridor of arbitrary positive normalized width is the
strict horizontal tube with that width in the original coordinates. -/
theorem normalizedStepCadlagPathIcc_mem_centeredOpenInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width : ℝ} (hwidth : 0 < width) (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2) ↔
      InOpenHorizontalTube (1 / 2) (width * scale n) n increment := by
  rw [normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
    scale hn (by linarith) (by linarith)]
  constructor <;> intro h k
  · have hk := h k
    dsimp only at hk
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div] at hk
    change -(1 / 2 : ℝ) * (width * scale n) <
        partialSum (k + 1) increment ∧
      partialSum (k + 1) increment <
        (1 - (1 / 2 : ℝ)) * (width * scale n)
    have hkl := (lt_div_iff₀ hscale).mp hk.1
    have hku := (div_lt_iff₀ hscale).mp hk.2
    constructor <;> nlinarith
  · have hk := h k
    dsimp only
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div]
    change -(1 / 2 : ℝ) * (width * scale n) <
        partialSum (k + 1) increment ∧
      partialSum (k + 1) increment <
        (1 - (1 / 2 : ℝ)) * (width * scale n) at hk
    constructor
    · apply (lt_div_iff₀ hscale).mpr
      nlinarith [hk.1]
    · apply (div_lt_iff₀ hscale).mpr
      nlinarith [hk.2]

/-- The normalized càdlàg step path has a positive uniform margin inside the
horizontal interval exactly when all its positive grid values satisfy the
strict finite tube inequalities. -/
theorem normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenInterval (-a) (1 - a) ↔
      InOpenHorizontalTube a (scale n) n increment := by
  constructor
  · rintro ⟨margin, hmargin, hpath⟩ k
    let t : unitInterval :=
      ⟨((k.val + 1 : ℕ) : ℝ) / n, by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have ht := hpath t
    change -a + margin ≤ normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ∧
      normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ≤ 1 - a - margin at ht
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div] at ht
    constructor
    · apply (lt_div_iff₀ hscale).mp
      linarith [ht.1]
    · apply (div_lt_iff₀ hscale).mp
      linarith [ht.2]
  · intro htube
    have hlinear : normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInOpenInterval (-a) (1 - a) :=
      (normalizedLinearContinuousPathIcc_mem_horizontalCorridor_iff
        scale hn hscale ha haOne increment).2 htube
    obtain ⟨margin, hmargin, hpath⟩ :=
      (Skorokhod.ofContinuousMap_mem_rangeInOpenInterval_iff
        (by linarith : -a < 1 - a)
        (normalizedLinearContinuousPathIcc scale n increment)).2 hlinear
    refine ⟨margin, hmargin, fun t => ?_⟩
    obtain ⟨s, hs⟩ :=
      exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
        scale hn increment t
    simpa [hs] using hpath s

/-- Closed Skorokhod corridor membership of the normalized step path is
exactly the weak finite horizontal tube event. -/
theorem normalizedStepCadlagPathIcc_mem_rangeInClosedInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedInterval (-a) (1 - a) ↔
      InHorizontalTube a (scale n) n increment := by
  constructor
  · intro h k
    let t : unitInterval :=
      ⟨((k.val + 1 : ℕ) : ℝ) / n, by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have ht := h t
    change -a ≤ normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ∧
      normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ≤ 1 - a at ht
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div] at ht
    exact ⟨(le_div_iff₀ hscale).mp ht.1,
      (div_le_iff₀ hscale).mp ht.2⟩
  · intro htube t
    have hlinear : normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInClosedInterval (-a) (1 - a) :=
      (normalizedLinearContinuousPathIcc_mem_closedHorizontalCorridor_iff
        scale hn hscale ha haOne increment).2 htube
    obtain ⟨s, hs⟩ :=
      exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
        scale hn increment t
    have hvalue :=
      (ContinuousMap.mem_rangeInClosedInterval_iff.mp hlinear) s
    simpa [hs] using hvalue

end Combinatorics.Branching.Walk
