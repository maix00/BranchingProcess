/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Analysis.Asymptotics.Scale.Inverse.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Set.Nat
/-!
# Level multiplicity of a discrete scale

## Public declarations

For a monotone integer-valued scale `L`, `levelMultiplicity L δ` counts the
widths with the same value as `L δ`. If these multiplicities are eventually
bounded, both generalized inverses of `L δ + 1` are asymptotic to `δ`:
`δ / inverseScale L (L δ + 1) → 1` and
`δ / upperInverseScale L (L δ + 1) → 1`.

The public declarations are `Asymptotics.levelMultiplicity`,
`Asymptotics.HasEventuallyBoundedLevelMultiplicity`,
`Asymptotics.finite_levelSet_of_tendsto_atTop`, and
`Asymptotics.tendsto_width_div_inverseScales_of_boundedLevelMultiplicity`.
-/

public section

open Filter
open scoped BigOperators

namespace Asymptotics

/-- The cardinality of the fiber of an integer-valued scale at the value
`L δ`. -/
noncomputable def levelMultiplicity (L : ℕ → ℕ) (δ : ℕ) : ℕ :=
  ({η | L η = L δ} : Set ℕ).ncard

/-- An integer-valued scale has eventually bounded level multiplicities. -/
def HasEventuallyBoundedLevelMultiplicity (L : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ δ : ℕ in atTop, levelMultiplicity L δ ≤ C

/-- Every level set of a scale tending to infinity is finite. -/
theorem finite_levelSet_of_tendsto_atTop {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (δ : ℕ) :
    ({η | L η = L δ} : Set ℕ).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_atTop.1 hL (L δ + 1))
  apply Set.finite_Iio N |>.subset
  intro η hη
  rw [Set.mem_Iio]
  by_contra hnot
  have hNη : N ≤ η := Nat.le_of_not_gt hnot
  have hlarge := hN η hNη
  rw [hη] at hlarge
  omega

/-- At the threshold `L δ + 1`, the lower inverse lies in the level set of
`L δ`. -/
private lemma inverseScale_level_eq {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (hmono : Monotone L) (δ : ℕ) :
    L (inverseScale L (L δ + 1)) = L δ := by
  have hle := inverseScale_scale_add_one_le L δ
  have hmono' := hmono hle
  have hspec := inverseScale_spec hL (L δ + 1)
  omega

/-- At the threshold `L δ + 1`, the upper inverse also lies in the level set
of `L δ`. -/
private lemma upperInverseScale_level_eq {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (hmono : Monotone L) (δ : ℕ) :
    L (upperInverseScale L (L δ + 1)) = L δ := by
  have hle := (inverseScale_le_width_le_upperInverseScale hL hmono δ).2
  have hmono' := hmono hle
  have hinv := lt_inverseScale_scale_add_two hL hmono δ
  have hylt : upperInverseScale L (L δ + 1) < inverseScale L (L δ + 2) := by
    have hpositive : 0 < inverseScale L (L δ + 2) := by omega
    have hstrict : inverseScale L (L δ + 2) - 1 <
        inverseScale L (L δ + 2) := Nat.sub_lt hpositive (by omega)
    simpa [upperInverseScale_apply, Nat.add_assoc] using hstrict
  have hthreshold := lt_threshold_of_lt_inverseScale hylt
  omega

/-- The lower-inverse-to-width gap is bounded by the cardinality of the
corresponding level set. -/
private lemma inverseScale_gap_le_levelMultiplicity {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (hmono : Monotone L) (δ : ℕ) :
    δ - inverseScale L (L δ + 1) ≤ levelMultiplicity L δ := by
  have hxle := inverseScale_scale_add_one_le L δ
  have hxlevel := inverseScale_level_eq hL hmono δ
  have hsubset : Set.Icc (inverseScale L (L δ + 1)) δ ⊆
      {η : ℕ | L η = L δ} := by
    intro η hη
    simp only [Set.mem_Icc, Set.mem_ofPred_eq] at hη ⊢
    apply Nat.le_antisymm
    · exact hmono hη.2
    · calc
        L δ = L (inverseScale L (L δ + 1)) := hxlevel.symm
        _ ≤ L η := hmono hη.1
  have hcard := Set.ncard_le_ncard hsubset
    (finite_levelSet_of_tendsto_atTop hL δ)
  rw [Set.ncard_Icc_nat] at hcard
  dsimp [levelMultiplicity]
  calc
    δ - inverseScale L (L δ + 1) ≤
        δ + 1 - inverseScale L (L δ + 1) :=
      Nat.sub_le_sub_right (Nat.le_succ δ) _
    _ ≤ ({η : ℕ | L η = L δ} : Set ℕ).ncard := hcard

/-- The upper-inverse-to-width gap is bounded by the cardinality of the
corresponding level set. -/
private lemma upperInverseScale_gap_le_levelMultiplicity {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (hmono : Monotone L) (δ : ℕ) :
    upperInverseScale L (L δ + 1) - δ ≤ levelMultiplicity L δ := by
  have hyle := (inverseScale_le_width_le_upperInverseScale hL hmono δ).2
  have hylevel := upperInverseScale_level_eq hL hmono δ
  have hsubset : Set.Icc δ (upperInverseScale L (L δ + 1)) ⊆
      {η : ℕ | L η = L δ} := by
    intro η hη
    simp only [Set.mem_Icc, Set.mem_ofPred_eq] at hη ⊢
    apply Nat.le_antisymm
    · calc
        L η ≤ L (upperInverseScale L (L δ + 1)) := hmono hη.2
        _ = L δ := hylevel
    · exact hmono hη.1
  have hcard := Set.ncard_le_ncard hsubset
    (finite_levelSet_of_tendsto_atTop hL δ)
  rw [Set.ncard_Icc_nat] at hcard
  dsimp [levelMultiplicity]
  calc
    upperInverseScale L (L δ + 1) - δ ≤
        upperInverseScale L (L δ + 1) + 1 - δ :=
      Nat.sub_le_sub_right
        (Nat.le_succ (upperInverseScale L (L δ + 1))) _
    _ ≤ ({η : ℕ | L η = L δ} : Set ℕ).ncard := hcard

/-- If the level multiplicities of a nondecreasing scale are eventually
bounded, then the scale index is asymptotic to both inverse widths. -/

theorem tendsto_width_div_inverseScales_of_boundedLevelMultiplicity
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop) (hmono : Monotone L)
    (hbounded : HasEventuallyBoundedLevelMultiplicity L) :
    Tendsto (fun δ : ℕ => (δ : ℝ) /
      (inverseScale L (L δ + 1) : ℝ)) atTop (nhds 1) ∧
    Tendsto (fun δ : ℕ => (δ : ℝ) /
      (upperInverseScale L (L δ + 1) : ℝ)) atTop (nhds 1) := by
  obtain ⟨C, hC⟩ := hbounded
  have hindex : Tendsto (fun δ : ℕ => L δ + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [tendsto_atTop.1 hL b] with δ hδ
    omega
  have hxTop : Tendsto (fun δ : ℕ => inverseScale L (L δ + 1)) atTop atTop :=
    (tendsto_inverseScale_atTop hL).comp hindex
  have hyTop : Tendsto (fun δ : ℕ => upperInverseScale L (L δ + 1)) atTop atTop :=
    (tendsto_upperInverseScale_atTop hL).comp hindex
  have hxRealTop : Tendsto
      (fun δ : ℕ => (inverseScale L (L δ + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hxTop
  have hyRealTop : Tendsto
      (fun δ : ℕ => (upperInverseScale L (L δ + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hyTop
  have hxPos : ∀ᶠ δ : ℕ in atTop,
      0 < (inverseScale L (L δ + 1) : ℝ) :=
    hxRealTop.eventually (eventually_gt_atTop 0)
  have hyPos : ∀ᶠ δ : ℕ in atTop,
      0 < (upperInverseScale L (L δ + 1) : ℝ) :=
    hyRealTop.eventually (eventually_gt_atTop 0)
  have hgapX : ∀ᶠ δ : ℕ in atTop,
      δ ≤ inverseScale L (L δ + 1) + C := by
    filter_upwards [hC] with δ hCδ
    have hgap := inverseScale_gap_le_levelMultiplicity hL hmono δ
    have hxle := inverseScale_scale_add_one_le L δ
    omega
  have hgapY : ∀ᶠ δ : ℕ in atTop,
      upperInverseScale L (L δ + 1) ≤ δ + C := by
    filter_upwards [hC] with δ hCδ
    have hgap := upperInverseScale_gap_le_levelMultiplicity hL hmono δ
    have hyle := (inverseScale_le_width_le_upperInverseScale hL hmono δ).2
    omega
  have hCOverX : Tendsto (fun δ : ℕ => (C : ℝ) /
      (inverseScale L (L δ + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hxRealTop
  have hCOverY : Tendsto (fun δ : ℕ => (C : ℝ) /
      (upperInverseScale L (L δ + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hyRealTop
  have hxUpper : Tendsto (fun δ : ℕ => (1 : ℝ) +
      (C : ℝ) / (inverseScale L (L δ + 1) : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hCOverX
  have hyLower : Tendsto (fun δ : ℕ => (1 : ℝ) -
      (C : ℝ) / (upperInverseScale L (L δ + 1) : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hCOverY
  have hxBounds : (fun δ : ℕ => (1 : ℝ)) ≤ᶠ[atTop]
      (fun δ => (δ : ℝ) / (inverseScale L (L δ + 1) : ℝ)) ∧
    (fun δ : ℕ => (δ : ℝ) / (inverseScale L (L δ + 1) : ℝ)) ≤ᶠ[atTop]
      (fun δ => 1 + (C : ℝ) / (inverseScale L (L δ + 1) : ℝ)) := by
    constructor
    · filter_upwards [hxPos] with δ hxδ
      rw [le_div_iff₀ hxδ]
      have hxle : (inverseScale L (L δ + 1) : ℝ) ≤ δ := by
        exact_mod_cast inverseScale_scale_add_one_le L δ
      nlinarith
    · filter_upwards [hxPos, hgapX] with δ hxδ hgapδ
      rw [div_le_iff₀ hxδ]
      have hgapReal : (δ : ℝ) ≤
          (inverseScale L (L δ + 1) : ℝ) + C := by exact_mod_cast hgapδ
      have hxne : (inverseScale L (L δ + 1) : ℝ) ≠ 0 := ne_of_gt hxδ
      field_simp [hxne]
      nlinarith
  have hyBounds : (fun δ : ℕ => (1 : ℝ) -
      (C : ℝ) / (upperInverseScale L (L δ + 1) : ℝ)) ≤ᶠ[atTop]
      (fun δ => (δ : ℝ) / (upperInverseScale L (L δ + 1) : ℝ)) ∧
    (fun δ : ℕ => (δ : ℝ) / (upperInverseScale L (L δ + 1) : ℝ)) ≤ᶠ[atTop]
      (fun δ => (1 : ℝ)) := by
    constructor
    · filter_upwards [hyPos, hgapY] with δ hyδ hgapδ
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hyδ]
      have hgapReal : (upperInverseScale L (L δ + 1) : ℝ) ≤
          (δ : ℝ) + C := by exact_mod_cast hgapδ
      nlinarith
    · filter_upwards [hyPos] with δ hyδ
      rw [div_le_iff₀ hyδ]
      have hδle : (δ : ℝ) ≤ upperInverseScale L (L δ + 1) := by
        exact_mod_cast (inverseScale_le_width_le_upperInverseScale hL hmono δ).2
      nlinarith
  exact ⟨
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hxUpper hxBounds.1 hxBounds.2,
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hyLower tendsto_const_nhds hyBounds.1 hyBounds.2⟩
end Asymptotics
