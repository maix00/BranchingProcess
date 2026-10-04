/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.TwoBins

/-!
# A uniform return-block constant

Short-time directional return events and exact stable scaling produce a
positive unit-time return probability. The same probability then controls
every member of a shrinking-width family through the two-bin block bound.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal

/-- Two-sided increment mass supplies a single positive unit-time constant
for both directional return events, after choosing a sufficiently wide
spatial corridor. -/
theorem IsStableLevyProcess.exists_positive_unit_directionalReturn
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    ∃ δ : ℝ, 0 < δ ∧
      0 < (P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ 0 δ) ⊓
        P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ (-δ) 0)) := by
  obtain ⟨n, hn⟩ := (h.eventually_firstBlock_directionalReturn_probabilities_pos
    1 (-1) 1 (by norm_num) (by norm_num) (by norm_num) hpos hneg).exists
  let scale : ℝ :=
    ((rationalUniformBlockBoundary (n + 1) 1 (Nat.succ_pos n) : ℝ≥0) : ℝ) ^
      (-(1 / α))
  have hscale : 0 < scale := by
    dsimp [scale]
    apply Real.rpow_pos_of_pos
    apply NNReal.coe_pos.mpr
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    change 0 < (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
    positivity
  refine ⟨scale, hscale, ?_⟩
  rw [h.firstBlock_corridorReturn_scale_inv (n + 1) (Nat.succ_pos n)
      (-1) 1 0 1,
    h.firstBlock_corridorReturn_scale_inv (n + 1) (Nat.succ_pos n)
      (-1) 1 (-1) 0] at hn
  simpa [scale] using (lt_min hn.1 hn.2)

/-- One fixed pair of unit-time return probabilities controls every
uniform partition. For `blocks` pieces, the target tube width is the fixed
return scale divided by the stable spatial scaling factor. -/
theorem IsStableLevyProcess.unit_directionalReturn_pow_le_tube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    let scale : ℝ :=
      ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
    (P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ₀) δ₀ 0 δ₀) ⊓
      P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ₀) δ₀ (-δ₀) 0)) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (7 * δ₀ / scale)) := by
  let scale : ℝ :=
    ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _
  let δ : ℝ := δ₀ / scale
  have hδ : 0 < δ := div_pos hδ₀ hscale
  have hδscale : δ * scale = δ₀ := by
    dsimp [δ]
    exact div_mul_cancel₀ δ₀ (ne_of_gt hscale)
  have hbound := h.min_scaled_directional_probabilities_pow_le_rationalHorizonTube
    blocks hblocks (-3 * δ) (3 * δ) δ hδ (-δ) δ δ
    (by constructor <;> linarith)
    (by linarith) (by linarith)
  have hwidth : 3 * δ - (-3 * δ) + δ = 7 * δ := by ring
  rw [hwidth] at hbound
  have hwidth' : 7 * δ = 7 * δ₀ / scale := by
    dsimp [δ]
    ring
  rw [hwidth'] at hbound
  dsimp only [scale] at hδscale
  dsimp only at hbound
  rw [hδscale] at hbound
  rw [neg_mul, hδscale] at hbound
  simpa [scale] using hbound

/-- A single positive constant gives an exponential lower bound throughout
the canonical stable shrinking-width sequence. This establishes finiteness
of the lower escape exponent along these widths; identifying its limit and
the sharp constant is a separate step. -/
theorem IsStableLevyProcess.exists_exponential_tube_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    ∃ δ₀ : ℝ, ∃ c : ENNReal, 0 < δ₀ ∧ 0 < c ∧
      ∀ blocks : ℕ, ∀ hblocks : 0 < blocks,
        c ^ blocks ≤
          P (rationalHorizonTubeEvent X 1
            (7 * δ₀ /
              (((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
                (-(1 / α))))) := by
  obtain ⟨δ₀, hδ₀, hc⟩ := h.exists_positive_unit_directionalReturn hpos hneg
  let c : ENNReal :=
    P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn (-δ₀) δ₀ 0 δ₀) ⊓
    P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn (-δ₀) δ₀ (-δ₀) 0)
  refine ⟨δ₀, c, hδ₀, hc, ?_⟩
  intro blocks hblocks
  exact h.unit_directionalReturn_pow_le_tube blocks hblocks δ₀ hδ₀

end ProbabilityTheory

end
