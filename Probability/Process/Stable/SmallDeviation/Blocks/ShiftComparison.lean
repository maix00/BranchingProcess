module

public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceFactorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling

/-!
# Shifted corridor comparison

The full-path probability bound obtained by inserting a short entrance block
of duration `a ^ α`. This is the finite-scale inequality used in Mogulskii's
comparison of shifted intervals.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_shiftedFullCorridor_ge_entrance_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 1
        (c - (1 + ε)) (c + 1 + ε)
        (c - b - ε) (c - b + ε)) *
      P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1))) ≤
      P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε))) := by
  let cut := stableEntranceHorizon α a
  let remaining : ℝ≥0 := 1 - cut
  have hcut : cut < 1 :=
    stableEntranceHorizon_lt_one ha ha1 h.increments.strictlyStable.1
  have hcutPos : 0 < cut := by
    apply NNReal.coe_pos.mp
    simp [cut, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hremaining : 0 < remaining := tsub_pos_iff_lt.mpr hcut
  have hsum : cut + remaining = 1 := by
    exact add_tsub_cancel_of_le hcut.le
  have hbound := h.measure_fullCorridor_ge_entrance_mul_fullCorridor
    cut remaining hcutPos hremaining
    (a * (c - (1 + ε))) (a * (c + 1 + ε))
    (a * (c - b - ε)) (a * (c - b + ε))
  rw [hsum] at hbound
  have hscale := h.shortEntrance_fullCorridorReturn_probability a ha
    (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε)
  change P (fullSegmentCorridorReturnEvent X 0 cut
      (a * (c - (1 + ε))) (a * (c + 1 + ε))
      (a * (c - b - ε)) (a * (c - b + ε))) = _ at hscale
  rw [hscale] at hbound
  convert hbound using 1 <;> congr 2 <;> ring

end ProbabilityTheory

end
