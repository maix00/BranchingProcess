module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Bounded windows from two-sided measure mass

A real measure charging both open half-lines also charges a bounded positive
window and its reflected negative window, with common inner and outer radii.
-/

@[expose] public section

namespace MeasureTheory

open Set

theorem Measure.exists_twoSidedWindow_pos (μ : Measure ℝ)
    (hpos : 0 < μ (Ioi 0)) (hneg : 0 < μ (Iio 0)) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      0 < μ (Ioo r R) ∧ 0 < μ (Ioo (-R) (-r)) := by
  obtain ⟨xp, hxp, hxpSupport⟩ := μ.nonempty_inter_support_of_pos hpos
  obtain ⟨xn, hxn, hxnSupport⟩ := μ.nonempty_inter_support_of_pos hneg
  have hxp0 : 0 < xp := hxp
  have hxn0 : xn < 0 := hxn
  let r : ℝ := min xp (-xn) / 2
  let R : ℝ := max xp (-xn) + 1
  have hr : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min hxp0 (by linarith))
  have hxpWindow : xp ∈ Ioo r R := by
    constructor
    · dsimp [r]
      linarith [min_le_left xp (-xn)]
    · dsimp [R]
      linarith [le_max_left xp (-xn)]
  have hxnWindow : xn ∈ Ioo (-R) (-r) := by
    constructor
    · dsimp [R]
      linarith [le_max_right xp (-xn)]
    · dsimp [r]
      linarith [min_le_right xp (-xn)]
  refine ⟨r, R, hr, ?_, ?_, ?_⟩
  · exact lt_trans hxpWindow.1 hxpWindow.2
  · exact (Measure.mem_support_iff_forall xp).mp hxpSupport _
      (isOpen_Ioo.mem_nhds hxpWindow)
  · exact (Measure.mem_support_iff_forall xn).mp hxnSupport _
      (isOpen_Ioo.mem_nhds hxnWindow)

end MeasureTheory

end
