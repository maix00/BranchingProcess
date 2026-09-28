import Combinatorics.BranchingWalk.Walk.Path.Interpolation
import Combinatorics.BranchingWalk.Walk.Path.Corridor
import Combinatorics.BranchingWalk.Walk.Path.Corridor.Horizontal
import Topology.ContinuousMap.Corridor

/-!
# Corridor membership of polygonal walk paths

For a horizontal interval, the polygonal interpolation stays in the interval
exactly when all its grid vertices do.  This is deterministic and belongs to
the path layer rather than the probability layer.
-/

open Set

namespace Combinatorics.Branching.Walk

/-- Between consecutive grid points the normalized polygonal path is the
usual affine combination of the two endpoint partial sums. -/
theorem normalizedLinearPath_eq_lineMap
    (scale : ℕ → ℝ) {n : ℕ} (increment : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hfloor : ⌊(n : ℝ) * t⌋₊ < n) :
    normalizedLinearPath scale n increment t =
      AffineMap.lineMap
        ((scale n)⁻¹ * partialSum ⌊(n : ℝ) * t⌋₊ increment)
        ((scale n)⁻¹ * partialSum (⌊(n : ℝ) * t⌋₊ + 1) increment)
        (linearIncrementWeight n ⌊(n : ℝ) * t⌋₊ t) := by
  rw [normalizedLinearPath, sum_linearIncrementWeight_eq_partialSum_add
    ht hfloor, partialSum_succ]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  ring

/-- A polygonal walk path stays in a nonempty horizontal open interval iff
all positive grid vertices do; time zero is handled by the two explicit
starting-point hypotheses. -/
theorem normalizedLinearContinuousPathIcc_mem_rangeInOpenInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (increment : ℕ → ℝ) :
    normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInOpenInterval lower upper ↔
      InOpenCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment := by
  constructor
  · intro hpath k
    let t : Skorokhod.UnitInterval :=
      ⟨((k.val + 1 : ℕ) : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by positivity)]
        exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have ht := (ContinuousMap.mem_rangeInOpenInterval_iff.mp hpath) t
    change lower < normalizedLinearPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ∧
      normalizedLinearPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) < upper at ht
    dsimp only
    rw [normalizedLinearPath_grid scale hn
      (Nat.succ_le_iff.mpr k.isLt)] at ht
    rw [normalizedStepPath_grid scale hn]
    exact ht
  · intro hgrid
    have hvertex : ∀ k ≤ n,
        lower < (scale n)⁻¹ * partialSum k increment ∧
          (scale n)⁻¹ * partialSum k increment < upper := by
      intro k hk
      cases k with
      | zero => simpa using And.intro hlower hupper
      | succ k =>
          have hklt : k < n := Nat.succ_le_iff.mp hk
          have hkGrid := hgrid ⟨k, hklt⟩
          dsimp only at hkGrid
          rw [normalizedStepPath_grid scale hn] at hkGrid
          exact hkGrid
    apply ContinuousMap.mem_rangeInOpenInterval_iff.mpr
    intro t
    let m := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hmn : m ≤ n := by
      apply Nat.floor_le_of_le
      calc
        (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
        _ = n := by ring
    by_cases hmlt : m < n
    · have hp := hvertex m hmn
      have hq := hvertex (m + 1) (Nat.succ_le_iff.mpr hmlt)
      have hw0 : 0 ≤ linearIncrementWeight n m t :=
        linearIncrementWeight_nonneg n m t
      have hw1 : linearIncrementWeight n m t ≤ 1 :=
        linearIncrementWeight_le_one n m t
      rw [normalizedLinearContinuousPathIcc_apply,
        normalizedLinearPath_eq_lineMap scale increment t.property.1 hmlt]
      exact (convex_Ioo lower upper).segment_subset hp hq
        (lineMap_mem_segment ℝ _ _ ⟨hw0, hw1⟩)
    · have hmeq : m = n := Nat.le_antisymm hmn (Nat.le_of_not_gt hmlt)
      have hfloorLe : (m : ℝ) ≤ (n : ℝ) * (t : ℝ) := by
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) t.property.1)
      have htOne : (t : ℝ) = 1 := by
        rw [hmeq] at hfloorLe
        have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
        nlinarith [t.property.2]
      simpa [normalizedLinearContinuousPathIcc_apply, htOne] using
        hvertex n le_rfl

/-- In the customary horizontal-tube coordinates, continuous polygonal
corridor membership is exactly the strict finite random-walk tube event. -/
theorem normalizedLinearContinuousPathIcc_mem_horizontalCorridor_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) (increment : ℕ → ℝ) :
    normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInOpenInterval (-a) (1 - a) ↔
      InOpenHorizontalTube a (scale n) n increment := by
  rw [normalizedLinearContinuousPathIcc_mem_rangeInOpenInterval_iff
    scale hn (neg_lt_zero.mpr ha) (sub_pos.mpr haOne)]
  constructor <;> intro h k
  · have hk := h k
    dsimp only at hk
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div] at hk
    exact ⟨(lt_div_iff₀ hscale).mp hk.1,
      (div_lt_iff₀ hscale).mp hk.2⟩
  · have hk := h k
    dsimp only
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div]
    exact ⟨(lt_div_iff₀ hscale).mpr hk.1,
      (div_lt_iff₀ hscale).mpr hk.2⟩

end Combinatorics.Branching.Walk
