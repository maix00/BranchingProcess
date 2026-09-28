import Combinatorics.BranchingWalk.Walk.Path.Interpolation.Corridor
import Combinatorics.BranchingWalk.Walk.Path.Skorokhod
import Topology.Cadlag.Skorokhod.Corridor

/-!
# Corridor membership of càdlàg walk paths

The positive-uniform-margin corridor in Skorokhod path space is identified
with the strict finite-grid tube event for a normalized random-walk path.
-/

namespace Combinatorics.Branching.Walk

/-- Every value of the normalized step path is a grid-vertex value of its
polygonal interpolation. -/
theorem exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (t : Skorokhod.UnitInterval) :
    ∃ s : Skorokhod.UnitInterval,
      normalizedLinearContinuousPathIcc scale n increment s =
        normalizedStepCadlagPathIcc scale n increment t := by
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hkn : k ≤ n := natFloor_mul_le_of_mem_unitInterval n t
  let s : Skorokhod.UnitInterval :=
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
    let t : Skorokhod.UnitInterval :=
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

end Combinatorics.Branching.Walk
