import Probability.BranchingRandomWalk.Walk.Path.Interpolation.Corridor
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Maximal
import Probability.Process.Path.Tightness

/-!
# Global bounds for normalized polygonal paths

The maximal inequality for the discrete partial sums controls the full
polygonal interpolation, since a convex interval contains every segment as
soon as it contains the grid vertices.
-/

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- The normalized polygonal path leaves `[-radius, radius]` with probability
at most `1 / radius²` under the centered unit-second-moment assumptions. -/
theorem normalizedLinearPathLaw_compl_uniformBound_le
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {radius : ℝ} (hradius : 0 < radius) {n : ℕ} (hn : 0 < n) :
    normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
        {f : C(Skorokhod.UnitInterval, ℝ) |
          ∀ t, dist (f t) 0 ≤ radius}ᶜ ≤
      ENNReal.ofReal (1 / radius ^ 2) := by
  rw [normalizedLinearPathLaw, Measure.map_apply]
  · calc
      independentIncrementLaw nu
          ((normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n) ⁻¹'
            {f : C(Skorokhod.UnitInterval, ℝ) |
              ∀ t, dist (f t) 0 ≤ radius}ᶜ) ≤
          independentIncrementLaw nu {increment |
            ∃ k ∈ Finset.range ((n - 1) + 1),
              radius * Real.sqrt n ≤ |blockSum 0 (k + 1) increment|} := by
        apply measure_mono
        intro increment hincrement
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hincrement
        have hnotCorridor :
            normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n increment ∉
              ContinuousMap.rangeInClosedInterval (-radius) radius := by
          intro hcorridor
          apply hincrement
          intro t
          have ht := (ContinuousMap.mem_rangeInClosedInterval_iff.mp hcorridor) t
          simpa [Real.dist_eq] using abs_le.2 ht
        rw [normalizedLinearContinuousPathIcc_mem_rangeInClosedInterval_iff
          (fun n => Real.sqrt n) hn (le_of_lt (neg_neg_of_pos hradius)) hradius.le]
          at hnotCorridor
        simp only [InClosedCorridorOnGrid] at hnotCorridor
        push Not at hnotCorridor
        obtain ⟨k, hk⟩ := hnotCorridor
        refine ⟨k, by simp [Nat.sub_add_cancel hn], ?_⟩
        rw [normalizedStepPath_grid (fun n => Real.sqrt n) hn] at hk
        have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
        have habs : radius <
            |(Real.sqrt n)⁻¹ * partialSum (k + 1) increment| := by
          by_cases hlower :
              -radius ≤ (Real.sqrt n)⁻¹ * partialSum (k + 1) increment
          · exact (hk hlower).trans_le (le_abs_self _)
          · have hneg : (Real.sqrt n)⁻¹ * partialSum (k + 1) increment <
                -radius := lt_of_not_ge hlower
            rw [← neg_lt_neg_iff] at hneg
            simpa only [neg_neg] using hneg.trans_le (neg_le_abs _)
        rw [abs_mul, abs_inv, abs_of_pos hsqrt, inv_mul_eq_div] at habs
        have hscaled := (lt_div_iff₀ hsqrt).mp habs
        simpa [blockSum, partialSum] using hscaled.le
    _ ≤ ENNReal.ofReal (((n - 1 + 1 : ℕ) : ℝ) /
          (radius * Real.sqrt n) ^ 2) :=
      by
        simpa [independentIncrementLaw, Nat.cast_add, Nat.cast_one] using
          (measure_exists_abs_blockSum_ge_le nu hnu 0
            (mul_pos hradius (Real.sqrt_pos.2 (by exact_mod_cast hn :
              (0 : ℝ) < n))) (n - 1))
    _ = ENNReal.ofReal (1 / radius ^ 2) := by
      congr 1
      rw [Nat.sub_add_cancel hn]
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp [hnreal, hradius.ne']
  · exact measurable_normalizedLinearContinuousPathIcc _ _
  · have hclosed : IsClosed {f : C(Skorokhod.UnitInterval, ℝ) |
        ∀ t, dist (f t) 0 ≤ radius} := by
      rw [show {f : C(Skorokhod.UnitInterval, ℝ) |
          ∀ t, dist (f t) 0 ≤ radius} =
          ⋂ t, {f | dist (f t) 0 ≤ radius} by ext; simp]
      exact isClosed_iInter fun t =>
        isClosed_le (by fun_prop) (by fun_prop)
    exact hclosed.measurableSet.compl

/-- The normalized polygonal path laws are uniformly bounded in probability.
The radius depends only on the requested error mass, not on the number of
steps. -/
theorem exists_normalizedLinearPathLaw_uniformBound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {eta : ENNReal} (heta : 0 < eta) :
    ∃ radius : ℝ, ∀ n,
      normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
          {f : C(Skorokhod.UnitInterval, ℝ) |
            ∀ t, dist (f t) 0 ≤ radius}ᶜ ≤ eta := by
  by_cases hetaTop : eta = ⊤
  · refine ⟨1, fun n => ?_⟩
    simp [hetaTop]
  · have hetaReal : 0 < eta.toReal := ENNReal.toReal_pos (ne_of_gt heta) hetaTop
    let radius : ℝ := Real.sqrt (1 / eta.toReal) + 1
    have hradius : 0 < radius := by
      dsimp [radius]
      positivity
    have hratio : 1 / radius ^ 2 ≤ eta.toReal := by
      rw [div_le_iff₀ (sq_pos_of_pos hradius)]
      have hsqrtSq : (Real.sqrt (1 / eta.toReal)) ^ 2 = 1 / eta.toReal :=
        Real.sq_sqrt (by positivity)
      have hscaled : eta.toReal * (Real.sqrt (1 / eta.toReal)) ^ 2 = 1 := by
        rw [hsqrtSq]
        field_simp
      dsimp [radius]
      nlinarith [Real.sqrt_nonneg (1 / eta.toReal)]
    refine ⟨radius, fun n => ?_⟩
    by_cases hn : n = 0
    · subst n
      rw [normalizedLinearPathLaw, Measure.map_apply]
      · rw [show
          (normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) 0) ⁻¹'
              {f : C(Skorokhod.UnitInterval, ℝ) |
                ∀ t, dist (f t) 0 ≤ radius}ᶜ = ∅ by
            ext increment
            simp [normalizedLinearContinuousPathIcc_apply,
              normalizedLinearPath, hradius.le]]
        simp
      · exact measurable_normalizedLinearContinuousPathIcc _ _
      · have hclosed : IsClosed {f : C(Skorokhod.UnitInterval, ℝ) |
            ∀ t, dist (f t) 0 ≤ radius} := by
          rw [show {f : C(Skorokhod.UnitInterval, ℝ) |
              ∀ t, dist (f t) 0 ≤ radius} =
              ⋂ t, {f | dist (f t) 0 ≤ radius} by ext; simp]
          exact isClosed_iInter fun t =>
            isClosed_le (by fun_prop) (by fun_prop)
        exact hclosed.measurableSet.compl
    · exact (normalizedLinearPathLaw_compl_uniformBound_le
        nu hnu hradius (Nat.pos_of_ne_zero hn)).trans <| by
        rw [← ENNReal.ofReal_toReal hetaTop]
        exact ENNReal.ofReal_le_ofReal hratio

/-- Once one-scale oscillation estimates have been established, the maximal
inequality supplies the remaining global bound and hence tightness of the
whole family of normalized polygonal path laws. -/
theorem isTightMeasureSet_normalizedLinearPathLaw_of_eventually_oscillation
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    (hoscillation : ∀ {epsilon : ℝ}, 0 < epsilon →
      ∀ {eta : ENNReal}, 0 < eta →
        ∃ delta > 0, ∀ᶠ n : ℕ in Filter.atTop,
          normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
            {f : C(Skorokhod.UnitInterval, ℝ) |
              ContinuousMap.HasOscillationBound delta epsilon f}ᶜ < eta) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedLinearPathLaw nu (fun n => Real.sqrt n) n)) := by
  apply Process.Path.isTightMeasureSet_of_eventually_singleOscillationBound
    (fun n => normalizedLinearPathLaw nu (fun n => Real.sqrt n) n)
    (fun _ => inferInstance) hoscillation
  intro eta heta
  obtain ⟨radius, hradius⟩ :=
    exists_normalizedLinearPathLaw_uniformBound nu hnu heta
  exact ⟨0, radius, hradius⟩

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
