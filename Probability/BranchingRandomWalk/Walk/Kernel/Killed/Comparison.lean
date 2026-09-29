import Probability.BranchingRandomWalk.Walk.Kernel.Killed

/-!
# Comparison of killed-walk survival masses

Deterministic inclusions between translated path windows give order relations
between remaining masses of killed additive kernels.
-/

open MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Moving the initial position by at most `margin` and enlarging both sides
of the interval by that margin can only increase survival mass. -/
theorem remainingMass_killedIncrementKernel_Icc_mono_of_abs_sub_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper margin initial reference : ℝ) (n : ℕ)
    (hdistance : |initial - reference| ≤ margin) :
    Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (lower + margin) (upper - margin)) measurableSet_Icc)
        n reference ≤
      Kernel.remainingMass
        (killedIncrementKernel ν (Set.Icc lower upper) measurableSet_Icc)
        n initial := by
  unfold Kernel.remainingMass
  rw [killedIncrementKernel_pow_apply_univ,
    killedIncrementKernel_pow_apply_univ]
  exact measure_mono fun _increment hsurvives =>
    hsurvives.mono_Icc_of_abs_sub_le hdistance

/-- A finite family of reference positions transfers a common survival lower
bound from a shrunken interval to every initial position covered by the
family. -/
theorem le_remainingMass_killedIncrementKernel_Icc_of_finset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper margin : ℝ) (n : ℕ) (references : Finset ℝ)
    (lowerBound : ENNReal)
    (hcover : ∀ x ∈ Set.Icc lower upper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (href : ∀ y ∈ references,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (lower + margin) (upper - margin)) measurableSet_Icc)
        n y) :
    ∀ x : Set.Icc lower upper,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν (Set.Icc lower upper) measurableSet_Icc)
        n x := by
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x x.property
  exact (href y hy).trans
    (remainingMass_killedIncrementKernel_Icc_mono_of_abs_sub_le
      ν lower upper margin x y n hxy)

/-- Eventual finite-reference bounds may be intersected and transferred
uniformly to every normalized initial point.  Scaling is allowed to vary with
the filter index. -/
theorem eventually_forall_le_remainingMass_killedIncrementKernel_Icc_of_finset
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper margin : ℝ) (references : Finset ℝ)
    (scale : ι → ℝ) (duration : ι → ℕ) (lowerBound : ENNReal)
    (hscale : ∀ᶠ i in l, 0 ≤ scale i)
    (hcover : ∀ x ∈ Set.Icc lower upper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (href : ∀ y ∈ references, ∀ᶠ i in l,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * (lower + margin))
            (scale i * (upper - margin))) measurableSet_Icc)
        (duration i) (scale i * y)) :
    ∀ᶠ i in l, ∀ x : Set.Icc lower upper,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
        (duration i) (scale i * x) := by
  have hrefEventually : ∀ᶠ i in l, ∀ y ∈ references,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * (lower + margin))
            (scale i * (upper - margin))) measurableSet_Icc)
        (duration i) (scale i * y) :=
    references.eventually_all.2 href
  filter_upwards [hscale, hrefEventually] with i hscaleNonneg hi
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x x.property
  have hscaledDistance :
      |scale i * x - scale i * y| ≤ scale i * margin := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hscaleNonneg]
    exact mul_le_mul_of_nonneg_left hxy hscaleNonneg
  refine (hi y hy).trans ?_
  simpa only [mul_add, mul_sub] using
    remainingMass_killedIncrementKernel_Icc_mono_of_abs_sub_le
      ν (scale i * lower) (scale i * upper) (scale i * margin)
      (scale i * x) (scale i * y) (duration i) hscaledDistance

end ProbabilityTheory.RandomWalk
