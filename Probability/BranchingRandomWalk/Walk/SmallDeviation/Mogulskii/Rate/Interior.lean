import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Rate.FinitePartition

/-!
# Mogulskii lower rate for a strict interior horizontal tube

This file chooses a three-point return cover and discharges the geometric
hypotheses of the finite-partition lower bound.  The remaining hypothesis is
the genuinely analytic comparison between the maximal-inequality error and
the finite Gaussian products.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- For a horizontal tube whose zero starting point lies strictly inside,
three reference points suffice to implement the return-block geometry. -/
theorem exists_lowerRate_horizontalTubeProbability_of_strictInterior
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a margin : ℝ} (hmargin : 0 < margin)
    (hleft : 8 * margin < a) (hright : 8 * margin < 1 - a)
    (hprincipal : ∀ y ∈ ({-2 * margin, 0, 2 * margin} : Finset ℝ),
      ENNReal.ofReal (blocks * (constant / margin ^ 2)) <
        ∏ _j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              (((-y / (blocks : ℝ)) - margin / (blocks : ℝ)) /
                Real.sqrt constant)
              (((-y / (blocks : ℝ)) + margin / (blocks : ℝ)) /
                Real.sqrt constant))) :
    ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
      (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
        atTop.liminf (fun n =>
          scale n ^ 2 / (n : ℝ) *
            Real.log (horizontalTubeProbability
              (independentIncrementLaw ν) a (scale n) n).toReal) := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  let references : Finset ℝ := {-2 * margin, 0, 2 * margin}
  apply exists_lowerRate_horizontalTubeProbability_of_linearReturn
    ν hν hscale hscalePos hconstant hblocks ha0 ha1
    (returnLower := -3 * margin) (returnUpper := 3 * margin)
    (coverMargin := margin) (endpointMargin := margin)
    (blockRadius := margin / (blocks : ℝ))
    (references := references)
  · constructor <;> linarith
  · exact hmargin
  · exact div_pos hmargin hblocksReal
  · simp [references]
  · intro x hx
    rcases le_total x (-margin) with hxLeft | hxLeft
    · refine ⟨-2 * margin, by simp [references], ?_⟩
      rw [abs_le]
      constructor <;> linarith [hx.1]
    · rcases le_total margin x with hxRight | hxRight
      · refine ⟨2 * margin, by simp [references], ?_⟩
        rw [abs_le]
        constructor <;> linarith [hx.2]
      · refine ⟨0, by simp [references], ?_⟩
        rw [abs_le]
        constructor <;> linarith
  · intro y hy
    simp only [references, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> constructor <;> linarith
  · intro y hy
    simp only [references, Finset.mem_insert, Finset.mem_singleton] at hy
    have hradius : (blocks : ℝ) * (margin / (blocks : ℝ)) = margin := by
      field_simp [hblocksReal.ne']
    rcases hy with rfl | rfl | rfl <;> rw [hradius] <;>
      constructor <;> linarith
  · have hradius : (blocks : ℝ) * (margin / (blocks : ℝ)) = margin := by
      field_simp [hblocksReal.ne']
    rw [hradius]
    constructor <;> linarith
  · have hradius : (blocks : ℝ) * (margin / (blocks : ℝ)) = margin := by
      field_simp [hblocksReal.ne']
    rw [hradius]
    constructor <;> linarith
  · simpa [references] using hprincipal

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
