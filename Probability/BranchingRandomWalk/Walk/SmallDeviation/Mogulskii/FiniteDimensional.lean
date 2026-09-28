import Probability.BranchingRandomWalk.Walk.Path.Block.Law
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.CLT
import Probability.ConvergenceInDistribution.Independence

/-!
# Finite-dimensional Gaussian limits for Mogulskii blocks

The endpoint CLT is lifted to consecutive independent blocks.  These results
are finite-dimensional inputs for the path-level invariance principle; they
do not assert tightness in path space.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Two consecutive blocks of the same diffusive length converge jointly to
two independent centered Gaussian increments. -/
theorem tendstoInDistribution_two_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    TendstoInDistribution
      (fun n increment =>
        let length := diffusiveBlockLength constant scale n
        (blockSum 0 length increment / scale n,
          blockSum length length increment / scale n))
      atTop
      (fun z : ℝ × ℝ =>
        (z.1 * Real.sqrt constant, z.2 * Real.sqrt constant))
      (fun _ => independentIncrementLaw ν)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let length : ℕ → ℕ := diffusiveBlockLength constant scale
  let first : ℕ → (ℕ → ℝ) → ℝ := fun n increment =>
    blockSum 0 (length n) increment / scale n
  let second : ℕ → (ℕ → ℝ) → ℝ := fun n increment =>
    blockSum (length n) (length n) increment / scale n
  let limit : ℝ → ℝ := fun z => z * Real.sqrt constant
  have hbase := tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    ν hcentered hsecondMoment hscale hconstant
  have hfirst : TendstoInDistribution first atTop limit
      (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
    simpa only [first, length, blockSum_zero_start, limit] using hbase
  have hsecond : TendstoInDistribution second atTop limit
      (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
    apply hbase.congr_map_eventually
    · filter_upwards [] with n
      have hblock := iidSequenceLaw_map_blockSum ν (length n) (length n)
      have hdiv : Measurable (fun x : ℝ => x / scale n) :=
        measurable_id.div_const _
      calc
        (independentIncrementLaw ν).map
            (fun increment => partialSum (length n) increment / scale n) =
          ((independentIncrementLaw ν).map (partialSum (length n))).map
            (fun x => x / scale n) := by
              simpa only [Function.comp_def] using
                (Measure.map_map hdiv
                  (partialSum_measurable (length n))).symm
        _ = ((independentIncrementLaw ν).map
              (blockSum (length n) (length n))).map
              (fun x => x / scale n) := by
                rw [show (independentIncrementLaw ν).map
                    (blockSum (length n) (length n)) =
                    (independentIncrementLaw ν).map (partialSum (length n)) by
                  simpa [independentIncrementLaw] using hblock]
        _ = (independentIncrementLaw ν).map (second n) := by
          simpa only [second, Function.comp_def] using
            Measure.map_map hdiv
              (blockSum_measurable (length n) (length n))
    · intro n
      exact (blockSum_measurable (length n) (length n)).div_const _
        |>.aemeasurable
  have hindep (n : ℕ) : IndepFun (first n) (second n)
      (independentIncrementLaw ν) := by
    simpa [first, second, Function.comp_def, independentIncrementLaw] using
      (indepFun_blockSum_blockSum ν 0 (length n) (length n)).comp
        (measurable_id.div_const (scale n))
        (measurable_id.div_const (scale n))
  simpa only [first, second, length, limit] using
    hfirst.prodMk_of_indepFun hsecond (by fun_prop) (by fun_prop) hindep

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
