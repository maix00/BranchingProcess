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

/-- Any fixed finite vector of consecutive diffusive block sums converges to
independent centered Gaussian increments. -/
theorem tendstoInDistribution_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin blocks) =>
        let length := diffusiveBlockLength constant scale n
        blockSum (j * length) length increment / scale n)
      atTop
      (fun z (j : Fin blocks) => z j * Real.sqrt constant)
      (fun _ => independentIncrementLaw ν)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  let length : ℕ → ℕ := diffusiveBlockLength constant scale
  let X : ℕ → Fin blocks → (ℕ → ℝ) → ℝ := fun n j increment =>
    blockSum (j * length n) (length n) increment / scale n
  let Z : Fin blocks → ℝ → ℝ := fun _ z => z * Real.sqrt constant
  have hbase := tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    ν hcentered hsecondMoment hscale hconstant
  have hcoordinate (j : Fin blocks) :
      TendstoInDistribution (fun n => X n j) atTop (Z j)
        (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
    apply hbase.congr_map_eventually
    · filter_upwards [] with n
      have hblock := iidSequenceLaw_map_blockSum ν
        (j * length n) (length n)
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
              (blockSum (j * length n) (length n))).map
              (fun x => x / scale n) := by
                rw [show (independentIncrementLaw ν).map
                    (blockSum (j * length n) (length n)) =
                    (independentIncrementLaw ν).map
                      (partialSum (length n)) by
                  simpa [independentIncrementLaw] using hblock]
        _ = (independentIncrementLaw ν).map (X n j) := by
          simpa only [X, Function.comp_def] using
            Measure.map_map hdiv
              (blockSum_measurable (j * length n) (length n))
    · intro n
      exact (blockSum_measurable (j * length n) (length n)).div_const _
        |>.aemeasurable
  have hindep (n : ℕ) : iIndepFun (X n) (independentIncrementLaw ν) := by
    have h := iIndepFun_consecutiveBlockSums ν blocks (length n)
    exact h.comp (fun _ x => x / scale n)
      (fun _ => measurable_id.div_const _)
  simpa only [X, Z, length] using TendstoInDistribution.pi_of_iIndepFun
    hcoordinate (fun _ => by fun_prop) hindep

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
