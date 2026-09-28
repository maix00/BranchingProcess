import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.IntervalKernel
import Probability.Distributions.Rademacher
import Probability.Kernel.PartialTransition.Survival

/-!
# Killed Rademacher transition on a finite interval

The two Boolean branches represent the increments `-1` and `+1`, each with
mass `1/2`.  A branch whose endpoint lies outside the finite interval is
`none`, so its mass is killed.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

/-- The Rademacher step, restricted to the interior of a finite interval and
killed on exit. -/
noncomputable def intervalRademacherKernel (interiorCount : ℕ) :
    Kernel (Fin interiorCount) (Fin interiorCount) :=
  Kernel.ofFinitePartialTransition
    (fun _ : Bool => ENNReal.ofReal (1 / 2 : ℝ))
    (fun i step => if step then intervalRightNeighbor i else intervalLeftNeighbor i)

instance intervalRademacherKernel_isSubMarkovKernel (interiorCount : ℕ) :
    IsSubMarkovKernel (intervalRademacherKernel interiorCount) := by
  apply Kernel.isSubMarkovKernel_ofFinitePartialTransition
  rw [Fintype.sum_bool]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
  norm_num

private theorem sum_ite_option_eq_elim_ennreal {ι : Type*}
    [Fintype ι] [DecidableEq ι] (index : Option ι) (f : ι → ENNReal) :
    (∑ j, (if index = some j then ENNReal.ofReal (1 / 2 : ℝ) else 0) * f j) =
      index.elim 0 (fun j => ENNReal.ofReal (1 / 2 : ℝ) * f j) := by
  cases index with
  | none => simp
  | some i => simp

private theorem ofReal_two_half_indicators (p q : Prop)
    [Decidable p] [Decidable q] :
    ENNReal.ofReal
        ((if p then (1 / 2 : ℝ) else 0) + if q then (1 / 2 : ℝ) else 0) =
      (if p then ENNReal.ofReal (1 / 2 : ℝ) else 0) +
        if q then ENNReal.ofReal (1 / 2 : ℝ) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ite_true, ite_false, add_zero, zero_add, ENNReal.ofReal_zero]
  · exact ENNReal.ofReal_add (by norm_num) (by norm_num)

/-- The partial-transition construction from the two Rademacher moves is
exactly the kernel represented by the killed interval matrix. -/
theorem intervalRademacherKernel_eq_ofRealMatrix (interiorCount : ℕ) :
    intervalRademacherKernel interiorCount =
      Kernel.ofRealMatrix (intervalKernel interiorCount) := by
  ext i s hs
  change Kernel.ofFinitePartialTransition
      (fun _ : Bool => ENNReal.ofReal (1 / 2 : ℝ))
      (fun i step => if step then intervalRightNeighbor i else intervalLeftNeighbor i)
      i s = _
  rw [Kernel.ofFinitePartialTransition_apply _ _ _ _ hs,
    Kernel.ofRealMatrix_apply]
  simp only [Fintype.sum_bool, ↓reduceIte]
  simp only [intervalKernel]
  simp_rw [ofReal_two_half_indicators]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [sum_ite_option_eq_elim_ennreal, sum_ite_option_eq_elim_ennreal]
  cases intervalLeftNeighbor i <;> cases intervalRightNeighbor i <;>
    simp [add_comm]

/-- The total mass after `n` killed Rademacher steps is the recursively
accumulated weight of exactly the branch histories that remain inside the
interval. -/
theorem intervalRademacherKernel_pow_apply_univ
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      Kernel.partialTransitionSurvivalWeight
        (fun _ : Bool => ENNReal.ofReal (1 / 2 : ℝ))
        (fun i step => if step then intervalRightNeighbor i else intervalLeftNeighbor i)
        n start :=
  Kernel.pow_apply_univ_ofFinitePartialTransition _ _ n start

/-- Consequently the matrix row sum, kernel surviving mass, and surviving
Rademacher branch weight are the same quantity. -/
theorem intervalKernel_pow_rowSum_eq_survivalWeight
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    ENNReal.ofReal (∑ finish,
        (intervalKernel interiorCount ^ n) start finish) =
      Kernel.partialTransitionSurvivalWeight
        (fun _ : Bool => ENNReal.ofReal (1 / 2 : ℝ))
        (fun i step => if step then intervalRightNeighbor i else intervalLeftNeighbor i)
        n start := by
  rw [← intervalRademacherKernel_pow_apply_univ,
    intervalRademacherKernel_eq_ofRealMatrix,
    intervalKernel_pow_apply_univ]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
