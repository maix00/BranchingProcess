/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
public import Probability.BranchingRandomWalk.Spine.IncrementProcess
public import Probability.Process.RandomWalk.Law
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent endpoint realization

The canonical independent-increment process realizes the weighted and
reciprocal-weight endpoint recursions without using a branching field.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk

open Combinatorics.Branching MeasureTheory

theorem independentPosition_indepFun_next (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (partialSum n) (fun increment : ℕ → ℝ => increment n)
      (RandomWalk.independentIncrementLaw ν) := by
  have h := (RandomWalk.independentIncrementLaw_independent ν).indepFun_finsetSum_of_notMem
    (s := Finset.range n) (i := n)
    (fun _ => measurable_pi_apply _) Finset.notMem_range_self
  convert h using 1
  ext increment
  simp [partialSum]

/-- Iterating a fixed transition after applying it once is the same as one
more left-recursive iteration. -/
theorem tiltedEndpointIterate_operator
    (ν : Measure ℝ) (n : ℕ) (f : ℝ → ENNReal) :
    tiltedEndpointIterate ν n (tiltedEndpointOperator ν f) =
      tiltedEndpointIterate ν (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change tiltedEndpointOperator ν
          (tiltedEndpointIterate ν n (tiltedEndpointOperator ν f)) =
        tiltedEndpointOperator ν (tiltedEndpointIterate ν (n + 1) f)
      exact congrArg (tiltedEndpointOperator ν) ih

/-- A transition iterate is the endpoint expectation of its canonical
independent-increment random walk. -/
theorem lintegral_independentPosition_eq_iterate
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment, f (x + partialSum n increment)
          ∂RandomWalk.independentIncrementLaw ν) =
        tiltedEndpointIterate ν n f x
  | 0, x => by simp [partialSum, tiltedEndpointIterate]
  | n + 1, x => by
      let P := RandomWalk.independentIncrementLaw ν
      have hSn : Measurable (partialSum (E := ℝ) n) :=
        partialSum_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := independentPosition_indepFun_next ν n
      have hpair : P.map (fun increment =>
          (partialSum n increment, increment n)) =
          (P.map (partialSum n)).prod
            (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment, f (x + partialSum (n + 1) increment) ∂P) =
        tiltedEndpointIterate ν (n + 1) f x
      simp only [partialSum, Finset.sum_range_succ]
      calc
        (∫⁻ increment, f (x +
            (partialSum n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (partialSum n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂(P.map (partialSum n)).prod ν := by
              rw [hpair, RandomWalk.independentIncrementLaw_coordinate ν n]
        _ = ∫⁻ s, ∫⁻ y, f (x + (s + y)) ∂ν
              ∂P.map (partialSum n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ increment, tiltedEndpointOperator ν f
              (x + partialSum n increment) ∂P := by
              rw [lintegral_map (by fun_prop) hSn]
              apply lintegral_congr
              intro increment
              simp only [tiltedEndpointOperator]
              apply lintegral_congr
              intro y
              exact congrArg f
                (add_assoc x (partialSum n increment) y).symm
        _ = tiltedEndpointIterate ν n (tiltedEndpointOperator ν f) x := by
              exact lintegral_independentPosition_eq_iterate ν
                (measurable_tiltedEndpointOperator ν hf) n x
        _ = tiltedEndpointIterate ν (n + 1) f x :=
              congrFun (tiltedEndpointIterate_operator ν n f) x


theorem untiltedEndpointIterate_operator
    (ν : Measure ℝ) (n : ℕ) (f : ℝ → ENNReal) :
    untiltedEndpointIterate ν n (untiltedEndpointOperator ν f) =
      untiltedEndpointIterate ν (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change untiltedEndpointOperator ν
          (untiltedEndpointIterate ν n (untiltedEndpointOperator ν f)) =
        untiltedEndpointOperator ν (untiltedEndpointIterate ν (n + 1) f)
      exact congrArg (untiltedEndpointOperator ν) ih

/-- The reciprocal-weight iterate is the endpoint expectation of the
canonical independent-increment random walk. -/
theorem lintegral_independentPosition_untilted_eq_iterate
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment,
          ENNReal.ofReal (Real.exp (partialSum n increment)) *
            f (x + partialSum n increment)
          ∂RandomWalk.independentIncrementLaw ν) =
        untiltedEndpointIterate ν n f x
  | 0, x => by simp [partialSum, untiltedEndpointIterate]
  | n + 1, x => by
      let P := RandomWalk.independentIncrementLaw ν
      have hSn : Measurable (partialSum (E := ℝ) n) :=
        partialSum_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := independentPosition_indepFun_next ν n
      have hpair : P.map (fun increment =>
          (partialSum n increment, increment n)) =
          (P.map (partialSum n)).prod
            (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment,
          ENNReal.ofReal (Real.exp (partialSum (n + 1) increment)) *
            f (x + partialSum (n + 1) increment) ∂P) =
        untiltedEndpointIterate ν (n + 1) f x
      simp only [partialSum, Finset.sum_range_succ]
      calc
        (∫⁻ increment,
            ENNReal.ofReal
                (Real.exp (partialSum n increment + increment n)) *
              f (x + (partialSum n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (partialSum n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂(P.map (partialSum n)).prod ν := by
              rw [hpair, RandomWalk.independentIncrementLaw_coordinate ν n]
        _ = ∫⁻ s, ∫⁻ y,
              ENNReal.ofReal (Real.exp (s + y)) *
                f (x + (s + y)) ∂ν
              ∂P.map (partialSum n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp s) *
              untiltedEndpointOperator ν f (x + s)
              ∂P.map (partialSum n) := by
              apply lintegral_congr
              intro s
              simp only [untiltedEndpointOperator]
              rw [← lintegral_const_mul
                (ENNReal.ofReal (Real.exp s)) (by fun_prop)]
              apply lintegral_congr
              intro y
              rw [Real.exp_add,
                ENNReal.ofReal_mul (le_of_lt (Real.exp_pos s)), mul_assoc]
              congr 2
              exact congrArg f (add_assoc x s y).symm
        _ = ∫⁻ increment,
              ENNReal.ofReal (Real.exp (partialSum n increment)) *
                untiltedEndpointOperator ν f
                  (x + partialSum n increment) ∂P := by
              have hU : Measurable (untiltedEndpointOperator ν f) :=
                measurable_untiltedEndpointOperator ν hf
              have hexp : Measurable
                  (fun s : ℝ => ENNReal.ofReal (Real.exp s)) := by
                fun_prop
              have houter : Measurable (fun s : ℝ =>
                  ENNReal.ofReal (Real.exp s) *
                    untiltedEndpointOperator ν f (x + s)) :=
                hexp.mul (hU.comp (measurable_const.add measurable_id))
              rw [lintegral_map houter hSn]
        _ = untiltedEndpointIterate ν n
              (untiltedEndpointOperator ν f) x := by
              exact lintegral_independentPosition_untilted_eq_iterate ν
                (measurable_untiltedEndpointOperator ν hf) n x
        _ = untiltedEndpointIterate ν (n + 1) f x :=
              congrFun (untiltedEndpointIterate_operator ν n f) x

end ProbabilityTheory.BranchingRandomWalk.Spine
