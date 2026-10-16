/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.EndpointRealization.Independent

/-!
# Branching-field endpoint realization

The endpoint recursions for a tilted branching field are obtained by combining
the independent-increment realization with the field's product law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.RandomWalk

open Combinatorics.Branching MeasureTheory

theorem partialSum_indepFun_next {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    IndepFun (AdditivePath.displacement n) (fun increment : ℕ → ℝ => increment n)
      (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  have h :=
    (tiltedIncrementFieldLaw_independent φ μ hboundary).indepFun_finsetSum_of_notMem
      (s := Finset.range n) (i := n)
      (fun _ => measurable_pi_apply _) Finset.notMem_range_self
  convert h using 1
  ext increment
  simp [AdditivePath.displacement]

/-- The tilted endpoint recursion is the expectation of the endpoint after
`n` coordinates of the canonical independent increment process. -/
theorem lintegral_partialSum_eq_iterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment, f (x + AdditivePath.displacement n increment)
          ∂tiltedIncrementFieldLaw φ μ) =
        tiltedEndpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [AdditivePath.displacement, tiltedEndpointIterate]
  | n + 1, x => by
      let ν := tiltedPotentialLaw φ (-1) μ
      let P := tiltedIncrementFieldLaw φ μ
      let _ : IsProbabilityMeasure ν :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure P :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have hSn : Measurable (AdditivePath.displacement (E := ℝ) n) :=
        displacement_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := partialSum_indepFun_next φ μ hboundary n
      have hpair : P.map (fun increment =>
          (AdditivePath.displacement n increment, increment n)) =
          (P.map (AdditivePath.displacement n)).prod
          (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment, f (x + AdditivePath.displacement (n + 1) increment) ∂P) =
        tiltedEndpointIterate ν (n + 1) f x
      simp only [AdditivePath.displacement, Finset.sum_range_succ]
      calc
        (∫⁻ increment, f (x +
            (AdditivePath.displacement n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (AdditivePath.displacement n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂(P.map (AdditivePath.displacement n)).prod ν := by
              rw [hpair, tiltedIncrementFieldLaw_coordinate φ μ hboundary n]
        _ = ∫⁻ s, ∫⁻ y, f (x + (s + y)) ∂ν
              ∂P.map (AdditivePath.displacement n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ increment, tiltedEndpointOperator ν f
              (x + AdditivePath.displacement n increment) ∂P := by
              rw [lintegral_map (by fun_prop) hSn]
              apply lintegral_congr
              intro increment
              simp only [tiltedEndpointOperator]
              apply lintegral_congr
              intro y
              exact congrArg f
                (add_assoc x (AdditivePath.displacement n increment) y).symm
        _ = tiltedEndpointIterate ν n (tiltedEndpointOperator ν f) x := by
              exact lintegral_partialSum_eq_iterate φ μ hboundary
                (measurable_tiltedEndpointOperator ν hf) n x
        _ = tiltedEndpointIterate ν (n + 1) f x :=
              congrFun (tiltedEndpointIterate_operator ν n f) x


theorem lintegral_untiltedPartialSum_eq_iterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            f (x + AdditivePath.displacement n increment)
          ∂tiltedIncrementFieldLaw φ μ) =
        untiltedEndpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [AdditivePath.displacement, untiltedEndpointIterate]
  | n + 1, x => by
      let ν := tiltedPotentialLaw φ (-1) μ
      let P := tiltedIncrementFieldLaw φ μ
      let _ : IsProbabilityMeasure ν :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure P :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have hSn : Measurable (AdditivePath.displacement (E := ℝ) n) :=
        displacement_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := partialSum_indepFun_next φ μ hboundary n
      have hpair : P.map (fun increment =>
          (AdditivePath.displacement n increment, increment n)) =
          (P.map (AdditivePath.displacement n)).prod
          (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement (n + 1) increment)) *
            f (x + AdditivePath.displacement (n + 1) increment) ∂P) =
        untiltedEndpointIterate ν (n + 1) f x
      simp only [AdditivePath.displacement, Finset.sum_range_succ]
      calc
        (∫⁻ increment,
            ENNReal.ofReal
                (Real.exp (AdditivePath.displacement n increment + increment n)) *
              f (x + (AdditivePath.displacement n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (AdditivePath.displacement n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂(P.map (AdditivePath.displacement n)).prod ν := by
              rw [hpair, tiltedIncrementFieldLaw_coordinate φ μ hboundary n]
        _ = ∫⁻ s, ∫⁻ y,
              ENNReal.ofReal (Real.exp (s + y)) *
                f (x + (s + y)) ∂ν
              ∂P.map (AdditivePath.displacement n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp s) *
              untiltedEndpointOperator ν f (x + s)
              ∂P.map (AdditivePath.displacement n) := by
              apply lintegral_congr
              intro s
              simp only [untiltedEndpointOperator]
              rw [← lintegral_const_mul
                (ENNReal.ofReal (Real.exp s)) (by fun_prop)]
              apply lintegral_congr
              intro y
              rw [Real.exp_add,
                ENNReal.ofReal_mul (le_of_lt (Real.exp_pos s))]
              rw [mul_assoc]
              congr 2
              exact congrArg f (add_assoc x s y).symm
        _ = ∫⁻ increment,
              ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
                untiltedEndpointOperator ν f
                  (x + AdditivePath.displacement n increment) ∂P := by
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
              exact lintegral_untiltedPartialSum_eq_iterate φ μ hboundary
                (measurable_untiltedEndpointOperator ν hf) n x
        _ = untiltedEndpointIterate ν (n + 1) f x :=
              congrFun (untiltedEndpointIterate_operator ν n f) x

/-- Weighted product-process identity with separate raw mark and position
spaces. -/
theorem weightedEndpointManyToOne_product
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment, f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [weightedEndpointManyToOne d hd potential μ hboundary hf n]
  exact (lintegral_partialSum_eq_iterate
    (potential.comp d hd) μ hboundary hf n x).symm

/-- Unweighted product-process identity with separate raw mark and position
spaces. -/
theorem endpointManyToOne_product
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    branchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [endpointManyToOne d hd potential μ hboundary hf n]
  exact (lintegral_untiltedPartialSum_eq_iterate
    (potential.comp d hd) μ hboundary hf n x).symm

end ProbabilityTheory.BranchingRandomWalk.Spine
