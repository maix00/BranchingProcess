/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.ManyToOne.EndpointManyToOne
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.Process.RandomWalk.Kernel.Endpoint

/-!
# Branching-field endpoint realization

The endpoint recursions for a tilted branching field are obtained by combining
the independent-increment realization with the field's product law.

For `φ : Potential X`, a boundary-normalized step law `μ`, and measurable
`f : ℝ → [0,∞]`, the finite partial sum of the iid tilted increment field
realizes the endpoint iterate:

\[
\int^-_{\omega} f(x+S_n(\omega))\,
  \partial\operatorname{tiltedIncrementFieldLaw}(\varphi,\mu)
=\operatorname{endpointIterate}
  (\operatorname{tiltedPotentialLaw}(\varphi,-1,\mu),n,f)(x),
\]

where `S_n(ω) = AdditivePath.displacement n ω`.  The unweighted iterate has
the reciprocal exponential factor:

\[
\int^-_{\omega}\operatorname{ENNReal.ofReal}(e^{S_n(\omega)})
  f(x+S_n(\omega))\,
  \partial\operatorname{tiltedIncrementFieldLaw}(\varphi,\mu)
=\operatorname{exponentialEndpointIterate}
  (\operatorname{tiltedPotentialLaw}(\varphi,-1,\mu),n,f)(x).
\]

Composing these identities with the endpoint recursions identifies the
weighted and unweighted branching iterates with the same two increment
integrals.

## Public declarations

- `partialSum_indepFun_next`: the partial sum at time `n` is independent of
  the next coordinate under the boundary-normalized tilted law.
- `lintegral_partialSum_eq_iterate` and
  `lintegral_untiltedPartialSum_eq_iterate`: realize the weighted and
  unweighted endpoint-operator iterates as branching-field partial-sum
  integrals.
- `weightedEndpointManyToOne_product` and
  `endpointManyToOne_product`: the corresponding many-to-one formulas for the
  product law of the pre-sampled branching field.
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
        endpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [AdditivePath.displacement, endpointIterate]
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
        endpointIterate ν (n + 1) f x
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
        _ = ∫⁻ increment, endpointOperator ν f
              (x + AdditivePath.displacement n increment) ∂P := by
              rw [lintegral_map (by fun_prop) hSn]
              apply lintegral_congr
              intro increment
              simp only [endpointOperator]
              apply lintegral_congr
              intro y
              exact congrArg f
                (add_assoc x (AdditivePath.displacement n increment) y).symm
        _ = endpointIterate ν n (endpointOperator ν f) x := by
              exact lintegral_partialSum_eq_iterate φ μ hboundary
                (measurable_endpointOperator ν hf) n x
        _ = endpointIterate ν (n + 1) f x :=
              congrFun (endpointIterate_operator ν n f) x


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
        exponentialEndpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [AdditivePath.displacement, exponentialEndpointIterate]
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
        exponentialEndpointIterate ν (n + 1) f x
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
              exponentialEndpointOperator ν f (x + s)
              ∂P.map (AdditivePath.displacement n) := by
              apply lintegral_congr
              intro s
              simp only [exponentialEndpointOperator]
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
                exponentialEndpointOperator ν f
                  (x + AdditivePath.displacement n increment) ∂P := by
              have hU : Measurable (exponentialEndpointOperator ν f) :=
                measurable_exponentialEndpointOperator ν hf
              have hexp : Measurable
                  (fun s : ℝ => ENNReal.ofReal (Real.exp s)) := by
                fun_prop
              have houter : Measurable (fun s : ℝ =>
                  ENNReal.ofReal (Real.exp s) *
                    exponentialEndpointOperator ν f (x + s)) :=
                hexp.mul (hU.comp (measurable_const.add measurable_id))
              rw [lintegral_map houter hSn]
        _ = exponentialEndpointIterate ν n
              (exponentialEndpointOperator ν f) x := by
              exact lintegral_untiltedPartialSum_eq_iterate φ μ hboundary
                (measurable_exponentialEndpointOperator ν hf) n x
        _ = exponentialEndpointIterate ν (n + 1) f x :=
              congrFun (exponentialEndpointIterate_operator ν n f) x

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
