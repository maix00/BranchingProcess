import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
import Probability.BranchingRandomWalk.Spine.IncrementProcess
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi

/-!
# Realization of endpoint spine recursions

The abstract endpoint recursion is realized on the canonical countable product
of tilted increments.  Thus its `n`-step value is an expectation of a test of
the partial sum `tiltedPosition n`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

/-- Canonical independent increment field with common marginal `ν`. -/
noncomputable def independentIncrementLaw (ν : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => ν

noncomputable instance independentIncrementLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  infer_instance

theorem independentIncrementLaw_coordinate (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (independentIncrementLaw ν).map (fun increment => increment n) = ν := by
  unfold independentIncrementLaw
  exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) n

theorem independentIncrementLaw_independent (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
    (fun _ => measurable_id))

theorem independentPosition_indepFun_next (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (tiltedPosition n) (fun increment : ℕ → ℝ => increment n)
      (independentIncrementLaw ν) := by
  have h := (independentIncrementLaw_independent ν).indepFun_finsetSum_of_notMem
    (s := Finset.range n) (i := n)
    (fun _ => measurable_pi_apply _) Finset.notMem_range_self
  convert h using 1
  ext increment
  simp [tiltedPosition]

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
      (∫⁻ increment, f (x + tiltedPosition n increment)
          ∂independentIncrementLaw ν) =
        tiltedEndpointIterate ν n f x
  | 0, x => by simp [tiltedPosition, tiltedEndpointIterate]
  | n + 1, x => by
      let P := independentIncrementLaw ν
      have hSn : Measurable (tiltedPosition n) := tiltedPosition_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := independentPosition_indepFun_next ν n
      have hpair : P.map (fun increment =>
          (tiltedPosition n increment, increment n)) =
          (P.map (tiltedPosition n)).prod
            (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment, f (x + tiltedPosition (n + 1) increment) ∂P) =
        tiltedEndpointIterate ν (n + 1) f x
      simp only [tiltedPosition, Finset.sum_range_succ]
      calc
        (∫⁻ increment, f (x +
            (tiltedPosition n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (tiltedPosition n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂(P.map (tiltedPosition n)).prod ν := by
              rw [hpair, independentIncrementLaw_coordinate ν n]
        _ = ∫⁻ s, ∫⁻ y, f (x + (s + y)) ∂ν
              ∂P.map (tiltedPosition n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ increment, tiltedEndpointOperator ν f
              (x + tiltedPosition n increment) ∂P := by
              rw [lintegral_map (by fun_prop) hSn]
              apply lintegral_congr
              intro increment
              simp only [tiltedEndpointOperator]
              apply lintegral_congr
              intro y
              exact congrArg f
                (add_assoc x (tiltedPosition n increment) y).symm
        _ = tiltedEndpointIterate ν n (tiltedEndpointOperator ν f) x := by
              exact lintegral_independentPosition_eq_iterate ν
                (measurable_tiltedEndpointOperator ν hf) n x
        _ = tiltedEndpointIterate ν (n + 1) f x :=
              congrFun (tiltedEndpointIterate_operator ν n f) x

/-- The first `n` tilted increments, through their sum, are independent of the
next increment. -/
theorem tiltedPosition_indepFun_next {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    IndepFun (tiltedPosition n) (fun increment : ℕ → ℝ => increment n)
      (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  have h :=
    (tiltedIncrementFieldLaw_independent φ μ hboundary).indepFun_finsetSum_of_notMem
      (s := Finset.range n) (i := n)
      (fun _ => measurable_pi_apply _) Finset.notMem_range_self
  convert h using 1
  ext increment
  simp [tiltedPosition]

/-- The tilted endpoint recursion is the expectation of the endpoint after
`n` coordinates of the canonical independent increment process. -/
theorem lintegral_tiltedPosition_eq_iterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment, f (x + tiltedPosition n increment)
          ∂tiltedIncrementFieldLaw φ μ) =
        tiltedEndpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [tiltedPosition, tiltedEndpointIterate]
  | n + 1, x => by
      let ν := tiltedPotentialLaw φ (-1) μ
      let P := tiltedIncrementFieldLaw φ μ
      let _ : IsProbabilityMeasure ν :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure P :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have hSn : Measurable (tiltedPosition n) := tiltedPosition_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := tiltedPosition_indepFun_next φ μ hboundary n
      have hpair : P.map (fun increment =>
          (tiltedPosition n increment, increment n)) =
          (P.map (tiltedPosition n)).prod
          (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment, f (x + tiltedPosition (n + 1) increment) ∂P) =
        tiltedEndpointIterate ν (n + 1) f x
      simp only [tiltedPosition, Finset.sum_range_succ]
      calc
        (∫⁻ increment, f (x +
            (tiltedPosition n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (tiltedPosition n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ, f (x + (z.1 + z.2))
              ∂(P.map (tiltedPosition n)).prod ν := by
              rw [hpair, tiltedIncrementFieldLaw_coordinate φ μ hboundary n]
        _ = ∫⁻ s, ∫⁻ y, f (x + (s + y)) ∂ν
              ∂P.map (tiltedPosition n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ increment, tiltedEndpointOperator ν f
              (x + tiltedPosition n increment) ∂P := by
              rw [lintegral_map (by fun_prop) hSn]
              apply lintegral_congr
              intro increment
              simp only [tiltedEndpointOperator]
              apply lintegral_congr
              intro y
              exact congrArg f
                (add_assoc x (tiltedPosition n increment) y).symm
        _ = tiltedEndpointIterate ν n (tiltedEndpointOperator ν f) x := by
              exact lintegral_tiltedPosition_eq_iterate φ μ hboundary
                (measurable_tiltedEndpointOperator ν hf) n x
        _ = tiltedEndpointIterate ν (n + 1) f x :=
              congrFun (tiltedEndpointIterate_operator ν n f) x

/-- One more reciprocal-weight transition may be placed before or after an
existing iterate of the same transition. -/
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
          ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
            f (x + tiltedPosition n increment)
          ∂independentIncrementLaw ν) =
        untiltedEndpointIterate ν n f x
  | 0, x => by simp [tiltedPosition, untiltedEndpointIterate]
  | n + 1, x => by
      let P := independentIncrementLaw ν
      have hSn : Measurable (tiltedPosition n) := tiltedPosition_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := independentPosition_indepFun_next ν n
      have hpair : P.map (fun increment =>
          (tiltedPosition n increment, increment n)) =
          (P.map (tiltedPosition n)).prod
            (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment,
          ENNReal.ofReal (Real.exp (tiltedPosition (n + 1) increment)) *
            f (x + tiltedPosition (n + 1) increment) ∂P) =
        untiltedEndpointIterate ν (n + 1) f x
      simp only [tiltedPosition, Finset.sum_range_succ]
      calc
        (∫⁻ increment,
            ENNReal.ofReal
                (Real.exp (tiltedPosition n increment + increment n)) *
              f (x + (tiltedPosition n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (tiltedPosition n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂(P.map (tiltedPosition n)).prod ν := by
              rw [hpair, independentIncrementLaw_coordinate ν n]
        _ = ∫⁻ s, ∫⁻ y,
              ENNReal.ofReal (Real.exp (s + y)) *
                f (x + (s + y)) ∂ν
              ∂P.map (tiltedPosition n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp s) *
              untiltedEndpointOperator ν f (x + s)
              ∂P.map (tiltedPosition n) := by
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
              ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
                untiltedEndpointOperator ν f
                  (x + tiltedPosition n increment) ∂P := by
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

/-- The reciprocal-weight endpoint recursion is the product-process
expectation with the accumulated factor `exp (S_n)`. -/
theorem lintegral_untiltedPosition_eq_iterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ increment,
          ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
            f (x + tiltedPosition n increment)
          ∂tiltedIncrementFieldLaw φ μ) =
        untiltedEndpointIterate (tiltedPotentialLaw φ (-1) μ) n f x
  | 0, x => by
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      simp [tiltedPosition, untiltedEndpointIterate]
  | n + 1, x => by
      let ν := tiltedPotentialLaw φ (-1) μ
      let P := tiltedIncrementFieldLaw φ μ
      let _ : IsProbabilityMeasure ν :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure P :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have hSn : Measurable (tiltedPosition n) := tiltedPosition_measurable n
      have hXn : Measurable (fun increment : ℕ → ℝ => increment n) :=
        measurable_pi_apply n
      have hind := tiltedPosition_indepFun_next φ μ hboundary n
      have hpair : P.map (fun increment =>
          (tiltedPosition n increment, increment n)) =
          (P.map (tiltedPosition n)).prod
          (P.map (fun increment : ℕ → ℝ => increment n)) :=
        hind.map_prod_eq_prod_map_map hSn.aemeasurable hXn.aemeasurable
      change (∫⁻ increment,
          ENNReal.ofReal (Real.exp (tiltedPosition (n + 1) increment)) *
            f (x + tiltedPosition (n + 1) increment) ∂P) =
        untiltedEndpointIterate ν (n + 1) f x
      simp only [tiltedPosition, Finset.sum_range_succ]
      calc
        (∫⁻ increment,
            ENNReal.ofReal
                (Real.exp (tiltedPosition n increment + increment n)) *
              f (x + (tiltedPosition n increment + increment n)) ∂P) =
            ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂P.map (fun increment =>
                (tiltedPosition n increment, increment n)) := by
              rw [lintegral_map (by fun_prop) (hSn.prodMk hXn)]
        _ = ∫⁻ z : ℝ × ℝ,
              ENNReal.ofReal (Real.exp (z.1 + z.2)) *
                f (x + (z.1 + z.2))
              ∂(P.map (tiltedPosition n)).prod ν := by
              rw [hpair, tiltedIncrementFieldLaw_coordinate φ μ hboundary n]
        _ = ∫⁻ s, ∫⁻ y,
              ENNReal.ofReal (Real.exp (s + y)) *
                f (x + (s + y)) ∂ν
              ∂P.map (tiltedPosition n) := by
              exact lintegral_prod _ (by fun_prop)
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp s) *
              untiltedEndpointOperator ν f (x + s)
              ∂P.map (tiltedPosition n) := by
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
              ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
                untiltedEndpointOperator ν f
                  (x + tiltedPosition n increment) ∂P := by
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
              exact lintegral_untiltedPosition_eq_iterate φ μ hboundary
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
      ∫⁻ increment, f (x + tiltedPosition n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [weightedEndpointManyToOne d hd potential μ hboundary hf n]
  exact (lintegral_tiltedPosition_eq_iterate
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
        ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
          f (x + tiltedPosition n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [endpointManyToOne d hd potential μ hboundary hf n]
  exact (lintegral_untiltedPosition_eq_iterate
    (potential.comp d hd) μ hboundary hf n x).symm

end ProbabilityTheory.BranchingRandomWalk.Spine
