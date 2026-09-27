import Mathlib.Topology.Order.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Exceptional-event estimates

First-moment estimates for exceptional events, including the factorization
available when a reserve random variable is independent of the event.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

/-- A pointwise truncation inequality.  After integration, this is the
first-moment replacement for a Cauchy--Schwarz estimate on a rare event. -/
theorem bad_event_truncation (x K : ℝ) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + K * (if event then 1 else 0) := by
  classical
  by_cases he : event
  · simp only [ite_eq_left he, mul_one]
    by_cases hx : K < |x|
    · simp only [ite_eq_left hx]
      linarith
    · simp only [ite_eq_right hx]
      simpa using (le_of_not_gt hx)
  · simp only [ite_eq_right he, mul_zero, add_zero]
    split_ifs <;> positivity

/-! The same estimate summed over a finite labelled family.  This is the
finite-population form used before passing to a measure or a lintegral. -/
theorem bad_event_truncation_sum {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => (if K < |x i| then |x i| else 0) +
        K * (if event i then 1 else 0)) := by
  exact Finset.sum_le_sum fun i hi => bad_event_truncation (x i) K
    (event i) hK

theorem bad_event_truncation_sum_card {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => if K < |x i| then |x i| else 0) +
        K * (s.filter event).card := by
  calc
    s.sum (fun i => if event i then |x i| else 0) ≤
        s.sum (fun i => (if K < |x i| then |x i| else 0) +
          K * (if event i then 1 else 0)) :=
      bad_event_truncation_sum s x event K hK
    _ = s.sum (fun i => if K < |x i| then |x i| else 0) +
          K * (s.filter event).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      simp [Finset.sum_boole]

/-- An integrable observable independent of a measurable event gains the
probability of that event exactly. This is the `L¹` replacement used when a
reserve displacement is sampled independently of the failed trials. -/
theorem integral_abs_mul_indicator_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (E : Set Ω)
    (hf : Integrable f μ) (hE : MeasurableSet E)
    (hind : IndepFun (fun ω => |f ω|) (E.indicator (fun _ => (1 : ℝ))) μ) :
    (∫ ω, |f ω| * E.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      (∫ ω, |f ω| ∂μ) * μ.real E := by
  have habs : AEStronglyMeasurable (fun ω => |f ω|) μ :=
    hf.abs.aestronglyMeasurable
  have hfactor := hind.integral_mul_eq_mul_integral habs
    (measurable_const.indicator hE).aestronglyMeasurable
  change μ[(fun ω => |f ω|) * E.indicator (fun _ => (1 : ℝ))] = _
  rw [hfactor, integral_indicator_const (1 : ℝ) hE]
  simp

/-- Sigma-algebra form of `integral_abs_mul_indicator_eq`.  It connects the
fresh-subtree independence interface to the exceptional-event estimate. -/
theorem integral_abs_mul_indicator_eq_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (mPast : MeasurableSpace Ω) (f : Ω → ℝ) (E : Set Ω)
    (hf : Integrable f μ)
    (hE : MeasurableSet[mPast] E) (hEfull : MeasurableSet[mΩ] E)
    (hind : Indep mPast (MeasurableSpace.comap f inferInstance) μ) :
    (∫ ω, |f ω| * E.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      (∫ ω, |f ω| ∂μ) * μ.real E := by
  have hindicator :
      (E.indicator (fun _ => (1 : ℝ))) ⟂ᵢ[μ] f :=
    hind.indicator_indepFun (1 : ℝ) hE
  have habs :
      (fun ω => |f ω|) ⟂ᵢ[μ] E.indicator (fun _ => (1 : ℝ)) := by
    have hcomp := hindicator.symm.comp
      (by fun_prop : Measurable fun x : ℝ => |x|) measurable_id
    simpa [Function.comp_def] using hcomp
  exact @integral_abs_mul_indicator_eq Ω mΩ μ f E hf hEfull habs

end ProbabilityTheory.BranchingRandomWalk
