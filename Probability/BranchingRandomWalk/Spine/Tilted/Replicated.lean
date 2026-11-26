/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail

/-!
# Exponential bias of identically displaced offspring

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_map_replicated`:
  for a real displacement law `ν` and `m` children all displaced by `x`,
  the tilted increment law is `ν.withDensity (m exp(θx))`. This identity
  holds for every measure `ν`, real tilt `θ` and finite arity, including zero.

* `ProbabilityTheory.BranchingRandomWalk.Spine.relativeSpinalWeight_replicated`:
  for `m>0`, the relative mark at each child is exactly `log m`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.hasSpinalWeightTail_map_replicated`:
  every measure of these fixed-arity families has a vanishing quadratic
  reproductive tail, independently of the displacement moments.

The existing joint family/child bias is used throughout. Replication is the
ordinary function `x ↦ (fun _ : Fin m ↦ some x)`; no second reproduction-law
or biased-law construction is introduced.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching
open scoped ENNReal Topology

/-- Identical finite offspring turn the sum of slot weights into the
multiplicity times the scalar exponential weight. -/
theorem tiltedPotentialLaw_map_replicated (ν : Measure ℝ) (m : ℕ) (θ : ℝ) :
    tiltedPotentialLaw realPotential θ
      (ν.map (fun x : ℝ => fun _ : Fin m => some x)) =
      ν.withDensity (fun x => ENNReal.ofReal ((m : ℝ) * Real.exp (θ * x))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_tiltedPotentialLaw realPotential θ _ f hf]
  have hmap : Measurable (fun x : ℝ => fun _ : Fin m => some x) := by
    exact Measurable.of_eval (fun _ => measurable_option_some)
  have hsum : Measurable (fun ξ : Step (Fin m) ℝ => ∑' i : Fin m,
      realizedPotentialWeight realPotential θ ξ i * f (ξ.potentialValue' realPotential i)) := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable realPotential θ i).mul
      (hf.comp (Step.potentialValue'_measurable realPotential i))
  rw [lintegral_map hsum hmap,
    lintegral_withDensity_eq_lintegral_mul ν (by fun_prop) hf]
  apply lintegral_congr
  intro x
  simp [tsum_fintype, realizedPotentialWeight, survive, Step.potentialValue',
    Step.potentialAt?, realPotential, ENNReal.ofReal_mul (Nat.cast_nonneg m),
    Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The displacement cancels from the relative family weight. -/
theorem relativeSpinalWeight_replicated {m : ℕ} (hm : 0 < m) (x : ℝ) (i : Fin m) :
    relativeSpinalWeight realPotential ((fun _ : Fin m => some x), i) = Real.log m := by
  have hw : totalPotentialWeight realPotential (-1) (fun _ : Fin m => some x) =
      ENNReal.ofReal ((m : ℝ) * Real.exp (-x)) := by
    simp [totalPotentialWeight, realizedPotentialWeight, survive, Step.potentialValue',
      Step.potentialAt?, realPotential, tsum_fintype,
      ENNReal.ofReal_mul (Nat.cast_nonneg m), nsmul_eq_mul]
  unfold relativeSpinalWeight logTotalPotentialWeight
  rw [hw, ENNReal.toReal_ofReal (by positivity),
    Real.log_mul (by positivity : (m : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  simp [Step.potentialValue', Step.potentialAt?, realPotential]

/-- A bounded deterministic relative mark satisfies the weak tail condition,
even when the raw displacement has infinite moments. -/
theorem hasSpinalWeightTail_map_replicated (ν : Measure ℝ) {m : ℕ} (hm : 0 < m) :
    HasSpinalWeightTail realPotential
      (ν.map (fun x : ℝ => fun _ : Fin m => some x)) := by
  let μ := ν.map (fun x : ℝ => fun _ : Fin m => some x)
  let P := tiltedFamilyChildLaw realPotential (-1) μ
  have hraw : ∀ᵐ ξ ∂μ, ∀ i : Fin m,
      relativeSpinalWeight realPotential (ξ, i) = Real.log m := by
    apply (ae_map_iff (Measurable.of_eval (fun _ => measurable_option_some)).aemeasurable _).mpr
    · exact ae_of_all _ (fun x i => relativeSpinalWeight_replicated hm x i)
    · simpa only [Set.iInter_ofPred, Function.comp_def, id_eq] using (MeasurableSet.iInter fun i : Fin m =>
        measurableSet_eq_fun ((relativeSpinalWeight_measurable realPotential).comp
          (measurable_id.prodMk measurable_const)) measurable_const)
  have hw : ∀ᵐ ξ ∂μ.withDensity (totalPotentialWeight realPotential (-1)),
      ∀ i : Fin m, relativeSpinalWeight realPotential (ξ, i) = Real.log m :=
    hraw.filter_mono (Measure.ae_le_iff_absolutelyContinuous.mpr
      (withDensity_absolutelyContinuous μ _))
  have hfst : ∀ᵐ ξ ∂P.map Prod.fst,
      ∀ i : Fin m, relativeSpinalWeight realPotential (ξ, i) = Real.log m := by
    rwa [tiltedFamilyChildLaw_fst]
  have hmark : ∀ᵐ p ∂P, relativeSpinalWeight realPotential p = Real.log m := by
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hfst] with p hp
    exact hp p.2
  change Filter.Tendsto (fun x : ℝ => x ^ 2 * P.real
    {p | x < relativeSpinalWeight realPotential p}) Filter.atTop (nhds 0)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (Real.log m)] with x hx
  have he : {p | x < relativeSpinalWeight realPotential p} =ᵐ[P] (∅ : Set _) := by
    filter_upwards [hmark] with p hp
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [hp]
    exact not_lt.mpr hx
  simp only [measureReal_def, measure_congr he, measure_empty, ENNReal.toReal_zero, mul_zero]

end ProbabilityTheory.BranchingRandomWalk.Spine
