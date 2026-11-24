/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.FiniteExpectations
public import Probability.BranchingRandomWalk.Population.Processes.Selected.ParameterizedRootIndexed
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Nonempty
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
public import Probability.BranchingRandomWalk.Spine.ManyToOne.GenerationManyToOne
public import Probability.MeasureTheory.Moments.ExponentialMoment

/-!
# Negative endpoint moments for finite-root N-selection

## Public declarations

- `finiteRootStepFieldLaw_lintegral_exp_neg_selectedPopulationEndpoint_le`:
  under boundary normalization and nonempty offspring, for arbitrary initial
  positions $x_r$, the endpoint satisfies $\mathbb E[e^{-M_H}]\le\sum_r e^{-x_r}$.

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le`:
  under boundary normalization and nonempty offspring,
  \(\mathbb E[e^{-M_H}]\le m\), where \(M_H\) is the minimum selected
  endpoint among \(m\) roots at generation \(H\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.finiteRootStepFieldLaw_integrable_pow_four_max_neg_firstNSelectedEndpointMinimum`:
  the negative part is fourth-integrable and
  \(\mathbb E[((-M_H)^+)^4]\le2048(1+\log^4 m)\).

The endpoint of the selected population is bounded below, in the exponential
weight, by one term in the unrestricted generation sum of the root containing
the minimizing particle.  The many-to-one identity then bounds its negative
exponential moment by the number of initial roots.  This supplies the
negative-part fourth-moment input for the trajectory `L²` argument.
-/

open MeasureTheory
open scoped ENNReal BigOperators

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The expected exponential weight of the leftmost selected particle is
bounded by the sum of the initial particles' exponential weights. -/
theorem finiteRootStepFieldLaw_lintegral_exp_neg_selectedPopulationEndpoint_le
    (m N H : ℕ) (initial : Fin m → ℝ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    (∫⁻ field, ENNReal.ofReal (Real.exp
      (-RootIndexed.selectedPopulationEndpointWithParameter m N H (initial, field)))
      ∂finiteRootStepFieldLaw μ m) ≤
      ∑ r : Fin m, ENNReal.ofReal (Real.exp (-initial r)) := by
  classical
  let weight (r : Fin m) := ENNReal.ofReal (Real.exp (-initial r))
  let rootWeight (r : Fin m) (tree : StepField ℕ ℝ) :=
    weight r * Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0 tree
  have hrootMeas (r : Fin m) : Measurable (rootWeight r) :=
    measurable_const.mul (Spine.weightedGenerationEndpoint_measurable realPotential H
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const 0)
  have hsingle :
      (∫⁻ ξ, Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0 ξ
        ∂offspringFieldLaw μ) = 1 := by
    have hmany := Spine.weightedGenerationManyToOne
      (d := id) measurable_id realPotential μ hboundary
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const H 0
    letI := Spine.tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
    simpa [Potential.comp] using hmany
  calc
    _ ≤ ∫⁻ field, ∑ r : Fin m, rootWeight r (field r) ∂finiteRootStepFieldLaw μ m := by
      apply lintegral_mono_ae
      filter_upwards [RootIndexed.selectedPopulationTotalized_nonempty_ae N Finset.univ
        ⟨(⟨0, hm⟩ : Fin m), Finset.mem_univ _⟩ initial hN μ hboundary hnonempty] with field hpop
      let pop := RootIndexed.selectedPopulationWithParameter m N H (initial, field)
      let value := RootIndexed.observedPositionAtGeneration initial id id H field
      have hnonemptyPop : pop.Nonempty := hpop H
      obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' hnonemptyPop value
      have hend : RootIndexed.selectedPopulationEndpointWithParameter m N H (initial, field) =
          value p := by
        unfold RootIndexed.selectedPopulationEndpointWithParameter
        change (if h : pop.Nonempty then pop.inf' h value else 0) = _
        rw [dite_eq_left hnonemptyPop]
        exact hmin
      have hdepth := RootIndexed.selectedPopulationTotalized_depth N Finset.univ initial
        id id H field p hp
      have hsurv := RootIndexed.selectedPopulationTotalized_surviveAlong N Finset.univ initial
        id id H field p hp
      have hvalue : value p =
          initial p.1 + Spine.pathPotential realPotential (field p.1) p.2 := by
        simp [value, RootIndexed.observedPositionAtGeneration,
          RootIndexed.positionAtGeneration, RootIndexed.position, RootIndexed.displace,
          Spine.pathPotential, displaceWith, realPotential, hdepth]
      have hterm : ENNReal.ofReal (Real.exp (-value p)) = weight p.1 *
          Spine.weightedGenerationTerm realPotential H (fun _ => 1) 0 p.2 (field p.1) := by
        rw [hvalue, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
        simp [Spine.weightedGenerationTerm, hdepth, hsurv, weight]
      rw [hend, hterm]
      apply le_trans ?_ (Finset.single_le_sum (f := fun r => rootWeight r (field r))
        (fun _ _ => bot_le) (Finset.mem_univ p.1))
      change weight p.1 * _ ≤ weight p.1 * _
      gcongr
      exact le_tsum (f := fun u : TreeNode ℕ =>
        Spine.weightedGenerationTerm realPotential H (fun _ => 1) 0 u (field p.1)) p.2
    _ = _ := by
      rw [RootIndexed.lintegral_finset_root_observables μ Finset.univ rootWeight
        (fun r _ => hrootMeas r)]
      apply Finset.sum_congr rfl
      intro r _
      unfold rootWeight
      rw [lintegral_const_mul _ (Spine.weightedGenerationEndpoint_measurable realPotential H
        (f := fun _ => (1 : ℝ≥0∞)) measurable_const 0), hsingle, mul_one]

theorem finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    (∫⁻ field, ENNReal.ofReal
      (Real.exp (-firstNSelectedEndpointMinimum m N H field))
      ∂finiteRootStepFieldLaw μ m) ≤ ENNReal.ofReal (m : ℝ) := by
  have h := finiteRootStepFieldLaw_lintegral_exp_neg_selectedPopulationEndpoint_le
    m N H (fun _ => 0) hm hN μ hboundary hnonempty
  have heq (field : FiniteRootStepField m ℕ ℝ) :
      RootIndexed.selectedPopulationEndpointWithParameter m N H ((fun _ => 0), field) =
        firstNSelectedEndpointMinimum m N H field := by
    classical
    let pop := firstNSelectedPopulation m N H field
    change (if h : pop.Nonempty then pop.inf' h
        (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ)) id id H field)
        else 0) =
      (if h : pop.Nonempty then pop.inf' h
        (fun q => RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2)
        else 0)
    split
    · rename_i hpop
      apply Finset.inf'_congr hpop rfl
      intro q hq
      have hdepth := firstNSelectedPopulation_depth m N H field q hq
      simp [RootIndexed.observedPositionAtGeneration, RootIndexed.positionAtGeneration, hdepth]
    · rfl
  simpa [heq] using h

/-- The selected endpoint's negative part has a logarithmic fourth-moment
bound. This is the negative-side moment estimate needed by the
trajectory `L²` argument; the positive-side fourth-moment estimate is a
separate adapter. -/
theorem finiteRootStepFieldLaw_integrable_pow_four_max_neg_firstNSelectedEndpointMinimum
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    Integrable (fun field =>
      (max (-firstNSelectedEndpointMinimum m N H field) 0) ^ 4)
      (finiteRootStepFieldLaw μ m) ∧
      (∫ field,
        (max (-firstNSelectedEndpointMinimum m N H field) 0) ^ 4
        ∂finiteRootStepFieldLaw μ m) ≤
        2048 * (1 + Real.log (m : ℝ) ^ 4) := by
  have hmReal : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  exact ProbabilityTheory.integrable_pow_four_max_neg_of_lintegral_exp_neg_le
    (finiteRootStepFieldLaw μ m)
    (firstNSelectedEndpointMinimum m N H)
    (measurable_firstNSelectedEndpointMinimum m N H)
    hmReal
    (finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
      m N H hm hN μ hboundary hnonempty)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
