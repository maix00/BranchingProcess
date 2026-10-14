/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.FiniteExpectations
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Nonempty
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum
import Probability.BranchingRandomWalk.Spine.GenerationManyToOne
import Probability.MeasureTheory.Moments.ExponentialMoment

/-!
# Negative endpoint moments for finite-root N-selection

The endpoint of the selected population is bounded below, in the exponential
weight, by one term in the unrestricted generation sum of the root containing
the minimizing particle.  The many-to-one identity then bounds its negative
exponential moment by the number of initial roots.  This supplies the
negative-part fourth-moment input for the trajectory `L²` argument.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

private theorem rootPosition_eq_pathPotential (m : ℕ)
    (field : FiniteRootStepField m ℕ ℝ) (r : Fin m) (u : TreeNode ℕ) :
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r u =
      Spine.pathPotential realPotential (field r) u := by
  simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential,
    displaceWith, Spine.pathPotential, realPotential]

/-- The negative exponential moment of the totalized selected endpoint is at
most the number of initial roots.  The empty-population value is irrelevant:
under the paper's nonempty-offspring hypothesis, the selected population is
nonempty almost surely at every fixed generation. -/
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
  classical
  let endpointWeight : Fin m → FiniteRootStepField m ℕ ℝ → ℝ≥0∞ := fun r field =>
    Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0 (field r)
  have hweightMeas (r : Fin m) : Measurable (endpointWeight r) := by
    dsimp [endpointWeight]
    exact (Spine.weightedGenerationEndpoint_measurable realPotential H
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const 0).comp
        (measurable_pi_apply r)
  have hrootSumMeas : Measurable (fun field => ∑ r : Fin m,
      endpointWeight r field) := by
    exact Finset.measurable_sum Finset.univ (fun r hr => hweightMeas r)
  have hpointwise_ae : ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ENNReal.ofReal
          (Real.exp (-firstNSelectedEndpointMinimum m N H field)) ≤
        ∑ r : Fin m, endpointWeight r field := by
    filter_upwards [finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
      m N hm hN μ hboundary hnonempty] with field hpop
    have hpopulation : (firstNSelectedPopulation m N H field).Nonempty := by
      simpa [firstNSelectedPopulation] using hpop H
    let g : RootIndexed.TreeNode (Fin m) ℕ → ℝ := fun p =>
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2
    obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf'
      hpopulation g
    have hminimum : firstNSelectedEndpointMinimum m N H field = g p := by
      rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
        m N H field hpopulation]
      exact hmin
    have hpdepth : p.2.length = H :=
      firstNSelectedPopulation_depth m N H field p hp
    have hpsurvive : surviveAlong (field p.1) [] p.2 :=
      firstNSelectedPopulation_surviveAlong m N H field p hp
    have hterm :
        Spine.weightedGenerationTerm realPotential H (fun _ => 1) 0
            p.2 (field p.1) =
          ENNReal.ofReal (Real.exp (-g p)) := by
      simp [Spine.weightedGenerationTerm, hpdepth, hpsurvive, g,
        rootPosition_eq_pathPotential]
    have hroot :
        ENNReal.ofReal (Real.exp (-firstNSelectedEndpointMinimum m N H field)) ≤
          endpointWeight p.1 field := by
      calc
        ENNReal.ofReal
            (Real.exp (-firstNSelectedEndpointMinimum m N H field)) =
          Spine.weightedGenerationTerm realPotential H (fun _ => 1) 0
            p.2 (field p.1) := by rw [hminimum, hterm]
        _ ≤ Spine.weightedGenerationEndpoint realPotential H
            (fun _ => 1) 0 (field p.1) := by
          rw [Spine.weightedGenerationEndpoint]
          exact ENNReal.le_tsum
            (f := fun u : TreeNode ℕ =>
              Spine.weightedGenerationTerm realPotential H (fun _ => 1) 0 u
                (field p.1)) p.2
    have hsum : endpointWeight p.1 field ≤ ∑ r : Fin m, endpointWeight r field :=
      Finset.single_le_sum
        (f := fun r : Fin m => endpointWeight r field)
        (fun r hr => bot_le) (Finset.mem_univ p.1)
    exact hroot.trans hsum
  have hrootIntegral :
      (∫⁻ field, ∑ r : Fin m, endpointWeight r field
        ∂finiteRootStepFieldLaw μ m) =
        ∑ r : Fin m, ∫⁻ ξ,
          Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0 ξ
          ∂stepFieldLaw μ := by
    simpa [finiteRootStepFieldLaw, endpointWeight, Finset.sum_const,
      nsmul_eq_mul] using
      RootIndexed.lintegral_finset_root_observable
        (Root := Fin m) (α := ℕ) (X := ℝ) μ Finset.univ
        (Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0)
        (Spine.weightedGenerationEndpoint_measurable realPotential H
          (f := fun _ => (1 : ℝ≥0∞)) measurable_const 0)
  have hsingle :
      (∫⁻ ξ, Spine.weightedGenerationEndpoint realPotential H (fun _ => 1) 0 ξ
        ∂stepFieldLaw μ) = 1 := by
    have hmany := Spine.weightedGenerationManyToOne
      (d := id) measurable_id realPotential μ hboundary
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const H 0
    have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
      Spine.tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
    letI := htilted
    simpa [Potential.comp] using hmany
  have hsumIntegral :
      (∫⁻ field, ∑ r : Fin m, endpointWeight r field
        ∂finiteRootStepFieldLaw μ m) = ENNReal.ofReal (m : ℝ) := by
    rw [hrootIntegral]
    simp [hsingle]
  calc
    (∫⁻ field, ENNReal.ofReal
        (Real.exp (-firstNSelectedEndpointMinimum m N H field))
        ∂finiteRootStepFieldLaw μ m) ≤
      ∫⁻ field, ∑ r : Fin m, endpointWeight r field
        ∂finiteRootStepFieldLaw μ m :=
          lintegral_mono_ae hpointwise_ae
    _ = ENNReal.ofReal (m : ℝ) := hsumIntegral

/-- The selected endpoint's negative part has a logarithmic fourth-moment
bound. This is the negative-side moment estimate needed by the paper's
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
