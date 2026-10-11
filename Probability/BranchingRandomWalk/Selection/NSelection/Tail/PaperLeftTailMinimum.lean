/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.CountableRoots
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.PaperLeftTail

/-!
# Paper left-tail bound for the endpoint minimum

Transfer the finite-root endpoint event to the minimum observable on the
common countable-root forest. The only additional law condition is the paper's
almost-sure nonempty-offspring assumption, needed to identify the totalized
minimum with the ordinary finite-population minimum.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The paper's left-tail polynomial estimate for the generation-`ℓ_N`
endpoint minimum on the common countable-root forest. The offspring
nonemptiness, boundary normalization, supercriticality, and spine moment
conditions are kept as separate hypotheses. -/
theorem eventually_countableRootEndpointMinimum_sublevel_le_polynomial_of_paper_sequence
    {L : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ}
    (hboundary : HasBoundaryNormalization realPotential
      (L : Measure (Step ℕ ℝ)))
    (hnonempty : L.HasAtLeastOneChild)
    (hsupercritical : L.IsSupercritical)
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
      (L : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential (-1) (L : Measure (Step ℕ ℝ))))
    {horizon : ℕ → ℕ} {a t zeta : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n : ℕ => (horizon n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t))
    (hbelow : zeta < -a + (Real.pi ^ 2 / 2) *
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
        (L : Measure (Step ℕ ℝ))) * t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ)
        (L : Measure (Step ℕ ℝ)))
        {field | @countableRootEndpointMinimum (Nat.floor ((n : ℝ) ^ a)) n
          (horizon n) (paperRootAddressLinearOrder (Nat.floor ((n : ℝ) ^ a)))
          field ≤ zeta * Real.log (n : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (n : ℝ))) := by
  let μ : Measure (Step ℕ ℝ) := L
  let m : ℕ → ℕ := fun n => Nat.floor ((n : ℝ) ^ a)
  have hN : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
  have hmPositive : ∀ᶠ n : ℕ in atTop, 0 < m n := by
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow := Real.rpow_le_rpow_of_exponent_le hnReal ha_zero
    have hpow' : 1 ≤ (n : ℝ) ^ a := by simpa using hpow
    dsimp [m]
    exact Nat.le_floor (by exact_mod_cast hpow')
  obtain ⟨epsilon, hepsilon, hfiniteBound⟩ :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_paper_sequence
      hboundary hsupercritical hspineMean hspineFiniteVariance
      (horizon := horizon) (a := a) (t := t) (zeta := zeta)
      ha_zero ha_one ht hhorizon hbelow
  have hnonemptyMeasure : μ nonemptySupport = 1 := by
    simpa [HasAtLeastOneChild, μ] using hnonempty
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards [hfiniteBound, hmPositive,
    hN.eventually_ge_atTop 1] with n hbound hmpos hn
  letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
    paperRootAddressLinearOrder (m n)
  have hminEq :
      (finiteRootStepFieldLaw μ (m n))
        {field | firstNSelectedEndpointMinimum (m n) n (horizon n) field ≤
          zeta * Real.log (n : ℝ)} =
      (finiteRootStepFieldLaw μ (m n))
        (firstNSelectedEndpointBelow (m n) n (horizon n)
          (zeta * Real.log (n : ℝ))) := by
    apply measure_congr
    filter_upwards [firstNSelectedEndpointMinimum_le_iff_endpointBelow_ae
      (m n) n (horizon n) hmpos (by omega) μ hboundary
      hnonemptyMeasure (zeta * Real.log (n : ℝ))] with field hiff
    exact propext hiff.symm
  have hcountableEq := countableRootEndpointMinimum_sublevel_measure_eq
    μ (m n) n (horizon n) (zeta * Real.log (n : ℝ))
  calc
    (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | @countableRootEndpointMinimum (m n) n (horizon n)
          (paperRootAddressLinearOrder (m n)) field ≤
            zeta * Real.log (n : ℝ)} =
      (finiteRootStepFieldLaw μ (m n))
        {field | firstNSelectedEndpointMinimum (m n) n (horizon n) field ≤
          zeta * Real.log (n : ℝ)} := hcountableEq
    _ = (finiteRootStepFieldLaw μ (m n))
        (firstNSelectedEndpointBelow (m n) n (horizon n)
          (zeta * Real.log (n : ℝ))) := hminEq
    _ ≤ ENNReal.ofReal (Real.exp (-epsilon * Real.log (n : ℝ))) := hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
