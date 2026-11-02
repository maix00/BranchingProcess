/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Prefix
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.Drawdown
import Probability.BranchingProcess.Offspring.FieldLaw

/-!
# Proof lemma for the positive-depth affine-tube MRCA estimate

## Internal proof declarations

`lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown`
specializes the reusable prefix-continuation estimate to the affine corridor
and its drawdown bound. It is used to prove the positive-depth pair estimate
in `MRCA/PositiveDepth.lean`.

If the tilted continuation probability is at most $q$, the pair-integral
term in the declaration is bounded by
\[
 \mathcal I_{m,n}\le e^{-2a}e^{2U}q^2
   \left(\int^{\!*}\mathrm{crossPotentialWeight}_{\phi}(-1,\xi)\,d\mu(\xi)\right)
   e^{a-(\ell+dm)}
   \mathbb P_{\widetilde\nu}(\mathrm{prefix\ corridor}),
\]
where $a$ is the initial position, $U$ the terminal upper bound, $d$ the
drift, and $\ell$ the lower corridor level.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- The fixed-depth affine-corridor estimate follows from the drawdown bound
on continuation increments. The prefix and continuation lengths describe
paths through MRCA depth `m` and then `n + 1` further generations. -/
lemma lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ m
          ((affineCorridorPrefix m lower drift width).indicator
            (fun _ => (1 : ℝ≥0∞))) initial u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          ENNReal.ofReal
            (Real.exp (2 * (initial + pathPotential φ ω u))) *
          pathGenerationChildMeanOffDiagonal φ μ n
            ((affineCorridorHistoryEndpointCutoff n
              (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
                (fun _ => (1 : ℝ≥0∞)))
            (initial + pathPotential φ ω u) (ω u)
        ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * q ^ 2) *
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (ENNReal.ofReal (Real.exp
          (initial - (lower + drift * (m : ℝ)))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              affineCorridorPrefix m lower drift width}) := by
  let prefixCorridor := affineCorridorPrefix m lower drift width
  let continuationCorridor := affineCorridorHistoryEndpointCutoff n
    (lower + drift * (m : ℝ)) drift width endpointUpper
  have hprefixMeas : MeasurableSet prefixCorridor :=
    measurableSet_affineCorridorPrefix m lower drift width
  have hcontinuationMeas : MeasurableSet continuationCorridor :=
    measurableSet_affineCorridorHistoryEndpointCutoff n
      (lower + drift * (m : ℝ)) drift width endpointUpper
  have hprefixLower : ∀ history ∈ prefixCorridor,
      lower + drift * (m : ℝ) ≤ history ⟨m, Nat.lt_succ_self m⟩ := by
    intro history hh
    simpa [prefixCorridor, affineCorridorPrefix] using
      (hh ⟨m, Nat.lt_succ_self m⟩).1
  have hterminal : ∀ history ∈ continuationCorridor,
      history ⟨n + 1, by omega⟩ ≤ endpointUpper := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_terminalUpper n
      (lower + drift * (m : ℝ)) drift width endpointUpper history hh
  let window := affineCorridorFirstWindow
    (lower + drift * (m : ℝ)) drift width
  have hfirst : ∀ history ∈ continuationCorridor,
      history ⟨1, by omega⟩ ∈ window := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_firstWindow n
      (lower + drift * (m : ℝ)) drift width endpointUpper history hh
  have hcontinuation : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            continuationCorridor} ≤ q := by
    intro x y _
    exact tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
      φ μ n x (lower + drift * (m : ℝ)) drift width endpointUpper y hdrift q
      hdrawdown
  simpa [prefixCorridor, continuationCorridor, window] using
    lintegral_weightedPrefixContinuationPair_indicator_le
      φ μ hboundary m n prefixCorridor hprefixMeas initial
      (lower + drift * (m : ℝ)) hprefixLower continuationCorridor
      hcontinuationMeas endpointUpper hterminal window q hfirst hcontinuation

end ProbabilityTheory.BranchingRandomWalk.Spine
