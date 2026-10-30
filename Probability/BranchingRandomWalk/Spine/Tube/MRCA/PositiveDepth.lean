/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Combinatorics.UlamHarris.Basic
public import Probability.BranchingProcess.Offspring.FieldLaw
public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Generation
public import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import all Probability.BranchingRandomWalk.Spine.Tube.MRCA.Lemmas.AffineCorridorContinuation

/-!
# Positive-depth affine-tube MRCA contribution

`affineTubeMRCAPairContribution φ μ m n ...` is the expected ordered path
pair whose most recent common ancestor is at generation `m` and which has
`n + 1` generations remaining below it. It is
`∫⁻ ω, ∑' u, pathGenerationTerm φ m prefix initial u ω *
pathGenerationChildMeanOffDiagonal φ μ n continuation
(initial + pathPotential φ ω u) (ω u) ∂offspringFieldLaw μ`, where `prefix` and
`continuation` are the corresponding affine-corridor indicators. Its
normalization identity converts this path-pair expression into the
square-weighted continuation expression. The drawdown estimate bounds each
positive-depth term, and a finite sum gives the aggregate over all possible
MRCA generations.

## Public declarations

The declarations are `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution`,
`affineTubeMRCAPairContribution_eq_normalized`,
`affineTubeMRCAPairContribution_le_of_drawdown`, and
`sum_affineTubeMRCAPairContribution_le_of_drawdown`.

Let \(C_{m,n}\) denote the expected ordered pair contribution whose most
recent common ancestor is at generation \(m\), with \(n+1\) generations
below it. Put
\(M_\varphi=\int\texttt{crossPotentialWeight }\varphi\,(-1)\,\xi\,d\mu(\xi)\) and
\(P_{\mathrm{sp}}=\texttt{tiltedIncrementFieldLaw }\varphi\,\mu\), and
\(E_m=\{z\mid\texttt{history }m\,x\,z\in
\texttt{affineCorridorPrefix }m\,a\,v\,\Delta\}\). If the tilted-spine
drawdown event has probability at most \(q_n\), then
\[
  C_{m,n}
    \le e^{-2x}e^{2u}q_n^2
      M_\varphi e^{x-a-vm}\,P_{\mathrm{sp}}(E_m),
\]
where \(a\) is the affine-tube lower boundary, \(v\ge0\) its drift,
\(u\) the terminal upper bound, and \(E_m\) the tilted-spine prefix event.
Summing this estimate over the possible ancestor generations gives
\[
  \sum_{m=0}^{N-1}C_{m,N-m-1}
    \le \sum_{m=0}^{N-1}e^{-2x}e^{2u}q_{N-m-1}^{2}
      M_\varphi e^{x-a-vm}
      P_{\mathrm{sp}}(E_m).
\]
The one-use affine-corridor continuation estimate supplying the bound is in
`MRCA/Lemmas/AffineCorridorContinuation.lean`.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- Expected ordered successful path pairs whose most recent common ancestor
is at generation `m`, with `n + 1` generations remaining below that ancestor. -/
noncomputable def affineTubeMRCAPairContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X))
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' u : TreeNode ℕ,
    pathGenerationTerm φ m
      ((affineCorridorPrefix m lower drift width).indicator
        (fun _ => (1 : ℝ≥0∞))) initial u ω *
    pathGenerationChildMeanOffDiagonal φ μ n
      ((affineCorridorHistoryEndpointCutoff n
        (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞)))
      (initial + pathPotential φ ω u) (ω u) ∂offspringFieldLaw μ

private lemma expReciprocalSquareNormalization (x s : ℝ) :
    ENNReal.ofReal (Real.exp (-(2 * x))) *
      ((ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s))) *
        ENNReal.ofReal (Real.exp (2 * (x + s)))) = 1 := by
  have hcancel (t : ℝ) :
      ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp t) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-t)), ← Real.exp_add]
    simp
  have hdouble :
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s)) =
        ENNReal.ofReal (Real.exp (-(2 * s))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-s)), ← Real.exp_add]
    congr 1
    ring_nf
  have hsplit : ENNReal.ofReal (Real.exp (2 * (x + s))) =
      ENNReal.ofReal (Real.exp (2 * x)) *
        ENNReal.ofReal (Real.exp (2 * s)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (2 * x))]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc
    _ = (ENNReal.ofReal (Real.exp (-(2 * x))) *
          ENNReal.ofReal (Real.exp (2 * x))) *
        ((ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s))) *
          ENNReal.ofReal (Real.exp (2 * s))) := by ac_rfl
    _ = 1 := by
      rw [hcancel (2 * x), hdouble, hcancel (2 * s)]
      simp

/-- The square-weighted continuation expression is exactly the expected
ordered-pair contribution at this MRCA depth after the initial-position
normalization. -/
theorem affineTubeMRCAPairContribution_eq_normalized
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X))
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper =
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
          ∂offspringFieldLaw μ) := by
  let F : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    (affineCorridorPrefix m lower drift width).indicator
      (fun _ => (1 : ℝ≥0∞))
  let G : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    (affineCorridorHistoryEndpointCutoff n
      (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * initial)))
  have hterm (ω : StepField ℕ X) (u : TreeNode ℕ) :
      pathGenerationTerm φ m F initial u ω *
        pathGenerationChildMeanOffDiagonal φ μ n G
          (initial + pathPotential φ ω u) (ω u) =
      c * (weightedPathGenerationTerm φ m F initial u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        ENNReal.ofReal
          (Real.exp (2 * (initial + pathPotential φ ω u))) *
        pathGenerationChildMeanOffDiagonal φ μ n G
          (initial + pathPotential φ ω u) (ω u)) := by
    rw [weightedPathGenerationTerm_eq_reciprocal_mul_pathGenerationTerm]
    have hscalar := expReciprocalSquareNormalization initial
      (pathPotential φ ω u)
    dsimp [c]
    calc
      _ = 1 * (pathGenerationTerm φ m F initial u ω *
          pathGenerationChildMeanOffDiagonal φ μ n G
            (initial + pathPotential φ ω u) (ω u)) := by simp
      _ = (ENNReal.ofReal (Real.exp (-(2 * initial))) *
            ((ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) *
              ENNReal.ofReal
                (Real.exp (2 * (initial + pathPotential φ ω u))))) *
            (pathGenerationTerm φ m F initial u ω *
              pathGenerationChildMeanOffDiagonal φ μ n G
                (initial + pathPotential φ ω u) (ω u)) := by
          rw [hscalar]
      _ = _ := by ac_rfl
  calc
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper =
        ∫⁻ ω, c * (∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ m F initial u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            ENNReal.ofReal
              (Real.exp (2 * (initial + pathPotential φ ω u))) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (initial + pathPotential φ ω u) (ω u)) ∂offspringFieldLaw μ := by
      apply lintegral_congr
      intro ω
      calc
        _ = ∑' u : TreeNode ℕ,
            c * (weightedPathGenerationTerm φ m F initial u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
              ENNReal.ofReal
                (Real.exp (2 * (initial + pathPotential φ ω u))) *
              pathGenerationChildMeanOffDiagonal φ μ n G
                (initial + pathPotential φ ω u) (ω u)) := by
              apply tsum_congr
              intro u
              exact hterm ω u
        _ = _ := ENNReal.tsum_mul_left
    _ = c * (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ m F initial u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            ENNReal.ofReal
              (Real.exp (2 * (initial + pathPotential φ ω u))) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (initial + pathPotential φ ω u) (ω u)
          ∂offspringFieldLaw μ) := by
      exact lintegral_const_mul' c _ ENNReal.ofReal_ne_top
    _ = _ := by simp [c, F, G]

/-- The affine-tube MRCA pair contribution at each positive ancestor
generation is bounded by the same drawdown and cross-child estimates as its
normalized continuation term. -/
theorem affineTubeMRCAPairContribution_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * q ^ 2) *
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (ENNReal.ofReal (Real.exp
          (initial - (lower + drift * (m : ℝ)))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              affineCorridorPrefix m lower drift width}) := by
  rw [affineTubeMRCAPairContribution_eq_normalized]
  exact lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown
    φ μ hboundary m n initial lower drift width endpointUpper hdrift q hdrawdown

/-- Summing the affine-tube MRCA pair contributions over every possible
branching generation gives the corresponding finite aggregate estimate. -/
theorem sum_affineTubeMRCAPairContribution_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (N : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℕ → ℝ≥0∞)
    (hdrawdown : ∀ n,
      (tiltedIncrementFieldLaw φ μ)
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          n width (width + drift * (n : ℝ))) ≤ q n) :
    (∑ m : Fin N, affineTubeMRCAPairContribution φ μ m.val
        (N - m.val - 1) initial lower drift width endpointUpper) ≤
      ∑ m : Fin N,
        ENNReal.ofReal (Real.exp (-(2 * initial))) *
          (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
            q (N - m.val - 1) ^ 2) *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (ENNReal.ofReal
            (Real.exp (initial - (lower + drift * (m.val : ℝ)))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | ProbabilityTheory.RandomWalk.history m.val initial increment ∈
                affineCorridorPrefix m.val lower drift width}) := by
  apply Finset.sum_le_sum
  intro m hm
  exact affineTubeMRCAPairContribution_le_of_drawdown
    φ μ hboundary m.val (N - m.val - 1) initial lower drift width endpointUpper
    hdrift (q (N - m.val - 1)) (hdrawdown (N - m.val - 1))

end ProbabilityTheory.BranchingRandomWalk.Spine
