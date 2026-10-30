/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Spine.Tube.MRCA.ChildPairBound
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.UlamHarris.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Generation
public import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.BranchingProcess.Offspring.FieldLaw

/-!
# Weighted ancestral-prefix observables

Write \(P_{\mathrm{off}}=\texttt{offspringFieldLaw }\mu\),
\(P_{\mathrm{sp}}=\texttt{tiltedIncrementFieldLaw }\varphi\,\mu\),
\(c_\varphi(\xi)=\texttt{crossPotentialWeight }\varphi\,(-1)\,\xi\), and
\(E_n(C,x)=\{z\mid\texttt{history }n\,x\,z\in C\}\). For a generation-
\(n\) history observable \(F\) and frontier observable \(g\),
`weightedPrefixSquareObservableSum` is
\[
  \sum_{u\in\mathcal T_n}
    w_n(F,x,u,\omega)\,e^{-V_\varphi(u,\omega)}g(\omega_u),
\]
where \(w_n=\texttt{weightedPathGenerationTerm}\) and
\(V_\varphi=\texttt{pathPotential}\).
For a corridor \(D\) on the continuation histories, write
\[
  \operatorname{Off}_n(x,\xi;D)=
    \texttt{pathGenerationChildMeanOffDiagonal }\varphi\,\mu\,n\,
      (\mathbf 1_D)\,x\,\xi.
\]

## Public declarations

- `pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability` and its
  normalized forms: if every shifted continuation event has probability at
  most \(q\) on the first-step window and its endpoint is at most \(U\), then
  \[
    \operatorname{Off}_n(x,\xi)
      \le (e^{U-x}q)^2c_\varphi(\xi),\qquad
    e^{2x}\operatorname{Off}_n(x,\xi)
      \le e^{2U}q^2c_\varphi(\xi).
  \]
- `lintegral_generationPrefixParameterizedObservableSum_le` and
  `lintegral_generationPrefixChildPairObservable_le`: for a nonnegative
  generation-prefix weight \(A_u\), an offspring observable bounded by
  \(C c_\varphi\) factors as
  \[
    \int\!\sum_u A_u(\omega)g(x_u(\omega),\omega_u)\,dP_{\mathrm{off}}
      \le C\!\int c_\varphi\,d\mu\;
        \int\!\sum_u A_u\,dP_{\mathrm{off}}.
  \]
- `weightedPrefixCrossChildWeightSum`,
  `weightedPrefixSquareCrossChildWeightSum`,
  `weightedPrefixSquareObservableSum`, and their factorization theorems:
  the exact square-weighted identity is
  \[
    \int\!\sum_u w_n e^{-V_\varphi}g(\omega_u)\,dP_{\mathrm{off}}
      =\left(\int g\,d\mu\right)
        \int\!\sum_u w_n e^{-V_\varphi}\,dP_{\mathrm{off}}.
  \]
  Taking \(g=c_\varphi\) gives the cross-child moment factor
  \(\int c_\varphi\,d\mu\); with a corridor indicator, the resulting
  spine factor is \(P_{\mathrm{sp}}(E_n(C,x))\).
- `lintegral_weightedPrefixSquareMass_indicator_le_spineProbability` and
  `lintegral_weightedPrefixSquareCrossChildWeightSum_indicator_le`: if every
  endpoint in \(C\) is at least \(\ell\), then
  \[
    \int\!\sum_u w_n e^{-V_\varphi}\,dP_{\mathrm{off}}
      \le e^{x-\ell}P_{\mathrm{sp}}(E_n(C,x)),
  \]
  with the cross-child version multiplied by \(\int c_\varphi\,d\mu\).
- `lintegral_weightedPrefixContinuationPair_indicator_le`: if the prefix
  endpoint is at least \(\ell\), continuation endpoints are at most \(U\),
  and the shifted continuation probabilities are bounded by \(q\), then
  with \(A_u=w_m(\mathbf 1_{C_{\mathrm{prefix}}},x,u,\omega)
  e^{-V_\varphi(u,\omega)}\),
  \[
    e^{-2x}\int\!\sum_u A_u e^{2(x+V_u)}\operatorname{Off}_n(x+V_u,\omega_u)
      \,dP_{\mathrm{off}}
      \le e^{-2x}e^{2U}q^2
        \left(\int c_\varphi\,d\mu\right)e^{x-\ell}
        P_{\mathrm{sp}}(E_m(C_{\mathrm{prefix}},x)).
  \]

The one-use affine-corridor drawdown specialization for the positive-depth
MRCA estimate is kept under `MRCA/Lemmas/`.
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

/-- The pointwise continuation-pair observable is bounded by the
cross-child weight under the shifted-spine probability estimate used in the
one-ancestor second-moment bound. -/
theorem pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ ξ, pathGenerationChildMeanOffDiagonal φ μ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossPotentialWeight φ (-1) ξ := by
  intro ξ
  simpa [pathGenerationChildMeanOffDiagonal] using
    pathGenerationChildMean_offDiagonal_le_crossPotentialWeight
      φ μ hboundary n x terminalUpper corridor hcorridor hterminal
      window q hfirst hprob ξ

/-- After extracting the endpoint factor `exp(-2 * x)`, the continuation
pair observable has a bound uniform in the ancestor position. -/
theorem pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ ξ, ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
      ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
        crossPotentialWeight φ (-1) ξ := by
  intro ξ
  have hraw := pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal window q
    hfirst hprob ξ
  have hconstant :
      ENNReal.ofReal (Real.exp (2 * x)) *
          (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 =
        ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 := by
    have hexp :
        Real.exp (2 * x) *
            (Real.exp (terminalUpper - x) * Real.exp (terminalUpper - x)) =
          Real.exp (2 * terminalUpper) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (ENNReal.ofReal (Real.exp (2 * x)) *
            ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (terminalUpper - x))) * q ^ 2 := by
          simp only [pow_two]
          ac_rfl
      _ = ENNReal.ofReal
            (Real.exp (2 * x) *
              (Real.exp (terminalUpper - x) *
                Real.exp (terminalUpper - x))) * q ^ 2 := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
          congr 2
          ring
      _ = ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 := by
          rw [hexp]
  calc
    ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
        ENNReal.ofReal (Real.exp (2 * x)) *
          ((ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
            crossPotentialWeight φ (-1) ξ) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
          crossPotentialWeight φ (-1) ξ := by
      rw [← mul_assoc, hconstant]

/-- The normalized continuation-pair bound holds uniformly over every
ancestor position when the shifted-spine estimate is uniform in that
position. -/
theorem pathGenerationChildMeanOffDiagonal_normalized_le_of_uniformShiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ x ξ, ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
      ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
        crossPotentialWeight φ (-1) ξ := by
  intro x ξ
  exact pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal window q
    hfirst (fun y hy => hprob x y hy) ξ

/-- A generation-`n` prefix contributes its weighted ancestral path mass,
multiplied by the cross-child weight at the frontier mark. -/
noncomputable def weightedPrefixCrossChildWeightSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      crossPotentialWeight φ (-1) (ω u)

/-- The ancestor-prefix cross-weight sum with one extra reciprocal-potential
factor. In the MRCA expansion this contributes the prefix indicator times
`exp(-2 * pathPotential)` and the cross-child weight at that ancestor. -/
noncomputable def weightedPrefixSquareCrossChildWeightSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        crossPotentialWeight φ (-1) (ω u)

/-- The square-weighted prefix sum with an arbitrary observable of the
offspring mark at the generation-`n` frontier.  This is the reusable form of
the ancestor factor in an MRCA pair contribution;
`weightedPrefixSquareCrossChildWeightSum` is its cross-child specialization. -/
noncomputable def weightedPrefixSquareObservableSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) * g (ω u)

/-- A frontier continuation observable may depend on its ancestor's
position. A uniform bound in that position lets the position-dependent
observable be dominated by a fixed offspring observable, which then factors
from the generation prefix. -/
theorem lintegral_generationPrefixParameterizedObservableSum_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (g : ℝ → Step ℕ X → ℝ≥0∞)
    (hAgen : ∀ u, Measurable[generationFiltration (M := Step ℕ X) n]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hsupport : ∀ u, u.length ≠ n → A u = fun _ => 0)
    (C : ℝ≥0∞)
    (hbound : ∀ x ξ, g x ξ ≤ C * crossPotentialWeight φ (-1) ξ) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) ≤
        C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
  classical
  have hpoint (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        A u ω * g (position u ω) (ω u)) ≤
        ∑' u : TreeNode ℕ,
          A u ω * (C * crossPotentialWeight φ (-1) (ω u)) := by
    exact ENNReal.tsum_le_tsum (fun u =>
      mul_le_mul_of_nonneg_left (hbound (position u ω) (ω u)) (by positivity))
  have hbase : Measurable (fun ω : StepField ℕ X =>
      ∑' u : TreeNode ℕ, A u ω * crossPotentialWeight φ (-1) (ω u)) := by
    apply Measurable.tsum
    intro u
    exact (hA u).mul
      ((crossPotentialWeight_measurable φ (-1)).comp (measurable_pi_apply u))
  have hmajor (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        A u ω * (C * crossPotentialWeight φ (-1) (ω u))) =
        C * (∑' u : TreeNode ℕ,
          A u ω * crossPotentialWeight φ (-1) (ω u)) := by
    calc
      _ = ∑' u : TreeNode ℕ,
          C * (A u ω * crossPotentialWeight φ (-1) (ω u)) := by
        apply tsum_congr
        intro u
        ac_rfl
      _ = _ := ENNReal.tsum_mul_left
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) ≤
        ∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * (C * crossPotentialWeight φ (-1) (ω u))
          ∂offspringFieldLaw μ := lintegral_mono hpoint
    _ = C * (∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * crossPotentialWeight φ (-1) (ω u) ∂offspringFieldLaw μ) := by
      calc
        _ = ∫⁻ ω, C * (∑' u : TreeNode ℕ,
              A u ω * crossPotentialWeight φ (-1) (ω u)) ∂offspringFieldLaw μ := by
          apply lintegral_congr
          exact hmajor
        _ = _ := lintegral_const_mul C hbase
    _ = C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
      rw [lintegral_generationPrefixObservableSum_eq_mul μ n A
        (crossPotentialWeight φ (-1)) hAgen hA hsupport
        (crossPotentialWeight_measurable φ (-1))]
      ac_rfl

/-- The uniform shifted-spine continuation estimate can be averaged over a
generation-`prefixLength` prefix. This is the local expected-pair bound for one fixed
MRCA depth; the prefix weight `A` is supplied by its ancestral corridor. -/
theorem lintegral_generationPrefixChildPairObservable_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (prefixLength continuationLength : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (hAgen : ∀ u,
      Measurable[generationFiltration (M := Step ℕ X) prefixLength]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hsupport : ∀ u, u.length ≠ prefixLength → A u = fun _ => 0)
    (terminalUpper : ℝ)
    (corridor : Set (Fin (continuationLength + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨continuationLength + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history continuationLength (x + y) increment) ∈
            corridor} ≤ q) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
        pathGenerationChildMeanOffDiagonal φ μ continuationLength
          (corridor.indicator (fun _ => (1 : ℝ≥0∞)))
          (position u ω) (ω u) ∂offspringFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
  let g : ℝ → Step ℕ X → ℝ≥0∞ := fun x ξ =>
    ENNReal.ofReal (Real.exp (2 * x)) *
      pathGenerationChildMeanOffDiagonal φ μ continuationLength
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2
  have hbound : ∀ x ξ, g x ξ ≤ C * crossPotentialWeight φ (-1) ξ := by
    intro x ξ
    simpa [g, C, mul_assoc] using
      pathGenerationChildMeanOffDiagonal_normalized_le_of_uniformShiftedProbability
        φ μ hboundary continuationLength terminalUpper corridor hcorridor
        hterminal window q
        hfirst hprob x ξ
  simpa [g, C, mul_assoc] using
    lintegral_generationPrefixParameterizedObservableSum_le
      φ μ prefixLength A position g hAgen hA hsupport C hbound

private lemma displaceWith_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (v p : TreeNode ℕ)
    (hvp : v.length + p.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X =>
        Combinatorics.Branching.displaceWith φ ω v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      have hparent : v.length < n := by
        simp only [List.length_cons] at hvp
        omega
      have hstep : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X =>
            value' ((ω v).map φ) i) := by
        exact (value'_measurable i).comp
          ((Step.map_measurable φ.measurable_toFun).comp
            (mark_measurable_of_depth_lt (M := Step ℕ X) v n hparent))
      have htailBound : (v ++ [i]).length + p.length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at hvp
        omega
      have htail := ih (v := v ++ [i]) htailBound
      change Measurable[generationFiltration (M := Step ℕ X) n]
        (fun ω : StepField ℕ X =>
          value' ((ω v).map φ) i +
            Combinatorics.Branching.displaceWith φ ω (v ++ [i]) p)
      exact hstep.add htail

private lemma pathHistory_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (u : TreeNode ℕ)
    (hu : u.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X => pathHistory φ n x ω u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  rw [measurable_pi_iff]
  intro k
  have htake : (u.take k).length ≤ n := by
    have hlen : (u.take k).length ≤ k.val := by
      simp [List.length_take]
    omega
  exact measurable_const.add
    (displaceWith_measurable_generation φ n [] (u.take k)
      (by simpa using htake))

private lemma weightedPathGenerationTerm_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (x : ℝ) (u : TreeNode ℕ) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (weightedPathGenerationTerm φ n F x u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  by_cases hu : u.length = n
  · rw [weightedPathGenerationTerm]
    have hpotential :
        Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X => pathPotential φ ω u) := by
      simpa [pathPotential] using
        displaceWith_measurable_generation φ n [] u (by simpa [hu])
    have hhistory := pathHistory_measurable_generation φ n x u (by omega)
    have hvalue : Measurable[generationFiltration (M := Step ℕ X) n]
        (fun ω : StepField ℕ X =>
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            F (pathHistory φ n x ω u)) :=
      hpotential.neg.exp.ennreal_ofReal.mul (hF.comp hhistory)
    have hsurvive : MeasurableSet[generationFiltration (M := Step ℕ X) n]
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      exact surviveAlong_measurableSet (X := X) [] u n (by simpa [hu])
    have hset : {ω : StepField ℕ X |
        u.length = n ∧ surviveAlong ω [] u} =
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      ext ω
      simp [hu]
    rw [hset]
    exact hvalue.indicator hsurvive
  · have hzero : weightedPathGenerationTerm φ n F x u = 0 := by
      funext ω
      simp [weightedPathGenerationTerm, hu]
    rw [hzero]
    exact measurable_const

/-- Exact factorization of the square-weighted prefix observable.  Its
cross-child instance is the ancestor-side term in the positive-depth
MRCA sum. -/
theorem lintegral_weightedPrefixSquareObservableSum_eq_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, weightedPrefixSquareObservableSum φ n F x g ω
      ∂offspringFieldLaw μ) =
        (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂offspringFieldLaw μ) := by
  let A (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ := fun ω =>
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
  have hAgen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) n] (A u) := by
    by_cases hu : u.length = n
    · have hp := displaceWith_measurable_generation φ n [] u (by simpa [hu])
      have hpotential : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X => pathPotential φ ω u) := by
        simpa [pathPotential] using hp
      exact (weightedPathGenerationTerm_measurable_generation φ n hF x u).mul
        hpotential.neg.exp.ennreal_ofReal
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    by_cases hu : u.length = n
    · exact (weightedPathGenerationTerm_measurable φ n hF x u).mul
        ((ENNReal.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            ((pathPotential_measurable φ [] u).neg))))
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hsupport (u : TreeNode ℕ) (hu : u.length ≠ n) :
      A u = fun _ => 0 := by
    funext ω
    simp [A, weightedPathGenerationTerm, hu]
  simpa [weightedPrefixSquareObservableSum, A] using
    (lintegral_generationPrefixObservableSum_eq_mul μ n A g
      hAgen hA hsupport hg)

/-- A pointwise cross-child domination for a frontier continuation observable
can be pulled through the prefix sum.  This is the estimate used for a fixed
MRCA depth after the shifted continuation probabilities have been bounded. -/
theorem lintegral_weightedPrefixSquareObservableSum_le_of_crossChildBound
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (hg : Measurable g)
    (C : ℝ≥0∞)
    (hbound : ∀ ξ, g ξ ≤ C * crossPotentialWeight φ (-1) ξ) :
    (∫⁻ ω, weightedPrefixSquareObservableSum φ n F x g ω
      ∂offspringFieldLaw μ) ≤
        C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂offspringFieldLaw μ) := by
  rw [lintegral_weightedPrefixSquareObservableSum_eq_mul
    φ μ n F hF x g hg]
  have hmean :
      (∫⁻ ξ, g ξ ∂μ) ≤ C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
    calc
      (∫⁻ ξ, g ξ ∂μ) ≤
          ∫⁻ ξ, C * crossPotentialWeight φ (-1) ξ ∂μ := lintegral_mono hbound
      _ = C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
        rw [lintegral_const_mul _ (crossPotentialWeight_measurable φ (-1))]
  calc
    (∫⁻ ξ, g ξ ∂μ) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
          ∂offspringFieldLaw μ) ≤
      (C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ)) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
          ∂offspringFieldLaw μ) := by
      exact mul_le_mul_of_nonneg_right hmean (by positivity)
    _ = C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂offspringFieldLaw μ) := by
      ac_rfl

/-- The square-weighted prefix/cross-child observable factors into the
offspring cross-child moment and the mean square-weighted prefix mass. -/
theorem lintegral_weightedPrefixSquareCrossChildWeightSum_eq_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n F x ω
      ∂offspringFieldLaw μ) =
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂offspringFieldLaw μ) := by
  simpa [weightedPrefixSquareCrossChildWeightSum,
    weightedPrefixSquareObservableSum] using
    (lintegral_weightedPrefixSquareObservableSum_eq_mul
      φ μ n F hF x (crossPotentialWeight φ (-1)) (crossPotentialWeight_measurable φ (-1)))

/-- The frontier cross-child weight is independent of the generation-`n`
prefix. Consequently the expected weighted prefix/cross-weight sum factors
exactly into the finite cross-child moment and the spine prefix integral. This
is the ancestor-side factor in each positive-depth MRCA pair contribution. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_eq_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
      ∂offspringFieldLaw μ) =
      (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) := by
  classical
  let A (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ :=
    weightedPathGenerationTerm φ n F x u
  let B (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ :=
    fun ω => crossPotentialWeight φ (-1) (ω u)
  have hA (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) n] (A u) := by
    simpa [A] using
      weightedPathGenerationTerm_measurable_generation φ n hF x u
  have hB (u : TreeNode ℕ) :
      Measurable[MeasurableSpace.comap (subtreeStepField u) inferInstance]
        (B u) := by
    have hroot : Measurable (fun η : StepField ℕ X =>
        crossPotentialWeight φ (-1) (η [])) :=
      (crossPotentialWeight_measurable φ (-1)).comp
        (measurable_pi_apply ([] : TreeNode ℕ) :
          Measurable (fun η : StepField ℕ X => η []))
    apply Measurable.of_comap_le
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (f := subtreeStepField u) (g := B u)
      (h := fun η : StepField ℕ X => crossPotentialWeight φ (-1) (η [])) hroot (by
        funext ω
        simp [B, subtreeStepField])
  have hAfull (u : TreeNode ℕ) : Measurable (A u) := by
    simpa [A] using weightedPathGenerationTerm_measurable φ n hF x u
  have hBfull (u : TreeNode ℕ) : Measurable (B u) := by
    simpa [B, Function.comp_def] using
      (crossPotentialWeight_measurable φ (-1)).comp
        (measurable_pi_apply u :
          Measurable (fun ω : StepField ℕ X => ω u))
  have hfactor (u : TreeNode ℕ) :
      (∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ) =
        (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
    by_cases hu : u.length = n
    · subst n
      have hind : IndepFun (A u) (B u) (offspringFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right
          (indep_of_indep_of_le_left
            (generation_subtreeStepField_independent μ u) (hA u).comap_le)
          (hB u).comap_le
      calc
        (∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ) =
            (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
              (∫⁻ ξ, B u ξ ∂offspringFieldLaw μ) :=
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
            (hAfull u) (hBfull u) hind
        _ = (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
          congr 1
          change (∫⁻ ω, crossPotentialWeight φ (-1) (ω u) ∂offspringFieldLaw μ) = _
          calc
            _ = ∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂
                (offspringFieldLaw μ).map (fun ω : StepField ℕ X => ω u) := by
              exact (lintegral_map (crossPotentialWeight_measurable φ (-1))
                (measurable_pi_apply u :
                  Measurable (fun ω : StepField ℕ X => ω u))).symm
            _ = ∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ := by
              rw [offspringFieldLaw_coordinate μ u]
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      simp [hzero]
  have htermMeas (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X => A u ω * B u ω) :=
    ((weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((crossPotentialWeight_measurable φ (-1)).comp (measurable_pi_apply u)))
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermMeas u).aemeasurable
  have hweighted :
      (∑' u : TreeNode ℕ, ∫⁻ ω, A u ω ∂offspringFieldLaw μ) =
        ∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ := by
    simp only [weightedPathGeneration]
    rw [lintegral_tsum]
    intro u
    exact (weightedPathGenerationTerm_measurable φ n hF x u).aemeasurable
  calc
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
      ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ := by
      change (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω
        ∂offspringFieldLaw μ) = _
      exact hsumIntegral
    _ = ∑' u : TreeNode ℕ,
          (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
            (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
      apply tsum_congr
      intro u
      exact hfactor u
    _ = (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) := by
      rw [ENNReal.tsum_mul_right]
      rw [hweighted, mul_comm]

/-- For an indicator prefix corridor, the factorization above is exactly the
cross-child moment times the corresponding tilted-spine corridor probability.
This is the ancestor-prefix factor appearing in each positive-depth MRCA
pair contribution in Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 4, Lemma 4.5. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x : ℝ) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂offspringFieldLaw μ) =
      (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (ProbabilityTheory.RandomWalk.history_measurable n x)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hmanyToOne := weightedPathManyToOneCore φ μ hboundary n hF x
  calc
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
        ∂offspringFieldLaw μ) =
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) :=
      lintegral_weightedPrefixCrossChildWeightSum_eq_crossMoment_mul
        φ μ n F hF x
    _ = (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [hmanyToOne]
      congr 1
      change (∫⁻ increment, spineEvent.indicator
        (fun _ => (1 : ℝ≥0∞)) increment ∂tiltedIncrementFieldLaw φ μ) = _
      rw [lintegral_indicator_const hspineEvent]
      simp [spineEvent]

/-- A shifted-spine estimate for the prefix corridor immediately gives the
corresponding averaged ancestor cross-weight bound. No second-moment or
pair-bound assumption is introduced here. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_indicator_le_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x : ℝ) (q : ℝ≥0∞)
    (hprefix : (tiltedIncrementFieldLaw φ μ)
      {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} ≤ q) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂offspringFieldLaw μ) ≤
      (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) * q := by
  rw [lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
    φ μ hboundary n corridor hcorridor x]
  gcongr

/-- The lower boundary of a generation-`n` corridor controls the extra
reciprocal-potential factor in a squared ancestral weight.  The remaining
weighted path mass is exactly its tilted-spine probability. -/
theorem lintegral_weightedPrefixSquareMass_indicator_le_spineProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x lower : ℝ)
    (hlower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      weightedPathGenerationTerm φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
      ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (x - lower)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (x - lower))
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hterm (u : TreeNode ℕ) (ω : StepField ℕ X) :
      weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤
        K * weightedPathGenerationTerm φ n F x u ω := by
    by_cases hu : u.length = n
    · by_cases hs : surviveAlong ω [] u
      · by_cases hc : pathHistory φ n x ω u ∈ corridor
        · have hendpoint := hlower (pathHistory φ n x ω u) hc
          rw [pathHistory_last φ n x ω u hu] at hendpoint
          have hpotential : -pathPotential φ ω u ≤ x - lower := by linarith
          have hweight : weightedPathGenerationTerm φ n F x u ω =
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          have hextra : ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤ K := by
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr hpotential)
          rw [hweight]
          exact mul_le_mul_of_nonneg_right hextra (by positivity)
        · simp [weightedPathGenerationTerm, F, hu, hs, hc]
      · simp [weightedPathGenerationTerm, hu, hs]
    · simp [weightedPathGenerationTerm, hu]
  have hsumPointwise (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) ≤
        K * weightedPathGeneration φ n F x ω := by
    calc
      _ ≤ ∑' u : TreeNode ℕ,
          K * weightedPathGenerationTerm φ n F x u ω :=
        ENNReal.tsum_le_tsum (fun u => hterm u ω)
      _ = K * weightedPathGeneration φ n F x ω := by
        rw [weightedPathGeneration, ENNReal.tsum_mul_left]
  have hsumMeas : Measurable (fun ω : StepField ℕ X =>
      ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) := by
    apply Measurable.tsum
    intro u
    exact (weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp
          ((pathPotential_measurable φ [] u).neg))))
  have hweighted : Measurable (weightedPathGeneration φ n F x) :=
    weightedPathGeneration_measurable (ι := ℕ) φ n hF x
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
        ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact ((weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp
          ((pathPotential_measurable φ [] u).neg))))).aemeasurable
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (ProbabilityTheory.RandomWalk.history_measurable n x)
  have hmanyToOne := weightedPathManyToOneCore φ μ hboundary n hF x
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
        ∂offspringFieldLaw μ) ≤
      ∫⁻ ω, K * weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ :=
        lintegral_mono hsumPointwise
    _ = K * (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) :=
      lintegral_const_mul K hweighted
    _ = K * (∫⁻ increment, F
          (ProbabilityTheory.RandomWalk.history n x increment)
          ∂tiltedIncrementFieldLaw φ μ) := by rw [hmanyToOne]
    _ = K * (tiltedIncrementFieldLaw φ μ) spineEvent := by
      congr 1
      change (∫⁻ increment, spineEvent.indicator
        (fun _ => (1 : ℝ≥0∞)) increment ∂tiltedIncrementFieldLaw φ μ) = _
      rw [lintegral_indicator_const hspineEvent]
      simp [spineEvent]
    _ = _ := by
      simp only [K]
      congr 1

/-- A fixed MRCA depth factors into the continuation-pair estimate and the
square-weighted ancestral corridor mass. This is the positive-depth analogue
of the root-split contribution estimate, before summing over all possible MRCA depths. -/
theorem lintegral_weightedPrefixContinuationPair_indicator_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (prefixCorridor : Set (Fin (m + 1) → ℝ))
    (hprefixCorridor : MeasurableSet prefixCorridor)
    (initial prefixLower : ℝ)
    (hprefixLower : ∀ history ∈ prefixCorridor,
      prefixLower ≤ history ⟨m, Nat.lt_succ_self m⟩)
    (continuationCorridor : Set (Fin (n + 2) → ℝ))
    (hcontinuationCorridor : MeasurableSet continuationCorridor)
    (terminalUpper : ℝ)
    (hterminalUpper : ∀ history ∈ continuationCorridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ continuationCorridor,
      history ⟨1, by omega⟩ ∈ window)
    (hcontinuation : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            continuationCorridor} ≤ q) :
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ m
          (prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          ENNReal.ofReal
            (Real.exp (2 * (initial + pathPotential φ ω u))) *
          pathGenerationChildMeanOffDiagonal φ μ n
            (continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞)))
            (initial + pathPotential φ ω u) (ω u)
        ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2) *
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (initial - prefixLower)) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              prefixCorridor}) := by
  let F : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let G : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞ := fun u ω =>
    weightedPathGenerationTerm φ m F initial u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
  let position : TreeNode ℕ → StepField ℕ X → ℝ := fun u ω =>
    initial + pathPotential φ ω u
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2
  have hF : Measurable F := measurable_const.indicator hprefixCorridor
  have hG : Measurable G := measurable_const.indicator hcontinuationCorridor
  have hAgen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) m] (A u) := by
    by_cases hu : u.length = m
    · have hp :
          Measurable[generationFiltration (M := Step ℕ X) m]
            (fun ω : StepField ℕ X => pathPotential φ ω u) := by
        simpa [pathPotential] using
          displaceWith_measurable_generation φ m [] u (by simpa [hu])
      exact (weightedPathGenerationTerm_measurable_generation φ m hF initial u).mul
        hp.neg.exp.ennreal_ofReal
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    by_cases hu : u.length = m
    · exact (weightedPathGenerationTerm_measurable φ m hF initial u).mul
        ((ENNReal.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            ((pathPotential_measurable φ [] u).neg))))
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hsupport (u : TreeNode ℕ) (hu : u.length ≠ m) :
      A u = fun _ => 0 := by
    funext ω
    simp [A, weightedPathGenerationTerm, hu]
  have hpair :=
    lintegral_generationPrefixChildPairObservable_le
      φ μ hboundary m n A position hAgen hA hsupport terminalUpper
      continuationCorridor hcontinuationCorridor hterminalUpper window q
      hfirst hcontinuation
  have hmass :=
    lintegral_weightedPrefixSquareMass_indicator_le_spineProbability
      φ μ hboundary m prefixCorridor hprefixCorridor initial prefixLower
      hprefixLower
  have hpair' :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
          pathGenerationChildMeanOffDiagonal φ μ n G
            (position u ω) (ω u) ∂offspringFieldLaw μ) ≤
        C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
    simpa [A, G, position, C, mul_assoc] using hpair
  have hmass' :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (initial - prefixLower)) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              prefixCorridor} := by
    simpa [A, F] using hmass
  calc
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (position u ω) (ω u) ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ)) :=
      mul_le_mul_of_nonneg_left hpair' (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (C * (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (ENNReal.ofReal (Real.exp (initial - prefixLower)) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
                prefixCorridor})) := by
      gcongr
    _ = _ := by
      simp [C, mul_assoc]

/-- The prefix endpoint lower bound removes one of the two reciprocal
potential factors in a positive-depth MRCA term. The remaining expectation is
the spine prefix probability times the cross-child moment. -/
theorem lintegral_weightedPrefixSquareCrossChildWeightSum_indicator_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x lower : ℝ)
    (hlower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩) :
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (x - lower)) *
        (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (x - lower))
  have hprefixMeas : Measurable (weightedPrefixCrossChildWeightSum φ n F x) := by
    unfold weightedPrefixCrossChildWeightSum
    apply Measurable.tsum
    intro u
    exact (weightedPathGenerationTerm_measurable φ n
      (measurable_const.indicator hcorridor) x u).mul
      ((crossPotentialWeight_measurable φ (-1)).comp (measurable_pi_apply u))
  have hterm (u : TreeNode ℕ) (ω : StepField ℕ X) :
      weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          crossPotentialWeight φ (-1) (ω u) ≤
        K * (weightedPathGenerationTerm φ n F x u ω *
          crossPotentialWeight φ (-1) (ω u)) := by
    by_cases hu : u.length = n
    · by_cases hs : surviveAlong ω [] u
      · by_cases hc : pathHistory φ n x ω u ∈ corridor
        · have hterminal := hlower (pathHistory φ n x ω u) hc
          rw [pathHistory_last φ n x ω u hu] at hterminal
          have hpotential : -pathPotential φ ω u ≤ x - lower := by linarith
          have hextra : ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤ K := by
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hpotential)
          have hweight : weightedPathGenerationTerm φ n F x u ω =
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          rw [hweight]
          dsimp [K]
          calc
            _ = ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                (ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                  crossPotentialWeight φ (-1) (ω u)) := by ac_rfl
            _ ≤ ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                (ENNReal.ofReal (Real.exp (x - lower)) *
                  crossPotentialWeight φ (-1) (ω u)) := by gcongr
            _ = ENNReal.ofReal (Real.exp (x - lower)) *
                (ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                  crossPotentialWeight φ (-1) (ω u)) := by ac_rfl
        · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          simp [hzero]
      · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
          simp [weightedPathGenerationTerm, hu, hs]
        simp [hzero]
    · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
        simp [weightedPathGenerationTerm, hu]
      simp [hzero]
  have hpoint (ω : StepField ℕ X) :
      weightedPrefixSquareCrossChildWeightSum φ n F x ω ≤
        K * weightedPrefixCrossChildWeightSum φ n F x ω := by
    unfold weightedPrefixSquareCrossChildWeightSum weightedPrefixCrossChildWeightSum
    calc
      _ ≤ ∑' u : TreeNode ℕ, K *
          (weightedPathGenerationTerm φ n F x u ω *
            crossPotentialWeight φ (-1) (ω u)) :=
        ENNReal.tsum_le_tsum (fun u => hterm u ω)
      _ = K * ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            crossPotentialWeight φ (-1) (ω u) := ENNReal.tsum_mul_left
  calc
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n F x ω
        ∂offspringFieldLaw μ) ≤
        ∫⁻ ω, K * weightedPrefixCrossChildWeightSum φ n F x ω
          ∂offspringFieldLaw μ := lintegral_mono hpoint
    _ = K * (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
          ∂offspringFieldLaw μ) := lintegral_const_mul K hprefixMeas
    _ = K * ((∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}) := by
      rw [lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
        φ μ hboundary n corridor hcorridor x]
    _ = _ := by ac_rfl

end ProbabilityTheory.BranchingRandomWalk.Spine
