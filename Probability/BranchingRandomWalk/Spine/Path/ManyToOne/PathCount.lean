/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
public import Probability.MeasureTheory.Moments.PaleyZygmund

/-!
# Path-count events and moment bounds

For a measurable history set `A : Set (Fin (n + 1) → ℝ)`, let
`N_A(ω) := pathGeneration φ n (A.indicator 1) initial ω` and
`H_A := {ω | ∃ u, u.length = n ∧ surviveAlong ω [] u ∧
pathHistory φ n initial ω u ∈ A}`. The module proves
`N_A(ω) ≠ 0 ↔ ω ∈ H_A` and, for finite first and second moments,
`(𝔼[N_A])² / 𝔼[N_A²] ≤ ℙ(H_A)`. It also gives the many-to-one first-moment
bound when all terminal histories in `A` are bounded above.

The support-event moment inequality is the Paley--Zygmund inequality applied
to the nonnegative path count; the general probability inequality is due to
Paley and Zygmund, [*On some series of functions, (3)*, Lemma 19, p. 192
(1932)](https://doi.org/10.1017/S0305004100010860). Its corridor
specialization is used in the long-corridor argument of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5.

For a measurable path set `A`, let `N_A` be the number of surviving
generation-`n` addresses whose history belongs to `A`, and let `H_A` be the
event that at least one such address exists.  Then

\[
N_A(\omega)\ne0\quad\Longleftrightarrow\quad \omega\in H_A.
\]

If `m = ∫⁻ N_A d(offspringFieldLaw μ)` and
`∫⁻ N_A² d(offspringFieldLaw μ) ≤ s` for `0 < s < ∞`, the Paley--Zygmund
step yields

\[
\frac{m^2}{s}\le (\operatorname{offspringFieldLaw}\,\mu)(H_A).
\]

When every history in `A` ends at most at `b`, the many-to-one first-moment
estimate reads

\[
\int^- N_A\,d(\operatorname{offspringFieldLaw}\,\mu)
\le \operatorname{ENNReal.ofReal}(e^{b-x})
  (\operatorname{tiltedIncrementFieldLaw}\,\varphi\,\mu)
  \{z:\operatorname{ProbabilityTheory.RandomWalk.history}(n,x,z)\in A\}.
\]

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.pathGeneration_ne_zero_iff_hasPathHistoryIn`
  identifies the positive count event with existence of a surviving path.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_hasPathHistoryIn_ge_of_pathGeneration_moments`
  gives the lower bound `(𝔼[N_A])² / 𝔼[N_A²] ≤ ℙ(H_A)`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_le_exp_mul_spineProbability`
  bounds the expected path count by the endpoint exponential factor times the
  tilted-spine history probability.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- A corridor contains a surviving generation-`n` path exactly when the
unweighted corridor path count is nonzero. -/
theorem pathGeneration_ne_zero_iff_hasPathHistoryIn
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (initial : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (ω : StepField ℕ X) :
    Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ≠ 0 ↔
      ω ∈ hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
  classical
  constructor
  · intro hcount
    by_contra hpath
    have hterms (u : TreeNode ℕ) :
        Spine.pathGenerationTerm φ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 0 := by
      by_cases hu : u.length = n
      · by_cases hs : surviveAlong ω [] u
        · have hnot : Spine.pathHistory φ n initial ω u ∉ corridor := by
            intro hmem
            exact hpath ⟨u, hu, hs, hmem⟩
          simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hnot]
        · simp [Spine.pathGenerationTerm, hu, hs]
      · simp [Spine.pathGenerationTerm, hu]
    have hzero : Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω = 0 := by
      unfold Spine.pathGeneration
      rw [ENNReal.tsum_eq_zero]
      exact hterms
    exact hcount hzero
  · rintro ⟨u, hu, hs, hcorridor⟩
    have hterm : Spine.pathGenerationTerm φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 1 := by
      simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hcorridor]
    have hle : 1 ≤ Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω := by
      unfold Spine.pathGeneration
      calc
        1 = Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ℕ, Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω :=
          ENNReal.le_tsum (f := fun p => Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω) u
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)

/-- Paley--Zygmund converts first and second moment estimates for the
generation-`n` corridor path count into a lower bound on one-root tube
success. This is the probability step used in the long-corridor
estimate. -/
theorem measure_hasPathHistoryIn_ge_of_pathGeneration_moments
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂offspringFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂offspringFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤
      (offspringFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) := by
  let Xcount : StepField ℕ X → ℝ≥0∞ := fun ω =>
    Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
  have hX : Measurable Xcount := Spine.pathGeneration_measurable φ n
    (measurable_const.indicator hcorridor) initial
  have hPZ := measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    (offspringFieldLaw μ) Xcount hX mean second hmean hsecond
    hsecond_pos hsecond_top
  have hsupport : {ω : StepField ℕ X | Xcount ω ≠ 0} =
      hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
    ext ω
    exact pathGeneration_ne_zero_iff_hasPathHistoryIn
      φ n initial corridor ω
  simpa [Xcount, hsupport] using hPZ

/-- First-moment bound for the number of surviving particles whose complete
ancestral history lies in a measurable corridor. This is the form of the
many-to-one estimate used with Markov's inequality for a killed population. -/
theorem lintegral_pathGeneration_le_exp_mul_spineProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
      corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage
      (ProbabilityTheory.RandomWalk.history_measurable n initial)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hterminalPath (increment : ℕ → ℝ) (hevent : increment ∈ spineEvent) :
      AdditivePath.displacement n increment ≤ terminalUpper - initial := by
    have h := hterminal
      (ProbabilityTheory.RandomWalk.history n initial increment)
      (by simpa [spineEvent] using hevent)
    rw [ProbabilityTheory.RandomWalk.history_last,
      AdditivePath.fromIncrements_apply] at h
    linarith
  calc
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (ProbabilityTheory.RandomWalk.history n initial increment)
          ∂tiltedIncrementFieldLaw φ μ :=
      Spine.pathManyToOneCore φ μ hboundary n hF initial
    _ ≤ ∫⁻ increment,
          ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
          ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      change ENNReal.ofReal
          (Real.exp (AdditivePath.displacement n increment)) *
          F (ProbabilityTheory.RandomWalk.history n initial increment) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
          spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
      by_cases hevent : increment ∈ spineEvent
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor := by
          simpa [spineEvent] using hevent
        have hexp : ENNReal.ofReal
              (Real.exp (AdditivePath.displacement n increment)) ≤
            ENNReal.ofReal (Real.exp (terminalUpper - initial)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hterminalPath increment hevent))
        have hFval :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 1 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 1
          rw [Set.indicator_of_mem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        rw [hFval, hindicator]
        simpa using hexp
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∉
            corridor := by
          intro h
          exact hevent (by simpa [spineEvent] using h)
        have hFzero :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 0 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 0
          rw [Set.indicator_of_notMem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        rw [hFzero, hindicator]
        simp
    _ = ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [lintegral_const_mul _ (measurable_const.indicator hspineEvent)]
      rw [lintegral_indicator_const hspineEvent]
      simp


end ProbabilityTheory.BranchingRandomWalk.Spine

end
