/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.SecondMoment.TwoStage
import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import Probability.Distributions.Moments.Signs
import Probability.BranchingRandomWalk.Assumptions.Structural
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.MeasureTheory.Moments.PaleyZygmund

/-!
# A one-generation upper-tail bound from the offspring law

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistory` is the set
  of histories satisfying `lower + drift * k ≤ x k ≤ lower + drift * k + width`
  through time `n + 1`.
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorPrefix` imposes
  the same bounds through time `n`, and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorFirstWindow` is
  `{y | lower + drift ≤ y ∧ y ≤ lower + drift + width}`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistoryEndpointCutoff`
  is `affineCorridorHistory` intersected with the terminal constraint
  `x (n + 1) ≤ endpointUpper`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measurableSet_affineCorridorHistory`,
  `ProbabilityTheory.BranchingRandomWalk.Spine.measurableSet_affineCorridorPrefix`,
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.measurableSet_affineCorridorHistoryEndpointCutoff`
  establish measurability of these three history events.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistory_firstWindow`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistoryEndpointCutoff_firstWindow`
  place the first positive-time coordinate in the corresponding first window;
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistory_terminalUpper`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistoryEndpointCutoff_terminalUpper`
  give the terminal upper bounds.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeIncrement_mem_noLargeDropEndpointBelowEvent`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent`
  convert affine-tube constraints into the drawdown event
  `∀ i ≤ j ≤ n, S_i - S_j ≤ width`, with terminal bound
  `S_n ≤ width + drift * n`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown`
  bounds the tilted probability of the endpoint-cutoff corridor by the
  corresponding drawdown-and-endpoint probability.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildObservable_eq_manyToOne`
  identifies the conditional child-continuation integral with its
  many-to-one spine integral. The endpoint weight estimate
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildObservable_le_endpoint_weight`
  bounds it by the exponential terminal weight times the corridor probability.
* `ProbabilityTheory.BranchingRandomWalk.Spine.shiftedCorridorProbability_le_of_firstWindow`
  extends a first-window probability bound to all starting positions;
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight`
  give the corresponding child-moment bounds.
* `ProbabilityTheory.BranchingRandomWalk.Spine.ennreal_tsum_offDiagonal_mul_le_crossChildWeight_of_childMomentBound`
  bounds the ordered off-diagonal sum by the cross-child weight. Its fixed-root
  and integrated forms are
  `ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationChildMean_offDiagonal_le_crossChildWeight`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_succ_sq_le_diagonal_add_crossWeight`,
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight`,
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight_of_drawdown`
  give the one-generation second-moment recursion: the next second moment is
  bounded by the diagonal continuation term plus the cross-child term, with
  the latter controlled either by a corridor or drawdown probability bound.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_mul_distinct_child_subtrees_eq_product`
  factors the integral of two observables in distinct child subtrees as the
  product of their integrals.
* `ProbabilityTheory.BranchingRandomWalk.Spine.pathGeneration_ne_zero_iff_hasPathHistoryIn`
  identifies a nonzero corridor path count with existence of a path history in
  the corridor. The moment bound
  `ProbabilityTheory.BranchingRandomWalk.Spine.measure_hasPathHistoryIn_ge_of_pathGeneration_moments`
  converts its first and second moments into a one-root success lower bound.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment`
  gives the one-step lower bound `p^2 / (ENNReal.ofReal (exp (-a)) * p + C) ≤ μ{ξ |
  hasPotentialChildIn φ I ξ}`, where `p = tiltedPotentialLaw φ (-1) μ I` and
  `C = ∫⁻ ξ, crossChildWeight φ ξ ∂μ`, assuming `I` is measurable, bounded
  below by `a`, has positive tilted mass, and the cross-child moment is finite.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_noRootHasPotentialChildIn_eq_pow`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.measure_allRootsAvoidStepFieldEvent_eq_pow`
  express independent-root failure probabilities as `q^m`.
  `ProbabilityTheory.BranchingRandomWalk.Spine.measure_allRootsAvoidStepFieldEvent_le_exp`
  bounds them by `exp (-m * p)` when each root succeeds with probability at
  least `p`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_allRootsAvoidPathHistoryIn_le_exp`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.measure_allRootsAvoidPathHistoryIn_le_exp_of_pathGeneration_moments`
  give the exponential all-root failure estimate for corridor paths, the
  latter from first- and second-moment hypotheses.
  `ProbabilityTheory.BranchingRandomWalk.Spine.measure_noRootHasPotentialChildIn_le_secondMomentPower`
  gives the corresponding one-generation estimate from the offspring second
  moment.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_le_exp_mul_spineProbability`
  bounds the expected corridor path count by the endpoint exponential factor
  times the tilted-spine corridor probability.

The cross-child moment assumption gives a quantitative lower bound for a
one-step tube hit. Independent initial roots then give an upper bound for the
probability that no root produces such a child. This is a finite-horizon
consequence of the model assumptions; the longer corridor estimates used in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5,
are separate.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Histories that stay in a fixed-width affine corridor, including the
initial root coordinate. -/
def affineCorridorHistory (n : ℕ) (lower drift width : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | ∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
    history k ≤ lower + drift * (k.val : ℝ) + width}

/-- Histories through time `n` that stay in a fixed-width affine corridor.
Unlike `affineCorridorHistory`, this prefix has no extra terminal time. -/
def affineCorridorPrefix (n : ℕ) (lower drift width : ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {history | ∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
    history k ≤ lower + drift * (k.val : ℝ) + width}

/-- The corridor window at its first positive time coordinate. -/
def affineCorridorFirstWindow (lower drift width : ℝ) : Set ℝ :=
  {y | lower + drift ≤ y ∧ y ≤ lower + drift + width}

/-- The affine corridor in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 4, Lemma 4.5, with its terminal endpoint restricted by the
additional cutoff. -/
def affineCorridorHistoryEndpointCutoff (n : ℕ) (lower drift width endpointUpper : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | history ∈ affineCorridorHistory n lower drift width ∧
    history ⟨n + 1, by omega⟩ ≤ endpointUpper}

theorem measurableSet_affineCorridorHistory
    (n : ℕ) (lower drift width : ℝ) :
    MeasurableSet (affineCorridorHistory n lower drift width) := by
  rw [show affineCorridorHistory n lower drift width =
      ⋂ k : Fin (n + 2), {history | lower + drift * (k.val : ℝ) ≤ history k ∧
        history k ≤ lower + drift * (k.val : ℝ) + width} by
        ext history
        simp [affineCorridorHistory]]
  apply MeasurableSet.iInter
  intro k
  exact MeasurableSet.inter
    (measurableSet_le measurable_const (measurable_pi_apply k))
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem measurableSet_affineCorridorPrefix
    (n : ℕ) (lower drift width : ℝ) :
    MeasurableSet (affineCorridorPrefix n lower drift width) := by
  rw [show affineCorridorPrefix n lower drift width =
      ⋂ k : Fin (n + 1), {history | lower + drift * (k.val : ℝ) ≤ history k ∧
        history k ≤ lower + drift * (k.val : ℝ) + width} by
        ext history
        simp [affineCorridorPrefix]]
  apply MeasurableSet.iInter
  intro k
  exact MeasurableSet.inter
    (measurableSet_le measurable_const (measurable_pi_apply k))
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem affineCorridorHistory_firstWindow
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width := by
  have hcoord := h ⟨1, by omega⟩
  simpa [affineCorridorHistory, affineCorridorFirstWindow] using hcoord

theorem affineCorridorHistory_terminalUpper
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨n + 1, by omega⟩ ≤
      lower + drift * ((n + 1 : ℕ) : ℝ) + width := by
  have hcoord := (h ⟨n + 1, by omega⟩).2
  simpa [affineCorridorHistory] using hcoord

theorem measurableSet_affineCorridorHistoryEndpointCutoff
    (n : ℕ) (lower drift width endpointUpper : ℝ) :
    MeasurableSet
      (affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) := by
  rw [show affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper =
      affineCorridorHistory n lower drift width ∩
        {history | history ⟨n + 1, by omega⟩ ≤ endpointUpper} by
        ext history
        simp [affineCorridorHistoryEndpointCutoff]]
  exact (measurableSet_affineCorridorHistory n lower drift width).inter
    (measurableSet_le
      (measurable_pi_apply (⟨n + 1, by omega⟩ : Fin (n + 2)))
      measurable_const)

theorem affineCorridorHistoryEndpointCutoff_firstWindow
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width :=
  affineCorridorHistory_firstWindow n lower drift width history h.1

theorem affineCorridorHistoryEndpointCutoff_terminalUpper
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨n + 1, by omega⟩ ≤ endpointUpper := h.2

/-- On a nondecreasing affine tube, every earlier position is at most one
width above every later position. The terminal increment is bounded by the
width plus the total tube drift. This is the deterministic reduction used to
apply the drawdown estimate to one block in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.2. -/
theorem affineTubeIncrement_mem_noLargeDropEndpointBelowEvent
    (n : ℕ) (lower drift width start : ℝ) (hdrift : 0 ≤ drift)
    (increment : ℕ → ℝ)
    (htube : ∀ k : Fin (n + 1),
      lower + drift * (k.val : ℝ) ≤
          start + AdditivePath.displacement k.val increment ∧
        start + AdditivePath.displacement k.val increment ≤
          lower + drift * (k.val : ℝ) + width) :
    increment ∈
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ)) := by
  change (∀ i j : ℕ, i ≤ j → j ≤ n →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ width) ∧
    AdditivePath.displacement n increment ≤ width + drift * (n : ℝ)
  refine ⟨?_, ?_⟩
  · intro i j hij hj
    let i' : Fin (n + 1) := ⟨i, by omega⟩
    let j' : Fin (n + 1) := ⟨j, by omega⟩
    have hi := (htube i').2
    have hj' := (htube j').1
    have hpositions :
        AdditivePath.displacement i increment -
            AdditivePath.displacement j increment ≤
          width + drift * (i : ℝ) - drift * (j : ℝ) := by
      calc
        _ = (start + AdditivePath.displacement i increment) -
            (start + AdditivePath.displacement j increment) := by ring
        _ ≤ (lower + drift * (i : ℝ) + width) -
            (lower + drift * (j : ℝ)) := sub_le_sub hi hj'
        _ = _ := by ring
    have hijReal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hdriftMono : drift * (i : ℝ) ≤ drift * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hijReal hdrift
    linarith
  · have hstart : lower ≤ start := by
      simpa using (htube (⟨0, by omega⟩ : Fin (n + 1))).1
    have hend := (htube (⟨n, by omega⟩ : Fin (n + 1))).2
    have hdisp : AdditivePath.displacement n increment ≤
        width + drift * (n : ℝ) := by
      have hn : start + AdditivePath.displacement n increment ≤
          lower + drift * (n : ℝ) + width := by
        simpa using hend
      linarith
    exact hdisp

/-- A continuation below an affine history tube is itself a tube path whose
lower boundary starts one drift step later. -/
theorem affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent
    (n : ℕ) (x lower drift width y : ℝ) (hdrift : 0 ≤ drift)
    (increment : ℕ → ℝ)
    (htube : prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          affineCorridorHistory n lower drift width) :
    increment ∈
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ)) := by
  change (∀ k : Fin (n + 2),
      lower + drift * (k.val : ℝ) ≤
          prependHistory x
            (ProbabilityTheory.RandomWalk.history n (x + y) increment) k ∧
        prependHistory x
            (ProbabilityTheory.RandomWalk.history n (x + y) increment) k ≤
          lower + drift * (k.val : ℝ) + width) at htube
  apply affineTubeIncrement_mem_noLargeDropEndpointBelowEvent
    n (lower + drift) drift width (x + y) hdrift increment
  intro k
  have hcoord := htube k.succ
  have hcoord' :
      lower + drift * ((k.val : ℝ) + 1) ≤
          (x + y) + AdditivePath.displacement k.val increment ∧
        (x + y) + AdditivePath.displacement k.val increment ≤
          lower + drift * ((k.val : ℝ) + 1) + width := by
    simpa [Fin.val_succ, ProbabilityTheory.RandomWalk.history_eq_fromIncrements,
      AdditivePath.fromIncrements] using hcoord
  constructor
  · convert hcoord'.1 using 1 <;> ring
  · convert hcoord'.2 using 1 <;> ring

/-- The probability of a child continuation in an endpoint-truncated affine
corridor is bounded by the corresponding drawdown-and-endpoint probability.
The pathwise event inclusion transfers any available drawdown estimate to the
corridor probability used by the affine-tube second-moment recursion. -/
theorem tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (x lower drift width endpointUpper y : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    (tiltedIncrementFieldLaw φ μ)
      {increment | prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper} ≤ q := by
  apply le_trans (measure_mono ?_) hdrawdown
  intro increment hcutoff
  exact affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent
    n x lower drift width y hdrift increment hcutoff.1

/-- The conditional first moment of one child continuation is the spine
many-to-one integral, provided that child is present. -/
theorem lintegral_pathGenerationChildObservable_eq_manyToOne
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ) =
      survivingPotentialTest φ
        (fun y => ∫⁻ increment,
          ENNReal.ofReal (Real.exp
            (AdditivePath.displacement n increment)) *
            F (prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ) ξ i := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  have hmean (y : ℝ) :
      (∫⁻ η, Spine.pathGeneration φ n tailTest (x + y) η
        ∂stepFieldLaw μ) =
        ∫⁻ increment,
          ENNReal.ofReal (Real.exp
            (AdditivePath.displacement n increment)) *
            F (prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ := by
    simpa [tailTest] using
      (Spine.pathManyToOneCore φ μ hboundary n htailTest (x + y))
  classical
  by_cases hi : survive ξ i
  · simp [pathGenerationChildObservable, survivingPotentialTest,
      tailTest, hi, hmean]
  · simp [pathGenerationChildObservable, survivingPotentialTest, hi]

/-- The terminal cutoff in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 4, Lemma 4.5, bounds a child's continuation moment by the
exponential terminal weight times the corresponding spine corridor
probability. -/
theorem lintegral_pathGenerationChildObservable_le_endpoint_weight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
      survivingPotentialTest φ
        (fun y => ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                corridor}) ξ i := by
  classical
  rw [lintegral_pathGenerationChildObservable_eq_manyToOne
    φ μ hboundary n (corridor.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hcorridor) x i ξ]
  by_cases hi : survive ξ i
  · simp only [survivingPotentialTest, if_pos hi]
    let y : ℝ := ξ.potentialValue' φ i
    let E : Set (ℕ → ℝ) := {increment | prependHistory x
      (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈ corridor}
    have hE : MeasurableSet E :=
      hcorridor.preimage ((prependHistory_joint_measurable n).comp
        (measurable_const.prodMk
          (ProbabilityTheory.RandomWalk.history_measurable n (x + y))))
    have hterminalPath (increment : ℕ → ℝ) (hevent : increment ∈ E) :
        AdditivePath.displacement n increment ≤ terminalUpper - (x + y) := by
      have h := hterminal
        (prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment)) hevent
      have hindex :
          (⟨n + 1, by omega⟩ : Fin (n + 2)) =
            Fin.succ ⟨n, Nat.lt_succ_self n⟩ := by
        apply Fin.ext
        rfl
      rw [hindex, prependHistory_succ, ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements_apply] at h
      linarith
    have htailBound :
        (∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            (corridor.indicator fun _ => (1 : ℝ≥0∞))
              (prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment))
          ∂tiltedIncrementFieldLaw φ μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
          (tiltedIncrementFieldLaw φ μ) E := by
      calc
        _ ≤ ∫⁻ increment,
            ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
              E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            ∂tiltedIncrementFieldLaw φ μ := by
          apply lintegral_mono
          intro increment
          by_cases hevent : increment ∈ E
          · have hweight :
                ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) ≤
                  ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) :=
              ENNReal.ofReal_le_ofReal
                (Real.exp_le_exp.mpr (hterminalPath increment hevent))
            change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
                corridor.indicator (fun _ => (1 : ℝ≥0∞))
                  (prependHistory x
                    (ProbabilityTheory.RandomWalk.history n (x + y) increment)) ≤
              ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
                E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            have hcorridorMem : prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor := by
              simpa [E] using hevent
            simp only [Set.indicator_of_mem hcorridorMem,
              Set.indicator_of_mem hevent]
            simpa using hweight
          · have hcorridorNot :
                prependHistory x
                  (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∉
                    corridor := hevent
            change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
                corridor.indicator (fun _ => (1 : ℝ≥0∞))
                  (prependHistory x
                    (ProbabilityTheory.RandomWalk.history n (x + y) increment)) ≤
              ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
                E.indicator (fun _ => (1 : ℝ≥0∞)) increment
            simp only [Set.indicator_of_notMem hcorridorNot,
              Set.indicator_of_notMem hevent]
            simp
        _ = ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ) E := by
          rw [lintegral_const_mul _ (measurable_const.indicator hE)]
          rw [lintegral_indicator_const hE]
          simp
    simpa [y, E] using htailBound
  · simp [survivingPotentialTest, hi]

/-- A continuation corridor must contain the child's position at its first
time coordinate. Thus a probability bound only for starts in the first
window extends to all starts: outside the window the continuation event is
empty. -/
theorem shiftedCorridorProbability_le_of_firstWindow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (x : ℝ) (corridor : Set (Fin (n + 2) → ℝ))
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ y : ℝ,
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q := by
  intro y
  by_cases hy : x + y ∈ window
  · exact hprob y hy
  · have hempty : {increment | prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          corridor} = ∅ := by
      ext increment
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hmem
      have hwindow := hfirst _ hmem
      have hindex : (⟨1, by omega⟩ : Fin (n + 2)) =
          Fin.succ (⟨0, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hindex, prependHistory_succ] at hwindow
      have hwindow' : x + y ∈ window := by simpa using hwindow
      exact hy hwindow'
    rw [hempty]
    simp

/-- If every shifted spine corridor has probability at most `q`, the child
continuation mean is bounded by the endpoint factor, `q`, and the child's
realized exponential weight. This is the input for the cross-child part of
the MRCA estimate. -/
theorem lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (q : ℝ≥0∞)
    (hprob : ∀ y : ℝ,
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
          realizedPotentialWeight φ (-1) ξ i := by
  have hendpoint := lintegral_pathGenerationChildObservable_le_endpoint_weight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal i ξ
  by_cases hi : survive ξ i
  · let y : ℝ := ξ.potentialValue' φ i
    have hrealExp : Real.exp (terminalUpper - (x + y)) =
        Real.exp (terminalUpper - x) * Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfactor :
        ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) =
          ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (-y)) := by
      rw [hrealExp, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have hmean : survivingPotentialTest φ
        (fun z => ENNReal.ofReal (Real.exp (terminalUpper - (x + z))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | prependHistory x
              (ProbabilityTheory.RandomWalk.history n (x + z) increment) ∈
                corridor}) ξ i =
          ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor} := by
      simp [survivingPotentialTest, hi, y]
    calc
      _ ≤ survivingPotentialTest φ
          (fun z => ENNReal.ofReal (Real.exp (terminalUpper - (x + z))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + z) increment) ∈
                  corridor}) ξ i := hendpoint
      _ = ENNReal.ofReal (Real.exp (terminalUpper - (x + y))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | prependHistory x
                (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
                  corridor} := hmean
      _ ≤ ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (-y)) * q := by
          rw [hfactor]
          gcongr
          exact hprob y
      _ = ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
            realizedPotentialWeight φ (-1) ξ i := by
          simp [realizedPotentialWeight, hi, y]
          ac_rfl
  · simpa [survivingPotentialTest, realizedPotentialWeight, hi] using
      hendpoint

/-- The child moment estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.5, needs the uniform corridor
probability only for child positions that lie in the tube at the first time
step. -/
theorem lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
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
            corridor} ≤ q)
    (i : ℕ) (ξ : Step ℕ X) :
    (∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - x)) * q *
          realizedPotentialWeight φ (-1) ξ i := by
  exact lintegral_pathGenerationChildObservable_le_uniform_spineProbability_mul_weight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal q
    (shiftedCorridorProbability_le_of_firstWindow φ μ n x corridor window q
      hfirst hprob) i ξ

/-- If each child continuation mean is bounded by a common factor times its
realized exponential weight, then the ordered off-diagonal pair sum is
bounded by the cross-child weight. -/
theorem ennreal_tsum_offDiagonal_mul_le_crossChildWeight_of_childMomentBound
    {X : Type*} [MeasurableSpace X] [Countable ℕ]
    (φ : Potential X) (ξ : Step ℕ X) (K : ℝ≥0∞)
    (m : ℕ → ℝ≥0∞)
    (hm : ∀ i, m i ≤ K * realizedPotentialWeight φ (-1) ξ i) :
    (∑' i, ∑' j, if i ≠ j then m i * m j else 0) ≤
      K ^ 2 * crossChildWeight φ ξ := by
  classical
  have hzero (i : ℕ) (hi : ¬ survive ξ i) : m i = 0 := by
    apply le_antisymm
    · have h := hm i
      simpa [realizedPotentialWeight, hi] using h
    · exact bot_le
  have hpair (i j : ℕ) :
      (if i ≠ j then m i * m j else 0) ≤
        K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) := by
    by_cases hij : i ≠ j
    · by_cases hi : survive ξ i
      · by_cases hj : survive ξ j
        · have hweight :
              realizedPotentialWeight φ (-1) ξ i *
                  realizedPotentialWeight φ (-1) ξ j =
                ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
            rw [show realizedPotentialWeight φ (-1) ξ i =
                ENNReal.ofReal (Real.exp (-ξ.potentialValue' φ i)) by
                  simp [realizedPotentialWeight, hi],
              show realizedPotentialWeight φ (-1) ξ j =
                ENNReal.ofReal (Real.exp (-ξ.potentialValue' φ j)) by
                  simp [realizedPotentialWeight, hj]]
            have hexp : Real.exp (-ξ.potentialValue' φ i) *
                Real.exp (-ξ.potentialValue' φ j) =
              Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [← ENNReal.ofReal_mul
              (Real.exp_nonneg (-ξ.potentialValue' φ i)), hexp]
          have hproducts :
              m i * m j ≤
                (K * realizedPotentialWeight φ (-1) ξ i) *
                  (K * realizedPotentialWeight φ (-1) ξ j) :=
            mul_le_mul (hm i) (hm j) (by positivity) (by positivity)
          have hfactor :
              (K * realizedPotentialWeight φ (-1) ξ i) *
                  (K * realizedPotentialWeight φ (-1) ξ j) =
                K ^ 2 * ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
            calc
              _ = (K * K) *
                  (realizedPotentialWeight φ (-1) ξ i *
                    realizedPotentialWeight φ (-1) ξ j) := by ac_rfl
              _ = K ^ 2 * ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i +
                    ξ.potentialValue' φ j))) := by
                rw [pow_two, hweight]
          simpa [hij, hi, hj] using hproducts.trans_eq hfactor
        · simp [hij, hj, hzero j hj]
      · simp [hij, hi, hzero i hi]
    · simp [hij]
  have hinner (i : ℕ) :
      (∑' j, if i ≠ j then m i * m j else 0) ≤
        ∑' j, K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) :=
    ENNReal.tsum_le_tsum (fun j => hpair i j)
  calc
    (∑' i, ∑' j, if i ≠ j then m i * m j else 0) ≤
        ∑' i, ∑' j, K ^ 2 * (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
          else 0) := ENNReal.tsum_le_tsum hinner
    _ = K ^ 2 * crossChildWeight φ ξ := by
      let fLeft : ℕ → ℕ → ℝ≥0∞ := fun i j => by
        letI : Decidable (i = j) := instDecidableEqNat i j
        letI : Decidable (i ≠ j) := instDecidableNot
        letI : Decidable (survive ξ i) := Classical.propDecidable _
        letI : Decidable (survive ξ j) := Classical.propDecidable _
        exact if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
        else 0
      let fRight : ℕ → ℕ → ℝ≥0∞ := fun i j => by
        letI : Decidable (i = j) := Classical.propDecidable _
        letI : Decidable (i ≠ j) := instDecidableNot
        letI : Decidable (survive ξ i) := Classical.propDecidable _
        letI : Decidable (survive ξ j) := Classical.propDecidable _
        exact if i ≠ j ∧ survive ξ i ∧ survive ξ j then
          ENNReal.ofReal
            (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
        else 0
      have hsumLeft : (∑' i, ∑' j, K ^ 2 * fLeft i j) =
          K ^ 2 * (∑' i, ∑' j, fLeft i j) := by
        calc
          (∑' i, ∑' j, K ^ 2 * fLeft i j) =
              ∑' i, K ^ 2 * (∑' j, fLeft i j) := by
            apply tsum_congr
            intro i
            exact ENNReal.tsum_mul_left
          _ = K ^ 2 * (∑' i, ∑' j, fLeft i j) := ENNReal.tsum_mul_left
      have hpairEq : (∑' i, ∑' j, fLeft i j) =
          ∑' i, ∑' j, fRight i j := by
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        by_cases h : i ≠ j ∧ survive ξ i ∧ survive ξ j <;>
          simp [fLeft, fRight, h]
      have hcross : (∑' i, ∑' j, fRight i j) =
          crossChildWeight φ ξ := by
        unfold crossChildWeight
        rfl
      change (∑' i, ∑' j, K ^ 2 * fLeft i j) =
        K ^ 2 * crossChildWeight φ ξ
      calc
        _ = K ^ 2 * (∑' i, ∑' j, fLeft i j) := hsumLeft
        _ = K ^ 2 * (∑' i, ∑' j, fRight i j) := by rw [hpairEq]
        _ = K ^ 2 * crossChildWeight φ ξ := by rw [hcross]

/-- The root's ordered off-diagonal continuation terms are controlled by the
cross-child exponential weight once the shifted spine corridor probabilities
have a uniform bound. This is the fixed-ancestor estimate in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5. -/
theorem pathGenerationChildMean_offDiagonal_le_crossChildWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (ξ : Step ℕ X) :
    (∑' i, ∑' j, if i ≠ j then
      (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂stepFieldLaw μ) *
      (∫⁻ ζ, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
        ∂stepFieldLaw μ)
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossChildWeight φ ξ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (terminalUpper - x)) * q
  let m : ℕ → ℝ≥0∞ := fun i =>
    ∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂stepFieldLaw μ
  have hm (i : ℕ) : m i ≤ K * realizedPotentialWeight φ (-1) ξ i := by
    simpa [m, K] using
      lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob i ξ
  simpa [K, m] using
    ennreal_tsum_offDiagonal_mul_le_crossChildWeight_of_childMomentBound
      φ ξ K m hm

/-- Integrating the fixed-ancestor off-diagonal estimate over the root step
gives the expected cross-child contribution in the MRCA decomposition. -/
theorem lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    (∑' i, ∑' j, if i ≠ j then
      ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂stepFieldLaw μ) *
        (∫⁻ ζ, pathGenerationChildObservable φ n
          (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
          ∂stepFieldLaw μ) ∂μ
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator fun _ => (1 : ℝ≥0∞)
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [F] using pathGenerationChildObservable_measurable
      φ n (corridor.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hcorridor) x i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hoffInner (i : ℕ) :
      Measurable (fun ξ => ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ξ => ∑' i, ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ξ, ∑' j, offTerm i j ξ ∂μ) =
        ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ) =
        ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hoffInnerIntegral i
    · intro i
      exact (hoffInner i).aemeasurable
  have hoffTermIntegral (i j : ℕ) :
      (∫⁻ ξ, offTerm i j ξ ∂μ) =
        if i ≠ j then ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0 := by
    by_cases hij : i ≠ j
    · simp [offTerm, hij]
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hsum :
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) =
        ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := by
    calc
      _ = ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        rw [hoffTermIntegral]
      _ = ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := hoffIntegral.symm
  have hpointwise (ξ : Step ℕ X) :
      (∑' i, ∑' j, offTerm i j ξ) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossChildWeight φ ξ := by
    simpa [offTerm, childMean, F] using
      pathGenerationChildMean_offDiagonal_le_crossChildWeight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob ξ
  have hbound := calc
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) ≤
          ∫⁻ ξ, (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
            crossChildWeight φ ξ ∂μ := by
        rw [hsum]
        exact lintegral_mono hpointwise
      _ = (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
        rw [lintegral_const_mul _ (crossChildWeight_measurable φ)]
  simpa [F, childMean] using hbound

/-- One generation of the second-moment recursion, with the
off-diagonal MRCA contribution bounded by the cross-child exponential moment.
The diagonal term remains as the next recursive second moment. -/
theorem lintegral_pathGeneration_succ_sq_le_diagonal_add_crossWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x ω) ^ 2
      ∂stepFieldLaw μ) ≤
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator fun _ => (1 : ℝ≥0∞)
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hrec := lintegral_pathGeneration_succ_sq_eq_childPairRecursion
    φ μ n F hF x
  have hcross := lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal
    window q hfirst hprob
  calc
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
        ∂stepFieldLaw μ) =
        (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        ∑' i, ∑' j, if i ≠ j then
          ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
                ∂stepFieldLaw μ) *
            (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
                ∂stepFieldLaw μ) ∂μ else 0 := hrec
    _ ≤ (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
      apply add_le_add_right
      simpa [F] using hcross

/-- The first-generation second-moment recursion for the affine tube
with a terminal endpoint cutoff. A probability estimate for the uncut tube
also bounds its endpoint-restricted version by monotonicity. -/
theorem lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x lower drift width endpointUpper : ℝ)
    (q : ℝ≥0∞)
    (hprob : ∀ y : ℝ,
      x + y ∈ affineCorridorFirstWindow lower drift width →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            affineCorridorHistory n lower drift width} ≤ q) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
        fun _ => (1 : ℝ≥0∞)) x ω) ^ 2 ∂stepFieldLaw μ) ≤
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
            fun _ => (1 : ℝ≥0∞)) x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (endpointUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let window := affineCorridorFirstWindow lower drift width
  have hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window := by
    intro history hhistory
    exact affineCorridorHistoryEndpointCutoff_firstWindow
      n lower drift width endpointUpper history hhistory
  have hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ endpointUpper := by
    intro history hhistory
    exact affineCorridorHistoryEndpointCutoff_terminalUpper
      n lower drift width endpointUpper history hhistory
  have hprobCut : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q := by
    intro y hy
    apply le_trans (measure_mono ?_) (hprob y hy)
    intro increment hincrement
    exact hincrement.1
  exact lintegral_pathGeneration_succ_sq_le_diagonal_add_crossWeight
    φ μ hboundary n x endpointUpper corridor
    (measurableSet_affineCorridorHistoryEndpointCutoff
      n lower drift width endpointUpper)
    hterminal window q hfirst hprobCut

/-- The affine-tube second-moment recursion can consume a drawdown estimate
directly. The pathwise reduction supplies the shifted corridor probability
bound for every allowed child start. -/
theorem lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
        fun _ => (1 : ℝ≥0∞)) x ω) ^ 2 ∂stepFieldLaw μ) ≤
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
            fun _ => (1 : ℝ≥0∞)) x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        (ENNReal.ofReal (Real.exp (endpointUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let window := affineCorridorFirstWindow lower drift width
  have hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            affineCorridorHistory n lower drift width} ≤ q := by
    intro y hy
    apply le_trans (measure_mono ?_) hdrawdown
    intro increment hincrement
    exact affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent
      n x lower drift width y hdrift increment hincrement
  exact lintegral_pathGeneration_affineTube_succ_sq_le_diagonal_add_crossWeight
    φ μ hboundary n x lower drift width endpointUpper q hprob

/-- Integrals of products of observables in distinct child subtrees factor.
This is the analytic form of the off-diagonal branching property. -/
theorem lintegral_mul_distinct_child_subtrees_eq_product
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (f g : StepField ι X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
      ∂stepFieldLaw μ) =
      (∫⁻ ω, f ω ∂stepFieldLaw μ) * ∫⁻ ω, g ω ∂stepFieldLaw μ := by
  let pair : StepField ι X → StepField ι X × StepField ι X := fun ω =>
    (subtreeStepField [i] ω, subtreeStepField [j] ω)
  have hpair : Measurable pair :=
    (subtreeStepField_measurable [i]).prodMk
      (subtreeStepField_measurable [j])
  have hproduct : Measurable (fun p : StepField ι X × StepField ι X =>
      f p.1 * g p.2) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
        ∂stepFieldLaw μ) =
        ∫⁻ p, f p.1 * g p.2 ∂(stepFieldLaw μ).map pair := by
      exact (lintegral_map hproduct hpair).symm
    _ = (∫⁻ ω, f ω ∂stepFieldLaw μ) *
          ∫⁻ ω, g ω ∂stepFieldLaw μ := by
      rw [show pair = fun ω : StepField ι X =>
        (subtreeStepField [i] ω, subtreeStepField [j] ω) from rfl,
        distinct_child_subtreeFields_joint_law μ i j hij]
      exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable

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
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) := by
  let Xcount : StepField ℕ X → ℝ≥0∞ := fun ω =>
    Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
  have hX : Measurable Xcount := Spine.pathGeneration_measurable φ n
    (measurable_const.indicator hcorridor) initial
  have hPZ := measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    (stepFieldLaw μ) Xcount hX mean second hmean hsecond
    hsecond_pos hsecond_top
  have hsupport : {ω : StepField ℕ X | Xcount ω ≠ 0} =
      hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
    ext ω
    exact pathGeneration_ne_zero_iff_hasPathHistoryIn
      φ n initial corridor ω
  simpa [Xcount, hsupport] using hPZ

/-- Quantitative one-step Paley--Zygmund estimate for offspring entering a
bounded-below position window. -/
theorem measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I) :
    (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ≤
      μ {ξ | hasPotentialChildIn φ I ξ} := by
  let p : ℝ≥0∞ := tiltedPotentialLaw φ (-1) μ I
  let c : ℝ≥0∞ := ∫⁻ ξ, crossChildWeight φ ξ ∂μ
  let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a)) * p + c
  have htilted : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  have hp : 0 < p := hpositive
  have hp_top : p ≠ ∞ := measure_ne_top (tiltedPotentialLaw φ (-1) μ) I
  have hc_top : c ≠ ∞ := hcross
  have hcoef_pos : 0 < ENNReal.ofReal (Real.exp (-a)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hd_pos : 0 < d := by
    dsimp [d, p, c]
    exact lt_of_lt_of_le
      (ENNReal.mul_pos (ne_of_gt hcoef_pos) (ne_of_gt hpositive))
      (le_add_right le_rfl)
  have hd_top : d ≠ ∞ := by
    dsimp [d, p, c]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top, hc_top⟩
  have hq := tiltedWindowProbability_le_sqrt_success_mul_secondMoment
    φ I a hI hlower μ
  have hroot (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [pow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
      _ = x := by
        have hhalf : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [hhalf, ENNReal.rpow_one]
  have hmul :
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
        ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ)) =
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    calc
      _ = ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ)) *
          (d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ)) := by ac_rfl
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
        rw [hroot, hroot]
  have hsq : p ^ 2 ≤
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    have hsquare := mul_le_mul hq hq (by positivity) (by positivity)
    calc
      p ^ 2 = p * p := by rw [pow_two]
      _ ≤ (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
          ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            d ^ (1 / 2 : ℝ)) := by
          simpa [p, d, mul_assoc] using hsquare
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := hmul
  have hq : p ^ 2 / d ≤ μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl hd_pos.ne') (Or.inl hd_top)).2
    simpa [mul_comm] using hsq
  have hsuccess :
      μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} =
        μ {ξ | hasPotentialChildIn φ I ξ} := by
    congr 1
    ext ξ
    exact (weightedOffspringWindowMass_ne_zero_iff φ I ξ)
  simpa [p, d, hsuccess] using hq

/-- Under the finite-root product law, the probability that every initial root
fails to produce a child in `I` is the `m`th power of the one-root failure
probability. -/
theorem measure_noRootHasPotentialChildIn_eq_pow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ)
        {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])}) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  have hE : MeasurableSet E := by
    exact (measurableSet_hasPotentialChildIn φ I hI).preimage
      (measurable_pi_apply ([] : TreeNode ℕ))
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (stepFieldLaw μ) Eᶜ := by
    rw [← Measure.map_apply (measurable_pi_apply r) hE.compl]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have hfactor :=
    (finiteRootStepFieldLaw_roots_independent μ m).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun _ : Fin m => Eᶜ)
      (by intro r hr; exact hE.compl)
  have hset :
      (⋂ r ∈ Finset.univ,
          (fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} := by
    ext field
    simp [E]
  rw [hset] at hfactor
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hprod :
      (∏ r ∈ Finset.univ,
          (finiteRootStepFieldLaw μ m)
            ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  rw [hnot] at hfactor
  exact hfactor

/-- The independent initial roots all miss a measurable one-root event with
probability equal to the one-root failure probability raised to the number of
roots.  The event may inspect the entire pre-sampled descendant field of a
root, so this is the independence interface needed for multi-generation tube
success events as well as one-generation hits. -/
theorem measure_allRootsAvoidStepFieldEvent_eq_pow
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (stepFieldLaw μ) Eᶜ := by
    rw [← Measure.map_apply (measurable_pi_apply r) hE.compl]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have hfactor :=
    (finiteRootStepFieldLaw_roots_independent μ m).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun _ : Fin m => Eᶜ)
      (by intro r hr; exact hE.compl)
  have hset :
      (⋂ r ∈ Finset.univ,
        (fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        {field : FiniteRootStepField m ℕ X | ∀ r : Fin m, field r ∉ E} := by
    ext field
    simp
  rw [hset] at hfactor
  have hprod :
      (∏ r ∈ Finset.univ,
        (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  exact hfactor

/-- If one initial root has probability at least `p` of a measurable event
in its whole descendant field, then the chance that all `m` independent
roots miss the event is at most `exp (-m * p)`. -/
theorem measure_allRootsAvoidStepFieldEvent_le_exp
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ) E).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  let q : ℝ≥0∞ := (stepFieldLaw μ) E
  have hqtop : q ≠ ∞ := measure_ne_top _ _
  have hpq : ENNReal.ofReal p ≤ q := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal q.toReal :=
        ENNReal.ofReal_le_ofReal hprob
      _ = q := ENNReal.ofReal_toReal hqtop
  have hfailure :
      (stepFieldLaw μ) Eᶜ ≤ 1 - ENNReal.ofReal p := by
    have hcompl := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := ENNReal.ofReal p) (s := E)
      (by simpa [q] using hpq) hE
    exact hcompl
  have hbase :
      1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    simpa using (ENNReal.ofReal_sub 1 hp).symm
  have hexp : (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
    calc
      (1 - p) ^ m ≤ (Real.exp (-p)) ^ m :=
        pow_le_pow_left₀ (sub_nonneg.mpr hp_one) (Real.one_sub_le_exp_neg p) m
      _ = Real.exp (-(m : ℝ) * p) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hpow :
      (ENNReal.ofReal (1 - p)) ^ m ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
    calc
      (ENNReal.ofReal (1 - p)) ^ m = ENNReal.ofReal ((1 - p) ^ m) :=
        (ENNReal.ofReal_pow (sub_nonneg.mpr hp_one) m).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) :=
        ENNReal.ofReal_le_ofReal hexp
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m :=
        measure_allRootsAvoidStepFieldEvent_eq_pow μ E hE m
    _ ≤ (1 - ENNReal.ofReal p) ^ m :=
      pow_le_pow_left₀ (by positivity) hfailure m
    _ = (ENNReal.ofReal (1 - p)) ^ m := by rw [hbase]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := hpow

/-- Exponential extinction bound for independent roots when success means
that the root's branching field contains a surviving generation-`n` path in
a prescribed measurable history corridor. -/
theorem measure_allRootsAvoidPathHistoryIn_le_exp
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ)
      (hasPathHistoryIn (ι := ℕ) φ n initial corridor)).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  exact measure_allRootsAvoidStepFieldEvent_le_exp μ _
    (measurableSet_hasPathHistoryIn φ n initial corridor hcorridor)
    m p hp hp_one hprob

/-- Combining the path-count Paley--Zygmund bound with independent roots:
first and second moment estimates for one root give an exponential bound on
the probability that every initial root misses the corridor. -/
theorem measure_allRootsAvoidPathHistoryIn_le_exp_of_pathGeneration_moments
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp
        (-(m : ℝ) * (mean ^ 2 / second).toReal)) := by
  let E : Set (StepField ℕ X) :=
    hasPathHistoryIn (ι := ℕ) φ n initial corridor
  let q : ℝ≥0∞ := mean ^ 2 / second
  have hE : MeasurableSet E :=
    measurableSet_hasPathHistoryIn φ n initial corridor hcorridor
  have hsuccess : q ≤ (stepFieldLaw μ) E := by
    dsimp [q, E]
    exact measure_hasPathHistoryIn_ge_of_pathGeneration_moments
      φ μ n initial corridor hcorridor mean second hmean hsecond
      hsecond_pos hsecond_top
  have hqtop : q ≠ ∞ := ne_top_of_le_ne_top
    (measure_ne_top (stepFieldLaw μ) E) hsuccess
  have hqle : q ≤ 1 := by
    calc
      q ≤ (stepFieldLaw μ) E := hsuccess
      _ ≤ (stepFieldLaw μ) Set.univ := measure_mono (Set.subset_univ E)
      _ = 1 := measure_univ
  have hprob : q.toReal ≤ ((stepFieldLaw μ) E).toReal :=
    ENNReal.toReal_mono (measure_ne_top (stepFieldLaw μ) E) hsuccess
  have hp_one : q.toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hqtop ENNReal.one_ne_top).2 hqle
  have hroots := measure_allRootsAvoidStepFieldEvent_le_exp
    μ E hE m q.toReal ENNReal.toReal_nonneg hp_one hprob
  simpa [E, q] using hroots

/-- A one-generation upper bound for all-root failure.  Its one-root success
probability is bounded below from the actual offspring law by the
second-moment estimate. -/
theorem measure_noRootHasPotentialChildIn_le_secondMomentPower
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I)
    (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  let A : Set (Step ℕ X) := {ξ | hasPotentialChildIn φ I ξ}
  have hA : MeasurableSet A := measurableSet_hasPotentialChildIn φ I hI
  have hE : MeasurableSet E := by
    exact hA.preimage (measurable_pi_apply ([] : TreeNode ℕ))
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hmap : (stepFieldLaw μ) E = μ A := by
    rw [show E = (fun ω : StepField ℕ X => ω []) ⁻¹' A by rfl]
    rw [← Measure.map_apply (measurable_pi_apply ([] : TreeNode ℕ)) hA]
    rw [stepFieldLaw_coordinate μ []]
  have hhit := measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    φ I a hI hlower μ hboundary hcross hpositive
  have hprob :
      (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≤ μ A := by
    simpa [A] using hhit
  have hmiss :
      (stepFieldLaw μ) Eᶜ ≤
        1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
          (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
            ∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
    have hmiss' := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := μ A) (s := E)
      (by rw [hmap]) hE
    exact hmiss'.trans (tsub_le_tsub_left hprob 1)
  have hformula := measure_noRootHasPotentialChildIn_eq_pow φ I hI μ m
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
        rw [hformula]
        rw [← hnot]
    _ ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m :=
      pow_le_pow_left₀ (by positivity) hmiss m

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
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) ≤
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
