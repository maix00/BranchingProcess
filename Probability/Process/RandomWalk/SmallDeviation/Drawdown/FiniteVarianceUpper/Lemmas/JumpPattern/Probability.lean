/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.Setup

/-!
# Conditional probability of a fixed jump pattern

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound`:
  if every non-jump block has conditional probability at most $p$, then the
  probability of the fixed-pattern tube intersection is at most the product
  of its factors $1$ on jumps and $p$ on non-jumps.

These are the conditional block steps in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of
Lemma 3.3, using its Lemma 3.2.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

lemma measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d tubeWidth₀ : ℝ}
    (hblockBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ length : ℕ, 1 ≤ length → ∀ start : ℕ,
      ∀ center : (Fin start → ℝ) → ℝ, Measurable center →
      ∀ᵐ increment ∂iidSequenceLaw ν,
        condExp
          (ProbabilityTheory.sequencePrefixFiltration (E := ℝ) start)
          (iidSequenceLaw ν)
          ((drawdownTubeBlockEvent start length center tubeWidth).indicator
            (fun _ => (1 : ℝ))) increment ≤
          Real.exp (tubeWidth ^ v - d * ((length : ℝ) / tubeWidth ^ 2)))
    (remainder q blockLength : ℕ) (hblockLength : 1 ≤ blockLength) :
    ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth : ℝ, ∀ pattern : Finset (Fin q),
        (iidSequenceLaw ν).real
          (ProbabilityTheory.conditionalBlockIntersection
            (drawdownJumpPatternTubeEvent remainder blockLength pattern
              upper binWidth tubeWidth) q) ≤
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
  intro tubeWidth htubeWidth upper binWidth pattern
  let filtration : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun n => ProbabilityTheory.sequencePrefixFiltration (E := ℝ)
      (remainder + n * blockLength)
  let events : ℕ → Set (ℕ → ℝ) :=
    drawdownJumpPatternTubeEvent remainder blockLength pattern
      upper binWidth tubeWidth
  let p := Real.exp (tubeWidth ^ v -
    d * ((blockLength : ℝ) / tubeWidth ^ 2))
  let bounds : ℕ → ℝ := fun n => drawdownJumpPatternBound pattern p n
  have hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1) := by
    intro n
    dsimp [filtration]
    apply (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).mono'
    have htime : remainder + n * blockLength + blockLength =
        remainder + (n + 1) * blockLength := by
      simp [Nat.add_mul, Nat.add_assoc]
    rw [← htime]
    exact Nat.le_add_right _ _
  have hfiltrationAmbient : ∀ n,
      filtration n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
    intro n
    exact (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).le'
      (remainder + n * blockLength)
  have heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n) := by
    intro n
    have htime : remainder + (n + 1) * blockLength =
        remainder + n * blockLength + blockLength := by
      simp [Nat.add_mul, Nat.add_assoc]
    change MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
      (E := ℝ) (remainder + (n + 1) * blockLength)]
      (drawdownJumpPatternTubeEvent remainder blockLength pattern
        upper binWidth tubeWidth n)
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · simp [drawdownJumpPatternTubeEvent, hn, hjump]
      · rw [htime]
        simpa [drawdownJumpPatternTubeEvent, hn, hjump] using
          measurableSet_drawdownTubeBlockEvent
          (remainder + n * blockLength) blockLength
          (drawdownPastDiscretizedMaximum
            (start := remainder + n * blockLength) upper binWidth)
          (measurable_drawdownPastDiscretizedMaximum upper binWidth) tubeWidth
    · simp [drawdownJumpPatternTubeEvent, hn]
  have hboundNonneg : ∀ n, 0 ≤ bounds n := by
    intro n
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · simp [bounds, drawdownJumpPatternBound, hn, hjump]
      · simp [bounds, drawdownJumpPatternBound, hn, hjump, p]
        positivity
    · simp [bounds, drawdownJumpPatternBound, hn]
  have hconditional : ∀ n, ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp (filtration n) (iidSequenceLaw ν)
        ((events n).indicator (fun _ => (1 : ℝ))) increment ≤ bounds n := by
    intro n
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · have hconst := condExp_const (μ := iidSequenceLaw ν)
          (hfiltrationAmbient n) (1 : ℝ)
        have hconstAE : ∀ᵐ increment ∂iidSequenceLaw ν,
            condExp (filtration n) (iidSequenceLaw ν)
              (fun _ => (1 : ℝ)) increment = 1 := by
          rw [hconst]
          exact Filter.Eventually.of_forall (fun _ => rfl)
        have hevent : events n = Set.univ := by
          simp [events, drawdownJumpPatternTubeEvent, hn, hjump]
        rw [hevent]
        filter_upwards [hconstAE] with increment hvalue
        simpa [bounds, drawdownJumpPatternBound, hn, hjump] using hvalue.le
      · filter_upwards
          [hblockBound tubeWidth htubeWidth blockLength hblockLength
            (remainder + n * blockLength)
            (drawdownPastDiscretizedMaximum
              (start := remainder + n * blockLength) upper binWidth)
            (measurable_drawdownPastDiscretizedMaximum upper binWidth)]
          with increment hbound
        simpa [events, bounds, p, drawdownJumpPatternTubeEvent,
          drawdownJumpPatternBound, hn, hjump, filtration] using hbound
    · have hconst := condExp_const (μ := iidSequenceLaw ν)
        (hfiltrationAmbient n) (1 : ℝ)
      have hconstAE : ∀ᵐ increment ∂iidSequenceLaw ν,
          condExp (filtration n) (iidSequenceLaw ν)
            (fun _ => (1 : ℝ)) increment = 1 := by
        rw [hconst]
        exact Filter.Eventually.of_forall (fun _ => rfl)
      have hevent : events n = Set.univ := by
        simp [events, drawdownJumpPatternTubeEvent, hn]
      rw [hevent]
      filter_upwards [hconstAE] with increment hvalue
      simpa [bounds, drawdownJumpPatternBound, hn] using hvalue.le
  have hconditionalOnPrefix : ∀ n, ∀ᵐ increment ∂iidSequenceLaw ν,
      increment ∈ ProbabilityTheory.conditionalBlockIntersection events n →
        condExp (filtration n) (iidSequenceLaw ν)
          ((events n).indicator (fun _ => (1 : ℝ))) increment ≤ bounds n := by
    intro n
    filter_upwards [hconditional n] with increment hbound
    intro _
    exact hbound
  exact ProbabilityTheory.measureReal_conditionalBlockIntersection_le_prod
    filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
    bounds hboundNonneg hconditionalOnPrefix q

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
