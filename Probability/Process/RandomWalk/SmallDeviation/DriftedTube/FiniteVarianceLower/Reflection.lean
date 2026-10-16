/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointEvent
public import Probability.Sequence.IID.Basic

/-!
# Reflection of the tilted-tube endpoint event

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeUpperEndpointWindowEvent`:
  a tube of width $\Delta$ with
  its terminal window $[s_L-v\Delta,s_L]$ adjacent to the upper edge.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.mem_driftedTubeUpperEndpointWindowEvent_iff_reflected`:
  reflecting every increment sends this event to the lower-endpoint
  event with lower edge $-r_0-\Delta$ and drift $-c$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measure_driftedTubeUpperEndpointWindowEvent_eq_reflected`:
  $\mathbb P_\nu(E_{\mathrm{upper}}(c,r_0))$
  equals $\mathbb P_{-\nu}(E_{\mathrm{lower}}(-c,-r_0-\Delta))$.

This is the deterministic reflection in the symmetric construction of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- A tilted tube with its terminal window adjacent to the upper edge. -/
def driftedTubeUpperEndpointWindowEvent
    (horizon : ℕ) (width drift base endpointFraction : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | (∀ j : ℕ, 1 ≤ j → j ≤ horizon →
      base + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        base + drift * (j : ℝ) / width ^ 2 + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2 + width -
          endpointFraction * width)
        (base + drift * (horizon : ℝ) / width ^ 2 + width)}

/-- Reflecting all increments exchanges the upper endpoint window with a
lower endpoint window and reverses the drift. -/
theorem mem_driftedTubeUpperEndpointWindowEvent_iff_reflected
    (horizon : ℕ) (width drift base endpointFraction : ℝ)
    (increment : ℕ → ℝ) :
    increment ∈ driftedTubeUpperEndpointWindowEvent
        horizon width drift base endpointFraction ↔
      (fun j => -increment j) ∈ driftedTubeEndpointWindowEvent
        horizon width (-drift) (-base - width) endpointFraction := by
  change ((∀ j : ℕ, 1 ≤ j → j ≤ horizon →
      base + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        base + drift * (j : ℝ) / width ^ 2 + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2 + width -
          endpointFraction * width)
        (base + drift * (horizon : ℝ) / width ^ 2 + width)) ↔ _
  constructor
  · rintro ⟨hpath, hend⟩
    constructor
    · intro j hj hL
      obtain ⟨hl, hu⟩ := hpath j hj hL
      rw [AdditivePath.displacement_neg]
      constructor
      · convert neg_le_neg hu using 1; ring
      · convert neg_le_neg hl using 1; ring
    · rw [AdditivePath.displacement_neg]
      constructor
      · convert neg_le_neg hend.2 using 1; ring
      · convert neg_le_neg hend.1 using 1; ring
  · rintro ⟨hpath, hend⟩
    constructor
    · intro j hj hL
      obtain ⟨hl, hu⟩ := hpath j hj hL
      rw [AdditivePath.displacement_neg] at hl hu
      constructor
      · convert neg_le_neg hu using 1 <;> ring
      · convert neg_le_neg hl using 1 <;> ring
    · rw [AdditivePath.displacement_neg] at hend
      constructor
      · convert neg_le_neg hend.2 using 1 <;> ring
      · convert neg_le_neg hend.1 using 1 <;> ring

/-- The lower-endpoint tilted-tube event is measurable. -/
private lemma measurableSet_driftedTubeEndpointWindowEvent
    (horizon : ℕ) (width drift base endpointFraction : ℝ) :
    MeasurableSet (driftedTubeEndpointWindowEvent
      horizon width drift base endpointFraction) := by
  have hpath : MeasurableSet
      {increment : ℕ → ℝ | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
        base + drift * (j : ℝ) / width ^ 2 ≤
          AdditivePath.displacement j increment ∧
        AdditivePath.displacement j increment ≤
          base + drift * (j : ℝ) / width ^ 2 + width} := by
    rw [show {increment : ℕ → ℝ | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
          base + drift * (j : ℝ) / width ^ 2 ≤
            AdditivePath.displacement j increment ∧
          AdditivePath.displacement j increment ≤
            base + drift * (j : ℝ) / width ^ 2 + width} =
        ⋂ j : ℕ, {increment : ℕ → ℝ | 1 ≤ j → j ≤ horizon →
          AdditivePath.displacement j increment ∈
            Set.Icc (base + drift * (j : ℝ) / width ^ 2)
              (base + drift * (j : ℝ) / width ^ 2 + width)} by
      ext increment
      simp [Set.mem_Icc]]
    apply MeasurableSet.iInter
    intro j
    by_cases hfirst : 1 ≤ j
    · by_cases hlast : j ≤ horizon
      · have hcoord : Measurable (fun increment : ℕ → ℝ =>
            AdditivePath.displacement j increment) :=
          RandomWalk.displacement_measurable j
        have hIcc : MeasurableSet
            (Set.Icc (base + drift * (j : ℝ) / width ^ 2)
              (base + drift * (j : ℝ) / width ^ 2 + width)) :=
          measurableSet_Icc
        convert (hIcc.preimage hcoord) using 1
        ext increment
        simp [hfirst, hlast, Set.mem_Icc]
      · simp [hfirst, hlast]
    · simp [hfirst]
  have hend : MeasurableSet
      {increment : ℕ → ℝ |
        AdditivePath.displacement horizon increment ∈
          Set.Icc (base + drift * (horizon : ℝ) / width ^ 2)
            (base + drift * (horizon : ℝ) / width ^ 2 +
              endpointFraction * width)} :=
    measurableSet_Icc.preimage
      (RandomWalk.displacement_measurable (E := ℝ) horizon)
  exact hpath.inter hend

/-- Reflection transfers the upper-endpoint probability to the
lower-endpoint probability for the reflected increment law. -/
theorem measure_driftedTubeUpperEndpointWindowEvent_eq_reflected
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
    (horizon : ℕ) (width drift base endpointFraction : ℝ) :
    ProbabilityTheory.iidSequenceLaw ν
        (driftedTubeUpperEndpointWindowEvent
          horizon width drift base endpointFraction) =
      ProbabilityTheory.iidSequenceLaw
        (ν.map fun x : ℝ => -x)
        (driftedTubeEndpointWindowEvent
          horizon width (-drift) (-base - width) endpointFraction) := by
  let reflect : (ℕ → ℝ) → ℕ → ℝ := fun increment j => -increment j
  have hreflect : Measurable reflect :=
    Measurable.of_eval fun j => (measurable_pi_apply j).neg
  have hevent := measurableSet_driftedTubeEndpointWindowEvent
    horizon width (-drift) (-base - width) endpointFraction
  calc
    _ = (ProbabilityTheory.iidSequenceLaw ν)
        (reflect ⁻¹' driftedTubeEndpointWindowEvent
          horizon width (-drift) (-base - width) endpointFraction) := by
      congr 1
      ext increment
      exact mem_driftedTubeUpperEndpointWindowEvent_iff_reflected
        horizon width drift base endpointFraction increment
    _ = ((ProbabilityTheory.iidSequenceLaw ν).map reflect)
        (driftedTubeEndpointWindowEvent
          horizon width (-drift) (-base - width) endpointFraction) :=
      (MeasureTheory.Measure.map_apply hreflect hevent).symm
    _ = _ := by
      rw [ProbabilityTheory.iidSequenceLaw_map_coordinatewise
        ν (fun x : ℝ => -x) measurable_neg]

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
