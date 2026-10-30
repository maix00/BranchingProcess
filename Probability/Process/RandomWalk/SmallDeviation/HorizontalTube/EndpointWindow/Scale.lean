/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
public import Probability.Sequence.IID.Basic

/-!
# Scaling finite endpoint-window probabilities

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.iidSequenceLaw_endpointWindowBlockEvent_scale`:
  for positive `scale`, the probability of the correspondingly widened open
  tube and normalized endpoint window equals the probability of the unscaled
  endpoint-window event under the coordinatewise scaled increment law.
-/

open MeasureTheory ProbabilityTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

/-- Scaling every increment coordinate identifies a widened tube with a
normalized endpoint window under the scaled increment law. -/
theorem iidSequenceLaw_endpointWindowBlockEvent_scale
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n length : ℕ) (hscale : 0 < scale n)
    (radius spacing windowRadius : ℝ) (i : ℤ) :
    iidSequenceLaw ν {increment |
      InOpenHorizontalTube (1 / 2) (2 * radius * scale n) length increment ∧
        AdditivePath.displacement length increment / scale n ∈
          Set.Ioo ((i : ℝ) * spacing - windowRadius)
            ((i : ℝ) * spacing + windowRadius)} =
      iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointWindowBlockEvent radius spacing windowRadius i length) := by
  let normalize : (ℕ → ℝ) → (ℕ → ℝ) := fun sequence k => sequence k / scale n
  have hwidth : (2 * radius * scale n) / scale n = 2 * radius := by
    field_simp [hscale.ne']
  have hsum (sequence : ℕ → ℝ) :
      AdditivePath.displacement length (normalize sequence) =
        AdditivePath.displacement length sequence / scale n := by
    simp [normalize, AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  have hset :
      {increment | InOpenHorizontalTube (1 / 2)
          (2 * radius * scale n) length increment ∧
        AdditivePath.displacement length increment / scale n ∈
          Set.Ioo ((i : ℝ) * spacing - windowRadius)
            ((i : ℝ) * spacing + windowRadius)} =
        normalize ⁻¹' endpointWindowBlockEvent radius spacing windowRadius i length := by
    ext increment
    change (InOpenHorizontalTube (1 / 2) (2 * radius * scale n)
        length increment ∧
      AdditivePath.displacement length increment / scale n ∈
        Set.Ioo ((i : ℝ) * spacing - windowRadius)
          ((i : ℝ) * spacing + windowRadius)) ↔
      InOpenHorizontalTube (1 / 2) (2 * radius) length (normalize increment) ∧
        AdditivePath.displacement length (normalize increment) ∈
          Set.Ioo ((i : ℝ) * spacing - windowRadius)
            ((i : ℝ) * spacing + windowRadius)
    have htube := inOpenHorizontalTube_div_iff (1 / 2)
      (2 * radius * scale n) length increment hscale
    rw [hwidth] at htube
    constructor
    · rintro ⟨htube', hend⟩
      exact ⟨htube.mpr htube', by simpa [hsum] using hend⟩
    · rintro ⟨htube', hend⟩
      exact ⟨htube.mp htube', by simpa [hsum] using hend⟩
  have hnormalize : Measurable normalize :=
    Measurable.of_eval fun k =>
      (measurable_id.div_const (scale n)).comp (measurable_pi_apply k)
  rw [← iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => x / scale n) (measurable_id.div_const (scale n)),
    Measure.map_apply hnormalize
      (measurableSet_endpointWindowBlockEvent radius spacing windowRadius i length), hset]

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

end
