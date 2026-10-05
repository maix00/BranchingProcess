/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Local oscillation bounds for càdlàg functions

Right continuity and the existence of left limits give separate local
oscillation bounds on the two sides of every time. These are the local inputs
for finite oscillation partitions.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {T E : Type*} [LinearOrder T]
  [PseudoMetricSpace T] [PseudoMetricSpace E]
  {f : T → E}

/-- A càdlàg function has arbitrarily small oscillation on a sufficiently
short interval immediately to the left of any time. -/
theorem IsCadlag.exists_left_oscillation_radius
    (hf : IsCadlag f) (t : T) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ radius > 0, ∀ s u, s < t → u < t → dist s t < radius →
      dist u t < radius → dist (f s) (f u) ≤ epsilon := by
  obtain ⟨leftLimit, hleftLimit⟩ := hf.tendsto_nhdsLT t
  have heventually : ∀ᶠ x in 𝓝[<] t,
      f x ∈ Metric.ball leftLimit (epsilon / 2) :=
    hleftLimit.eventually (Metric.ball_mem_nhds leftLimit (by positivity))
  change {x | f x ∈ Metric.ball leftLimit (epsilon / 2)} ∈ 𝓝[<] t at heventually
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at heventually
  obtain ⟨u, hu, hsubset⟩ := heventually
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨radius, hradius, ?_⟩
  intro s v hs hv hsr hvr
  have hfs : f s ∈ Metric.ball leftLimit (epsilon / 2) := by
    apply hsubset
    exact ⟨hball (Metric.mem_ball.mpr hsr), hs⟩
  have hfv : f v ∈ Metric.ball leftLimit (epsilon / 2) := by
    apply hsubset
    exact ⟨hball (Metric.mem_ball.mpr hvr), hv⟩
  apply le_of_lt
  calc
    dist (f s) (f v) ≤ dist (f s) leftLimit + dist leftLimit (f v) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := by
      exact add_lt_add (Metric.mem_ball.mp hfs)
        (by simpa [dist_comm] using Metric.mem_ball.mp hfv)
    _ = epsilon := by ring

/-- A càdlàg function has arbitrarily small oscillation on a sufficiently
short interval immediately to the right of any time, including the value at
the left endpoint. -/
theorem IsCadlag.exists_right_oscillation_radius
    (hf : IsCadlag f) (t : T) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ radius > 0, ∀ s u, t ≤ s → t ≤ u → dist s t < radius →
      dist u t < radius → dist (f s) (f u) ≤ epsilon := by
  have hright : ContinuousWithinAt f (Ioi t) t := hf.isRightContinuous t
  have heventually : ∀ᶠ x in 𝓝[>] t,
      f x ∈ Metric.ball (f t) (epsilon / 2) :=
    hright.eventually (Metric.ball_mem_nhds (f t) (by positivity))
  change {x | f x ∈ Metric.ball (f t) (epsilon / 2)} ∈ 𝓝[>] t at heventually
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at heventually
  obtain ⟨u, hu, hsubset⟩ := heventually
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨radius, hradius, ?_⟩
  intro s v hts htv hsr hvr
  have hfs : dist (f s) (f t) < epsilon / 2 := by
    by_cases hs : s = t
    · simp [hs, hepsilon]
    · have hst : t < s := lt_of_le_of_ne hts (Ne.symm hs)
      have hmem : f s ∈ Metric.ball (f t) (epsilon / 2) := by
        apply hsubset
        exact ⟨hball (Metric.mem_ball.mpr hsr), hst⟩
      exact Metric.mem_ball.mp hmem
  have hfv : dist (f v) (f t) < epsilon / 2 := by
    by_cases hv : v = t
    · simp [hv, hepsilon]
    · have hvt : t < v := lt_of_le_of_ne htv (Ne.symm hv)
      have hmem : f v ∈ Metric.ball (f t) (epsilon / 2) := by
        apply hsubset
        exact ⟨hball (Metric.mem_ball.mpr hvr), hvt⟩
      exact Metric.mem_ball.mp hmem
  apply le_of_lt
  calc
    dist (f s) (f v) ≤ dist (f s) (f t) + dist (f t) (f v) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := by
      exact add_lt_add hfs (by simpa [dist_comm] using hfv)
    _ = epsilon := by ring

end
