/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Oscillation

example {T E : Type*} [LinearOrder T]
    [PseudoMetricSpace T] [PseudoMetricSpace E] {f : T → E}
    (hf : IsCadlag f) (t : T) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ radius > 0, ∀ s u, s < t → u < t → dist s t < radius →
      dist u t < radius → dist (f s) (f u) ≤ epsilon :=
  hf.exists_left_oscillation_radius t hepsilon

example {T E : Type*} [LinearOrder T]
    [PseudoMetricSpace T] [PseudoMetricSpace E] {f : T → E}
    (hf : IsCadlag f) (t : T) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ radius > 0, ∀ s u, t ≤ s → t ≤ u → dist s t < radius →
      dist u t < radius → dist (f s) (f u) ≤ epsilon :=
  hf.exists_right_oscillation_radius t hepsilon

#print axioms IsCadlag.exists_left_oscillation_radius
#print axioms IsCadlag.exists_right_oscillation_radius
