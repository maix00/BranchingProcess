/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.Parameters
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_endpoint_deviation_parameters

example : ∃ b d c epsilon : ℝ,
    1 < b ∧ 0 < d ∧ d < 2 ∧
    0 < c ∧ c < 1 / 2 ∧ b + 1 + (-10) < b / c ∧
    0 < epsilon ∧ epsilon < b - 1 ∧
    epsilon < d * 1 / b ^ 2 - (1 + (-10)) := by
  exact ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_endpoint_deviation_parameters
    (a := 1) (t := 1) (C := 2) (zeta := -10) (by norm_num)
    (by norm_num) (by norm_num)
