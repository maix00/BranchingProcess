/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.Process.RandomWalk.Path.Restart.Basic

/-!
# Restarted second-stage tube events for killed capacity

The public declarations in namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveASecondStageWindow ell ellN κ c v j`: with
  $D=\ell_N-\ell$, $w=D^{1/3}$, and
  $d_j=(\kappa/c^2)D^{-2/3}j$, the window is $\{0\}$ at $j=0$,
  $[d_j,d_j+cw]$ for $0<j<D$, $[d_D,d_D+vw]$ when $0<j=D$, and empty
  after the terminal generation.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveASecondStageTubeEvent ell ellN κ c v` is the set of paths
  whose displacement at every $j\in[0,D]$ lies in the corresponding window.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v` imposes the
  same window condition for every $j\in[0,d]$.

These event constructions encode the restarted tube in the proof of the
positive-initial-mass estimate, Proposition 3.1, equation (4.15), of Elie
Aïdékon and Yueyun Hu, *Average-weight percolation on the complete graph*,
arXiv:2512.23266 (2025). The inclusions and probability comparisons used to
assemble the estimate remain in `Lemmas/Tube.lean`.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-- The relative-generation interval used for the restarted second-stage
tube in Proposition 3.1, equation (4.15), of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageWindow
    (ell ellN : ℕ) (κ c v : ℝ) (j : ℕ) : Set ℝ :=
  let D := ellN - ell
  let width := ((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ)
  if j = 0 then Set.Icc 0 0
  else if j < D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + c * width)
  else if j = D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + v * width)
  else ∅

/-- Paths whose displacement at each time through the restart horizon belongs
to the corresponding second-stage window in Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageTubeEvent
    (ell ellN : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (ellN - ell + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

/-- Paths whose displacement satisfies the second-stage window conditions
through a specified prefix. This event is used in the prefix comparison for
Proposition 3.1, equation (4.15), of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageTubePrefixEvent
    (ell ellN d : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (d + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
