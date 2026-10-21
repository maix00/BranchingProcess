/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic

/-!
# Corridor events in Mogul'skii's equation (34)

The public definitions are:

- `SourceBridgeCenter = \{x : ℝ \mid -1 < x < 1\}`: interior centers for
  finite bridge covers.
- `sourceBaseCorridorEvent scale n`: increments whose partial-sum path stays
  in the open centered tube of width `2 * scale` through time `n`.
- `sourceEndpointCorridorEvent scale ε c b n`: increments whose path stays in
  the widened open tube of width `2 * (1 + ε) * scale` and whose normalized
  terminal displacement lies in `Set.Ioc c b`.

These events are used in equation (34), Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The open interval of admissible centers for the finite source bridge
cover. -/
abbrev SourceBridgeCenter := {x : ℝ // -1 < x ∧ x < 1}

/-- The open centered corridor event used as the base event in Mogul'skii's
equation (34). -/
def sourceBaseCorridorEvent (scale : ℝ) (horizon : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * scale) horizon increment}

/-- The widened source corridor event with its `Set.Ioc` terminal endpoint
convention. -/
def sourceEndpointCorridorEvent (scale ε c b : ℝ) (horizon : ℕ) :
    Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * (1 + ε) * scale)
      horizon increment ∧
    AdditivePath.displacement horizon increment / scale ∈ Set.Ioc c b}

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
