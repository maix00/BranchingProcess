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

## Public declarations

- `sourceBaseCorridorEvent scale n`: increments whose partial-sum path stays
  in the open centered tube of width `2 * scale` through time `n`.
- `sourceEndpointCorridorEvent scale ε c b n`: increments whose path stays in
  the widened open tube of width `2 * (1 + ε) * scale` and whose normalized
  terminal displacement lies in `Set.Ioc c b`.

Writing $S_j=\sum_{k<j}\xi_k$, these events are
\[
 B_n=\{\xi:|S_j|<s\ (1\leq j\leq n)\},\qquad
 E_n=\left\{\xi:|S_j|<(1+\varepsilon)s\ (1\leq j\leq n),\quad
             \frac{S_n}{s}\in(c,b]\right\},
\]
where $s=\texttt{scale}$. The second event uses the source's endpoint
convention $\mathrm{Set.Ioc}(c,b)=(c,b]$.

These events are used in equation (34), Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

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
