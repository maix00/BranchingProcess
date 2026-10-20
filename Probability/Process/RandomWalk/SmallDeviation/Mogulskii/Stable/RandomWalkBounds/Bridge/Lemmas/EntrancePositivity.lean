/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.AllIndices

/-! # Stable bridge entrance positivity

The public lemma is `sourceBridgeEntrance_pos_of_cdfAtZero_allIndices`. For
a stable Lévy process with $0<\mathbb P(X_1\le 0)<1$, positive radius $r$,
and centers $x,y\in(-1,1)$, it proves

$$
\mathbb P\!\left(\begin{array}{l}
 -1-x<X_t<1-x\quad(0\le t\le1),\\
 y-x-r<X_1<y-x+r
\end{array}\right)>0.
$$

This is the shifted unit-time entrance estimate used for the finite bridge
cells in Mogul'skii's equation (34), Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The source bridge event at any interior center has positive stable-law
mass under the source CDF sign condition. This specializes the all-index
entrance theorem to the shifted corridor used by the finite bridge cells. -/
lemma sourceBridgeEntrance_pos_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (radius x y : ℝ) (hradius : 0 < radius)
    (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) :
    0 < Q (fullSegmentCorridorReturnEvent X 0 1
      (-1 - x) (1 - x) (y - x - radius) (y - x + radius)) := by
  convert hX.measure_fullEntrance_pos_of_cdfAtZero_allIndices hcdf
    (-y) (-x) radius
    (by constructor <;> linarith [hy.1, hy.2])
    (by constructor <;> linarith [hx.1, hx.2]) hradius using 1; ring_nf

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
