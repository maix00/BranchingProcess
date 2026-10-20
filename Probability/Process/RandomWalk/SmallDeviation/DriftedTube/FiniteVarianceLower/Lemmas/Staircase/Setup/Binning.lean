/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Binning parameters in the Lemma 3.5 proof

The definitions used by the internal staircase proof are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinLower`:
  the lower edge $b_l=-2/3+l/(3m)$ of bin $l$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinUpper`:
  the upper edge $b_{l+1}=b_l+1/(3m)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinWidth`:
  the common width factor $\beta_m=1-1/(3m)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinTubeParameter`:
  the translated tube parameter $a_l=-b_{l+1}/\beta_m$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinEndpointLowerFraction` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinEndpointUpperFraction`:
  the terminal interval fractions $v_1/\beta_m$ and
  $(v_2-1/(3m))/\beta_m$.

These parameters encode the finite spatial bins in the proof of Lemma 3.5,
Chapter 3 of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring*.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lower endpoint of one spatial bin in the staircase. -/
noncomputable def staircaseBinLower (m l : ℕ) : ℝ :=
  -(2 : ℝ) / 3 + (l : ℝ) / (3 * (m : ℝ))

/-- The upper endpoint of one spatial bin in the staircase. -/
noncomputable def staircaseBinUpper (m l : ℕ) : ℝ :=
  staircaseBinLower m l + 1 / (3 * (m : ℝ))

/-- The common width factor of the narrowed tube for each bin. -/
noncomputable def staircaseBinWidth (m : ℕ) : ℝ :=
  1 - 1 / (3 * (m : ℝ))

/-- The translated tube parameter whose lower edge is the bin's upper edge. -/
noncomputable def staircaseBinTubeParameter (m l : ℕ) : ℝ :=
  -staircaseBinUpper m l / staircaseBinWidth m

/-- Lower endpoint fraction of the common terminal interval. -/
noncomputable def staircaseBinEndpointLowerFraction (m : ℕ) (v₁ : ℝ) : ℝ :=
  v₁ / staircaseBinWidth m

/-- Upper endpoint fraction of the common terminal interval. -/
noncomputable def staircaseBinEndpointUpperFraction (m : ℕ) (v₂ : ℝ) : ℝ :=
  (v₂ - 1 / (3 * (m : ℝ))) / staircaseBinWidth m

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
