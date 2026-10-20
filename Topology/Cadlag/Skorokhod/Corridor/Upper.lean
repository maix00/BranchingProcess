/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Open upper corridors in Skorokhod path space

The public objects and theorems in this file are:

- `Skorokhod.rangeBelow`: the paths satisfying
  $\exists\varepsilon>0\;\forall t,\ f(t)\le b-\varepsilon$.
- `Skorokhod.isOpen_rangeBelow`: this upper corridor is open in $J_1$.
- `Skorokhod.rangeBelowEndsIn`: the same upper corridor with
  $f(1)\in(a,c)$.
- `Skorokhod.isOpen_rangeBelowEndsIn`: the combined event is open in $J_1$.

The one-sided form allows paths starting at zero, as required for the
Brownian meander corridor in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 3, Lemma 3.5 and Appendix A.2.
-/

@[expose] public section

open scoped ENNReal Topology

namespace Skorokhod

/-- Paths whose entire range lies uniformly below `upper`. -/
def rangeBelow (upper : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ margin > 0, ∀ t, path t ≤ upper - margin}

/-- An upper corridor with a positive margin is open for the Skorokhod
`J₁` topology. Time changes preserve the range of a path. -/
theorem isOpen_rangeBelow (upper : ℝ) : IsOpen (rangeBelow upper) := by
  rw [isOpen_iff_forall_mem_open]
  intro path hpath
  obtain ⟨margin, hmargin, hpath⟩ := hpath
  refine ⟨Metric.ball path (margin / 2), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hmargin)⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal (margin / 2) := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff (half_pos hmargin)]
    simpa [dist_comm] using hother
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act path) other <
      ENNReal.ofReal (margin / 2) :=
    (le_max_right _ _).trans_lt hchange
  refine ⟨margin / 2, half_pos hmargin, fun t => ?_⟩
  have ht := (edist_apply_le_uniformEDist (change.act path) other t).trans_lt
    huniform
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (half_pos hmargin)] at ht
  have hp := hpath (change t)
  rw [Real.dist_eq, abs_lt] at ht
  change -(margin / 2) < path (change t) - other t ∧
    path (change t) - other t < margin / 2 at ht
  linarith

/-- An upper corridor with an open terminal interval. -/
def rangeBelowEndsIn (upper endpointLower endpointUpper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  rangeBelow upper ∩
    (fun path : CadlagPath unitInterval ℝ => path ⊤) ⁻¹'
      Set.Ioo endpointLower endpointUpper

/-- The upper corridor and terminal window form an open path event. -/
theorem isOpen_rangeBelowEndsIn (upper endpointLower endpointUpper : ℝ) :
    IsOpen (rangeBelowEndsIn upper endpointLower endpointUpper) :=
  (isOpen_rangeBelow upper).inter
    (isOpen_Ioo.preimage continuous_apply_top)

end Skorokhod

end
