/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Spatial scales below a reference normalization

This deterministic predicate isolates the scale relation shared by Gaussian
and stable small-deviation theorems.  The reference normalization is supplied
by the relevant domain-of-attraction theorem; no stability exponent or
specific probability law belongs in this layer.
-/

public section

open Filter

namespace Asymptotics

/-- A spatial scale diverges but is asymptotically negligible compared with a
reference normalization. -/
def IsSmallDeviationScale (scale normalization : ℕ → ℝ) : Prop :=
  Tendsto scale atTop atTop ∧
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0)

namespace IsSmallDeviationScale

theorem tendsto_atTop {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    Tendsto scale atTop atTop := h.1

theorem tendsto_div {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2

theorem eventually_pos {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    ∀ᶠ n in atTop, 0 < scale n :=
  h.tendsto_atTop.eventually (eventually_gt_atTop 0)

end IsSmallDeviationScale

end Asymptotics
