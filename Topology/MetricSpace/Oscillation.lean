/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Pairwise oscillation bounds for metric-valued functions

## Public declarations

- `Metric.OscillationBounded f C` means
  `dist (f s) (f t) ≤ C` for every pair of indices `s` and `t`.
- `.mono` enlarges the allowed bound, and `.symm` reverses the two indices.
- `.ediam_range_le` and `.of_ediam_range_le` identify the pairwise bound with
  Mathlib's extended diameter bound on `Set.range f` when `0 ≤ C`.

The function-level predicate is the direct pointwise form of a range-diameter
bound. Mathlib's `Metric.ediam` supplies the corresponding set-level API.
For a nonnegative bound `C`, the two formulations agree:
\[
  \bigl(\forall s,t,\ d(f(s),f(t))\le C\bigr)
  \quad\Longleftrightarrow\quad
  \operatorname{ediam}(f(\iota))\le\operatorname{ofReal}(C).
\]
-/

@[expose] public section

namespace Metric

/-- A function has oscillation at most `bound` if the distance between every
pair of its values is at most `bound`. -/
def OscillationBounded {ι E : Type*} [PseudoMetricSpace E]
    (f : ι → E) (bound : ℝ) : Prop :=
  ∀ s t, dist (f s) (f t) ≤ bound

/-- Increasing the allowed oscillation preserves boundedness. -/
theorem OscillationBounded.mono {ι E : Type*} [PseudoMetricSpace E]
    {f : ι → E} {bound₁ bound₂ : ℝ} (hbound : bound₁ ≤ bound₂)
    (h : OscillationBounded f bound₁) : OscillationBounded f bound₂ :=
  fun s t => (h s t).trans hbound

/-- Oscillation boundedness is symmetric in its two indices. -/
theorem OscillationBounded.symm {ι E : Type*} [PseudoMetricSpace E]
    {f : ι → E} {bound : ℝ} (h : OscillationBounded f bound) (s t : ι) :
    dist (f t) (f s) ≤ bound := by
  simpa [dist_comm] using h s t

/-- A pairwise oscillation bound controls the extended diameter of the range. -/
theorem OscillationBounded.ediam_range_le {ι E : Type*} [PseudoMetricSpace E]
    {f : ι → E} {bound : ℝ} (h : OscillationBounded f bound) :
    ediam (Set.range f) ≤ ENNReal.ofReal bound := by
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  rcases hx with ⟨s, rfl⟩
  rcases hy with ⟨t, rfl⟩
  exact h s t

/-- If Mathlib's extended diameter of a range is at most `bound`, then every
pair of values of the function is within `bound`, provided `bound` is
nonnegative. -/
theorem OscillationBounded.of_ediam_range_le {ι E : Type*} [PseudoMetricSpace E]
    {f : ι → E} {bound : ℝ} (hbound : 0 ≤ bound)
    (hdiam : ediam (Set.range f) ≤ ENNReal.ofReal bound) :
    OscillationBounded f bound := by
  intro s t
  have hfinite : ediam (Set.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdiam
  have hdist : dist (f s) (f t) ≤ diam (Set.range f) :=
    dist_le_diam_of_mem' hfinite ⟨s, rfl⟩ ⟨t, rfl⟩
  have hdiam' : diam (Set.range f) ≤ bound :=
    ENNReal.toReal_le_of_le_ofReal hbound hdiam
  exact hdist.trans hdiam'

end Metric

end
