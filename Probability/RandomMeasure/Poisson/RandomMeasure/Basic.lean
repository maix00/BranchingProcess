/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Probability.RandomMeasure.Poisson.PointFamily.Basic
public import Probability.RandomMeasure.Poisson.PointFamily.Thinning

/-!
# Poisson random measure construction

For a count-and-mark family, `poissonRandomMeasure K X ω` is the sum of unit atoms
`∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. This module defines the realized measure and proves
measurability of its set evaluations and of the measure-valued map.

For every measurable `A`, its evaluation is
`poissonRandomMeasure K X ω A = ∑' k, (thinnedCount K X A k ω : ℝ≥0∞)`.
If each count and point coordinate is measurable, then both
`ω ↦ poissonRandomMeasure K X ω A` and `ω ↦ poissonRandomMeasure K X ω` are measurable.

## Public declarations

- `poissonRandomMeasure K X ω` defines the realized point measure.
- `poissonRandomMeasure_apply` identifies its value on a measurable set with the total thinned count.
- `measurable_poissonRandomMeasure_apply` and `measurable_poissonRandomMeasure` give the evaluation
  and measure-valued measurability statements.

For measurable `A`, the realized measure counts the points whose marks lie in
`A`; measurable point and count coordinates make both evaluation and the
measure-valued map measurable:

\[\begin{aligned}
\mathcal N_\omega(A)
&=\sum_{k\ge0}\sum_{n<K(k,\omega)}\mathbf1_A(X(k,n,\omega))\\
&=\sum_{k\ge0}
  \bigl(\operatorname{thinnedCount}(K,X,A,k,\omega):\overline{\mathbb R}_{\ge0}\bigr),\\
\omega&\longmapsto\mathcal N_\omega(A),\qquad
\omega\longmapsto\mathcal N_\omega\quad\text{are measurable}.
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E] {μ : Measure Ω} {A B : Set E} {ω : Ω}

/-- **The Poisson random measure** of a Poisson point family: for each `ω`, the measure placing a
unit Dirac mass at each of the realized points `X k n ω` (for `n < K k ω`) across all pieces `k`.
Equivalently `∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. -/
noncomputable def poissonRandomMeasure (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (ω : Ω) : Measure E :=
  Measure.sum fun k => Measure.sum fun n =>
    if n < K k ω then Measure.dirac (X k n ω) else 0

omit [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] in
/-- The `ℝ≥0∞`-cast of the thinned count as a finite sum of point-membership indicators. -/
private lemma thinnedCount_toENNReal :
    (thinnedCount K X A k ω : ℝ≥0∞)
      = ∑ n ∈ Finset.range (K k ω), A.indicator (1 : E → ℝ≥0∞) (X k n ω) := by
  classical
  rw [thinnedCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : X k n ω ∈ A
  · rw [Set.indicator_of_mem hx, ite_eq_left hx, Pi.one_apply, Nat.cast_one]
  · rw [Set.indicator_of_notMem hx, ite_eq_right hx, Nat.cast_zero]

omit [MeasurableSpace Ω] [Nonempty E] in
/-- **Evaluation of the Poisson random measure.** On a measurable set `A`, the random measure counts
the total number of realized points across all pieces landing in `A`. -/
theorem poissonRandomMeasure_apply (hA : MeasurableSet A) :
    poissonRandomMeasure K X ω A = ∑' k, (thinnedCount K X A k ω : ℝ≥0∞) := by
  classical
  rw [poissonRandomMeasure, Measure.sum_apply _ hA]
  refine tsum_congr fun k => ?_
  rw [Measure.sum_apply _ hA]
  have hterm : ∀ n, (if n < K k ω then Measure.dirac (X k n ω) else 0) A
      = if n < K k ω then A.indicator (1 : E → ℝ≥0∞) (X k n ω) else 0 := by
    intro n
    rw [apply_ite (fun ν : Measure E => ν A), Measure.dirac_apply' _ hA, Measure.coe_zero,
      Pi.zero_apply]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [ite_eq_right (by simpa [Finset.mem_range] using hn)]]
  rw [thinnedCount_toENNReal]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [ite_eq_left (by simpa [Finset.mem_range] using hn)]

omit [Nonempty E] in
/-- The set evaluation of the Poisson random measure is a measurable function of `ω`. -/
theorem measurable_poissonRandomMeasure_apply (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable fun ω => poissonRandomMeasure K X ω A := by
  simp_rw [poissonRandomMeasure_apply hA]
  refine Measurable.tsum fun k => ?_
  exact measurable_from_top.comp (measurable_thinnedCount (hK k) (hX k) hA)

omit [Nonempty E] in
/-- The Poisson random measure is measurable as a map into the space of measures. -/
theorem measurable_poissonRandomMeasure (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) :
    Measurable (poissonRandomMeasure K X) :=
  Measure.measurable_of_measurable_coe _ fun _ hA =>
    measurable_poissonRandomMeasure_apply hK hX hA


end ProbabilityTheory
