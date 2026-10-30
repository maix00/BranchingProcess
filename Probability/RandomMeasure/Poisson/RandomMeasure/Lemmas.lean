/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Probability.RandomMeasure.Poisson.RandomMeasure.Basic

/-!
# Internal lemmas for Poisson random-measure evaluation

This module holds proof support shared by the evaluation-law and independence proofs; it is not a
public theorem entry point.

## Internal proof declarations

- `tsum_measure_prmPiece_inter` decomposes $m(A)$ as
  $\sum_k m(\operatorname{prmPiece}(m,k) \cap A)$ for measurable $A$.
- `measurable_filterCard` proves measurability of
  $g \mapsto \#\{n < \mathrm{cnt}(g): \mathrm{pt}_n(g) \in A\}$.
- `prmPartialCount K X A n ω` counts points in $A$ from pieces $0,\ldots,n$.
- `measurable_prmPartialCount` proves its measurability from coordinate measurability.
- `tendsto_rate_prmPartialCount` states
  $\sum_{k\le n}m(\operatorname{prmPiece}(m,k)\cap A)\to m(A)$ for finite $m(A)$.
- `tendsto_natCast_prmPartialCount` states that the real-valued partial counts converge to
  $N_\omega(A).toReal$ whenever $N_\omega(A)<\infty$.
-/

section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E] {μ : Measure Ω} {A : Set E} {ω : Ω}

omit [Nonempty E] in
/-- The rates of the per-piece thinned counts sum to the total mass: `∑ₖ m (piece k ∩ A) = m A`,
since the pieces intersected with `A` partition `A`. -/
lemma tsum_measure_prmPiece_inter (hA : MeasurableSet A) :
    ∑' k, m (prmPiece m k ∩ A) = m A := by
  rw [← measure_iUnion (fun i j hij =>
        (pairwise_disjoint_prmPiece hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => measurableSet_prmPiece.inter hA),
    ← Set.iUnion_inter, iUnion_prmPiece, Set.univ_inter]

omit [Nonempty E] in
open Classical in
/-- Measurability skeleton for the count of points of a single piece landing in `A`, phrased over an
abstract coordinate space `D` supplying the count `cnt` and the points `pt`. Both the thinned-count
extractors used in the superposition independence step are instances. -/
lemma measurable_filterCard {D : Type*} [MeasurableSpace D] (hA : MeasurableSet A)
    (cnt : D → ℕ) (pt : ℕ → D → E) (hcnt : Measurable cnt) (hpt : ∀ n', Measurable (pt n')) :
    Measurable fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card := by
  have hcard : (fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card)
      = fun g => ∑ n' ∈ Finset.range (cnt g), (if pt n' g ∈ A then (1 : ℕ) else 0) := by
    funext g; rw [Finset.card_filter]
  rw [hcard]
  have hP : Measurable
      fun p : D × ℕ => ∑ n' ∈ Finset.range p.2, (if pt n' p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n' _ =>
        Measurable.ite (hpt n' hA) measurable_const measurable_const
  exact hP.comp (measurable_id.prodMk hcnt)


/-- **The partial superposition count**: the number of realized points landing in `A` coming from the
first `n + 1` pieces. Its `n → ∞` limit is the total count in `A`. -/
noncomputable def prmPartialCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (n : ℕ)
    (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), thinnedCount K X A k ω

omit [Nonempty E] in
open Classical in
/-- The partial superposition count is measurable. -/
lemma measurable_prmPartialCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (prmPartialCount K X A n) :=
  Finset.measurable_sum _ fun k _ => measurable_thinnedCount (hK k) (hX k) hA

omit [Nonempty E] in
/-- The accumulated rates increase to the total mass `m A`, as a real limit; used to identify the
limit of the partial-count characteristic functions. -/
lemma tendsto_rate_prmPartialCount (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
      atTop (𝓝 (m A).toReal) := by
  have hsum : ∑' k, m (prmPiece m k ∩ A) = m A := tsum_measure_prmPiece_inter hA
  have hHS : HasSum (fun k => (m (prmPiece m k ∩ A)).toReal)
      (∑' k, (m (prmPiece m k ∩ A)).toReal) :=
    ENNReal.hasSum_toReal (by rw [hsum]; exact hfin.ne)
  have hval : (∑' k, (m (prmPiece m k ∩ A)).toReal) = (m A).toReal := by
    rw [← ENNReal.tsum_toReal_eq fun k => (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne, hsum]
  rw [hval] at hHS
  exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

omit [Nonempty E] [MeasurableSpace Ω] in
/-- Almost surely the partial superposition counts increase to the total count in `A`: the partial
sums of the `ℝ≥0∞`-valued thinned counts tend to their tsum, which is finite on the almost-sure
finiteness event, so `ENNReal.toReal` is continuous there. -/
lemma tendsto_natCast_prmPartialCount (hA : MeasurableSet A) (ω : Ω)
    (hω : poissonRandomMeasure K X ω A < ⊤) :
    Tendsto (fun n => (prmPartialCount K X A n ω : ℝ)) atTop
      (𝓝 (poissonRandomMeasure K X ω A).toReal) := by
  have hHS : HasSum (fun k => (thinnedCount K X A k ω : ℝ≥0∞)) (poissonRandomMeasure K X ω A) := by
    rw [poissonRandomMeasure_apply hA]; exact ENNReal.summable.hasSum
  have hcast : ∀ n, ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)
      = ∑ i ∈ Finset.range (n + 1), (thinnedCount K X A i ω : ℝ≥0∞) := by
    intro n; rw [prmPartialCount]; exact Nat.cast_sum _ _
  have hpart : Tendsto (fun n => ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)) atTop
      (𝓝 (poissonRandomMeasure K X ω A)) := by
    simp_rw [hcast]
    exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := (ENNReal.tendsto_toReal hω.ne).comp hpart
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using hlim


end ProbabilityTheory
