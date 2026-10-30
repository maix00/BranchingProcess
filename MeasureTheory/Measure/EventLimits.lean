/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Limits of measures of event sequences

These results concern finite measures and probability measures on arbitrary
measurable spaces. They do not depend on a stochastic process or a particular
probability model.

## Public declarations

- `tendsto_measure_of_ae_tendsto_indicator_of_nullMeasurableSet`: for a
  countable index type and countably generated filter $L$, if $A_i$ and $A$
  are null-measurable and $\mathbf 1_{A_i}\to\mathbf 1_A$ almost everywhere
  along $L$, then $\mu(A_i)\to_L\mu(A)$ for finite $\mu$.
- `eventually_measure_inter_pos_of_tendsto_one`: for any filter $L$, if
  $\mu(A_i)\to_L1$ and $\mu(B_i)\ge c>0$, then $\mu(A_i\cap B_i)>0$
  eventually for a probability measure, even when each $A_i$ is only
  null-measurable.
-/

@[expose] public section

namespace MeasureTheory

open Filter
open scoped Topology

theorem tendsto_measure_of_ae_tendsto_indicator_of_nullMeasurableSet
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    [IsFiniteMeasure P] (L : Filter ι) [L.IsCountablyGenerated]
    (A : ι → Set Ω) (B : Set Ω)
    (hA : ∀ i, NullMeasurableSet (A i) P) (hB : NullMeasurableSet B P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ i in L, (ω ∈ A i ↔ ω ∈ B)) :
    Tendsto (fun i => P (A i)) L (𝓝 (P B)) := by
  let C : ι → Set Ω := fun i => toMeasurable P (A i)
  let D : Set Ω := toMeasurable P B
  have heqA : ∀ᵐ ω ∂P, ∀ i, (ω ∈ C i ↔ ω ∈ A i) := by
    apply ae_all_iff.mpr
    intro i
    exact (hA i).toMeasurable_ae_eq.mem_iff
  have heqB : ∀ᵐ ω ∂P, (ω ∈ D ↔ ω ∈ B) :=
    hB.toMeasurable_ae_eq.mem_iff
  have hC : ∀ᵐ ω ∂P, ∀ᶠ i in L, (ω ∈ C i ↔ ω ∈ D) := by
    filter_upwards [heqA, heqB, h] with ω hωA hωB hω
    filter_upwards [hω] with i hi
    exact (hωA i).trans (hi.trans hωB.symm)
  have hlim : Tendsto (fun i => P (C i)) L (𝓝 (P D)) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L
      (measurableSet_toMeasurable P B)
      (fun i => measurableSet_toMeasurable P (A i)) hC
  have hmeasure (i : ι) : P (A i) = P (C i) :=
    measure_congr (hA i).toMeasurable_ae_eq.symm
  have hmeasureB : P B = P D :=
    measure_congr hB.toMeasurable_ae_eq.symm
  simpa only [hmeasure, hmeasureB] using hlim

/-- An event whose probability tends to one eventually has a positive
intersection with any event whose probability has a fixed positive lower
bound. The first event may be only null-measurable. -/
theorem eventually_measure_inter_pos_of_tendsto_one
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {L : Filter ι} (A B : ι → Set Ω) (hA : ∀ i, NullMeasurableSet (A i) P)
    (hlim : Tendsto (fun i => P (A i)) L (𝓝 1))
    {c : ENNReal} (hc : 0 < c) (hB : ∀ i, c ≤ P (B i)) :
    ∀ᶠ i in L, 0 < P (A i ∩ B i) := by
  have hcomp : Tendsto (fun i => P ((A i)ᶜ)) L (𝓝 0) := by
    have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := (1 : ENNReal))) hlim
      (Or.inl ENNReal.one_ne_top)
    have heq : ∀ i, P ((A i)ᶜ) = 1 - P (A i) := by
      intro i
      simpa [measure_univ] using
        (measure_compl₀ (hA i) (measure_ne_top P (A i)))
    simpa [heq] using hsub
  obtain ⟨ε, hε0, hεc⟩ := exists_between hc
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hcomp ε hε0] with i hi
  by_contra hnot
  have hzero : P (A i ∩ B i) = 0 := (not_lt.mp hnot).antisymm bot_le
  have hsplit := measure_inter_add_sdiff₀ (B i) (hA i)
  rw [Set.inter_comm, hzero, zero_add] at hsplit
  have hle : P (B i) ≤ P ((A i)ᶜ) := by
    rw [← hsplit]
    exact measure_mono (Set.sdiff_subset_compl (B i) (A i))
  exact (not_le_of_gt hεc) ((hB i).trans (hle.trans hi))

end MeasureTheory
