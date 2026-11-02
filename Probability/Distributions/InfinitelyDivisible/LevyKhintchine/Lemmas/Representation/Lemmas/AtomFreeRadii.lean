/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import MeasureTheory.Measure.LevelSet
import MeasureTheory.Measure.Levy.Basic

/-!
# Proof support for atom-free Lévy cutoffs

The generic measurable-fiber selector is in
`MeasureTheory.Measure.LevelSet`. This file specializes it to radial boundary
spheres of a Lévy measure for the Lévy–Khintchine representation proof chain.

## Internal proof declarations

- `exists_atomFree_radius` gives $r\in(a,b]$ with
  $\nu(\{x:|x|=r\})=0$ whenever $0\le a<b$.
- `exists_atomFree_seq_tendsto_zero` gives $\delta_n\in(0,c)$ with
  $\nu(\{x:|x|=\delta_n\})=0$ and $\delta_n\to0$ for every $c>0$.

Only the Lévy–Khintchine representation modules currently use these
specializations. The proof uses finite mass away from the origin and
`MeasureTheory.exists_measure_zero_fiber_of_not_countable`.
-/

section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory.IsLevyMeasure

variable {ν : Measure ℝ}

/-- A Lévy measure has an atom-free radius in every interval `(a, b]` with `0 ≤ a < b`. -/
lemma exists_atomFree_radius (hν : IsLevyMeasure ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) :
    ∃ r ∈ Set.Ioc a b, ν {x | |x| = r} = 0 := by
  have hb_pos : 0 < b := ha.trans_lt hab
  let c := max a (b / 2)
  have hc_pos : 0 < c := lt_of_lt_of_le (by linarith) (le_max_right a (b / 2))
  have hc_lt_b : c < b := max_lt hab (by linarith)
  have hc_ge_a : a ≤ c := le_max_left a (b / 2)
  let hfinite : IsFiniteMeasure (ν.restrict {x | c / 2 ≤ |x|}) :=
    hν.isFiniteMeasure_restrict_abs_ge (by positivity)
  have huncountable : ¬ (Set.Ioc c b).Countable := by
    rw [Cardinal.Real.Ioc_countable_iff]
    exact not_le_of_gt hc_lt_b
  have hr_exists : ∃ r ∈ Set.Ioc c b,
      (ν.restrict {x | c / 2 ≤ |x|}) {x | |x| = r} = 0 := by
    exact MeasureTheory.exists_measure_zero_fiber_of_not_countable
      (μ := ν.restrict {x | c / 2 ≤ |x|}) continuous_abs.measurable huncountable
  obtain ⟨r, hr_mem, hr_null⟩ := hr_exists
  have hsub : {x : ℝ | |x| = r} ⊆ {x | c / 2 ≤ |x|} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [hx]
    linarith [hr_mem.1, hc_pos]
  rw [Measure.restrict_apply'
        (measurableSet_le measurable_const continuous_abs.measurable),
      Set.inter_eq_self_of_subset_left hsub] at hr_null
  exact ⟨r, ⟨hc_ge_a.trans_lt hr_mem.1, hr_mem.2⟩, hr_null⟩

/-- Atom-free radii decreasing to `0`, all below any fixed positive bound. -/
lemma exists_atomFree_seq_tendsto_zero (hν : IsLevyMeasure ν)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧ (∀ m, δ m < c) ∧
      (∀ m, ν {x | |x| = δ m} = 0) ∧ Tendsto δ atTop (𝓝 0) := by
  have hb : ∀ m : ℕ, (0 : ℝ) < min (c / 2) (1 / ((m : ℝ) + 1)) := fun m => by
    positivity
  choose δ hδ_mem hδ_null using fun m =>
    hν.exists_atomFree_radius le_rfl (hb m)
  refine ⟨δ, fun m => (hδ_mem m).1, fun m => ?_, hδ_null, ?_⟩
  · calc δ m ≤ min (c / 2) (1 / ((m : ℝ) + 1)) := (hδ_mem m).2
      _ ≤ c / 2 := min_le_left _ _
      _ < c := by linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun m => (hδ_mem m).1.le) (fun m => ?_)
    exact (hδ_mem m).2.trans (min_le_right _ _)

end MeasureTheory.IsLevyMeasure
