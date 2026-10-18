/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage.Basic
public import Probability.Process.Path.Reflection.Basic
public import Probability.Process.TimeGrid.UnitInterval
public import Probability.Process.TimeGrid.Ceiling

/-!
# Finite-grid approximation of continuous first passage

The public definition and theorems in this file are:

- `ProbabilityTheory.firstPassageGridCeiling`: for a continuous path $f$ and
  a finite ordered grid $(r_i)_{i=0}^N$, the least index with
  $\tau_a(f)\le r_i$, where $\tau_a(f)=\inf\{t:f(t)\le a\}$; it equals $N$
  if no grid time reaches the passage time.
- `ProbabilityTheory.firstPassageBelow_le_gridCeiling`: if $\tau_a(f)$ is
  at most the final grid time, it is at most the selected grid time.
- `ProbabilityTheory.firstPassageGridCeiling_le_of_passage_le`: every grid
  index whose time is at or after $\tau_a(f)$ bounds the selected index.
- `ProbabilityTheory.firstPassageGridCeiling_eq_last_of_not_le`: if passage
  occurs after the final grid time, the selected index is $N$.
- `ProbabilityTheory.tendsto_firstPassageGridCeiling_time_of_finite`: if the
  grids eventually cover a finite passage time and contain points arbitrarily
  close above it, their selected times converge to that passage time.
- `ProbabilityTheory.tendsto_reflectAfter_firstPassageGridCeiling_of_finite`:
  reflection of a continuous path at those selected times converges in the
  compact-open topology.
- `ProbabilityTheory.tendsto_unitIntervalGridCeiling_time` and
  `ProbabilityTheory.tendsto_reflectAfter_unitIntervalGridCeiling`: the
  uniform unit-interval grids approximate a passage time in $[0,1]$ and the
  corresponding reflected paths.
- `ProbabilityTheory.tendsto_unitIntervalGridCeiling_time_capped` and
  `ProbabilityTheory.tendsto_reflectAfter_unitIntervalGridCeiling_capped`:
  for every path, the selected times and reflected paths converge to those
  at $\tau_a(f)\wedge1$.
- `ProbabilityTheory.measurable_firstPassageGridCeiling`: the finite-grid
  selector is Borel measurable as a function of the path.
- `ProbabilityTheory.firstPassageGridCeiling_eq_iff_of_agreeOn`: its fiber at
  index $i$ is determined by the path through time $r_i$.

These are pathwise finite-grid results. Brownian path-law invariance for
reflection at the selected times is stated separately in
`Probability.Process.Brownian.Reflection.FirstPassage.GridLaw`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first grid index by which a continuous path has fallen below
`a`, using the last index if this has not yet happened. -/
noncomputable def firstPassageGridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ)) : Fin (N + 1) :=
  timeGridCeiling N r (fun g => firstPassageBelow g a) f

/-- If the passage has occurred by the end of the grid, the selected
grid time is at or after the continuous first-passage time. -/
theorem firstPassageBelow_le_gridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ))
    (hlast : firstPassageBelow f a ≤ r (Fin.last N)) :
    firstPassageBelow f a ≤ r (firstPassageGridCeiling N r a f) := by
  exact time_le_timeGridCeiling N r (fun g => firstPassageBelow g a) f hlast

/-- Every grid point after the first passage bounds the selected
first-passage index from above. -/
theorem firstPassageGridCeiling_le_of_passage_le (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ))
    (i : Fin (N + 1)) (hi : firstPassageBelow f a ≤ r i) :
    firstPassageGridCeiling N r a f ≤ i := by
  exact timeGridCeiling_le_of_time_le N r (fun g => firstPassageBelow g a) f i hi

/-- If the continuous first passage occurs after the final grid time,
the selected index is the last one. -/
theorem firstPassageGridCeiling_eq_last_of_not_le (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) (f : C(ℝ≥0, ℝ))
    (hnot : ¬ firstPassageBelow f a ≤ r (Fin.last N)) :
    firstPassageGridCeiling N r a f = Fin.last N := by
  exact timeGridCeiling_eq_last_of_not_le N r hr
    (fun g => firstPassageBelow g a) f hnot

/-- The first grid observation after a finite passage converges to the
passage time whenever the grids eventually reach it and contain points
arbitrarily close above it. -/
theorem tendsto_firstPassageGridCeiling_time_of_finite
    (N : ℕ → ℕ) (r : ∀ n, Fin (N n + 1) → ℝ≥0)
    (hr : ∀ n, Monotone (r n)) (a : ℝ) (f : C(ℝ≥0, ℝ)) (τ : ℝ≥0)
    (hτ : firstPassageBelow f a = τ)
    (hcover : ∀ᶠ n in Filter.atTop, τ ≤ r n (Fin.last (N n)))
    (hdense : ∀ b : ℝ≥0, τ < b →
      ∀ᶠ n in Filter.atTop, ∃ i : Fin (N n + 1), τ ≤ r n i ∧ r n i < b) :
    Filter.Tendsto (fun n => r n (firstPassageGridCeiling (N n) (r n) a f))
      Filter.atTop (nhds τ) := by
  exact tendsto_timeGridCeiling_time_of_finite N r hr
    (fun g => firstPassageBelow g a) f τ hτ hcover hdense

/-- Reflection at the first grid observation converges to reflection
at a finite continuous first-passage time. -/
theorem tendsto_reflectAfter_firstPassageGridCeiling_of_finite
    (N : ℕ → ℕ) (r : ∀ n, Fin (N n + 1) → ℝ≥0)
    (hr : ∀ n, Monotone (r n)) (a : ℝ) (f : C(ℝ≥0, ℝ)) (τ : ℝ≥0)
    (hτ : firstPassageBelow f a = τ)
    (hcover : ∀ᶠ n in Filter.atTop, τ ≤ r n (Fin.last (N n)))
    (hdense : ∀ b : ℝ≥0, τ < b →
      ∀ᶠ n in Filter.atTop, ∃ i : Fin (N n + 1), τ ≤ r n i ∧ r n i < b) :
    Filter.Tendsto
      (fun n => reflectAfter f (r n (firstPassageGridCeiling (N n) (r n) a f)))
      Filter.atTop (nhds (reflectAfter f τ)) := by
  exact (continuous_reflectAfter_time f).continuousAt.tendsto.comp
    (tendsto_firstPassageGridCeiling_time_of_finite N r hr a f τ hτ hcover hdense)

/-- For a passage time in $[0,1]$, the selected uniform grid times
converge to the continuous first-passage time. -/
theorem tendsto_unitIntervalGridCeiling_time (a : ℝ) (f : C(ℝ≥0, ℝ))
    (τ : ℝ≥0) (hτ : firstPassageBelow f a = τ) (hτ1 : τ ≤ 1) :
    Filter.Tendsto
      (fun n => unitIntervalGridTime n
        (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f))
      Filter.atTop (nhds τ) := by
  exact tendsto_firstPassageGridCeiling_time_of_finite
    (fun n => n + 1) (fun n => unitIntervalGridTime n)
    unitIntervalGridTime_mono a f τ hτ
    (Filter.Eventually.of_forall (fun n => by
      rw [unitIntervalGridTime_last]
      exact hτ1))
    (fun b hb => unitIntervalGridTime_dense τ b hτ1 hb)

/-- Reflection at the uniform first-passage grid time converges in
continuous-path space to reflection at the continuous passage time. -/
theorem tendsto_reflectAfter_unitIntervalGridCeiling (a : ℝ) (f : C(ℝ≥0, ℝ))
    (τ : ℝ≥0) (hτ : firstPassageBelow f a = τ) (hτ1 : τ ≤ 1) :
    Filter.Tendsto
      (fun n => reflectAfter f (unitIntervalGridTime n
        (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f)))
      Filter.atTop (nhds (reflectAfter f τ)) := by
  exact (continuous_reflectAfter_time f).continuousAt.tendsto.comp
    (tendsto_unitIntervalGridCeiling_time a f τ hτ hτ1)

/-- The selected unit-interval grid time converges to the first-passage
time capped at $1$, including paths with no passage by time $1$. -/
theorem tendsto_unitIntervalGridCeiling_time_capped (a : ℝ) (f : C(ℝ≥0, ℝ)) :
    Filter.Tendsto
      (fun n => unitIntervalGridTime n
        (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f))
      Filter.atTop
      (nhds (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) := by
  by_cases h : firstPassageBelow f a ≤ (1 : WithTop ℝ≥0)
  · obtain ⟨u, _, hu⟩ := (firstPassageBelow_le_iff f a 1).mp h
    let τ : ℝ≥0 := sInf {t : ℝ≥0 | f t ≤ a}
    have hτ : firstPassageBelow f a = τ := by
      simp only [firstPassageBelow, firstPassageLE,
        ite_eq_left (show ∃ t : ℝ≥0, f t ≤ a from ⟨u, hu⟩)]
      rfl
    have hτ1 : τ ≤ 1 := by
      rw [hτ] at h
      exact WithTop.coe_le_coe.mp h
    have hcap : (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA = τ := by
      rw [hτ]
      have hmin : min (τ : WithTop ℝ≥0) 1 = τ := min_eq_left (by exact_mod_cast hτ1)
      rw [hmin]
      rfl
    rw [hcap]
    exact tendsto_unitIntervalGridCeiling_time a f τ hτ hτ1
  · have hidx (n : ℕ) :
        firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f =
          Fin.last (n + 1) := by
      apply firstPassageGridCeiling_eq_last_of_not_le
        (n + 1) (unitIntervalGridTime n) (unitIntervalGridTime_mono n) a f
      simpa [unitIntervalGridTime_last] using h
    have hcap : (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA = 1 := by
      rw [min_eq_right (lt_of_not_ge h).le]
      simp
    rw [hcap]
    simp [hidx, unitIntervalGridTime_last]

/-- Reflection at the selected grid time converges for every path to
reflection at its first-passage time capped at $1$. -/
theorem tendsto_reflectAfter_unitIntervalGridCeiling_capped
    (a : ℝ) (f : C(ℝ≥0, ℝ)) :
    Filter.Tendsto
      (fun n => reflectAfter f (unitIntervalGridTime n
        (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f)))
      Filter.atTop
      (nhds (reflectAfter f
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA)) := by
  exact (continuous_reflectAfter_time f).continuousAt.tendsto.comp
    (tendsto_unitIntervalGridCeiling_time_capped a f)

/-- The selected finite-grid index is a measurable function of the
continuous path. -/
theorem measurable_firstPassageGridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) :
    Measurable (firstPassageGridCeiling N r a) := by
  exact measurable_timeGridCeiling N r (fun f => firstPassageBelow f a)
    (measurable_firstPassageBelow a)

/-- A first-passage grid selector is determined at index `i` by the
path up to its observation time `r i`. -/
theorem firstPassageGridCeiling_eq_iff_of_agreeOn
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) (i : Fin (N + 1)) (f g : C(ℝ≥0, ℝ))
    (hprefix : ∀ v : ℝ≥0, v ≤ r i → f v = g v) :
    firstPassageGridCeiling N r a f = i ↔
      firstPassageGridCeiling N r a g = i := by
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → Bool :=
    fun j p => if firstPassageBelow p a ≤ r j then true else false
  have hum (j : Fin (N + 1)) : StronglyMeasurable (u j) := by
    have hset : MeasurableSet {p : C(ℝ≥0, ℝ) |
        firstPassageBelow p a ≤ r j} :=
      (measurable_firstPassageBelow a) measurableSet_Iic
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  let ℱ := Filtration.natural u hum
  have hu : Adapted ℱ u := (Filtration.stronglyAdapted_natural hum).adapted
  have hτ : IsStoppingTime ℱ
      (fun p : C(ℝ≥0, ℝ) =>
        (firstPassageGridCeiling N r a p : WithTop (Fin (N + 1)))) := by
    exact hu.isStoppingTime_hittingBtwn (measurableSet_singleton true)
  have hi : MeasurableSet[ℱ i] {p : C(ℝ≥0, ℝ) |
      firstPassageGridCeiling N r a p = i} := by
    simpa using hτ.measurableSet_eq i
  rw [Filtration.natural_eq_comap u hum i] at hi
  obtain ⟨E, hE, hEeq⟩ := (MeasurableSpace.measurableSet_comap).mp hi
  have hupast : (fun j : Set.Iic i => u j f) =
      (fun j : Set.Iic i => u j g) := by
    funext j
    have hprefix_j (v : ℝ≥0) (hv : v ≤ r j) : f v = g v :=
      hprefix v (hv.trans (hr j.2))
    have hpassage := firstPassageBelow_le_congr_of_agreeOn
      f g a (r j) hprefix_j
    change (if firstPassageBelow f a ≤ r j then true else false) =
      (if firstPassageBelow g a ≤ r j then true else false)
    exact ite_congr (propext hpassage) (fun _ => rfl) (fun _ => rfl)
  change f ∈ {p : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a p = i} ↔
    g ∈ {p : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a p = i}
  rw [← hEeq]
  simpa only [Set.mem_preimage] using (congrArg (· ∈ E) hupast).to_iff

end ProbabilityTheory

end
