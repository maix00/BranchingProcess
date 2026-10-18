/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassage.FiniteStoppingTime
public import Probability.Process.Path.FirstPassage.Basic
public import Probability.Process.Path.TimeGrid.UnitInterval
public import Probability.MeasureTheory.Convergence.InvariantLaw
public import Mathlib.Probability.Process.HittingTime

/-!
# Finite observation times for continuous first passage

The public definition and theorem in this file are:

- `ProbabilityTheory.firstPassageGridCeiling`: the first observation index
  by which the continuous first passage below $a$ has occurred, taking
  the last index when no such observation exists.
- `ProbabilityTheory.firstPassageBelow_le_gridCeiling`: if passage occurs
  by the last observation, it occurs by the selected grid time.
- `ProbabilityTheory.firstPassageGridCeiling_le_of_passage_le`: a grid index
  following the passage bounds the selected index from above.
- `ProbabilityTheory.firstPassageGridCeiling_eq_last_of_not_le`: when the
  passage occurs after the last grid time, the selected index is last.
- `ProbabilityTheory.tendsto_firstPassageGridCeiling_time_of_finite`:
  nested grids with points arbitrarily close above a finite passage time
  have selected times converging to that passage time.
- `ProbabilityTheory.tendsto_reflectAfter_firstPassageGridCeiling_of_finite`:
  the corresponding reflected continuous paths converge in the
  compact-open topology.
- `ProbabilityTheory.tendsto_unitIntervalGridCeiling_time`: the uniform
  unit-interval grid times converge to a passage time in $[0,1]$.
- `ProbabilityTheory.tendsto_reflectAfter_unitIntervalGridCeiling`:
  reflection at these grid times converges to reflection at passage.
- `ProbabilityTheory.tendsto_unitIntervalGridCeiling_time_capped`:
  for every path, the selected grid time converges to the first-passage
  time capped at $1$.
- `ProbabilityTheory.tendsto_reflectAfter_unitIntervalGridCeiling_capped`:
  for every path, reflection at the selected grid time converges to
  reflection at the capped first-passage time.
- `ProbabilityTheory.measurable_firstPassageGridCeiling`: the selected
  finite-grid index is measurable.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_firstPassageBeforeOne_eq`:
  reflection at the first passage below $a$, capped at time $1$,
  preserves Brownian path law.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq`:
  reflection after this finite approximation preserves Brownian path law.

This is the upward finite-valued stopping-time approximation in the proof
of Theorem 2.1 of S. J. Dilworth and Duncan Wright, *A direct proof of the
reflection principle for Brownian motion*, Theory Stoch. Process. 21(37):2
(2016), 1--3, arXiv:1810.01783. The resulting reflection principle is
used for the Lévy running-minimum identity cited in Lemma 2.3 of Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first grid index by which a continuous path has fallen below
`a`, using the last index if this has not yet happened. -/
noncomputable def firstPassageGridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ)) : Fin (N + 1) :=
  hittingBtwn
    (fun i (g : C(ℝ≥0, ℝ)) =>
      if firstPassageBelow g a ≤ r i then true else false)
    {true} 0 (Fin.last N) f

/-- If the passage has occurred by the end of the grid, the selected
grid time is at or after the continuous first-passage time. -/
theorem firstPassageBelow_le_gridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ))
    (hlast : firstPassageBelow f a ≤ r (Fin.last N)) :
    firstPassageBelow f a ≤ r (firstPassageGridCeiling N r a f) := by
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → Bool :=
    fun i g => if firstPassageBelow g a ≤ r i then true else false
  have hexists : ∃ i ∈ Set.Icc (0 : Fin (N + 1)) (Fin.last N),
      u i f ∈ ({true} : Set Bool) := by
    refine ⟨Fin.last N, ⟨bot_le, le_rfl⟩, ?_⟩
    change (if firstPassageBelow f a ≤ r (Fin.last N) then true else false) = true
    split_ifs
    rfl
  have hmem := hittingBtwn_mem_set (u := u) (s := ({true} : Set Bool))
    (n := (0 : Fin (N + 1))) (m := Fin.last N) (ω := f) hexists
  change (if firstPassageBelow f a ≤
      r (firstPassageGridCeiling N r a f) then true else false) = true at hmem
  split_ifs at hmem with hhit
  · exact hhit

/-- Every grid point after the first passage bounds the selected
first-passage index from above. -/
theorem firstPassageGridCeiling_le_of_passage_le (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ))
    (i : Fin (N + 1)) (hi : firstPassageBelow f a ≤ r i) :
    firstPassageGridCeiling N r a f ≤ i := by
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → Bool :=
    fun j g => if firstPassageBelow g a ≤ r j then true else false
  have hmem : u i f ∈ ({true} : Set Bool) := by
    change (if firstPassageBelow f a ≤ r i then true else false) = true
    split_ifs
    rfl
  exact hittingBtwn_le_of_mem (u := u) (s := ({true} : Set Bool)) (n := (0 : Fin (N + 1)))
    (m := Fin.last N) (ω := f) (i := i) bot_le (Fin.le_last i) hmem

/-- If the continuous first passage occurs after the final grid time,
the selected index is the last one. -/
theorem firstPassageGridCeiling_eq_last_of_not_le (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) (f : C(ℝ≥0, ℝ))
    (hnot : ¬ firstPassageBelow f a ≤ r (Fin.last N)) :
    firstPassageGridCeiling N r a f = Fin.last N := by
  have hnone : ¬ ∃ j ∈ Set.Icc (0 : Fin (N + 1)) (Fin.last N),
      (if firstPassageBelow f a ≤ r j then true else false) ∈ ({true} : Set Bool) := by
    rintro ⟨j, _, hj⟩
    have hjhit : firstPassageBelow f a ≤ r j := by
      change (if firstPassageBelow f a ≤ r j then true else false) = true at hj
      split_ifs at hj with hp
      exact hp
    exact hnot (hjhit.trans (WithTop.coe_le_coe.mpr (hr (Fin.le_last j))))
  unfold firstPassageGridCeiling hittingBtwn
  simp only [ite_eq_right hnone]

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
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [hcover] with n hn
    have hlast : firstPassageBelow f a ≤ r n (Fin.last (N n)) := by
      rw [hτ]
      exact WithTop.coe_le_coe.mpr hn
    have hle := firstPassageBelow_le_gridCeiling (N n) (r n) a f hlast
    rw [hτ] at hle
    exact lt_of_lt_of_le hb (WithTop.coe_le_coe.mp hle)
  · intro b hb
    filter_upwards [hdense b hb] with n ⟨i, hi, hib⟩
    have hpass : firstPassageBelow f a ≤ r n i := by
      rw [hτ]
      exact WithTop.coe_le_coe.mpr hi
    have hidx := firstPassageGridCeiling_le_of_passage_le (N n) (r n) a f i hpass
    exact lt_of_le_of_lt (hr n hidx) hib

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
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → Bool :=
    fun i f => if firstPassageBelow f a ≤ r i then true else false
  have hum (i : Fin (N + 1)) : StronglyMeasurable (u i) := by
    have hset : MeasurableSet {f : C(ℝ≥0, ℝ) |
        firstPassageBelow f a ≤ r i} :=
      (measurable_firstPassageBelow a) measurableSet_Iic
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  let ℱ := Filtration.natural u hum
  have hu : Adapted ℱ u := (Filtration.stronglyAdapted_natural hum).adapted
  have hτ : IsStoppingTime ℱ
      (fun f : C(ℝ≥0, ℝ) =>
        (firstPassageGridCeiling N r a f : WithTop (Fin (N + 1)))) := by
    exact hu.isStoppingTime_hittingBtwn (measurableSet_singleton true)
  have hfiber (i : Fin (N + 1)) :
      MeasurableSet {f : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a f = i} := by
    have hi : MeasurableSet[ℱ i] {f : C(ℝ≥0, ℝ) |
        firstPassageGridCeiling N r a f = i} := by
      simpa using hτ.measurableSet_eq i
    exact (ℱ.le i) _ hi
  intro s hs
  have heq : (firstPassageGridCeiling N r a) ⁻¹' s =
      ⋃ i : s, {f : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a f = i} := by
    ext f
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => hfiber i)

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

/-- Reflection at the first grid time after continuous first passage
preserves Brownian path law. This is the finite-valued stopping-time
approximation in Theorem 2.1 of S. J. Dilworth and Duncan Wright,
*A direct proof of the reflection principle for Brownian motion*,
arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (firstPassageGridCeiling N r a f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  have hT : Measurable (firstPassageGridCeiling N r a) :=
    measurable_firstPassageGridCeiling N r a
  have hlocal (i : Fin (N + 1)) (f g : C(ℝ≥0, ℝ))
      (hprefix : ∀ v : ℝ≥0, v ≤ r i → f v = g v) :
      firstPassageGridCeiling N r a f = i ↔
        firstPassageGridCeiling N r a g = i :=
    firstPassageGridCeiling_eq_iff_of_agreeOn N r hr a i f g hprefix
  exact hB.measure_reflectAfter_finitePathwiseStoppingTime_eq
    hBmeasurable (firstPassageGridCeiling N r a) r hT hlocal

/-- Reflection at the first passage below `a`, capped at time `1`,
preserves Brownian path law. Finite-grid reflection invariance passes to
the pointwise path limit by bounded convergence, as in Theorem 2.1 of
S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_firstPassageBeforeOne_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f
          (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  haveI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  haveI : IsFiniteMeasure μ := inferInstance
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    reflectAfter f (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA
  let Fₙ : ℕ → C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun n f =>
    reflectAfter f (unitIntervalGridTime n
      (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f))
  have hTmeas : Measurable
      (fun f : C(ℝ≥0, ℝ) =>
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) :=
    ((measurable_firstPassageBelow a).min measurable_const).untopA
  have hF : Measurable F :=
    measurable_reflectAfter_pair.comp (measurable_id.prodMk hTmeas)
  have hFₙ (n : ℕ) : Measurable (Fₙ n) := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        unitIntervalGridTime n
          (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f)) :=
      (measurable_of_finite (unitIntervalGridTime n)).comp
        (measurable_firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a)
    exact measurable_reflectAfter_pair.comp (measurable_id.prodMk hT)
  have hlim (f : C(ℝ≥0, ℝ)) :
      Filter.Tendsto (fun n => Fₙ n f) Filter.atTop (nhds (F f)) :=
    tendsto_reflectAfter_unitIntervalGridCeiling_capped a f
  have hinv (n : ℕ) : μ.map (Fₙ n) = μ :=
    hB.measure_reflectAfter_firstPassageGridCeiling_eq hBmeasurable
      (n + 1) (unitIntervalGridTime n) (unitIntervalGridTime_mono n) a
  exact Measure.map_eq_of_pointwise_limit μ F Fₙ hF hFₙ hlim hinv

end ProbabilityTheory

end
