/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Levy
public import Probability.Process.IndepIncrements.FiniteDimensional

/-!
# Finite-dimensional laws of stable-increment processes

## Public declarations

- `HasStableClockIncrements.finiteDimensional_identDistrib` states that
  matching stable increment specifications imply
  \(\operatorname{Law}((X_{t_j})_{j=1}^n)=
  \operatorname{Law}((Y_{t_j})_{j=1}^n)\) on each finite monotone grid.
- `HasStableClockIncrements.finiteRestriction_identDistrib` gives the same
  equality for \((X_t)_{t\in I}\) and \((Y_t)_{t\in I}\) on every finite
  \(I\) in a linearly ordered time type.
- `HasStableClockIncrements.aemeasurable_eval` states that every coordinate
  \(\omega\mapsto X_t(\omega)\) is almost-everywhere measurable.
- `HasStableClockIncrements.process_identDistrib_of_aemeasurable` and
  `HasStableClockIncrements.process_identDistrib` give equality in law of
  the whole time-indexed processes, under joint almost-everywhere
  measurability or countable time, respectively.
- `IsStableLevyProcess.timeSpaceScale_positions_identDistrib` states the
  finite-grid self-similarity identity
  \(\operatorname{Law}((X_{t_j})_j)=
  \operatorname{Law}((r^{-1/\alpha}X_{rt_j})_j)\).

The finite-dimensional arguments are proved generically from independent
increments in `Probability.Process.IndepIncrements.FiniteDimensional`. This
file only supplies the stable-process increment-law specialization.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Stable-increment processes on possibly different probability spaces with
the same stable clock specification have the same position-vector law on every
finite monotone grid. The conclusion uses only the generic independent-
increment theorem; stability enters through the matching one-step increment
laws. -/
theorem HasStableClockIncrements.finiteDimensional_identDistrib
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y Q)
    (n : ℕ) (grid : Fin (n + 1) → Time) (hgrid : Monotone grid)
    (hstart : grid 0 = ⊥) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) => Y (grid i.succ) ω) P Q := by
  exact HasIndepIncrements.finiteDimensional_identDistrib
    hX.indepIncrements hY.indepIncrements hX.ae_start_eq_zero hY.ae_start_eq_zero
    (fun s t hst => (hX.increment_hasLaw s t hst).identDistrib
      (hY.increment_hasLaw s t hst)) n grid hgrid hstart

/-- Stable-increment processes on possibly different probability spaces with
the same clock specification have the same position law on every finite
subset of a linearly ordered time axis. -/
theorem HasStableClockIncrements.finiteRestriction_identDistrib
    {Time : Type*} [LinearOrder Time] [OrderBot Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y Q)
    (I : Finset Time) :
    IdentDistrib (fun ω => I.restrict (X · ω))
      (fun ω => I.restrict (Y · ω)) P Q := by
  apply HasIndepIncrements.finiteRestriction_identDistrib
    hX.indepIncrements hY.indepIncrements hX.ae_start_eq_zero hY.ae_start_eq_zero
  intro s t hst
  exact (hX.increment_hasLaw s t hst).identDistrib (hY.increment_hasLaw s t hst)

/-- Every coordinate of a stable clock process is almost-everywhere
measurable. The increment from the least time is measurable by its law, and
the starting value is zero almost surely.
-/
theorem HasStableClockIncrements.aemeasurable_eval
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasStableClockIncrements α μ clock X P) (t : Time) :
    AEMeasurable (fun ω => X t ω) P := by
  exact HasIndepIncrements.aemeasurable_eval h.ae_start_eq_zero
    (fun s t hst => (h.increment_hasLaw s t hst).aemeasurable) t

/-- On a countable linearly ordered time type, equal stable increment specifications
give the same law for the whole time-indexed process. The generic uniqueness
step is Mathlib's finite-dimensional-law theorem.
-/
theorem HasStableClockIncrements.process_identDistrib_of_aemeasurable
    {Time : Type*} [LinearOrder Time] [OrderBot Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y Q)
    (hXmeas : AEMeasurable (fun ω (t : Time) => X t ω) P)
    (hYmeas : AEMeasurable (fun ω (t : Time) => Y t ω) Q) :
    IdentDistrib (fun ω (t : Time) => X t ω)
      (fun ω t => Y t ω) P Q := by
  exact HasIndepIncrements.process_identDistrib_of_aemeasurable
    hX.indepIncrements hY.indepIncrements hX.ae_start_eq_zero hY.ae_start_eq_zero
    (fun s t hst => (hX.increment_hasLaw s t hst).identDistrib
      (hY.increment_hasLaw s t hst)) hXmeas hYmeas

/-- On a countable linearly ordered time type, equal stable increment specifications
give the same law for the whole time-indexed process. Coordinate measurability
follows from the increment laws and zero initial value.
-/
theorem HasStableClockIncrements.process_identDistrib
    {Time : Type*} [LinearOrder Time] [OrderBot Time] [Countable Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X Y : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y P) :
    IdentDistrib (fun ω (t : Time) => X t ω)
      (fun ω t => Y t ω) P P := by
  apply hX.process_identDistrib_of_aemeasurable hY
  · exact AEMeasurable.of_eval fun t => hX.aemeasurable_eval t
  · exact AEMeasurable.of_eval fun t => hY.aemeasurable_eval t

/-- A stable Lévy process and its canonical time-space rescaling have the same
joint law at every finite monotone grid. This is the finite-dimensional form
of the self-similarity identity; it deliberately makes no path-space law
claim.
-/
theorem IsStableLevyProcess.timeSpaceScale_positions_identDistrib
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (r : ℝ≥0) (hr : 0 < r)
    (n : ℕ) (grid : Fin (n + 1) → ℝ≥0) (hgrid : Monotone grid)
    (hstart : grid 0 = 0) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) =>
        (r : ℝ) ^ (-(1 / α)) * X (r * grid i.succ) ω) P P := by
  apply h.increments.finiteDimensional_identDistrib
    (h.timeSpaceScale r hr).increments n grid hgrid ?_
  simpa using hstart

end ProbabilityTheory

end
