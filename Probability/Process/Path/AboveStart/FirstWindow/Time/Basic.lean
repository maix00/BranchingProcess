/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.Time.Core
import all Probability.Process.Path.AboveStart.FirstWindow.Time.Lemmas.Approximation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-!
# Measurability of first nonnegative unit-window times

## Public declarations

- `ProbabilityTheory.measurable_firstNonnegativeWindowStartUpTo`:
  for each finite horizon $s$, the map $f\mapsto T^s(f)$ is Borel
  measurable.
- `ProbabilityTheory.firstNonnegativeWindowStart_eq_iInf_upTo`:
  the unrestricted time satisfies $T(f)=\inf_n T^n(f)$.
- `ProbabilityTheory.measurable_firstNonnegativeWindowStart`:
  the unrestricted first-window time $f\mapsto T(f)$ is Borel measurable.

This is the measurability conclusion of Bolthausen, *On a Functional Central
Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.1,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098. The rational-grid
proof is kept in the internal `Time/Lemmas/Approximation` module.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- Bolthausen's Lemma 2.1: the first eligible window time is Borel
measurable on continuous path space for every finite horizon. -/
theorem measurable_firstNonnegativeWindowStartUpTo (s : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStartUpTo f s) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe u =>
      simpa only [Set.preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        measurableSet_firstNonnegativeWindowStartUpTo_le s u

/-- The unrestricted first eligible window is the decreasing limit of
the finite-horizon first-window times. -/
theorem firstNonnegativeWindowStart_eq_iInf_upTo
    (f : C(ℝ≥0, ℝ)) :
    firstNonnegativeWindowStart f =
      ⨅ n : ℕ, firstNonnegativeWindowStartUpTo f n := by
  apply le_antisymm
  · exact le_iInf fun n => firstNonnegativeWindowStart_le_upTo f n
  · by_cases hfinite : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t
    · obtain ⟨t, ht, hmin⟩ :=
        exists_earliestNonnegativeWindowStart f hfinite
      have hfirst : firstNonnegativeWindowStart f = t :=
        (firstNonnegativeWindowStart_eq_coe_iff f t).mpr
          ⟨ht, hmin⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (t + 1)
      have hcut : firstNonnegativeWindowStartUpTo f n = t :=
        firstNonnegativeWindowStartUpTo_eq_first_of_le f hfirst hn.le
      calc
        (⨅ m : ℕ, firstNonnegativeWindowStartUpTo f m) ≤
            firstNonnegativeWindowStartUpTo f n := iInf_le _ n
        _ = firstNonnegativeWindowStart f := by rw [hcut, hfirst]
    · have htop : firstNonnegativeWindowStart f = ⊤ := by
        simp [firstNonnegativeWindowStart, hfinite]
      rw [htop]
      exact le_top

/-- Bolthausen's Lemma 2.1 also covers $T=T^\infty$: the unrestricted
first-window time is Borel measurable as a countable infimum of the
finite-horizon times. -/
theorem measurable_firstNonnegativeWindowStart :
    Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStart f) := by
  have hmeas : Measurable (fun f : C(ℝ≥0, ℝ) =>
      ⨅ n : ℕ, firstNonnegativeWindowStartUpTo f n) :=
    Measurable.iInf fun n => measurable_firstNonnegativeWindowStartUpTo n
  convert hmeas using 1
  funext f
  exact firstNonnegativeWindowStart_eq_iInf_upTo f

end ProbabilityTheory
