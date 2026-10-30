/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.CompactOpen

/-!
# Continuous transformations of paths

## Public declarations

- `ProbabilityTheory.freezeAfter` maps $f$ to $u\mapsto f(\min(u,r))$.
  `measurable_freezeAfter`, `measurable_freezeAfter_pair`, and
  `continuous_freezeAfter` give its fixed-time measurability, joint
  measurability, and joint continuity.
- `ProbabilityTheory.shiftToZero` maps $f$ to $u\mapsto f(r+u)-f(r)$.
  `measurable_shiftToZero` and `continuous_shiftToZero` give the joint
  measurability and continuity of this rebasing operation.
- `ProbabilityTheory.shiftPath` maps $f$ to $u\mapsto f(r+u)$.
  `continuous_shiftPath` and `measurable_shiftPath` give joint continuity
  and measurability of time translation.

These deterministic maps act on continuous path space and do not require a
stochastic process.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- Freeze a continuous path at the value it has at time `r`. -/
noncomputable def freezeAfter (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun u => f (min u r), by fun_prop⟩

/-- Freezing a continuous path is jointly continuous in path and time. -/
theorem continuous_freezeAfter :
    Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => freezeAfter p.1 p.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.min (continuous_snd.comp continuous_fst)))

/-- Joint measurability of the stopped past path. -/
theorem measurable_freezeAfter_pair :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => freezeAfter p.1 p.2) :=
  continuous_freezeAfter.measurable

/-- Rebase a continuous path at time `r`, with initial value zero. -/
noncomputable def shiftToZero (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun u => f (r + u) - f r, by fun_prop⟩

/-- The future increment path is jointly measurable in its path and
its starting time. -/
theorem measurable_shiftToZero :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => shiftToZero p.1 p.2) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  exact (continuous_eval.comp
    (continuous_fst.prodMk (continuous_snd.add continuous_const))).measurable.sub
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd)).measurable

/-- Shifting a continuous path by a variable starting time is jointly
continuous for the compact-open topology. -/
theorem continuous_shiftToZero :
    Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => shiftToZero p.1 p.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hpath : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.1) :=
    continuous_fst.comp continuous_fst
  have htime : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.2 + p.2) :=
    (continuous_snd.comp continuous_fst).add continuous_snd
  have hfirst : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.1 (p.1.2 + p.2)) :=
    continuous_eval.comp (hpath.prodMk htime)
  have hbase : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.1 p.1.2) :=
    continuous_eval.comp
      (hpath.prodMk (continuous_snd.comp continuous_fst))
  exact hfirst.sub hbase

/-- Translate the time origin of a continuous path to `r`. -/
noncomputable def shiftPath (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun u => f (r + u), by fun_prop⟩

/-- Time translation of continuous paths is jointly continuous for
the compact-open topology. -/
theorem continuous_shiftPath :
    Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => shiftPath p.1 p.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).add continuous_snd))

/-- Joint measurability of time translation of continuous paths. -/
theorem measurable_shiftPath :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => shiftPath p.1 p.2) :=
  continuous_shiftPath.measurable

/-- Freezing a continuous path at a fixed time is measurable. -/
theorem measurable_freezeAfter (r : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => freezeAfter f r) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  exact ContinuousMap.measurable_eval (min u r)

end ProbabilityTheory
