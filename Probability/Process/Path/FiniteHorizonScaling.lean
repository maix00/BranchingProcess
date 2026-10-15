/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FiniteHorizon
public import Probability.Process.Path.UnitInterval

/-!
# Rescaling a unit-time continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.unitTimeOfFiniteTime`: the map $t\mapsto t/s$
  from $[0,s]$ into $[0,1]$ for $s>0$.
- `ProbabilityTheory.continuous_unitTimeOfFiniteTime`: this time map
  is continuous.
- `ProbabilityTheory.restrictPathToUnitInterval`: the restriction of a
  whole-time path to the real unit interval.
- `ProbabilityTheory.continuous_restrictPathToUnitInterval`: this
  restriction is continuous.
- `ProbabilityTheory.unitIntervalPathOfNNReal`: reparametrization from
  $C([0,1]_{\mathbb R_{\ge0}},\mathbb R)$ to
  $C([0,1]_{\mathbb R},\mathbb R)$.
- `ProbabilityTheory.unitIntervalTimeAsNNRealIcc`: the corresponding
  coordinate map between the two unit intervals.
- `ProbabilityTheory.continuous_unitIntervalTimeAsNNRealIcc` and
  `ProbabilityTheory.continuous_unitIntervalPathOfNNReal`: continuity
  of these coordinate changes.
- `ProbabilityTheory.restrictPathToUnitInterval_eq`: compatibility of
  the two unit-interval restrictions.
- `ProbabilityTheory.rescaleUnitPath`: for $s>0$ and $a\in\mathbb R$,
  the map $g\mapsto(t\mapsto a g(t/s))$ from
  $C([0,1],\mathbb R)$ to $C([0,s],\mathbb R)$.
- `ProbabilityTheory.continuous_rescaleUnitPath`: this rescaling is
  continuous in the compact-open topologies.

The rescaling is the finite-horizon operation used to transfer the
unit-time Donsker principle to the path law $Q_n\Pi_s^{-1}$ in
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Section 3, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- Rescale a time in $[0,s]$ to a time in the unit interval. -/
noncomputable def unitTimeOfFiniteTime (s : ℝ≥0) (hs : 0 < s)
    (t : Set.Icc (0 : ℝ≥0) s) : unitInterval :=
  ⟨(t.1 : ℝ) / s, by
    constructor
    · exact div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    · exact (div_le_one (NNReal.coe_pos.mpr hs)).mpr
        (NNReal.coe_le_coe.mpr t.property.2)⟩

theorem continuous_unitTimeOfFiniteTime (s : ℝ≥0) (hs : 0 < s) :
    Continuous (unitTimeOfFiniteTime s hs) := by
  exact Continuous.subtype_mk
    ((NNReal.continuous_coe.comp continuous_subtype_val).div_const s) _

/-- Restrict a whole-time path to the real unit interval. -/
noncomputable def restrictPathToUnitInterval (f : C(ℝ≥0, ℝ)) :
    C(unitInterval, ℝ) :=
  ⟨fun t => f (UnitInterval.toNNReal t),
    f.continuous.comp UnitInterval.continuous_toNNReal⟩

/-- Restriction to the real unit interval is continuous. -/
theorem continuous_restrictPathToUnitInterval :
    Continuous restrictPathToUnitInterval := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    (continuous_fst.prodMk
      (UnitInterval.continuous_toNNReal.comp continuous_snd))

noncomputable def unitIntervalTimeAsNNRealIcc
    (t : unitInterval) : Set.Icc (0 : ℝ≥0) 1 :=
  ⟨UnitInterval.toNNReal t,
    ⟨(UnitInterval.toNNReal t).property,
      UnitInterval.toNNReal_le_one t⟩⟩

theorem continuous_unitIntervalTimeAsNNRealIcc :
    Continuous unitIntervalTimeAsNNRealIcc :=
  Continuous.subtype_mk UnitInterval.continuous_toNNReal _

/-- Change the unit-time coordinate from nonnegative real time to real
time without changing path values. -/
noncomputable def unitIntervalPathOfNNReal
    (f : C(Set.Icc (0 : ℝ≥0) 1, ℝ)) : C(unitInterval, ℝ) :=
  ⟨fun t => f (unitIntervalTimeAsNNRealIcc t),
    f.continuous.comp continuous_unitIntervalTimeAsNNRealIcc⟩

/-- The unit-time change of coordinate is continuous in the path. -/
theorem continuous_unitIntervalPathOfNNReal :
    Continuous unitIntervalPathOfNNReal := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    (continuous_fst.prodMk
      (continuous_unitIntervalTimeAsNNRealIcc.comp continuous_snd))

/-- Restriction through nonnegative real time agrees with direct
restriction to the real unit interval. -/
theorem restrictPathToUnitInterval_eq (f : C(ℝ≥0, ℝ)) :
    restrictPathToUnitInterval f =
      unitIntervalPathOfNNReal (restrictPathTo 1 f) := by
  ext t
  rfl

/-- Stretch a unit-time path to $[0,s]$ and multiply its values by `a`. -/
noncomputable def rescaleUnitPath (s : ℝ≥0) (hs : 0 < s)
    (a : ℝ) (f : C(unitInterval, ℝ)) :
    C(Set.Icc (0 : ℝ≥0) s, ℝ) :=
  ⟨fun t => a * f (unitTimeOfFiniteTime s hs t),
    continuous_const.mul (f.continuous.comp
      (continuous_unitTimeOfFiniteTime s hs))⟩

/-- Rescaling a unit-time path is continuous in the path argument. -/
theorem continuous_rescaleUnitPath (s : ℝ≥0) (hs : 0 < s) (a : ℝ) :
    Continuous (rescaleUnitPath s hs a) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_const.mul
    (continuous_eval.comp
      (continuous_fst.prodMk
        ((continuous_unitTimeOfFiniteTime s hs).comp continuous_snd)))

end ProbabilityTheory

end
