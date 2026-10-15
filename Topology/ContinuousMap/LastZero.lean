/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The last zero of a continuous path

The public definition and theorems in this file are:

- `ContinuousMap.lastZero`: $g(f)=\sup\{t\in[0,1]:f(t)=0\}$.
- `ContinuousMap.lastZero_apply_eq_zero`: if $f(0)=0$, then $f(g(f))=0$.
- `ContinuousMap.lastZero_lt_top_of_ne_zero`: if $f(0)=0$ and
  $f(1)\ne0$, then $g(f)<1$.
- `ContinuousMap.measurable_lastZero`: $f\mapsto g(f)$ is Borel
  measurable on $C([0,1],\mathbb R)$.
- `ContinuousMap.ne_zero_of_lastZero_lt`: if $g(f)<t\le1$, then $f(t)\ne0$.
- `ContinuousMap.tailAffineTime`: $(a,t)\mapsto a+(1-a)t$ maps
  $[0,1]^2$ to $[0,1]$.
- `ContinuousMap.lastZeroMeanderTransform`:
  $f\mapsto\left(t\mapsto(1-g(f))^{-1/2}
  |f(g(f)+(1-g(f))t)|\right)$ when $g(f)<1$, with the zero path
  used when $g(f)=1$.
- `ContinuousMap.lastZeroMeanderTransform_zero`: if $f(0)=0$,
  the transformed path starts at zero.
- `ContinuousMap.lastZeroMeanderTransform_nonnegative`: the transformed
  path is nonnegative at every time.
- `ContinuousMap.lastZeroMeanderTransform_pos_of_lastZero_lt_top`:
  if $g(f)<1$, then the transformed path is strictly positive at
  every $t\in(0,1]$.
- `ContinuousMap.measurable_lastZeroMeanderTransform`: the terminal
  path transform is measurable on continuous path space.

This is the zero-time functional used by Donald L. Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, Section 3, to describe
Brownian meander through the terminal excursion.
-/

@[expose] public section

open MeasureTheory

namespace ContinuousMap

/-- The last zero of a continuous real path on the unit interval. -/
noncomputable def lastZero (f : C(unitInterval, ℝ)) : unitInterval :=
  sSup {t : unitInterval | f t = 0}

/-- Every zero of the path occurs no later than its last zero. -/
theorem le_lastZero_of_apply_eq_zero (f : C(unitInterval, ℝ))
    {t : unitInterval} (ht : f t = 0) : t ≤ lastZero f :=
  le_sSup ht

/-- The last zero is itself a zero when the path starts at zero. -/
theorem lastZero_apply_eq_zero (f : C(unitInterval, ℝ))
    (hf0 : f 0 = 0) : f (lastZero f) = 0 := by
  have hnonempty : Set.Nonempty {t : unitInterval | f t = 0} :=
    ⟨0, hf0⟩
  have hclosed : IsClosed {t : unitInterval | f t = 0} :=
    isClosed_singleton.preimage f.continuous
  exact IsClosed.sSup_mem hnonempty hclosed

/-- A path ending away from zero has its last zero strictly before one. -/
theorem lastZero_lt_top_of_ne_zero (f : C(unitInterval, ℝ))
    (hf0 : f 0 = 0) (hf1 : f ⊤ ≠ 0) : lastZero f < ⊤ := by
  exact lt_top_iff_ne_top.mpr (fun h =>
    hf1 (h ▸ lastZero_apply_eq_zero f hf0))

/-- The path has no zero after its last zero. -/
theorem ne_zero_of_lastZero_lt (f : C(unitInterval, ℝ))
    {t : unitInterval} (ht : lastZero f < t) : f t ≠ 0 := by
  intro hzero
  exact (not_le_of_gt ht) (le_lastZero_of_apply_eq_zero f hzero)

/-- For a fixed time, the paths whose last zero is at or after that
time form a closed set. -/
theorem isClosed_setOf_le_lastZero (c : unitInterval) :
    IsClosed {f : C(unitInterval, ℝ) | c ≤ lastZero f} := by
  by_cases hc : c = 0
  · subst c
    simp
  have hcpos : 0 < c := lt_of_le_of_ne bot_le (Ne.symm hc)
  let Z : Set (C(unitInterval, ℝ) × unitInterval) :=
    {p | c ≤ p.2 ∧ p.1 p.2 = 0}
  have hZclosed : IsClosed Z :=
    (isClosed_Ici.preimage continuous_snd).inter
      (isClosed_singleton.preimage continuous_eval)
  have himage :
      {f : C(unitInterval, ℝ) | c ≤ lastZero f} =
        Prod.fst '' Z := by
    ext f
    constructor
    · intro hf
      have hne : Set.Nonempty {t : unitInterval | f t = 0} := by
        by_contra hne
        have hempty : {t : unitInterval | f t = 0} = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hne
        have hlast : lastZero f = ⊥ := by simp [lastZero, hempty]
        change (⊥ : unitInterval) < c at hcpos
        exact (not_le_of_gt hcpos) (hlast ▸ hf)
      have hclosed : IsClosed {t : unitInterval | f t = 0} :=
        isClosed_singleton.preimage f.continuous
      have hzero : f (lastZero f) = 0 :=
        IsClosed.sSup_mem hne hclosed
      exact ⟨⟨f, lastZero f⟩, ⟨hf, hzero⟩, rfl⟩
    · rintro ⟨⟨g, t⟩, ⟨hct, ht⟩, rfl⟩
      exact hct.trans (le_lastZero_of_apply_eq_zero g ht)
  rw [himage]
  exact isClosedMap_fst_of_compactSpace Z hZclosed

/-- The last-zero functional is Borel measurable. -/
theorem measurable_lastZero :
    Measurable (lastZero : C(unitInterval, ℝ) → unitInterval) := by
  apply measurable_of_Ici
  intro c
  exact (isClosed_setOf_le_lastZero c).measurableSet

/-- Affine rescaling of the terminal interval `[start, 1]` to the
unit interval. -/
def tailAffineTime (start t : unitInterval) : unitInterval :=
  ⟨(start : ℝ) + (1 - (start : ℝ)) * (t : ℝ), by
    constructor
    · have hs := start.property.1
      have ht := t.property.1
      have hsu := start.property.2
      nlinarith
    · have hs := start.property.1
      have hsu := start.property.2
      have ht := t.property.1
      have htu := t.property.2
      nlinarith⟩

@[simp]
theorem tailAffineTime_zero (start : unitInterval) :
    tailAffineTime start 0 = start := by
  apply Subtype.ext
  simp [tailAffineTime]

@[simp]
theorem tailAffineTime_top (start : unitInterval) :
    tailAffineTime start ⊤ = ⊤ := by
  apply Subtype.ext
  simp [tailAffineTime]

theorem continuous_tailAffineTime (start : unitInterval) :
    Continuous (tailAffineTime start) := by
  have hreal : Continuous
      (fun t : unitInterval => (start : ℝ) + (1 - (start : ℝ)) * (t : ℝ)) := by
    fun_prop
  exact hreal.subtype_mk _

theorem continuous_tailAffineTime_left (t : unitInterval) :
    Continuous (fun start : unitInterval => tailAffineTime start t) := by
  have hreal : Continuous
      (fun start : unitInterval =>
        (start : ℝ) + (1 - (start : ℝ)) * (t : ℝ)) := by
    fun_prop
  exact hreal.subtype_mk _

/-- The terminal Brownian-meander path transform from Iglehart,
Section 3, expressed for an arbitrary continuous path. -/
noncomputable def lastZeroMeanderTransform
    (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  ⟨(fun t => if lastZero f = ⊤ then 0 else
      |f (tailAffineTime (lastZero f) t)| /
        Real.sqrt (1 - (lastZero f : ℝ))), by
    by_cases h : lastZero f = ⊤
    · simpa only [h, ↓reduceIte] using (continuous_const :
        Continuous (fun _ : unitInterval => (0 : ℝ)))
    · simpa only [h, ↓reduceIte, Function.comp_apply] using
        ((continuous_abs.comp (f.continuous.comp
          (continuous_tailAffineTime (lastZero f)))).div_const
            (Real.sqrt (1 - (lastZero f : ℝ))))⟩

/-- The last-zero transform starts at zero when the original path does. -/
theorem lastZeroMeanderTransform_zero
    (f : C(unitInterval, ℝ)) (hf0 : f 0 = 0) :
    lastZeroMeanderTransform f 0 = 0 := by
  by_cases h : lastZero f = ⊤
  · simp [lastZeroMeanderTransform, h]
  · simp [lastZeroMeanderTransform, h, lastZero_apply_eq_zero f hf0]

/-- The transformed path is nonnegative at every time. -/
theorem lastZeroMeanderTransform_nonnegative
    (f : C(unitInterval, ℝ)) (t : unitInterval) :
    0 ≤ lastZeroMeanderTransform f t := by
  unfold lastZeroMeanderTransform
  dsimp
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

/-- After a last zero strictly before one, the rescaled terminal
excursion is strictly positive at each positive time. -/
theorem lastZeroMeanderTransform_pos_of_lastZero_lt_top
    (f : C(unitInterval, ℝ)) (hcut : lastZero f < ⊤)
    {t : unitInterval} (ht : 0 < t) :
    0 < lastZeroMeanderTransform f t := by
  have hcutReal : (lastZero f : ℝ) < 1 := hcut
  have htReal : (0 : ℝ) < t := ht
  have hafter : lastZero f < tailAffineTime (lastZero f) t := by
    change (lastZero f : ℝ) <
      (lastZero f : ℝ) + (1 - (lastZero f : ℝ)) * (t : ℝ)
    nlinarith
  have hnonzero : f (tailAffineTime (lastZero f) t) ≠ 0 :=
    ne_zero_of_lastZero_lt f hafter
  have hdenom : 0 < Real.sqrt (1 - (lastZero f : ℝ)) :=
    Real.sqrt_pos.2 (by linarith)
  change 0 < if lastZero f = ⊤ then 0 else
    |f (tailAffineTime (lastZero f) t)| /
      Real.sqrt (1 - (lastZero f : ℝ))
  simpa [ne_of_lt hcut] using
    (div_pos (abs_pos.2 hnonzero) hdenom)

/-- The terminal-excursion transform is a measurable continuous-path
valued functional. -/
theorem measurable_lastZeroMeanderTransform :
    Measurable (lastZeroMeanderTransform :
      C(unitInterval, ℝ) → C(unitInterval, ℝ)) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  have htime : Measurable
      (fun f : C(unitInterval, ℝ) => tailAffineTime (lastZero f) t) :=
    (continuous_tailAffineTime_left t).measurable.comp measurable_lastZero
  have heval : Measurable
      (fun f : C(unitInterval, ℝ) => f (tailAffineTime (lastZero f) t)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk htime)
  have hdenom : Measurable
      (fun f : C(unitInterval, ℝ) =>
        Real.sqrt (1 - (lastZero f : ℝ))) := by
    exact Real.continuous_sqrt.measurable.comp
      (measurable_const.sub
        (continuous_subtype_val.measurable.comp measurable_lastZero))
  change Measurable (fun f : C(unitInterval, ℝ) =>
    if lastZero f = ⊤ then 0 else
      |f (tailAffineTime (lastZero f) t)| /
        Real.sqrt (1 - (lastZero f : ℝ)))
  have hset : MeasurableSet
      {f : C(unitInterval, ℝ) | lastZero f = ⊤} :=
    measurable_lastZero (measurableSet_singleton ⊤)
  exact Measurable.ite hset measurable_const
    ((continuous_abs.measurable.comp heval).div hdenom)

end ContinuousMap

end
