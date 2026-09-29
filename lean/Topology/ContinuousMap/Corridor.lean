module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Interval corridors in continuous path space

The set of real continuous paths whose whole range lies in an open interval
is an open ball for the uniform metric.  This deterministic fact is the
path-space interface needed by functional limit theorems and Portmanteau
arguments; it has no random-walk-specific content.
-/

open Set

namespace ContinuousMap

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

/-- Continuous paths whose range is contained in an open real interval. -/
def rangeInOpenInterval (lower upper : ℝ) : Set C(T, ℝ) :=
  {path | Set.range path ⊆ Set.Ioo lower upper}

/-- Continuous paths whose range is contained in a closed real interval. -/
def rangeInClosedInterval (lower upper : ℝ) : Set C(T, ℝ) :=
  {path | Set.range path ⊆ Set.Icc lower upper}

omit [CompactSpace T] in
theorem mem_rangeInOpenInterval_iff {lower upper : ℝ} {path : C(T, ℝ)} :
    path ∈ rangeInOpenInterval lower upper ↔
      ∀ t, lower < path t ∧ path t < upper := by
  constructor
  · intro hpath t
    exact hpath ⟨t, rfl⟩
  · intro hpath x hx
    obtain ⟨t, rfl⟩ := hx
    exact hpath t

/-- A nonempty horizontal corridor is exactly the uniform open ball centered
at its midpoint with radius half its width. -/
theorem rangeInOpenInterval_eq_ball {lower upper : ℝ} (h : lower < upper) :
    rangeInOpenInterval (T := T) lower upper =
      Metric.ball (ContinuousMap.const T ((lower + upper) / 2))
        ((upper - lower) / 2) := by
  ext path
  rw [mem_rangeInOpenInterval_iff, Metric.mem_ball,
    ContinuousMap.dist_lt_iff (by linarith)]
  constructor
  · intro hpath t
    rw [Real.dist_eq, abs_lt]
    dsimp
    constructor <;> linarith [(hpath t).1, (hpath t).2]
  · intro hpath t
    have ht := hpath t
    rw [Real.dist_eq, abs_lt] at ht
    dsimp at ht
    constructor <;> linarith

theorem isOpen_rangeInOpenInterval {lower upper : ℝ} (h : lower < upper) :
    IsOpen (rangeInOpenInterval (T := T) lower upper) := by
  rw [rangeInOpenInterval_eq_ball h]
  exact Metric.isOpen_ball

omit [CompactSpace T] in
theorem mem_rangeInClosedInterval_iff {lower upper : ℝ} {path : C(T, ℝ)} :
    path ∈ rangeInClosedInterval lower upper ↔
      ∀ t, lower ≤ path t ∧ path t ≤ upper := by
  constructor
  · intro hpath t
    exact hpath ⟨t, rfl⟩
  · intro hpath x hx
    obtain ⟨t, rfl⟩ := hx
    exact hpath t

/-- On a nonempty time domain, a closed horizontal corridor is exactly the
uniform closed ball centered at its midpoint with radius half its width. -/
theorem rangeInClosedInterval_eq_closedBall [Nonempty T]
    (lower upper : ℝ) :
    rangeInClosedInterval (T := T) lower upper =
      Metric.closedBall (ContinuousMap.const T ((lower + upper) / 2))
        ((upper - lower) / 2) := by
  ext path
  rw [mem_rangeInClosedInterval_iff, Metric.mem_closedBall,
    ContinuousMap.dist_le_iff_of_nonempty]
  constructor
  · intro hpath t
    rw [Real.dist_eq, abs_le]
    dsimp
    constructor <;> linarith [(hpath t).1, (hpath t).2]
  · intro hpath t
    have ht := hpath t
    rw [Real.dist_eq, abs_le] at ht
    dsimp at ht
    constructor <;> linarith

theorem isClosed_rangeInClosedInterval [Nonempty T]
    (lower upper : ℝ) :
    IsClosed (rangeInClosedInterval (T := T) lower upper) := by
  rw [rangeInClosedInterval_eq_closedBall lower upper]
  exact Metric.isClosed_closedBall

theorem measurableSet_rangeInOpenInterval
    [MeasurableSpace (ContinuousMap T ℝ)]
    [BorelSpace (ContinuousMap T ℝ)]
    {lower upper : ℝ} (h : lower < upper) :
    MeasurableSet (rangeInOpenInterval (T := T) lower upper) :=
  (isOpen_rangeInOpenInterval h).measurableSet

theorem measurableSet_rangeInClosedInterval [Nonempty T]
    [MeasurableSpace (ContinuousMap T ℝ)]
    [BorelSpace (ContinuousMap T ℝ)]
    (lower upper : ℝ) :
    MeasurableSet (rangeInClosedInterval (T := T) lower upper) :=
  (isClosed_rangeInClosedInterval lower upper).measurableSet

end ContinuousMap
