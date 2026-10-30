/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of continuous-path first passage

## Public declarations

- `ProbabilityTheory.isClosed_hasPassageBefore` and
  `ProbabilityTheory.isClosed_hasPassageAboveBefore` state that the sets of
  paths hitting a closed half-line by a fixed time are closed in continuous-
  path space.
- `ProbabilityTheory.measurable_firstPassageBelow` and
  `ProbabilityTheory.measurable_firstPassageAbove` state that the lower and
  upper first-passage maps into $[0,\infty]$ are Borel measurable.
- `ProbabilityTheory.measurable_firstPassageBelow_pair` states that the lower
  first-passage map is jointly Borel measurable in the path and the level.

The proofs use compactness of the bounded time interval to project the closed
path-time hitting set, then identify the sublevel sets of the passage-time maps.
-/

@[expose] public section

open scoped NNReal Classical

namespace ProbabilityTheory

/-- The paths that reach the closed sublevel set by a fixed time form a
closed subset of continuous-path space. The time interval is compact,
so projection of the closed path-time hitting set is closed. -/
theorem isClosed_hasPassageBefore (t : ℝ≥0) (a : ℝ) :
    IsClosed {f : C(ℝ≥0, ℝ) | ∃ u : ℝ≥0, u ≤ t ∧ f u ≤ a} := by
  let K := Set.Icc (0 : ℝ≥0) t
  let E : Set (C(ℝ≥0, ℝ) × K) := {p | p.1 (p.2 : ℝ≥0) ≤ a}
  have hE : IsClosed E := by
    have hcont : Continuous (fun p : C(ℝ≥0, ℝ) × K => p.1 (p.2 : ℝ≥0)) := by
      fun_prop
    exact isClosed_Iic.preimage hcont
  have hclosed : IsClosed ((Prod.fst : C(ℝ≥0, ℝ) × K → C(ℝ≥0, ℝ)) '' E) :=
    isClosedMap_fst_of_compactSpace E hE
  convert hclosed using 1
  ext f
  constructor
  · rintro ⟨u, hut, hfa⟩
    exact ⟨(f, ⟨u, ⟨bot_le, hut⟩⟩), hfa, rfl⟩
  · rintro ⟨⟨g, u⟩, hga, hgf⟩
    change g = f at hgf
    subst g
    exact ⟨u, u.2.2, hga⟩

/-- The continuous paths that reach the closed upper half-line by a
fixed time form a closed set. -/
theorem isClosed_hasPassageAboveBefore (t : ℝ≥0) (a : ℝ) :
    IsClosed {f : C(ℝ≥0, ℝ) | ∃ u : ℝ≥0, u ≤ t ∧ a ≤ f u} := by
  let K := Set.Icc (0 : ℝ≥0) t
  let E : Set (C(ℝ≥0, ℝ) × K) := {p | a ≤ p.1 (p.2 : ℝ≥0)}
  have hE : IsClosed E := by
    have hcont : Continuous (fun p : C(ℝ≥0, ℝ) × K => p.1 (p.2 : ℝ≥0)) := by
      fun_prop
    exact isClosed_Ici.preimage hcont
  have hclosed : IsClosed ((Prod.fst : C(ℝ≥0, ℝ) × K → C(ℝ≥0, ℝ)) '' E) :=
    isClosedMap_fst_of_compactSpace E hE
  convert hclosed using 1
  ext f
  constructor
  · rintro ⟨u, hut, hfa⟩
    exact ⟨(f, ⟨u, ⟨bot_le, hut⟩⟩), hfa, rfl⟩
  · rintro ⟨⟨g, u⟩, hga, hgf⟩
    change g = f at hgf
    subst g
    exact ⟨u, u.2.2, hga⟩

/-- The upper first-passage time is Borel measurable; its sublevel events
are the closed upper-level hitting events. -/
theorem measurable_firstPassageAbove (a : ℝ) :
    Measurable (fun f : C(ℝ≥0, ℝ) => firstPassageAbove f a) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe t =>
      have hset : {f : C(ℝ≥0, ℝ) | firstPassageAbove f a ≤ t} =
          {f | ∃ u : ℝ≥0, u ≤ t ∧ a ≤ f u} := by
        ext f
        exact firstPassageAbove_le_iff f a t
      simpa only [Set.preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        (hset ▸ (isClosed_hasPassageAboveBefore t a).measurableSet)

/-- The first-passage time of a continuous path is Borel measurable.
The sublevel event at time $t$ is the closed hitting-by-$t$ event. -/
theorem measurable_firstPassageBelow (a : ℝ) :
    Measurable (fun f : C(ℝ≥0, ℝ) => firstPassageBelow f a) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe t =>
      have hset : {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ t} =
          {f | ∃ u : ℝ≥0, u ≤ t ∧ f u ≤ a} := by
        ext f
        exact firstPassageBelow_le_iff f a t
      simpa only [Set.preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        (hset ▸ (isClosed_hasPassageBefore t a).measurableSet)

/-- The set of path-level pairs for which the path reaches the level's
closed sublevel by time `t` is closed. -/
theorem isClosed_hasPassageBelowBefore_pair (t : ℝ≥0) :
    IsClosed {p : C(ℝ≥0, ℝ) × ℝ |
      ∃ u : ℝ≥0, u ≤ t ∧ p.1 u ≤ p.2} := by
  let K := Set.Icc (0 : ℝ≥0) t
  let E : Set ((C(ℝ≥0, ℝ) × ℝ) × K) :=
    {p | p.1.1 (p.2 : ℝ≥0) ≤ p.1.2}
  have hE : IsClosed E := by
    have hpath : Continuous
        (fun p : (C(ℝ≥0, ℝ) × ℝ) × K => p.1.1 (p.2 : ℝ≥0)) := by
      fun_prop
    have hlevel : Continuous
        (fun p : (C(ℝ≥0, ℝ) × ℝ) × K => p.1.2) :=
      continuous_snd.comp continuous_fst
    exact isClosed_le hpath hlevel
  have hclosed : IsClosed
      ((Prod.fst : (C(ℝ≥0, ℝ) × ℝ) × K → C(ℝ≥0, ℝ) × ℝ) '' E) :=
    isClosedMap_fst_of_compactSpace E hE
  have himage :
      (Prod.fst : (C(ℝ≥0, ℝ) × ℝ) × K → C(ℝ≥0, ℝ) × ℝ) '' E =
        {p | ∃ u : ℝ≥0, u ≤ t ∧ p.1 u ≤ p.2} := by
    ext p
    constructor
    · rintro ⟨⟨⟨f, a⟩, u⟩, hu, rfl⟩
      exact ⟨u, u.2.2, hu⟩
    · rintro ⟨u, hut, hlevel⟩
      exact ⟨(p, ⟨u, ⟨bot_le, hut⟩⟩), hlevel, rfl⟩
  exact himage ▸ hclosed

/-- The lower first-passage time is jointly Borel measurable in the path
and the level. Its sublevel sets are projections of closed hitting sets over
compact time intervals. -/
theorem measurable_firstPassageBelow_pair :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ => firstPassageBelow p.1 p.2) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe t =>
      have hset :
          (fun p : C(ℝ≥0, ℝ) × ℝ => firstPassageBelow p.1 p.2) ⁻¹' Set.Iic t =
            {p | ∃ u : ℝ≥0, u ≤ t ∧ p.1 u ≤ p.2} := by
        ext p
        exact firstPassageBelow_le_iff p.1 p.2 t
      rw [hset]
      exact (isClosed_hasPassageBelowBefore_pair t).measurableSet

end ProbabilityTheory

end
