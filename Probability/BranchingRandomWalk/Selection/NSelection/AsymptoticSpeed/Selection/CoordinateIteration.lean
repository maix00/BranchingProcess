/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Coordinate-indexed block arrays

For an index type \(I\), `Configuration I` is \(I \to \mathbb R\),
`iterateTransition` applies a time-dependent one-step map, and
`iteratedFrontierArray` is the negative value of a specified coordinate
after iterating from the zero configuration.

## Public declarations

The declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed` are:

- `Configuration`, `translateConfiguration`, and `SpatiallyOrdered` define
  configurations, common translation, and a distinguished minimum.
- `iterateTransition` defines \(X_{s,0}=x\) and
  \(X_{s,n+1}=F_{s+n}(X_{s,n})\). `iterateTransition_add` gives
  \(X_{s,k+\ell}(x)=X_{s+k,\ell}(X_{s,k}(x))\).
- `iterateTransition_monotone` states that \(x\le y\) coordinatewise implies
  \(X_{s,n}(x)\le X_{s,n}(y)\); `iterateTransition_translate` states
  \(X_{s,n}(x+c)=X_{s,n}(x)+c\) under one-step translation covariance; and
  `iterateTransition_spatiallyOrdered` propagates
  \(X_{s,n}(x)_{first}\le X_{s,n}(x)_i\) from the one-step minimum property.
- `iteratedFrontier` evaluates the distinguished coordinate of \(X_{s,n}\)
  from zero; `iteratedFrontierArray` is its negative.
  `iteratedFrontierArray_subadditive` states
  \(A(s,k+\ell)\le A(s,k)+A(s+k,\ell)\) when each transition is
  coordinatewise monotone, translation covariant, and returns a configuration
  whose distinguished coordinate is minimal.
- `measurable_iterateTransition` states measurability of
  \(X_{s,n}(\omega,x(\omega))\) when each time-indexed transition is jointly
  measurable and the initial configuration is measurable.
  `measurable_iteratedFrontierArray` derives measurability of the array from
  joint measurability of the one-step transition.

The iteration and subadditivity interface is deterministic and does not
assume a probability law on the environment.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

section RankedArray

variable {N Ω : Type*}

/-- A configuration of `N` ranked particles on the real line. -/
abbrev Configuration (N : Type*) := N → ℝ

/-- Translation of a ranked particle configuration. -/
def translateConfiguration {N : Type*} (x : Configuration N) (c : ℝ) :
    Configuration N := fun i => x i + c

/-- A configuration is in spatial order when its distinguished first particle
is a minimum. -/
def SpatiallyOrdered {N : Type*} (x : Configuration N)
    (first : N) : Prop :=
  ∀ i, x first ≤ x i

/-- Iterate a time-dependent ranked one-step transition. -/
def iterateTransition {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (x : Configuration N) : Configuration N :=
  match length with
  | 0 => x
  | k + 1 => step (start + k) ω (iterateTransition step start k ω x)

theorem iterateTransition_add
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (start k l : ℕ) (ω : Ω) (x : Configuration N) :
    iterateTransition step start (k + l) ω x =
      iterateTransition step (start + k) l ω
        (iterateTransition step start k ω x) := by
  induction l with
  | zero => simp [iterateTransition]
  | succ l ih =>
      rw [Nat.add_succ, iterateTransition, iterateTransition, ih]
      congr 1
      omega

theorem iterateTransition_monotone
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t ω x y, (∀ i, x i ≤ y i) → ∀ i, step t ω x i ≤ step t ω y i)
    (start length : ℕ) (ω : Ω) {x y : Configuration N}
    (hxy : ∀ i, x i ≤ y i) :
    ∀ i, iterateTransition step start length ω x i ≤
      iterateTransition step start length ω y i := by
  induction length generalizing start x y with
  | zero => exact hxy
  | succ n ih =>
      intro i
      simp only [iterateTransition]
      apply hstep
      exact ih (start := start) hxy

theorem iterateTransition_translate
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (hshift : ∀ t ω x c,
      step t ω (translateConfiguration x c) =
        translateConfiguration (step t ω x) c)
    (start length : ℕ) (ω : Ω) (x : Configuration N) (c : ℝ) :
    iterateTransition step start length ω (translateConfiguration x c) =
      translateConfiguration (iterateTransition step start length ω x) c := by
  induction length generalizing start x with
  | zero => rfl
  | succ n ih =>
      simp only [iterateTransition]
      rw [ih, hshift]

theorem iterateTransition_spatiallyOrdered
    {N Ω : Type*}
    (step : ℕ → Ω → Configuration N → Configuration N)
    (first : N)
    (hordered : ∀ t ω x, SpatiallyOrdered (step t ω x) first)
    (start length : ℕ) (ω : Ω) (x : Configuration N)
    (hx : SpatiallyOrdered x first) :
    SpatiallyOrdered (iterateTransition step start length ω x) first := by
  induction length generalizing start x with
  | zero => exact hx
  | succ n _ =>
      rw [iterateTransition]
      exact hordered (start + n) ω
        (iterateTransition step start n ω x)

/-- The specified coordinate after iterating the transition from `start` for
`length` generations, from the all-zero configuration. -/
def iteratedFrontier {N Ω : Type*}
    (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (first : N) : ℝ :=
  iterateTransition step start length ω (fun _ => 0) first

/-- Negative displacement of the specified coordinate after a block. -/
def iteratedFrontierArray {N Ω : Type*}
    (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (first : N) : ℝ :=
  -iteratedFrontier step start length ω first

/-- The coordinate-indexed block array is pathwise subadditive whenever the
one-step transition is monotone in every input coordinate, commutes with
translations, and returns the configuration in spatial order. This is the
deterministic core of the restart comparison; an actual selection kernel must
still discharge these three hypotheses. -/
theorem iteratedFrontierArray_subadditive
    {N Ω : Type*}
    (step : ℕ → Ω → Configuration N → Configuration N)
    (first : N)
    (hstepMono : ∀ t ω x y, (∀ i, x i ≤ y i) →
      ∀ i, step t ω x i ≤ step t ω y i)
    (hstepShift : ∀ t ω x c,
      step t ω (translateConfiguration x c) =
        translateConfiguration (step t ω x) c)
    (hstepOrdered : ∀ t ω x, SpatiallyOrdered (step t ω x) first) :
    ∀ start k l ω,
      iteratedFrontierArray step start (k + l) ω first ≤
        iteratedFrontierArray step start k ω first +
          iteratedFrontierArray step (start + k) l ω first := by
  intro start k l ω
  have hordered : ∀ m, SpatiallyOrdered
      (iterateTransition step m k ω (fun _ => 0)) first := by
    intro m
    exact iterateTransition_spatiallyOrdered step first hstepOrdered m k ω
      (fun _ => 0) (fun i => by simp)
  have hfront : ∀ i,
      iterateTransition step start k ω (fun _ => 0) first ≤
        iterateTransition step start k ω (fun _ => 0) i :=
    (hordered start)
  have hconst : ∀ i,
      (fun _ : N => iterateTransition step start k ω (fun _ => 0) first) i ≤
        iterateTransition step start k ω (fun _ => 0) i := by
    intro i
    exact hfront i
  have hfuture := iterateTransition_monotone step hstepMono
    (start + k) l ω hconst
  have hshift := iterateTransition_translate step hstepShift
    (start + k) l ω (fun _ : N => 0)
    (iterateTransition step start k ω (fun _ => 0) first)
  have hcomp := iterateTransition_add step start k l ω (fun _ => 0)
  have hcoord :
      iteratedFrontier step start (k + l) ω first ≥
        iteratedFrontier step start k ω first +
          iteratedFrontier step (start + k) l ω first := by
    change iterateTransition step start (k + l) ω (fun _ => 0) first ≥ _
    rw [hcomp]
    have hfutureFirst := hfuture first
    have hconst_eq :
        (fun _ : N => iterateTransition step start k ω (fun _ => 0) first) =
          translateConfiguration (fun _ => 0)
            (iterateTransition step start k ω (fun _ => 0) first) := by
      funext i
      simp [translateConfiguration]
    rw [hconst_eq, hshift] at hfutureFirst
    have hfutureFirst' :
        iteratedFrontier step start k ω first +
          iteratedFrontier step (start + k) l ω first ≤
        iterateTransition step (start + k) l ω
          (iterateTransition step start k ω (fun _ => 0)) first := by
      simpa [iteratedFrontier, translateConfiguration, add_comm] using hfutureFirst
    exact hfutureFirst'
  unfold iteratedFrontierArray
  linarith

/-- Joint measurability of iterated transitions follows by induction from a
jointly measurable one-step map. -/
theorem measurable_iterateTransition
    {N Ω : Type*} [MeasurableSpace Ω]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t, Measurable fun p : Ω × Configuration N => step t p.1 p.2)
    (start length : ℕ) (initial : Ω → Configuration N) (hinitial : Measurable initial) :
    Measurable fun ω => iterateTransition step start length ω (initial ω) := by
  induction length generalizing start initial with
  | zero => simpa [iterateTransition] using hinitial
  | succ n ih =>
      simp only [iterateTransition]
      exact (hstep (start + n)).comp (measurable_id.prodMk
        (ih (start := start) initial hinitial))

/-- Measurability of the coordinate-indexed block array follows from
measurability of the one-step transition. -/
theorem measurable_iteratedFrontierArray
    {N Ω : Type*} [MeasurableSpace Ω]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t, Measurable fun p : Ω × Configuration N => step t p.1 p.2)
    (start length : ℕ) (first : N) :
    Measurable fun ω => iteratedFrontierArray step start length ω first := by
  unfold iteratedFrontierArray iteratedFrontier
  exact measurable_neg.comp <| (measurable_pi_apply first).comp <|
    measurable_iterateTransition step hstep start length (fun _ _ => 0)
      measurable_const

end RankedArray


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
