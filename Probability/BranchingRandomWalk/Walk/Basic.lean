import Probability.BranchingRandomWalk.Basic
import Combinatorics.BranchingWalk.Walk.Basic

/-!
# Random walks as one-branch branching random walks

A random walk has one fixed initial position and a probability law on its
increment sequence.  Mapping every increment sequence to the singleton-slot
walk gives its canonical realization as a branching random walk.  Keeping the
increment law in the structure rules out missing edges by construction.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A single-root random walk, represented by its fixed initial position and
the joint law of its increment sequence.  Independence or identical
distribution are properties of `incrementLaw`, rather than fields forced by
the basic definition. -/
structure RandomWalk (Mark Position : Type*)
    [MeasurableSpace Mark] where
  initial : Position
  incrementLaw : Measure (ℕ → Mark)
  prob : IsProbabilityMeasure incrementLaw

namespace RandomWalk

instance {Mark Position : Type*} [MeasurableSpace Mark]
    (walk : RandomWalk Mark Position) :
    IsProbabilityMeasure walk.incrementLaw := walk.prob

/-- Encoding an increment sequence as its singleton-slot branching walk is
measurable. -/
theorem measurable_ofIncrements
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) :
    Measurable (Walk.ofIncrements initial : (ℕ → Mark) → Walk Mark Position) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  apply ((measurable_pi_iff.mpr fun _ : PUnit =>
    measurable_pi_iff.mpr fun u =>
      measurable_pi_iff.mpr fun _ : PUnit =>
        measurable_option_some.comp (measurable_pi_apply u.length)).prodMk
      (measurable_pi_iff.mpr fun _ : PUnit => measurable_const)) ht

/-- The canonical realization of a random walk as a singleton-slot branching
random walk. -/
noncomputable def toBranchingRandomWalk
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) :
    BranchingRandomWalk PUnit Mark Position := by
  let _ : IsProbabilityMeasure walk.incrementLaw := walk.prob
  exact
    ⟨walk.incrementLaw.map (Walk.ofIncrements walk.initial), by
      infer_instance⟩

@[simp] theorem toBranchingRandomWalk_law
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) :
    walk.toBranchingRandomWalk.law =
      walk.incrementLaw.map (Walk.ofIncrements walk.initial) := rfl

/-- Position at time `n`, as a random variable on the increment sample space. -/
def positionAt {Mark Position : Type*} [MeasurableSpace Mark]
    [AddCommMonoid Position]
    (d : Mark → Position) (walk : RandomWalk Mark Position)
    (n : ℕ) (increment : ℕ → Mark) : Position :=
  walk.initial + ∑ k ∈ Finset.range n, d (increment k)

/-- The position viewed with mathlib's process convention
`Time → Sample → State`.  The canonical sample space is the increment path
space `ℕ → Mark`. -/
def process {Mark Position : Type*} [MeasurableSpace Mark]
    [AddCommMonoid Position]
    (d : Mark → Position) (walk : RandomWalk Mark Position) :
    ℕ → (ℕ → Mark) → Position :=
  walk.positionAt d

@[simp] theorem process_apply
    {Mark Position : Type*} [MeasurableSpace Mark]
    [AddCommMonoid Position]
    (d : Mark → Position) (walk : RandomWalk Mark Position)
    (n : ℕ) (increment : ℕ → Mark) :
    walk.process d n increment = walk.positionAt d n increment :=
  rfl

theorem measurable_process
    {Mark Position : Type*} [MeasurableSpace Mark]
    [MeasurableSpace Position] [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d)
    (walk : RandomWalk Mark Position) (n : ℕ) :
    Measurable (walk.process d n) := by
  simp only [process]
  exact measurable_const.add
    (Finset.measurable_sum (Finset.range n)
      (fun k _ => hd.comp (measurable_pi_apply k)))

theorem process_succ
    {Mark Position : Type*} [MeasurableSpace Mark]
    [AddCommMonoid Position]
    (d : Mark → Position) (walk : RandomWalk Mark Position)
    (n : ℕ) (increment : ℕ → Mark) :
    walk.process d (n + 1) increment =
      walk.process d n increment + d (increment n) := by
  simp [process, positionAt, Finset.sum_range_succ, add_assoc]

theorem branchingPosition_ofIncrements
    {Mark Position : Type*} [MeasurableSpace Mark] [AddCommMonoid Position]
    (d : Mark → Position) (walk : RandomWalk Mark Position)
    (n : ℕ) (increment : ℕ → Mark) :
    (Walk.ofIncrements walk.initial increment).position d PUnit.unit
        (Walk.lineNode n) =
      walk.positionAt d n increment := by
  exact Walk.position_lineNode d walk.initial increment n

/-- A singleton-slot branching random walk comes from a random walk when its
law has a canonical increment-path realization.  This condition excludes
extinction along the unique slot, which an arbitrary singleton-slot
branching random walk may still allow. -/
def IsIncrementPathRealization
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (branchingWalk : BranchingRandomWalk PUnit Mark Position) : Prop :=
  ∃ walk : RandomWalk Mark Position,
    walk.toBranchingRandomWalk.law = branchingWalk.law

/-- Recover a random-walk realization from a singleton-slot branching random
walk known to have an increment-path realization. -/
noncomputable def ofBranchingRandomWalk
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (branchingWalk : BranchingRandomWalk PUnit Mark Position)
    (h : IsIncrementPathRealization branchingWalk) :
    RandomWalk Mark Position :=
  h.choose

theorem toBranchingRandomWalk_ofBranchingRandomWalk_law
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (branchingWalk : BranchingRandomWalk PUnit Mark Position)
    (h : IsIncrementPathRealization branchingWalk) :
    (ofBranchingRandomWalk branchingWalk h).toBranchingRandomWalk.law =
      branchingWalk.law :=
  h.choose_spec

theorem isIncrementPathRealization_toBranchingRandomWalk
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) :
    IsIncrementPathRealization walk.toBranchingRandomWalk :=
  ⟨walk, rfl⟩

end RandomWalk

end ProbabilityTheory.BranchingRandomWalk
