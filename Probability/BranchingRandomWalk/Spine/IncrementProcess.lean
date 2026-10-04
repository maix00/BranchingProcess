/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.TiltedLaw
public import Combinatorics.BranchingWalk.Walk.Path.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The independent tilted increment process

Under boundary normalization the integrated tilted potential law is a
probability measure.  Its countable product is the canonical spine increment
process.  This file records the coordinate laws, independence, and measurable
partial-sum positions used in the path form of the many-to-one formula.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

noncomputable def tiltedIncrementFieldLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) :
    Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => tiltedPotentialLaw φ (-1) μ)

theorem tiltedIncrementFieldLaw_isProbability {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  infer_instance

theorem tiltedIncrementFieldLaw_coordinate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    (tiltedIncrementFieldLaw φ μ).map (fun increment => increment n) =
      tiltedPotentialLaw φ (-1) μ := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  exact Measure.infinitePi_map_eval
    (fun _ : ℕ => tiltedPotentialLaw φ (-1) μ) n

theorem tiltedIncrementFieldLaw_independent {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => tiltedPotentialLaw φ (-1) μ)
    (X := fun _ : ℕ => id) (fun _ => measurable_id))


end ProbabilityTheory.BranchingRandomWalk.Spine
