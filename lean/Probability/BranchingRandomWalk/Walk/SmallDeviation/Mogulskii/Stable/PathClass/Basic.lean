module

public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.ContinuousMap
public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Mogul'skii path classes `M₁` and `M₂`

This is the statement layer from §1 of Mogul'skii's paper.  A boundary is a
finite right-continuous step function with values in the extended reals, so
unbounded sides of a corridor are represented rather than silently replaced
by finite real bounds.  `M₂` adds exactly the source's nonempty continuous-path
condition.  The finite-union and approximation classes `M₃` and `M` are kept
for the next file, where their energy functional is introduced.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- A finite right-continuous step boundary on `[0,1]`, with values in the
extended real line.  At a knot the new level is used, giving the right-
continuous convention; knots at `1` are excluded so the terminal value is
the left limit. -/
structure StepBoundary where
  knots : Finset unitInterval
  noTopKnot : ∀ t ∈ knots, t ≠ ⊤
  levels : Fin (knots.card + 1) → EReal

namespace StepBoundary

/-- The level index is the number of knots already reached. -/
noncomputable def levelIndex (b : StepBoundary) (t : unitInterval) : Fin (b.knots.card + 1) :=
  ⟨(b.knots.filter fun s => s ≤ t).card,
    Nat.lt_succ_of_le <| Finset.card_le_card (Finset.filter_subset _ _)⟩

/-- Evaluate the step boundary at time `t`. -/
noncomputable def eval (b : StepBoundary) (t : unitInterval) : EReal :=
  b.levels (b.levelIndex t)

@[simp]
theorem eval_empty (v : EReal) (t : unitInterval) :
    (⟨∅, by simp, fun _ => v⟩ : StepBoundary).eval t = v := by
  simp [eval]

end StepBoundary

/-- The path set determined by an upper and a lower finite-step boundary.
Paths start at zero and satisfy the strict strip constraints at interior
times, matching class `M₁` in the source. -/
def corridorSet (upper lower : StepBoundary) : Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0 ∧ ∀ t : unitInterval, t ≠ ⊥ → t ≠ ⊤ →
    lower.eval t < (f t : EReal) ∧ (f t : EReal) < upper.eval t}

/-- A path set belongs to the source's class `M₁` when it is a strict corridor
with finite step boundaries, allowing either boundary to take infinite values. -/
def IsM₁ (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ upper lower : StepBoundary, G = corridorSet upper lower

/-- A finite-step corridor has a continuous admissible path when its set
contains a continuous path starting at zero. -/
def HasContinuousAdmissiblePath (upper lower : StepBoundary) : Prop :=
  ∃ f : C(unitInterval, ℝ), f ⊥ = 0 ∧
    (Skorokhod.ofContinuousMap f : CadlagPath unitInterval ℝ) ∈
      corridorSet upper lower

/-! ## Corridors in `M₂` -/

/-- A corridor together with the source's admissibility condition that its
intersection with continuous paths is nonempty. -/
structure M2Corridor where
  upper : StepBoundary
  lower : StepBoundary
  hasContinuousAdmissiblePath : HasContinuousAdmissiblePath upper lower

/-- The path set represented by an `M₂` corridor. -/
def M2Corridor.toSet (c : M2Corridor) : Set (CadlagPath unitInterval ℝ) :=
  corridorSet c.upper c.lower

/-- Class `M₂` consists of the `M₁` corridors whose intersection with the
continuous paths is nonempty. -/
def IsM₂ (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ c : M2Corridor, G = c.toSet

theorem isM₁_corridorSet (upper lower : StepBoundary) :
    IsM₁ (corridorSet upper lower) :=
  ⟨upper, lower, rfl⟩

theorem isM₂_corridorSet {upper lower : StepBoundary}
    (h : HasContinuousAdmissiblePath upper lower) :
    IsM₂ (corridorSet upper lower) :=
  ⟨⟨upper, lower, h⟩, rfl⟩

end ProbabilityTheory.RandomWalk.Mogulskii
