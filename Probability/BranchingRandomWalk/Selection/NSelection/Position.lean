import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

/-!
# Adapted spatial selection in a pre-sampled forest

This file instantiates dynamic measurable selection with the positions of a
finite-root pre-sampled branching walk.  The mark, additive position, and
ordered observation types remain separate.  Selection in the opposite
spatial direction is obtained by applying `OrderDual` only to the observation
type.
-/

open MeasureTheory Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching

noncomputable section

variable {Mark Position Value : Type*}

/-- Lexicographic root/address order used only to break ties between equal
observed positions. -/
@[instance_reducible]
private noncomputable def finiteRootParticleLinearOrder (m : ℕ) :
    LinearOrder (Fin m × 𝕍) :=
  Equiv.linearOrder (toLex : (Fin m × 𝕍) ≃ (Fin m ×ₗ 𝕍))

local instance (m : ℕ) : LinearOrder (Fin m × 𝕍) :=
  finiteRootParticleLinearOrder m

/-- The observed position of a labelled particle at generation `n`.  Labels
at another depth receive the additive zero; actual generation candidate sets
contain only labels of depth `n`. -/
def observedPositionAtGeneration
    {m : ℕ} [AddCommMonoid Position]
    (initial : Fin m → Position) (d : Mark → Position)
    (φ : Position → Value) (n : ℕ)
    (ω : FiniteRootStepField m ℕ Mark) (p : Fin m × 𝕍) : Value :=
  φ (multiRootPositionAtGeneration initial d n p.1 p.2 ω)

/-- Dynamic leftmost selection is causal for the generation domain flow of a
finite-root pre-sampled forest. -/
noncomputable def finiteRootLeftmostBy
    {m : ℕ} [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Fin m → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalNSelection ℕ (FiniteRootStepField m ℕ Mark) (Fin m × 𝕍) N
      (fun n => multiRootStepFiltration (m := m) (X := Mark) n) :=
  CausalNSelection.leftmostByOfMeasurableValue N
    (observedPositionAtGeneration initial d φ)
    (fun n p => hφ.comp
      (multiRootPositionAtGeneration_measurable initial d hd n p.1 p.2))

@[simp] theorem finiteRootLeftmostBy_select
    {m : ℕ} [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Fin m → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : FiniteRootStepField m ℕ Mark)
    (s : Finset (Fin m × 𝕍)) :
    (finiteRootLeftmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) s :=
  rfl

/-- The opposite spatial selection uses the same position process and changes
only its ordered observation to `OrderDual Value`. -/
noncomputable def finiteRootRightmostBy
    {m : ℕ} [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Fin m → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalNSelection ℕ (FiniteRootStepField m ℕ Mark) (Fin m × 𝕍) N
      (fun n => multiRootStepFiltration (m := m) (X := Mark) n) :=
  finiteRootLeftmostBy N initial d hd
    (fun x => OrderDual.toDual (φ x)) hφ

@[simp] theorem finiteRootRightmostBy_select
    {m : ℕ} [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Fin m → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : FiniteRootStepField m ℕ Mark)
    (s : Finset (Fin m × 𝕍)) :
    (finiteRootRightmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (fun p => OrderDual.toDual
          (observedPositionAtGeneration initial d φ n ω p)) s :=
  rfl

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
