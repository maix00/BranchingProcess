import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.AddressFiltration.PastFuture

open MeasureTheory ProbabilityTheory
open Combinatorics.UlamHarris Combinatorics.Branching

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

example {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    multiRootStepGenerationSpace (m := m) (X := X) n =
      RootIndexed.stepGenerationSpace (Root := Fin m) (α := ℕ) (X := X) n := rfl

example {m : ℕ} {X : Type*} [MeasurableSpace X] :
    multiRootStepFiltration (m := m) (X := X) =
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := X) := rfl

example {m : ℕ} {X : Type*} [MeasurableSpace X] :
    multiRootStepGenerationSpace (m := m) (X := X) 0 = ⊥ :=
  RootIndexed.stepGenerationSpace_zero (Root := Fin m) (α := ℕ) (X := X)

example {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : 𝕍) (hu : u.length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => ω i u) :=
  RootIndexed.step_measurable (Root := Fin m) (α := ℕ) (X := X) i u hu

example {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (chosen : FiniteRootStepField m ℕ X → 𝕍)
    (hchosen : Measurable[multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => ω i (chosen ω)) :=
  multiRootSelectedStep_measurable i chosen hchosen hdepth

example {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    iIndep (RootIndexed.stepCoordinateSpace (Root := Fin m) (α := ℕ) (X := X))
      (RootIndexed.stepFieldLaw (Root := Fin m) μ) :=
  RootIndexed.stepFieldLaw_coordinates_independent μ

example {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n)
      (RootIndexed.stepFutureSpace (Root := Root) (α := α) (X := X) n)
      (RootIndexed.stepFieldLaw (Root := Root) μ) :=
  RootIndexed.step_past_future_independent μ n

example {m : ℕ} {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initial : Fin m → Position) (d : Mark → Position) (hd : Measurable d)
    (n : ℕ) (i : Fin m)
    (chosen : FiniteRootStepField m ℕ Mark → 𝕍)
    (hchosen : Measurable[multiRootStepFiltration (m := m) (X := Mark) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
      (fun ω => RootIndexed.position initial d ω i (chosen ω)) :=
  RootIndexed.selectedPositionAtGeneration_measurable_of_countableAddress
    initial d hd n i chosen hchosen hdepth

example {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initial : Root → Position) (d : Mark → Position) (hd : Measurable d)
    (n : ℕ) (i : Root)
    (chosen : RootIndexed.StepField Root α Mark → TreeNode α)
    (hchosen : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (hcount : (Set.range chosen).Countable) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (fun ω => RootIndexed.position initial d ω i (chosen ω)) :=
  RootIndexed.selectedPositionAtGeneration_measurable
    initial d hd n i chosen hchosen hdepth hcount

example {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} (σ : ι → TreeNode α) (hσ : Function.Injective σ) :
    iIndepFun (fun i (ω : StepField α X) => ω (σ i)) (offspringFieldLaw μ) :=
  (offspringFieldLaw_independent μ).precomp hσ

end ProbabilityTheory.BranchingRandomWalk
