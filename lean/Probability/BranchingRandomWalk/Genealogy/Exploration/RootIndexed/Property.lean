import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Property
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def multiRootSubtreeStepField {m : ℕ} {X : Type*}
    (i : Fin m) (u : 𝕍) (ω : FiniteRootStepField m ℕ X) :
    𝕍 → Step ℕ X :=
  subtreeStepField u (ω i)

theorem multiRootSubtreeStepField_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : 𝕍) :
    Measurable (multiRootSubtreeStepField (X := X) i u) := by
  exact (subtreeStepField_measurable (X := X) u).comp
    (measurable_pi_apply i)

theorem multiRootSubtreeStepField_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (i : Fin m) (u : 𝕍) :
    (finiteRootStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      stepFieldLaw μ := by
  calc
    (finiteRootStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      ((finiteRootStepFieldLaw μ m).map (fun ω => ω i)).map
        (subtreeStepField (X := X) u) := by
          rw [Measure.map_map]
          · rfl
          · exact subtreeStepField_measurable u
          · exact measurable_pi_apply i
    _ = stepFieldLaw μ := by
      rw [finiteRootStepFieldLaw_root_marginal μ i,
        subtreeStepField_law μ u]

theorem multiRootSubtreeStepFields_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → 𝕍) :
    iIndepFun
      (fun i (ω : FiniteRootStepField m ℕ X) =>
        multiRootSubtreeStepField i (root i) ω)
      (finiteRootStepFieldLaw μ m) := by
  exact (finiteRootStepFieldLaw_roots_independent μ m).comp
    (fun i => subtreeStepField (X := X) (root i))
    (fun i => subtreeStepField_measurable (X := X) (root i))

theorem multiRootSubtreeStepFields_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → 𝕍) :
    (finiteRootStepFieldLaw μ m).map
        (fun ω i => multiRootSubtreeStepField i (root i) ω) =
      Measure.infinitePi (fun _ : Fin m => stepFieldLaw μ) := by
  have hind := multiRootSubtreeStepFields_independent μ root
  have hmeas : ∀ i : Fin m, Measurable
      (fun ω : FiniteRootStepField m ℕ X =>
        multiRootSubtreeStepField i (root i) ω) := by
    intro i
    exact multiRootSubtreeStepField_measurable i (root i)
  rw [hind.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  exact multiRootSubtreeStepField_law μ i (root i)

theorem multiRootSubtree_position_decomposition
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootStepField m ℕ X) (i : Fin m)
    (u v : 𝕍) :
    RootIndexed.displace step i (u ++ v) =
      RootIndexed.displace step i u +
        displace (multiRootSubtreeStepField i u step) [] v := by
  exact RootIndexed.displace_append step i u v

end ProbabilityTheory.BranchingRandomWalk
