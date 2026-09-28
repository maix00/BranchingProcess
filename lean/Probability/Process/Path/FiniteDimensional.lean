import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Finite-dimensional projections of continuous paths

This file contains the general path-space interface connecting functional
convergence with finite-dimensional convergence.  It is independent of any
particular random walk or limiting process.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Process.Path

/-- Evaluate a continuous path at a finite family of times. -/
def finiteEvaluation {Time State I : Type*} [TopologicalSpace Time]
    [TopologicalSpace State] (time : I → Time) :
    C(Time, State) → (I → State) :=
  fun path i => path (time i)

theorem continuous_finiteEvaluation {Time State I : Type*}
    [TopologicalSpace Time] [TopologicalSpace State]
    [Finite I] (time : I → Time) :
    Continuous (finiteEvaluation time : C(Time, State) → (I → State)) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_eval_const (time i)

/-- Functional convergence in continuous path space implies convergence of
every finite-dimensional marginal. -/
theorem tendstoInDistribution_finiteEvaluation
    {J Time State I Omega' : Type*}
    [TopologicalSpace Time] [MeasurableSpace Time]
    [TopologicalSpace State] [MeasurableSpace State]
    [BorelSpace State] [SecondCountableTopology State]
    [Finite I] [Countable I]
    [MeasurableSpace Omega']
    {OmegaJ : J → Type*} [mOmegaJ : ∀ j, MeasurableSpace (OmegaJ j)]
    {P : (j : J) → Measure (OmegaJ j)} [∀ j, IsProbabilityMeasure (P j)]
    {P' : Measure Omega'} [IsProbabilityMeasure P']
    {l : Filter J}
    {X : (j : J) → OmegaJ j → C(Time, State)}
    {Z : Omega' → C(Time, State)}
    (h : TendstoInDistribution X l Z P P') (time : I → Time) :
    TendstoInDistribution
      (fun j => finiteEvaluation time ∘ X j) l
      (finiteEvaluation time ∘ Z) P P' :=
  h.continuous_comp (continuous_finiteEvaluation time)

end ProbabilityTheory.Process.Path
