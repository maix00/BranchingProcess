import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Finite-dimensional projections of continuous paths

This file contains the general path-space interface connecting functional
convergence with finite-dimensional convergence.  It is independent of any
particular random walk or limiting process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology

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

/-- Evaluation on a dense sequence is a measurable embedding of continuous
path space into sequence space. -/
theorem measurableEmbedding_finiteEvaluation_of_denseRange
    {Time State : Type*} [TopologicalSpace Time] [MeasurableSpace Time]
    [TopologicalSpace State] [MeasurableSpace State]
    [BorelSpace State] [T2Space State]
    [SecondCountableTopology Time] [SecondCountableTopology State]
    [LocallyCompactSpace Time] [StandardBorelSpace C(Time, State)]
    (time : ℕ → Time) (htime : DenseRange time) :
    MeasurableEmbedding
      (finiteEvaluation time : C(Time, State) → (ℕ → State)) := by
  have hmeas : Measurable
      (finiteEvaluation time : C(Time, State) → (ℕ → State)) := by
    rw [measurable_pi_iff]
    intro n
    exact ContinuousMap.measurable_eval (time n)
  apply hmeas.measurableEmbedding
  intro f g hfg
  apply ContinuousMap.ext
  exact congrFun (htime.equalizer f.continuous g.continuous hfg)

/-- Two finite path measures coincide if all their finite-dimensional laws
along one dense sequence of times coincide. -/
theorem measure_eq_of_map_finiteEvaluation_eq_of_denseRange
    {Time State : Type*} [TopologicalSpace Time] [MeasurableSpace Time]
    [TopologicalSpace State] [MeasurableSpace State]
    [BorelSpace State] [PolishSpace State]
    [SecondCountableTopology Time]
    [LocallyCompactSpace Time] [StandardBorelSpace C(Time, State)]
    (time : ℕ → Time) (htime : DenseRange time)
    (μ ν : Measure C(Time, State)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfinite : ∀ I : Finset ℕ,
      μ.map (finiteEvaluation (fun i : I => time i)) =
        ν.map (finiteEvaluation (fun i : I => time i))) :
    μ = ν := by
  let P : ∀ I : Finset ℕ, Measure (I → State) := fun I =>
    μ.map (finiteEvaluation (fun i : I => time i))
  have hμ : IsProjectiveLimit
      (μ.map (finiteEvaluation time : C(Time, State) → (ℕ → State))) P := by
    intro I
    rw [Measure.map_map]
    · rfl
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · rw [measurable_pi_iff]
      intro n
      exact ContinuousMap.measurable_eval (time n)
  have hν : IsProjectiveLimit
      (ν.map (finiteEvaluation time : C(Time, State) → (ℕ → State))) P := by
    intro I
    rw [Measure.map_map]
    · exact hfinite I |>.symm
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · rw [measurable_pi_iff]
      intro n
      exact ContinuousMap.measurable_eval (time n)
  have hmap := hμ.unique hν
  exact (measurableEmbedding_finiteEvaluation_of_denseRange time htime).map_injective hmap

/-- Tightness and convergence of every finite-dimensional marginal along a
dense time sequence imply weak convergence of continuous-path laws. -/
theorem ProbabilityMeasure.tendsto_of_tight_of_finiteEvaluation
    {Time State : Type*} [TopologicalSpace Time] [MeasurableSpace Time]
    [TopologicalSpace State] [MeasurableSpace State]
    [BorelSpace State] [PolishSpace State]
    [SecondCountableTopology Time]
    [LocallyCompactSpace Time] [PolishSpace C(Time, State)]
    (time : ℕ → Time) (htime : DenseRange time)
    {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure C(Time, State))
    (μ₀ : ProbabilityMeasure C(Time, State))
    (htight : IsTightMeasureSet {((μ i : ProbabilityMeasure C(Time, State)) :
      Measure C(Time, State)) | i})
    (hfinite : ∀ I : Finset ℕ,
      Tendsto (fun i => (μ i).map
          (finiteEvaluation (fun j : I => time j))) l
        (nhds (μ₀.map (finiteEvaluation (fun j : I => time j))))) :
    Tendsto μ l (nhds μ₀) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable C(Time, State)
  obtain rfl | _ := l.eq_or_neBot
  · simp
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU => ?_
  have hcompact : IsCompact (closure {μ i | i}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight)
  obtain ⟨μ', -, hμ' : Tendsto _ _ _⟩ := hcompact.ultrafilter_le_nhds (U.map μ)
    (.trans (by simp) (monotone_principal subset_closure))
  suffices μ' = μ₀ by simpa [this] using hμ'
  apply Subtype.ext
  apply measure_eq_of_map_finiteEvaluation_eq_of_denseRange time htime
    (μ'.toFiniteMeasure : Measure C(Time, State))
    (μ₀.toFiniteMeasure : Measure C(Time, State))
  intro I
  have hlimitFromCluster : Tendsto
      (fun i => (μ i).map (finiteEvaluation (fun j : I => time j))) U
      (nhds (μ'.map (finiteEvaluation (fun j : I => time j)))) :=
    Filter.Tendsto.comp
      (ProbabilityMeasure.continuous_map
        (continuous_finiteEvaluation (fun j : I => time j))).continuousAt hμ'
  have hlimitTarget := (hfinite I).comp hU
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hlimitFromCluster hlimitTarget)

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
