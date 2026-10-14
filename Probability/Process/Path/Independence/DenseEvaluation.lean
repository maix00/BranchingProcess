/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.ContinuousMap.FiniteDimensional
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of continuous paths from dense evaluations

The public theorem in this file is:

- `ProbabilityTheory.IndepFun.of_indep_finiteEvaluation`:
  two continuous-path-valued random variables are independent whenever
  their coordinate families on countable dense time sets are independent.

The theorem uses that dense evaluation is a measurable embedding of
continuous path space. It supplies the path-level independence needed
for the rational-interval step in Lemma 2.3 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Independence of path-valued variables follows from independence of
their evaluations on countable dense subsets of their time domains. -/
theorem IndepFun.of_indep_finiteEvaluation
    {Ω S T I J : Type*} [MeasurableSpace Ω]
    [Countable I] [Countable J]
    [TopologicalSpace S] [MeasurableSpace S]
    [SecondCountableTopology S] [LocallyCompactSpace S]
    [StandardBorelSpace C(S, ℝ)]
    [TopologicalSpace T] [MeasurableSpace T]
    [SecondCountableTopology T] [LocallyCompactSpace T]
    [StandardBorelSpace C(T, ℝ)]
    {P : Measure Ω} {F : Ω → C(S, ℝ)} {G : Ω → C(T, ℝ)}
    (s : I → S) (hs : DenseRange s)
    (t : J → T) (ht : DenseRange t)
    (h : (ContinuousMap.finiteEvaluation s ∘ F) ⟂ᵢ[P]
      (ContinuousMap.finiteEvaluation t ∘ G)) : F ⟂ᵢ[P] G := by
  have heS := ContinuousMap.measurableEmbedding_finiteEvaluation_of_denseRange
    (State := ℝ) s hs
  have heT := ContinuousMap.measurableEmbedding_finiteEvaluation_of_denseRange
    (State := ℝ) t ht
  change Kernel.Indep
    (MeasurableSpace.comap (ContinuousMap.finiteEvaluation s ∘ F) inferInstance)
    (MeasurableSpace.comap (ContinuousMap.finiteEvaluation t ∘ G) inferInstance)
    (Kernel.const Unit P) (Measure.dirac ()) at h
  rw [← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp,
    heS.comap_eq, heT.comap_eq] at h
  exact h

end ProbabilityTheory

end
