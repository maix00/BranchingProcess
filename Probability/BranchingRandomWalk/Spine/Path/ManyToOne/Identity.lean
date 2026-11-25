/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Generation
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.FamilySelection

/-!
# Path-functional many-to-one identities

## Public declarations

- `weightedPathManyToOneCore` states
  $\mathbb E[\widehat Z_n(F,x)]=\mathbb E_{\widehat\mu}[F(H_n)]$ for a
  measurable path functional $F$ and the boundary-normalized tilted law.
- `pathManyToOneCore` states
  $\mathbb E[Z_n(F,x)]=\mathbb E_{\widehat\mu}
  [e^{S_n}F(H_n)]$, where $S_n$ is the increment displacement.
- `weightedPathManyToOne` and `pathManyToOne` give the same identities when
  the offspring mark space and the real-valued position space are separate,
  for every measurable displacement map.

The test function sees the complete ancestral position history at times
`0, ..., n`.  The two identities correspond to the exponentially weighted
and unweighted branching sums. The ordinary identity is obtained by accepting every family in the general
family-selection many-to-one theorem and forgetting the reproductive mark.
The weighted identity follows by terminal exponential cancellation.
No branching expectation is reproved by induction. The right-hand measure is the auxiliary tilted IID
law, whose position law equals the spine under the changed tree measure.
Compare Zhan Shi, *Branching Random Walks* (2015), Theorems 1.1, 4.3 and
4.4(ii), DOI 10.1007/978-3-319-25372-5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.RandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory Finset Preorder

/-- Ordinary path-functional many-to-one is the universal-family special case
of `pathManyToOne_selectFamily`, followed by forgetting the reproductive mark. -/
theorem pathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration φ n F x ω ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (history n x increment)
        ∂tiltedIncrementFieldLaw φ μ := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let mark : Combinatorics.Branching.Step ι X → Unit := fun _ => ()
  let ν := tiltedMarkedPotentialLaw φ (-1) μ (fun p => mark p.1)
  let : IsProbabilityMeasure ν := tiltedMarkedPotentialLaw_isProbability φ μ hboundary measurable_const
  have h := pathManyToOne_selectFamily φ μ hboundary
    (mark := mark) measurable_const (accepted := Set.univ) MeasurableSet.univ n hF x
  have hsel : (Combinatorics.Branching.Step.selectFamily Set.univ :
      Combinatorics.Branching.Step ι X → _) = id := by
    funext ξ
    exact Combinatorics.Branching.Step.selectFamily_of_mem (Set.mem_univ ξ)
  simp only [Set.preimage_univ, hsel, Measure.map_id, Set.mem_univ] at h
  have htrue : ∀ j : ℕ, j < n → True := fun _ _ => True.intro
  simp only [ite_eq_left htrue] at h
  have hmap : (iidSequenceLaw ν).map (fun sequence j => (sequence j).1) =
      tiltedIncrementFieldLaw φ μ := by
    rw [iidSequenceLaw_map_coordinatewise ν Prod.fst measurable_fst,
      tiltedMarkedPotentialLaw_fst φ (-1) μ measurable_const]
    rfl
  have hG : Measurable (fun increment : ℕ → ℝ =>
      ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) * F (history n x increment)) :=
    (displacement_measurable n).exp.ennreal_ofReal.mul (hF.comp (history_measurable n x))
  refine h.trans ?_
  rw [← hmap, lintegral_map hG (by fun_prop)]

/-- The weighted identity follows from ordinary path-functional many-to-one
by the reciprocal terminal exponential. -/
theorem weightedPathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) =
        ∫⁻ increment, F (history n x increment)
          ∂tiltedIncrementFieldLaw φ μ := by
  intro n F hF x
  let G (h : Fin (n + 1) → ℝ) := ENNReal.ofReal (Real.exp (-(h (Fin.last n) - x))) * F h
  have hG : Measurable G := by fun_prop
  have hw (field : Combinatorics.Branching.StepField ι X) :
      weightedPathGeneration φ n F x field = pathGeneration φ n G x field := by
    apply tsum_congr
    intro u
    by_cases hu : u.length = n
    · by_cases hs : surviveAlong field [] u
      · simp [weightedPathGenerationTerm, pathGenerationTerm, G, hu, hs,
          pathHistory_last, Fin.last]
      · simp [weightedPathGenerationTerm, pathGenerationTerm, G, hu, hs]
    · simp [weightedPathGenerationTerm, pathGenerationTerm, hu]
  calc
    _ = ∫⁻ field, pathGeneration φ n G x field ∂offspringFieldLaw μ := lintegral_congr hw
    _ = _ := pathManyToOneCore φ μ hboundary n hG x
    _ = _ := by
      apply lintegral_congr
      intro increment
      simp only [G]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simp

/-- Path-functional weighted many-to-one with separate mark and position
spaces.  The displacement map is only required to be measurable. -/
theorem weightedPathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPathGeneration (potential.comp d hd) n F x ω
        ∂offspringFieldLaw μ) =
      ∫⁻ increment, F (history n x increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  weightedPathManyToOneCore (potential.comp d hd) μ hboundary n hF x

/-- Path-functional unweighted many-to-one with separate mark and position
spaces. -/
theorem pathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration (potential.comp d hd) n F x ω
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (history n x increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  pathManyToOneCore (potential.comp d hd) μ hboundary n hF x

end ProbabilityTheory.BranchingRandomWalk.Spine
