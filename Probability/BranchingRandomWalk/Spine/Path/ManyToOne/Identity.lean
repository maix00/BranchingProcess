/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Generation
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Marked

/-!
# Path-functional many-to-one identities

The test function sees the complete ancestral position history at times
`0, ..., n`.  The two identities correspond to the exponentially weighted
and unweighted branching sums. The weighted identity is obtained from the
complete-family many-to-one theorem by forgetting reproductive records.
No branching expectation is reproved by induction. The right-hand measure is the auxiliary tilted IID
law, whose position law equals the spine under the changed tree measure.
Compare Zhan Shi, *Branching Random Walks* (2015), Theorems 1.1, 4.3 and
4.4(ii), DOI 10.1007/978-3-319-25372-5.

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
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.RandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory Finset Preorder

private lemma tsum_lists_length {ι : Type*} (n : ℕ) (H : List ι → ℝ≥0∞) :
    (∑' u : List ι, if u.length = n then H u else 0) =
      ∑' z : Fin n → ι, H (List.ofFn z) := by
  rw [← List.equivSigmaTuple.symm.tsum_eq]
  change (∑' c : Σ k, Fin k → ι,
    if (List.ofFn c.2).length = n then H (List.ofFn c.2) else 0) = _
  simp only [List.length_ofFn]
  rw [tsum_sigma', tsum_eq_single n]
  · simp
  · intro k hk
    simp [hk]

private lemma measurable_finitePrefix (n : ℕ) (x : ℝ) :
    Measurable (AdditivePath.finitePrefix x : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  apply measurable_pi_iff.mpr
  intro k
  induction k using Fin.induction with
  | zero => simpa only [AdditivePath.finitePrefix_zero] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => x))
  | succ k ih =>
    simp only [AdditivePath.finitePrefix_succ]
    exact measurable_add.comp (ih.prodMk (measurable_pi_apply k))

/-- Weighted path-functional many-to-one identity for the pre-sampled
branching field, obtained by forgetting the family data in the complete-record
many-to-one identity. -/
theorem weightedPathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) =
        ∫⁻ increment, F (history n x increment)
          ∂tiltedIncrementFieldLaw φ μ := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  intro n F hF x
  let : IsProbabilityMeasure (tiltedFamilyChildLaw φ (-1) μ) :=
    tiltedFamilyChildLaw_isProbability φ μ hboundary
  let : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  let read (p : Step ι X × ι) := p.1.potentialValue' φ p.2
  let increments (records : Fin n → Step ι X × ι) := fun j => read (records j)
  let G (records : Fin n → Step ι X × ι) :=
    ENNReal.ofReal (Real.exp (-∑ j, read (records j))) *
      F (AdditivePath.finitePrefix x (increments records))
  have hr : Measurable read := measurable_from_prod_countable_left
    (fun i => Step.potentialValue'_measurable φ i)
  have hi : Measurable increments := measurable_pi_iff.mpr
    (fun j => hr.comp (measurable_pi_apply j))
  have hG : Measurable G :=
    (Finset.measurable_sum _ (fun j _ => hr.comp (measurable_pi_apply j))).neg.exp.ennreal_ofReal.mul (hF.comp ((measurable_finitePrefix n x).comp hi))
  have heq (field : StepField ι X) : weightedPathGeneration φ n F x field =
      ∑' z : Fin n → ι, if surviveAlong field [] (List.ofFn z)
        then G (Mark.pathRecords field z) else 0 := by
    unfold weightedPathGeneration
    have hh : (∑' u : List ι, weightedPathGenerationTerm φ n F x u field) =
        ∑' u : List ι, if u.length = n then
          (if surviveAlong field [] u then
            ENNReal.ofReal (Real.exp (-pathPotential φ field u)) *
              F (pathHistory φ n x field u) else 0) else 0 := by
      apply tsum_congr
      intro u
      by_cases hn : u.length = n <;> by_cases hs : surviveAlong field [] u <;>
        simp [weightedPathGenerationTerm, hn, hs]
    rw [hh, tsum_lists_length]
    apply tsum_congr
    intro z
    have hp := congrFun (pathHistory_eq_finitePrefix_records φ n 0 field z) (Fin.last n)
    have ht : pathPotential φ field (List.ofFn z) =
        ∑ j, read (Mark.pathRecords field z j) := by
      simpa [pathHistory, AdditivePath.finitePrefix, Fin.partialSum,
        List.take_of_length_le, List.sum_ofFn, read] using hp
    simp only [G, increments, ht, pathHistory_eq_finitePrefix_records, read]
  have hmany := familyPathManyToOne φ μ hboundary n hG
  calc
    _ = ∫⁻ field, ∑' z : Fin n → ι,
        if surviveAlong field [] (List.ofFn z) then G (Mark.pathRecords field z) else 0
        ∂offspringFieldLaw μ := lintegral_congr heq
    _ = ∫⁻ records, ENNReal.ofReal (Real.exp (∑ j, read (records j))) * G records
        ∂Measure.pi (fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ) := hmany
    _ = ∫⁻ records, F (AdditivePath.finitePrefix x (increments records))
        ∂Measure.pi (fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ) := by
      apply lintegral_congr
      intro records
      dsimp only [G]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simp
    _ = ∫⁻ v, F (AdditivePath.finitePrefix x v)
        ∂Measure.pi (fun _ : Fin n => tiltedPotentialLaw φ (-1) μ) := by
      have hm := lintegral_map (hF.comp (measurable_finitePrefix n x)) hi
        (μ := Measure.pi (fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ))
      rw [Measure.pi_map_pi (fun _ => hr.aemeasurable)] at hm
      simpa only [tiltedFamilyChildLaw_map_potential, increments, read, Function.comp_def] using hm.symm
    _ = _ := by
      rw [← iidSequenceLaw_map_finPrefix (tiltedPotentialLaw φ (-1) μ) n]
      have hm := lintegral_map
        (show Measurable (fun v : Fin n → ℝ => F (AdditivePath.finitePrefix x v)) from
          hF.comp (measurable_finitePrefix n x))
        (show Measurable (fun v : ℕ → ℝ => fun j : Fin n => v j) from by fun_prop)
        (μ := iidSequenceLaw (tiltedPotentialLaw φ (-1) μ))
      exact hm

/-- Unweighted path-functional many-to-one identity, with the reciprocal
exponential weight determined by the terminal spine displacement. -/
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
  let weightedTest : (Fin (n + 1) → ℝ) → ENNReal := fun history =>
    ENNReal.ofReal
      (Real.exp (history ⟨n, Nat.lt_succ_self n⟩ - x)) * F history
  have hweightedTest : Measurable weightedTest := by
    exact ((measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).sub
      measurable_const).exp.ennreal_ofReal.mul hF
  simp_rw [pathGeneration_eq_weightedPathGeneration]
  rw [weightedPathManyToOneCore φ μ hboundary n hweightedTest x]
  apply lintegral_congr
  intro increment
  unfold weightedTest
  rw [history_last]
  rw [AdditivePath.fromIncrements_apply]
  rw [show x + AdditivePath.displacement n increment - x =
    AdditivePath.displacement n increment by ring]

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
