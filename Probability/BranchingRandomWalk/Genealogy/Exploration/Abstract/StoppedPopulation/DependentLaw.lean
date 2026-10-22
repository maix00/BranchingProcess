/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.CellFactorization
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence

/-!
# A dependent law for a stopped finite population

The public declarations in namespace `ProbabilityTheory.BranchingRandomWalk`
are:

- `StoppedSubtreeFamily X := Σ k, Fin k → 𝕍 → Step ℕ X` packages a finite
  descendant vector together with its number of roots.
- `stoppedSubtreeFamilyMk k fields = ⟨k, fields⟩` includes one fixed-cardinality
  vector in that dependent sum.
- `stoppedPopulationSubtrees population step` is
  \[
    \left\langle |\operatorname{population}(\mathrm{step})|,
      \Phi_{\operatorname{enum}(\operatorname{population}(\mathrm{step}))}
        (\mathrm{step})\right\rangle,
  \]
  where `enum s : Fin s.card → Fin m × 𝕍` is a duplicate-free enumeration
  and, for roots $u_i=(r_i,v_i)$,
  $\Phi_{\mathbf u}(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$.
- `stoppedPopulationSubtrees_measurable τ hτ population hpopulation` proves
  measurability of this random-cardinality descendant vector.
- `stoppedPopulationSubtrees_factorization μ τ hτ hfinite population
  hpopulation hdepth A hA B hB` gives its stopped-past joint law as the
  countable mixture
  \[
    \nu_m\!\left(A\cap
      \operatorname{stoppedPopulationSubtrees}(\operatorname{population})^{-1}(B)\right)
    =\sum_s \nu_m\!\left(A\cap\{\operatorname{population}=s\}\right)
      \left(\nu^{\otimes |s|}\right)
      \left(\iota_{|s|}^{-1}(B)\right),
  \]
  with `νₘ = finiteRootStepFieldLaw μ m`, `ν = stepFieldLaw μ`, and
  `ιₖ = stoppedSubtreeFamilyMk k`. The assumptions are that `τ` is an
  everywhere-finite stopping time, each population fibre is measurable at
  `τ`, and every selected root has depth `τ`.

The empty population is the `k = 0` fibre of this same statement.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- A finite family of descendant step fields with its cardinality retained
in the type. -/
abbrev StoppedSubtreeFamily (X : Type*) [MeasurableSpace X] :=
  Sigma (fun k : ℕ => Fin k → 𝕍 → Step ℕ X)

/-- The canonical measurable inclusion of one fixed-cardinality fibre into
the dependent family. -/
def stoppedSubtreeFamilyMk {X : Type*} [MeasurableSpace X] (k : ℕ) :
    (Fin k → 𝕍 → Step ℕ X) → StoppedSubtreeFamily X :=
  fun fields => ⟨k, fields⟩

private lemma stoppedSubtreeFamilyMk_measurable
    {X : Type*} [MeasurableSpace X] (k : ℕ) :
    Measurable (stoppedSubtreeFamilyMk (X := X) k) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ k

private noncomputable def stoppedPopulationRootEquiv {m : ℕ}
    (s : Finset (Fin m × 𝕍)) : {p : Fin m × 𝕍 // p ∈ s} ≃ Fin s.card :=
  Fintype.equivFinOfCardEq (by simp)

private noncomputable def stoppedPopulationRoots {m : ℕ}
    (s : Finset (Fin m × 𝕍)) : Fin s.card → Fin m × 𝕍 :=
  fun j => ((stoppedPopulationRootEquiv s).symm j).1

private lemma stoppedPopulationRoots_cover {m : ℕ}
    (s : Finset (Fin m × 𝕍)) :
    s = Finset.univ.image (stoppedPopulationRoots s) := by
  classical
  let e := stoppedPopulationRootEquiv s
  ext p
  constructor
  · intro hp
    exact Finset.mem_image.mpr
      ⟨e ⟨p, hp⟩, Finset.mem_univ _, by simp [stoppedPopulationRoots, e]⟩
  · intro hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact (e.symm j).2

private lemma stoppedPopulationRoots_injective {m : ℕ}
    (s : Finset (Fin m × 𝕍)) :
    Function.Injective (stoppedPopulationRoots s) := by
  intro i j hij
  apply (stoppedPopulationRootEquiv s).symm.injective
  exact Subtype.ext hij

/-- All descendant fields below a stopped finite population, packaged without
padding the random number of roots by dummy coordinates. -/
noncomputable def stoppedPopulationSubtrees
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (step : FiniteRootStepField m ℕ X) : StoppedSubtreeFamily X :=
  let s := population step
  stoppedSubtreeFamilyMk s.card
    (multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) step)

/-- The dependent descendant family is a random variable on the full sample
space. The population itself is stopped-past measurable, while its descendant
fields necessarily use future coordinates. The proof partitions by the
countably many population values; within each cell its cardinality and root
enumeration are fixed. -/
theorem stoppedPopulationSubtrees_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s}) :
    Measurable (stoppedPopulationSubtrees population) := by
  intro B hB
  have hsection : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet
        ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    intro s
    exact hB.preimage (stoppedSubtreeFamilyMk_measurable s.card)
  have hpieces : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet
        ({step | population step = s} ∩
          multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B)) := by
    intro s
    exact (hτ.measurableSpace_le _ (hpopulation s)).inter
      ((multiRootSubtreeStepFieldVector_measurable
        (stoppedPopulationRoots s)) (hsection s))
  have heq : stoppedPopulationSubtrees population ⁻¹' B =
      ⋃ s : Finset (Fin m × 𝕍),
        {step | population step = s} ∩
          multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    ext step
    constructor
    · intro h
      refine Set.mem_iUnion.mpr ⟨population step, rfl, ?_⟩
      exact h
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
      rcases hs with ⟨hpop, hBstep⟩
      change population step = s at hpop
      subst s
      exact hBstep
  rw [heq]
  exact MeasurableSet.iUnion hpieces

/-- The joint stopped branching law with random cardinality.  Conditional on
each population cell, the fibre has the appropriate finite product law; the
unconditional expression is their countable mixture. -/
theorem stoppedPopulationSubtrees_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × 𝕍), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (FiniteRootStepField m ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set (StoppedSubtreeFamily X)) (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ stoppedPopulationSubtrees population ⁻¹' B) =
      ∑' s : Finset (Fin m × 𝕍),
        finiteRootStepFieldLaw μ m
            (A ∩ {step | population step = s}) *
          (Measure.infinitePi
            (fun _ : Fin s.card => stepFieldLaw μ))
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
  let P := finiteRootStepFieldLaw μ m
  let D : Finset (Fin m × 𝕍) → Set (FiniteRootStepField m ℕ X) :=
    fun s => (A ∩ {step | population step = s}) ∩
      multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
        ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B)
  have hsection (s : Finset (Fin m × 𝕍)) : MeasurableSet
      ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) :=
    hB.preimage (stoppedSubtreeFamilyMk_measurable s.card)
  have hDmeas (s : Finset (Fin m × 𝕍)) : MeasurableSet (D s) :=
    ((hτ.measurableSpace_le _ hA).inter
      (hτ.measurableSpace_le _ (hpopulation s))).inter
        ((multiRootSubtreeStepFieldVector_measurable
          (stoppedPopulationRoots s)) (hsection s))
  have hDpair : Pairwise (fun s t => Disjoint (D s) (D t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro step hs ht
    exact hst (hs.1.2.symm.trans ht.1.2)
  have hDunion : (⋃ s, D s) =
      A ∩ stoppedPopulationSubtrees population ⁻¹' B := by
    ext step
    constructor
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
      rcases hs with ⟨⟨hAstep, hpop⟩, hBstep⟩
      refine ⟨hAstep, ?_⟩
      subst s
      exact hBstep
    · rintro ⟨hAstep, hBstep⟩
      refine Set.mem_iUnion.mpr ⟨population step, ⟨⟨hAstep, rfl⟩, ?_⟩⟩
      exact hBstep
  have hcell s : P (D s) =
      P (A ∩ {step | population step = s}) *
        (Measure.infinitePi
          (fun _ : Fin s.card => stepFieldLaw μ))
          ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    exact abstractStoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s (stoppedPopulationRoots s)
      (stoppedPopulationRoots_cover s) (stoppedPopulationRoots_injective s)
      _ (hsection s)
  calc
    P (A ∩ stoppedPopulationSubtrees population ⁻¹' B) =
        P (⋃ s, D s) := by rw [hDunion]
    _ = ∑' s, P (D s) := measure_iUnion hDpair hDmeas
    _ = _ := tsum_congr hcell

end ProbabilityTheory.BranchingRandomWalk
