/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.CellFactorization
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingPopulation
public import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Random-cardinality branching for the selected population

## Public declarations

The public declaration in namespace `ProbabilityTheory.BranchingRandomWalk` is
`selectedPopulation_random_size_branching μ N x τ hτ hfinite`. For every
finite population value $s$, it gives an injective enumeration of the roots
and the cellwise product law; it also states that the population cells
partition every stopped-past event in measure:
\[
  \sum_s \nu_m\!\left(A\cap
      \{\operatorname{selectedPopulationAt}(N,x,\tau)=s\}\right)
  =\nu_m(A),
\]
where $\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$. The cellwise
factorization is
\[
  \nu_m\!\left((A\cap\{\operatorname{selectedPopulationAt}=s\})
      \cap\Phi_u^{-1}(B)\right)
  =\nu_m\!\left(A\cap\{\operatorname{selectedPopulationAt}=s\}\right)
      \left(\nu^{\otimes |s|}\right)(B),
\]
where $\nu=\operatorname{offspringFieldLaw}(\mu)$ and, for the enumerated roots
$u_i=(r_i,v_i)$, $\Phi_u(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$. The
assumptions require an everywhere-finite stopping time; the selected
population is measurable at that stopping time and every selected address
has depth $\tau$.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- The stopped selected population satisfies the abstract
cellwise branching theorem.  This is the concrete interface used by later
coupling arguments. -/
private lemma selectedPopulation_stopped_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
            ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
              RootIndexed.subtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m
            (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => offspringFieldLaw μ)) B := by
  classical
  obtain ⟨roots, hmap⟩ :=
    Function.Embedding.exists_of_card_eq_finset
      (α := Fin s.card) (s := s) (by simp)
  have hcover : s = Finset.univ.image roots := by
    rw [← Finset.map_eq_image]
    exact hmap.symm
  exact ⟨roots, hcover, fun A hA B hB =>
    abstractStoppedPopulation_cell_factorization μ τ hτ hfinite
      (selectedPopulationAt N x τ)
      (fun t => selectedPopulationAt_cell_measurable N x τ hτ hfinite t)
      (selectedPopulationAt_depth N x τ) A hA s roots hcover roots.injective B hB⟩

/-- Unified random-cardinality interface for the selected population: every
finite cell has a duplicate-free multi-root enumeration with the product
descendant law, and all cells form the countable probability partition. -/
theorem selectedPopulation_random_size_branching
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤) :
    (∀ s : Finset (RootAddress m ℕ),
      ∃ roots : Fin s.card → RootAddress m ℕ,
        s = Finset.univ.image roots ∧
        ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
          (_ : MeasurableSet[hτ.measurableSpace] A)
          (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
          (_ : MeasurableSet B),
          finiteRootStepFieldLaw μ m
              ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
                RootIndexed.subtreeStepFieldVector roots ⁻¹' B) =
            finiteRootStepFieldLaw μ m
              (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
              (Measure.infinitePi
                (fun _ : Fin s.card => offspringFieldLaw μ)) B) ∧
    (∀ A : Set (FiniteRootStepField m ℕ ℝ),
      MeasurableSet[hτ.measurableSpace] A →
      (∑' s : Finset (RootAddress m ℕ),
        finiteRootStepFieldLaw μ m
          (A ∩ {ω | selectedPopulationAt N x τ ω = s})) =
        finiteRootStepFieldLaw μ m A) := by
  constructor
  · intro s
    exact selectedPopulation_stopped_cell_branches μ N x τ hτ hfinite s
  · intro A hA
    classical
    let ν := finiteRootStepFieldLaw μ m
    let f := selectedPopulationAt N x τ
    have hf : ∀ s : Finset (RootAddress m ℕ),
        MeasurableSet (f ⁻¹' {s}) := by
      intro s
      exact hτ.measurableSpace_le _
        (selectedPopulationAt_cell_measurable N x τ hτ hfinite s)
    have hsum := MeasureTheory.tsum_measure_preimage_singleton
      (μ := ν.restrict A) (s := Set.univ)
      Set.countable_univ (by intro s hs; exact hf s)
    have hcell (s : Finset (RootAddress m ℕ)) :
        ν (A ∩ {ω | f ω = s}) = (ν.restrict A) (f ⁻¹' {s}) := by
      rw [Measure.restrict_apply (hf s)]
      congr 1
      ext ω
      simp [Set.inter_comm]
    calc
      (∑' s : Finset (RootAddress m ℕ),
          ν (A ∩ {ω | f ω = s})) =
        ∑' s : Finset (RootAddress m ℕ), (ν.restrict A) (f ⁻¹' {s}) := by
          apply tsum_congr
          intro s
          exact hcell s
      _ = (ν.restrict A) (f ⁻¹' (Set.univ : Set (Finset (RootAddress m ℕ)))) := by
        exact ((Equiv.Set.univ (Finset (RootAddress m ℕ))).tsum_eq
          (fun s : Finset (RootAddress m ℕ) => (ν.restrict A) (f ⁻¹' {s}))).symm.trans hsum
      _ = ν A := by
        rw [Set.preimage_univ, Measure.restrict_apply_univ]

end ProbabilityTheory.BranchingRandomWalk
