/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Selected.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.CellBranching.Lemmas.Enumeration

/-!
# Branching on a cell of the selected population

The public declarations in namespace `ProbabilityTheory.BranchingRandomWalk`
use $P_{N,x,n}(\omega)=\operatorname{selectedPopulation}(N,x,n,\omega)$,
$\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$,
$\nu=\operatorname{stepFieldLaw}(\mu)$, and, for roots
$u_i=(r_i,v_i)$,
\[
  \Phi_{\mathbf u}(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v),
  \qquad
  \pi_{\mathbf u}(\omega)_i=\operatorname{RootIndexed.position}
      (x,\operatorname{id},\omega,r_i,v_i).
\]

- `selectedPopulation_cell_factorization μ N x n A hA s roots hcover hinj B hB`
  proves
  \[
    \nu_m\!\left((A\cap\{P_{N,x,n}=s\})
        \cap\Phi_{\mathbf u}^{-1}(B)\right)
    =\nu_m\!\left(A\cap\{P_{N,x,n}=s\}\right)
        \left(\nu^{\otimes k}\right)(B).
  \]
- `selectedPopulation_each_cell_branches μ N x n s` supplies such an
  injective enumeration for each finite $s$ and the same factorization for all
  generation-measurable $A$ and measurable $B$.
- `selectedPopulation_cell_position_factorization μ N x n A hA s roots
  hcover hinj D hD B hB` gives the same product law after also restricting
  the current root-position vector to $D$:
  \[
    \nu_m\!\left(((A\cap\pi_{\mathbf u}^{-1}(D))\cap\{P_{N,x,n}=s\})
        \cap\Phi_{\mathbf u}^{-1}(B)\right)
    =\nu_m\!\left((A\cap\pi_{\mathbf u}^{-1}(D))
        \cap\{P_{N,x,n}=s\}\right)\left(\nu^{\otimes k}\right)(B).
  \]
The finite population enumeration is in `Lemmas/`; one-use measurability
facts are private to this module. The exported results are the cellwise
branching laws.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- Current positions of a fixed vector of generation-`n` particles are
observable before their descendant marks are exposed. -/
private lemma multiRootPositionVector_measurable {m k n : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m ℕ)
    (hlen : ∀ j, (roots j).2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (fun ω : FiniteRootStepField m ℕ ℝ =>
        fun j : Fin k => RootIndexed.position x id ω (roots j).1 (roots j).2) := by
  apply (@measurable_pi_iff (FiniteRootStepField m ℕ ℝ) (Fin k)
    (fun _ => ℝ) (multiRootStepFiltration (m := m) (X := ℝ) n)
    (fun _ => inferInstance) _).2
  intro j
  have hj := RootIndexed.position_measurable x id measurable_id (roots j).1 (roots j).2
  rw [hlen j] at hj
  exact hj

/-- The event that the actual selected population is a prescribed labelled
set belongs to the generation domain sigma algebra. -/
private lemma selectedPopulation_cell_measurable {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m ℕ)) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
      (A ∩ {ω | selectedPopulation N x n ω = s}) :=
  hA.inter ((selectedPopulation_adapted N x n)
    (measurableSet_singleton s))

/-- Joint branching for the actual selected population, conditional on a
specified finite population cell.  `roots` is merely an enumeration of the
prescribed set; the spatial selection already took place in `A` and the
cell event. -/
theorem selectedPopulation_cell_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m ℕ))
    (roots : Fin k → RootAddress m ℕ)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → (𝕍 → Step ℕ ℝ)))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      ((A ∩ {ω | selectedPopulation N x n ω = s}) ∩
        multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        (A ∩ {ω | selectedPopulation N x n ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  by_cases hcell : ∃ ω, ω ∈ A ∧ selectedPopulation N x n ω = s
  · obtain ⟨ω, _, hω⟩ := hcell
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      apply selectedPopulation_depth N x n ω
      rw [hω, hcover]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots hlen
      hinj _ B (selectedPopulation_cell_measurable N x n A hA s) hB
  · have hempty : A ∩ {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hcell ⟨ω, h.1, h.2⟩
    simp [hempty]

/-- The actual selected population has a product descendant law on **each**
of its (possibly different-cardinality) generation-`n` cells.  The finite
index type is chosen separately for each cell. -/
theorem selectedPopulation_each_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
        (_ : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
          ((A ∩ {ω | selectedPopulation N x n ω = s}) ∩
            multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m
            (A ∩ {ω | selectedPopulation N x n ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    selectedPopulation_cell_factorization μ N x n A hA s roots hcover hinj B hB⟩

/-- The cellwise branching formula still holds after testing the current
spatial configuration.  This is the measurable input for later spatially
translated descendant processes. -/
theorem selectedPopulation_cell_position_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m ℕ))
    (roots : Fin k → RootAddress m ℕ)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (D : Set (Fin k → ℝ)) (hD : MeasurableSet D)
    (B : Set (Fin k → (𝕍 → Step ℕ ℝ)))
    (hB : MeasurableSet B) :
    let positions := fun ω : FiniteRootStepField m ℕ ℝ =>
      fun j : Fin k => RootIndexed.position x id ω (roots j).1 (roots j).2
    finiteRootStepFieldLaw μ m
      (((A ∩ positions ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s}) ∩
        multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        ((A ∩ positions ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  dsimp
  by_cases hcell : ∃ ω, ω ∈ A ∧ selectedPopulation N x n ω = s
  · obtain ⟨ω, _, hω⟩ := hcell
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      apply selectedPopulation_depth N x n ω
      rw [hω, hcover]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    apply selectedPopulation_cell_factorization μ N x n
      (A ∩ (fun ω : FiniteRootStepField m ℕ ℝ =>
        fun j : Fin k => RootIndexed.position x id ω (roots j).1 (roots j).2) ⁻¹' D)
      (hA.inter ((multiRootPositionVector_measurable x roots hlen) hD))
      s roots hcover hinj B hB
  · have hempty : A ∩ {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hcell ⟨ω, h.1, h.2⟩
    have hempty' :
        (A ∩ (fun ω : FiniteRootStepField m ℕ ℝ =>
          fun j : Fin k => RootIndexed.position x id ω (roots j).1 (roots j).2) ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      constructor
      · intro h
        have h' : ω ∈ A ∩ {ω | selectedPopulation N x n ω = s} :=
          ⟨h.1.1, h.2⟩
        rw [hempty] at h'
        exact h'
      · intro h
        exact h.elim
    simp [hempty']

end ProbabilityTheory.BranchingRandomWalk
