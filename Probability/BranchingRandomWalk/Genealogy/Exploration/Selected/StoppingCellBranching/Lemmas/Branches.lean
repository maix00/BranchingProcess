/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.Lemmas.Factorization
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.CellBranching
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingPopulation

/-!
# Choosing an enumeration on each stopped population cell

For each finite population value $s$, the proof-only lemma
`multiRoot_stoppedPopulation_each_cell_branches` chooses an injective
enumeration $u:\mathrm{Fin}(|s|)\to s$ and gives, for every stopped-past event
$A$ and measurable descendant-vector event $B$,
\[
  \nu_m\!\left((A\cap\{\operatorname{population}=s\})
      \cap\Phi_u^{-1}(B)\right)
  =\nu_m\!\left(A\cap\{\operatorname{population}=s\}\right)
      \left(\nu^{\otimes |s|}\right)(B),
\]
where $\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$,
$\nu=\operatorname{stepFieldLaw}(\mu)$, and, writing $u_i=(r_i,v_i)$,
$\Phi_u(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$. This specialization
feeds the public random-cardinality statement in `RandomSize.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- Every cell of a stopped finite population admits an enumeration whose
descendant vector branches with the appropriate (cell-dependent) finite
product law. -/
lemma multiRoot_stoppedPopulation_each_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ}
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : FiniteRootStepField m ℕ ℝ → Finset (RootAddress m ℕ))
    (hpopulation : ∀ s : Finset (RootAddress m ℕ),
      MeasurableSet[hτ.measurableSpace] {ω | population ω = s})
    (hdepth : ∀ ω (u : RootAddress m ℕ), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
            ((A ∩ {ω | population ω = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m (A ∩ {ω | population ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    abstractStoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s roots hcover hinj B hB⟩

end ProbabilityTheory.BranchingRandomWalk
