/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.DependentLaw
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingPopulation

/-!
# The dependent stopped branching law for the selected process

The public declarations in namespace `ProbabilityTheory.BranchingRandomWalk`
specialize the abstract stopped-population law to the selected population
$P=\operatorname{selectedPopulationAt}(N,x,\tau)$:

- `selectedPopulation_stoppedSubtrees_measurable N x τ hτ hfinite` proves
  measurability of $\omega\mapsto\operatorname{stoppedPopulationSubtrees}(P)(\omega)$.
- `selectedPopulation_stoppedSubtrees_factorization μ N x τ hτ hfinite A hA B hB`
  states
  \[
    \nu_m\!\left(A\cap
      \operatorname{stoppedPopulationSubtrees}(P)^{-1}(B)\right)
    =\sum_s \nu_m\!\left(A\cap\{P=s\}\right)
      \left(\nu^{\otimes |s|}\right)
      \left(\iota_{|s|}^{-1}(B)\right),
  \]
  where $\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$,
  $\nu=\operatorname{stepFieldLaw}(\mu)$, and
  $\iota_k(\mathrm{fields})=\langle k,\mathrm{fields}\rangle$. Here $\tau$
  is an everywhere-finite stopping time, $A$ is measurable at $\tau$, and
  $B$ is measurable in the dependent descendant-family space. For roots
  $u_i=(r_i,v_i)$, the descendant-vector map is
  $\Phi_{\mathbf u}(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- The descendant-family random variable of the selected population at a
finite stopping time is measurable on the full pre-sampled space. -/
theorem selectedPopulation_stoppedSubtrees_measurable
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤) :
    Measurable (stoppedPopulationSubtrees
      (selectedPopulationAt N x τ)) :=
  stoppedPopulationSubtrees_measurable τ hτ
    (selectedPopulationAt N x τ)
    (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)

/-- At a finite stopping time, the selected population's dependent descendant
family has the countable mixture of the appropriate finite product laws. -/
theorem selectedPopulation_stoppedSubtrees_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set (StoppedSubtreeFamily ℝ)) (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ stoppedPopulationSubtrees
          (selectedPopulationAt N x τ) ⁻¹' B) =
      ∑' s : Finset (RootAddress m ℕ),
        finiteRootStepFieldLaw μ m
            (A ∩ {step | selectedPopulationAt N x τ step = s}) *
          (Measure.infinitePi
            (fun _ : Fin s.card => stepFieldLaw μ))
            ((stoppedSubtreeFamilyMk (X := ℝ) s.card) ⁻¹' B) := by
  exact stoppedPopulationSubtrees_factorization μ τ hτ hfinite
    (selectedPopulationAt N x τ)
    (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)
    (selectedPopulationAt_depth N x τ) A hA B hB

end ProbabilityTheory.BranchingRandomWalk
