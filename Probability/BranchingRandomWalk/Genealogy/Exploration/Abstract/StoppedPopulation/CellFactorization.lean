/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
public import Probability.Process.HittingTime.Declarations

import MeasureTheory.Measure.Partition

/-!
# Cellwise factorization for a stopped finite population

## Public declarations

The theorem `abstractStoppedPopulation_cell_factorization` states
that, for a fixed population value $s$ and an injective enumeration of its
roots, the event of a measurable descendant vector $B$ factors from any
stopped-past event $A$ on that population cell. For roots
$u_i=(r_i,v_i)$, define
$\Phi_{\mathbf u}(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$,
$\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$, and
$\nu=\operatorname{offspringFieldLaw}(\mu)$. The lemma proves
\[
  \nu_m\!\left((A\cap\{\mathrm{population}=s\})
      \cap\Phi_{\mathbf u}^{-1}(B)\right)
  =\nu_m\!\left(A\cap\{\mathrm{population}=s\}\right)
    \left(\bigotimes_{i\in\mathrm{Fin}\,k}\nu\right)(B).
\]
It applies to arbitrary measurable mark spaces and supplies the cellwise
product law used by the random-cardinality mixture theorem in `RandomCardinalityLaw`
and by selected-population specializations.

- `abstractStoppedPopulation_cell_factorization` is the cellwise product-law
  identity displayed above, for a fixed finite population value and an
  injective enumeration of its roots.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem abstractStoppedPopulation_cell_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
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
    (s : Finset (Fin m × 𝕍))
    (roots : Fin k → Fin m × 𝕍)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → 𝕍 → Step ℕ X))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        ((A ∩ {step | population step = s}) ∩
          RootIndexed.subtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m (A ∩ {step | population step = s}) *
        (Measure.infinitePi (fun _ : Fin k => offspringFieldLaw μ)) B := by
  let P := finiteRootStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => offspringFieldLaw μ)
  let E : Set (FiniteRootStepField m ℕ X) :=
    A ∩ {step | population step = s}
  let C : ℕ → Set (FiniteRootStepField m ℕ X) :=
    fun n => E ∩ {step | τ step = (n : WithTop ℕ)}
  let D : ℕ → Set (FiniteRootStepField m ℕ X) :=
    fun n => C n ∩ RootIndexed.subtreeStepFieldVector roots ⁻¹' B
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    hA.inter (hpopulation s)
  have hCgen n : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] (C n) :=
    (hτ.measurableSet_inter_eq_iff E n).1
      (hE.inter (hτ.measurable
        (measurableSet_singleton (n : WithTop ℕ))))
  have hCmeas n : MeasurableSet (C n) :=
    (multiRootStepFiltration (m := m) (X := X) |>.le n) _ (hCgen n)
  have hDmeas n : MeasurableSet (D n) :=
    (hCmeas n).inter ((RootIndexed.subtreeStepFieldVector_measurable roots) hB)
  have hcell n : P (D n) = P (C n) * Q B := by
    by_cases hlen : ∀ j, (roots j).2.length = n
    · exact RootIndexed.subtreeStepFieldVector_event_factorization μ roots
        hlen hinj (C n) B (hCgen n) hB
    · have hempty : C n = ∅ := by
        ext step
        simp only [C, E, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hpop⟩, htime⟩
        apply hlen
        intro j
        apply hdepth step (roots j)
        · rw [hpop, hcover]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact htime
      simp [D, hempty]
  have hCpair : Pairwise (fun n l => Disjoint (C n) (C l)) := by
    intro n l hne
    apply Set.disjoint_left.mpr
    intro step hn hl
    apply hne
    exact WithTop.coe_injective (hn.2.symm.trans hl.2)
  have hDpair : Pairwise (fun n l => Disjoint (D n) (D l)) := by
    intro n l hne
    exact (hCpair hne).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ n, C n) = E := by
    ext step
    constructor
    · simp only [Set.mem_iUnion, C, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨n, hEstep, _⟩
      exact hEstep
    · intro hEstep
      cases htime : τ step with
      | top => exact False.elim (hfinite step htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, hEstep, htime⟩
  have hDunion : (⋃ n, D n) =
      E ∩ RootIndexed.subtreeStepFieldVector roots ⁻¹' B := by
    ext step
    constructor
    · simp only [Set.mem_iUnion, D, C, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage]
      rintro ⟨n, ⟨⟨hEstep, _⟩, hBstep⟩⟩
      exact ⟨hEstep, hBstep⟩
    · rintro ⟨hEstep, hBstep⟩
      cases htime : τ step with
      | top => exact False.elim (hfinite step htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hEstep, htime⟩, hBstep⟩⟩
  calc
    P (E ∩ RootIndexed.subtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ n, D n) := by rw [hDunion]
    _ = P (⋃ n, C n) * Q B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (Q B)
        hCmeas hDmeas hCpair hDpair hcell
    _ = P E * Q B := by rw [hCunion]

end ProbabilityTheory.BranchingRandomWalk
