/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.AddressFiltration

public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.UlamHarris.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Subtree

import Combinatorics.UlamHarris.Generation

/-!
# Joint law of an arbitrary family of abstract branching subtrees

## Public declarations

Distinct roots at one generation use disjoint coordinates.  Their descendant
step fields therefore have the joint law of independent copies of the full
pre-sampled branching-step field. Neither the family index nor the child-slot
type is restricted to a finite or countable type in this product-law theorem.

If the roots `r_i` are distinct and all have generation `n`, let
`\Phi(\omega)(i)(v)=\omega(r_i\mathbin{+\!+}v)` and let `\nu` be the
pre-sampled step-field law. Their joint subtree law and its independence from
the generation-`n` past are

\[\begin{aligned}
\Phi_{\#}\nu&=\nu^{\otimes\kappa},\\
\nu\bigl(A\cap\Phi^{-1}(B)\bigr)
&=\nu(A)\,\nu^{\otimes\kappa}(B),
\quad A\in\mathscr F_n^-,\ B\text{ measurable}.
\end{aligned}\]

- `subtreeStepFieldVector roots ω` is the family
  `i ↦ (v ↦ ω (roots i ++ v))`; `subtreeStepFieldVector_measurable` proves
  measurability.
- `fixed_subtreeStepFieldVector_law` states, for same-generation distinct
  roots, that
  `Measure.map (offspringFieldLaw μ) (subtreeStepFieldVector roots) =
  Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)`.
  `fixed_subtreeStepFieldVector_independent` states independence of the
  generation-`n` past and this vector field; its event form is
  `ν (A ∩ Φ ⁻¹' B) = ν A * (Measure.infinitePi (fun _ : κ => ν)) B`,
  where `ν = offspringFieldLaw μ` and `Φ = subtreeStepFieldVector roots`.
- `fixed_subtreeStepFieldVector_event_factorization` states this event
  factorization explicitly for measurable `A` in the generation-`n` past and
  measurable `B`, assuming the roots have depth `n` and are injectively
  indexed.
- `stepDescendantSpace_le_future` and
  `subtreeStepFieldVector_future_measurable` place these descendants in the
  future-coordinate sigma-algebra.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def subtreeStepFieldVector {κ α X : Type*}
    (roots : κ → TreeNode α)
    (ω : TreeNode α → Step α X) :
    κ → TreeNode α → Step α X :=
  fun i => subtreeStepField (roots i) ω

theorem subtreeStepFieldVector_measurable
    {κ α X : Type*} [MeasurableSpace X]
    (roots : κ → TreeNode α) :
    Measurable (subtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro i
  exact subtreeStepField_measurable (roots i)

theorem fixed_subtreeStepFieldVector_law
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    (offspringFieldLaw μ).map (subtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : κ => offspringFieldLaw μ) := by
  let rooted : κ → Unit × TreeNode α := fun i => ((), roots i)
  have hrooted : Function.Injective rooted := by
    intro i j hij
    exact hinj (congrArg Prod.snd hij)
  have happend :=
    Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
      rooted hlen hrooted
  have hflatInjective : Function.Injective
      (fun p : κ × TreeNode α => (rooted p.1).2 ++ p.2) := by
    intro p q hp
    apply happend
    exact Prod.ext rfl hp
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode α => μ)
    (f := fun p : κ × TreeNode α => (rooted p.1).2 ++ p.2)
    hflatInjective
  have hcurry := Measure.infinitePi_map_curry
    (μ := fun (_ : κ) (_ : TreeNode α) => μ)
  change (Measure.infinitePi (fun _ : TreeNode α => μ)).map
    (fun ω i v => ω (roots i ++ v)) =
      Measure.infinitePi
        (fun _ : κ => Measure.infinitePi (fun _ : TreeNode α => μ))
  rw [← hcurry, ← hflat]
  rw [Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (κ) (TreeNode α)
      (Step α X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply (roots p.1 ++ p.2)

theorem stepDescendantSpace_le_future
    {α X : Type*} [MeasurableSpace X]
    (n : ℕ) (u : TreeNode α) (hu : n ≤ u.length) :
    stepDescendantSpace (X := X) u ≤
      stepFutureSpace n := by
  rw [stepDescendantSpace_eq_iSup]
  apply iSup_le
  intro w
  apply iSup_le
  rintro ⟨v, rfl⟩
  have hdepth : n ≤ (u ++ v).length := by simp; omega
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem subtreeStepFieldVector_future_measurable
    {α X : Type*} [MeasurableSpace X] {κ : Type*} {n : ℕ}
    (roots : κ → TreeNode α) (hlen : ∀ i, (roots i).length = n) :
    Measurable[stepFutureSpace n]
      (subtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff
    (TreeNode α → Step α X) (κ)
    (fun _ => TreeNode α → Step α X)
    (stepFutureSpace n) (fun _ => inferInstance)
    (subtreeStepFieldVector roots)).2
  intro i
  exact (subtreeStepField_descendant_measurable (X := X) (roots i)).mono
    (stepDescendantSpace_le_future n (roots i) (by rw [hlen i]))
    le_rfl

theorem fixed_subtreeStepFieldVector_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance)
      (offspringFieldLaw μ) :=
  indep_of_indep_of_le_right
    (generation_stepFuture_independent μ n)
    (subtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem fixed_subtreeStepFieldVector_event_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots)
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) :
    offspringFieldLaw μ (A ∩ subtreeStepFieldVector roots ⁻¹' B) =
      offspringFieldLaw μ A *
        (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance]
      (subtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_subtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepFieldVector_measurable roots) hB,
    fixed_subtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk

end
