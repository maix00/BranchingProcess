/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.AddressFiltration
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.SelectedSubtreeVector
import MeasureTheory.Measure.Partition

/-!
# Factorization of stopped subtree-vector events

## Public declarations

The public declaration in namespace `ProbabilityTheory.BranchingRandomWalk` is
`stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite μ τ hτ
roots hcount hfiber hdepth hinj A B hA hB`. For $A\in\mathcal F_\tau$ and
measurable $B$, it states
\[
  \nu\bigl((A\cap\{\tau<\infty\})\cap\Phi^{-1}(B)\bigr)
  =\nu(A\cap\{\tau<\infty\})\,\nu^{\otimes\kappa}(B),
\]
where $\nu=\operatorname{offspringFieldLaw}(\mu)$ and
$\Phi(\omega)(i,v)=\omega(\operatorname{roots}(\omega)(i)\mathbin{++}v)$.
The assumptions require a stopping time, countable range and stopped-measurable
fibres for `roots`, depth equal to $\tau$ on each finite-time cell, and
injectivity of `roots` whenever $\tau<\infty$.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

private def abstractStoppedVectorCell {κ α X : Type*}
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (p : ℕ × (κ → TreeNode α)) :
    Set (TreeNode α → Step α X) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | roots ω = p.2}

private lemma abstractStoppedVectorCell_measurable
    {κ α X : Type*} [MeasurableSpace X]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × (κ → TreeNode α))
    (hrootSet : MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = p.2}) :
    MeasurableSet[generationFiltration (M := Step α X) p.1]
      (abstractStoppedVectorCell τ roots A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hrootEq := (hτ.measurableSet_inter_eq_iff
    {ω | roots ω = p.2} p.1).1
      (hrootSet.inter (hτ.measurable
        (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : abstractStoppedVectorCell τ roots A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | roots ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [abstractStoppedVectorCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hrootEq


/-- Branching factorization on the event that a stopping generation is
finite.  The stopping time may equal `⊤` with positive probability; on that
event no generation-`τ` subtree family is used. -/
theorem stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω))
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    offspringFieldLaw μ
        ((A ∩ {ω | τ ω ≠ ⊤}) ∩
          selectedSubtreeStepFieldVector roots ⁻¹' B) =
      offspringFieldLaw μ (A ∩ {ω | τ ω ≠ ⊤}) *
        (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
  let P := offspringFieldLaw μ
  let Q := Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)
  let A' := A ∩ {ω | τ ω ≠ ⊤}
  have hfinite : MeasurableSet[hτ.measurableSpace]
      {ω | τ ω ≠ ⊤} := by
    have htop : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
      hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    exact htop.compl
  have hA' : MeasurableSet[hτ.measurableSpace] A' := hA.inter hfinite
  let S : Set (κ → TreeNode α) := Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun p : ℕ × S =>
    abstractStoppedVectorCell τ roots A' (p.1, p.2.1)
  let D := fun p : ℕ × S =>
    C p ∩ subtreeStepFieldVector p.2.1 ⁻¹' B
  have hCmeasAt (p : ℕ × S) : MeasurableSet[
      generationFiltration (M := Step α X) p.1] (C p) :=
    abstractStoppedVectorCell_measurable τ hτ roots A' hA'
      (p.1, p.2.1) (hfiber p.2.1)
  have hCmeas (p : ℕ × S) : MeasurableSet (C p) :=
    (generationFiltration (M := Step α X) |>.le p.1) _ (hCmeasAt p)
  have hDmeas (p : ℕ × S) : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeStepFieldVector_measurable p.2.1) hB)
  have hcell (p : ℕ × S) : P (D p) = P (C p) * Q B := by
    by_cases hvalid : (∀ i, (p.2.1 i).length = p.1) ∧
        Function.Injective p.2.1
    · have hcellGen := hCmeasAt p
      exact fixed_subtreeStepFieldVector_event_factorization μ p.2.1
        hvalid.1 hvalid.2 (C p) B hcellGen hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, abstractStoppedVectorCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htime⟩, hroot⟩
        apply hvalid
        constructor
        · intro i
          simpa [← hroot] using hdepth ω p.1 htime i
        · have hfiniteω : τ ω ≠ ⊤ := by simp [htime]
          simpa [← hroot] using hinj ω hfiniteω
      simp [D, hempty]
  have hCpair : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨n, r⟩ ⟨k, s⟩ hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    apply hpq
    exact Prod.ext
      (WithTop.coe_injective (hp.1.2.symm.trans hq.1.2))
      (Subtype.ext (hp.2.symm.trans hq.2))
  have hDpair : Pairwise (fun p q => Disjoint (D p) (D q)) := by
    intro p q hpq
    exact (hCpair hpq).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ p, C p) = A' := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨_, ⟨hAω, _⟩, _⟩
      exact hAω
    · intro hAω
      cases htime : τ ω with
      | top => exact False.elim (hAω.2 htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, ⟨roots ω, Set.mem_range_self ω⟩),
              ⟨⟨hAω, htime⟩, rfl⟩⟩
  have hDunion : (⋃ p, D p) =
      A' ∩ selectedSubtreeStepFieldVector roots ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtreeStepFieldVector]
      rintro ⟨p, ⟨⟨⟨hAω, _⟩, htime⟩, hroot⟩, hBω⟩
      exact ⟨⟨hAω, by simp [htime]⟩, by simpa [hroot] using hBω⟩
    · rintro ⟨⟨hAω, hfiniteω⟩, hBω⟩
      cases htime : τ ω with
      | top => exact (hfiniteω htime).elim
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, ⟨roots ω, Set.mem_range_self ω⟩),
              ⟨⟨⟨⟨hAω, hfiniteω⟩, htime⟩, rfl⟩, hBω⟩⟩
  calc
    P (A' ∩ selectedSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = P (⋃ p, C p) * Q B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (Q B)
        hCmeas hDmeas hCpair hDpair hcell
    _ = P A' * Q B := by rw [hCunion]

end ProbabilityTheory.BranchingRandomWalk

end
