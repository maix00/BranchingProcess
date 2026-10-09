/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Stopped vectors of subtrees in a root-indexed field

At a stopping generation, a stopped-measurable family of distinct roots has
fresh descendant fields with the product law, on the event that the stopping
generation is finite.  The root set may have arbitrary index type; only its
range is required to be countable so the stopped event can be partitioned into
fixed-root cells.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Branching factorization for a stopped family of subtrees in a
root-indexed field.  On the event of a finite stopping generation, a
stopped-measurable vector of distinct roots has the fresh product law,
independently of the stopped past. -/
theorem RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : RootIndexed.StepField Root α X → WithTop ℕ)
    (hτ : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) τ)
    (roots : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).2.length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω))
    (A : Set (RootIndexed.StepField Root α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        ((A ∩ {ω | τ ω ≠ ⊤}) ∩
          RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root) μ
        (A ∩ {ω | τ ω ≠ ⊤}) *
        RootIndexed.stepFieldLaw (Root := κ) μ B := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := κ) μ
  let A' := A ∩ {ω | τ ω ≠ ⊤}
  have hfinite : MeasurableSet[hτ.measurableSpace]
      {ω | τ ω ≠ ⊤} := by
    have htop : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
      hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    exact htop.compl
  have hA' : MeasurableSet[hτ.measurableSpace] A' := hA.inter hfinite
  let S : Set (κ → Root × TreeNode α) := Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun p : ℕ × S =>
    A' ∩ {ω | τ ω = (p.1 : WithTop ℕ)} ∩
      {ω | roots ω = p.2.1}
  let D := fun p : ℕ × S =>
    C p ∩ RootIndexed.subtreeStepFieldVector p.2.1 ⁻¹' B
  have hCmeasAt (p : ℕ × S) : MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) p.1]
      (C p) := by
    let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
    have hAeq : MeasurableSet[F p.1]
        (A' ∩ {ω | τ ω = (p.1 : WithTop ℕ)}) :=
      (hτ.measurableSet_inter_eq_iff A' p.1).1
        (hA'.inter (hτ.measurable
          (measurableSet_singleton (p.1 : WithTop ℕ))))
    have hreq : MeasurableSet[F p.1]
        ({ω | roots ω = p.2.1} ∩
          {ω | τ ω = (p.1 : WithTop ℕ)}) :=
      (hτ.measurableSet_inter_eq_iff
        {ω | roots ω = p.2.1} p.1).1
        ((hfiber p.2.1).inter (hτ.measurable
          (measurableSet_singleton (p.1 : WithTop ℕ))))
    have heq : C p =
        (A' ∩ {ω | τ ω = (p.1 : WithTop ℕ)}) ∩
          ({ω | roots ω = p.2.1} ∩
            {ω | τ ω = (p.1 : WithTop ℕ)}) := by
      ext ω
      simp [C, and_assoc, and_comm, and_left_comm]
    rw [heq]
    exact hAeq.inter hreq
  have hCmeas (p : ℕ × S) : MeasurableSet (C p) :=
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) |>.le p.1)
      _ (hCmeasAt p)
  have hDmeas (p : ℕ × S) : MeasurableSet (D p) :=
    (hCmeas p).inter
      (RootIndexed.subtreeStepFieldVector_measurable p.2.1 hB)
  have hcell (p : ℕ × S) : P (D p) = P (C p) * Q B := by
    by_cases hvalid :
        (∀ i, (p.2.1 i).2.length = p.1) ∧ Function.Injective p.2.1
    · exact RootIndexed.subtreeStepFieldVector_event_factorization μ
        p.2.1 hvalid.1 hvalid.2 (C p) B (hCmeasAt p) hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
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
    · simp only [Set.mem_iUnion, C, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
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
      A' ∩ RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage,
      RootIndexed.selectedSubtreeStepFieldVector]
    constructor
    · rintro ⟨p, ⟨⟨⟨hAω, _⟩, htime⟩, hroot⟩, hBω⟩
      exact ⟨⟨hAω, by simp [htime]⟩,
        by simpa [hroot] using hBω⟩
    · rintro ⟨⟨hAω, hfiniteω⟩, hBω⟩
      cases htime : τ ω with
      | top => exact (hfiniteω htime).elim
      | coe n =>
          let p : ℕ × S := (n, ⟨roots ω, Set.mem_range_self ω⟩)
          refine ⟨p, ?_⟩
          exact ⟨⟨⟨⟨hAω, hfiniteω⟩, rfl⟩, rfl⟩,
            by simpa [RootIndexed.selectedSubtreeStepFieldVector, p] using hBω⟩
  have hCsum : (∑' p, P (C p)) = P A' := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A' ∩ RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * Q B := tsum_congr hcell
    _ = (∑' p, P (C p)) * Q B := ENNReal.tsum_mul_right
    _ = P A' * Q B := by rw [hCsum]

end ProbabilityTheory.BranchingRandomWalk
