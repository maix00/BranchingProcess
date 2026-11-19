/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

import MeasureTheory.Measure.Partition

/-!
# Stopped vectors of subtrees in a root-indexed field

## Public declarations

The factorization declaration in namespace `ProbabilityTheory.BranchingRandomWalk`
is `RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite μ τ hτ roots hcount hfiber hdepth hinj A B hA hB`. For
$A\in\mathcal F_\tau$ and measurable $B$, it states
\[
  \nu_{\mathrm{Root}}\bigl((A\cap\{\tau<\infty\})\cap\Phi^{-1}(B)\bigr)
  =\nu_{\mathrm{Root}}(A\cap\{\tau<\infty\})\,\nu_\kappa(B),
\]
where
\[
  \Phi(\omega)(i,v)=\omega((\operatorname{roots}(\omega)(i))_1,
    (\operatorname{roots}(\omega)(i))_2\mathbin{++}v),
\]
with
$\nu_{\mathrm{Root}}=\operatorname{RootIndexed.stepFieldLaw}(\operatorname{Root}=\mathrm{Root},\mu)$ and
$\nu_\kappa=\operatorname{RootIndexed.stepFieldLaw}(\operatorname{Root}=\kappa,\mu)$.
The roots have arbitrary index type; the assumptions require countable range
and stopped-measurable fibres, depth equal to $\tau$ on finite-time cells, and
injectivity whenever $\tau<\infty$.

`RootIndexed.stopped_selectedSubtreeStepFieldVector_measure_test_le` gives
$\mathbb P(A,\tau\le T,\Phi\in B_\tau)\le\mathbb P(A,\tau\le T)p$
when each fresh-field test $B_i$ has probability at most $p$ for $i\le T$.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

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
  calc
    P (A' ∩ RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = P (⋃ p, C p) * Q B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (Q B)
        hCmeas hDmeas hCpair hDpair hcell
    _ = P A' * Q B := by rw [hCunion]

/-- A uniform fresh-field bound may be used for a test chosen by the observed
finite stopping generation. The weights of the stopping-time cells sum to
the probability that the test is performed. -/
theorem RootIndexed.stopped_selectedSubtreeStepFieldVector_measure_test_le
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : RootIndexed.StepField Root α X → WithTop ℕ)
    (hτ : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) τ)
    (roots : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace] {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).2.length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω))
    (A : Set (RootIndexed.StepField Root α X)) (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : ℕ → Set (κ → TreeNode α → Step α X)) (hB : ∀ i, MeasurableSet (B i))
    (T : ℕ) (p : ℝ≥0∞)
    (hp : ∀ i ≤ T, RootIndexed.stepFieldLaw (Root := κ) μ (B i) ≤ p) :
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    P {ω | ω ∈ A ∧ ∃ i ≤ T, τ ω = (i : WithTop ℕ) ∧
        RootIndexed.selectedSubtreeStepFieldVector roots ω ∈ B i} ≤
      P (A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}) * p := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := κ) μ
  let C (i : ℕ) := A ∩ {ω | τ ω = (i : WithTop ℕ)}
  let D (i : ℕ) := C i ∩ RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B i
  have hset : {ω | ω ∈ A ∧ ∃ i ≤ T, τ ω = (i : WithTop ℕ) ∧
      RootIndexed.selectedSubtreeStepFieldVector roots ω ∈ B i} =
      ⋃ i ∈ Finset.range (T + 1), D i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff,
      D, C, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hω, i, hi, ht, hb⟩
      exact ⟨i, hi, ⟨hω, ht⟩, hb⟩
    · rintro ⟨i, hi, ⟨hω, ht⟩, hb⟩
      exact ⟨hω, i, hi, ht, hb⟩
  have hC (i : ℕ) : MeasurableSet[hτ.measurableSpace] (C i) :=
    hA.inter (hτ.measurable (measurableSet_singleton (i : WithTop ℕ)))
  have hpair : Set.PairwiseDisjoint (↑(Finset.range (T + 1))) C := by
    intro i _ j _ hij
    apply Set.disjoint_left.2
    intro ω hi hj
    exact hij (WithTop.coe_injective (hi.2.symm.trans hj.2))
  have hcell (i : ℕ) : P (D i) = P (C i) * Q (B i) := by
    have hfinite : C i ∩ {ω | τ ω ≠ ⊤} = C i := by
      apply Set.inter_eq_left.mpr
      intro ω hω
      exact hω.2.trans_ne WithTop.coe_ne_top
    have h := RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots hcount hfiber hdepth hinj (C i) (B i) (hC i) (hB i)
    rw [hfinite] at h
    exact h
  intro _
  change P _ ≤ _
  rw [hset]
  calc
    _ ≤ ∑ i ∈ Finset.range (T + 1), P (D i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (T + 1), P (C i) * p := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hcell]
      exact mul_le_mul_right (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) _
    _ = P (⋃ i ∈ Finset.range (T + 1), C i) * p := by
      rw [← Finset.sum_mul, measure_biUnion_finset hpair]
      intro i _
      exact hτ.measurableSpace_le _ (hC i)
    _ ≤ _ := by
      apply mul_le_mul_left
      apply measure_mono
      intro ω hω
      simp only [Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff] at hω
      obtain ⟨i, hi, hω⟩ := hω
      exact ⟨hω.1, hω.2.le.trans (by exact_mod_cast hi)⟩

end ProbabilityTheory.BranchingRandomWalk
