/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Conditional expectations of stopped descendant fields

## Public declarations

* `RootIndexed.integral_stopped_selectedSubtreeStepFieldVector`: if
  $A\in\mathcal F_\tau$, the selected roots are distinct at generation $\tau$,
  and the fresh test $g_i$ is integrable for every $i\le T$, the stopped
  payoff is integrable on $A\cap\{\tau\le T\}$ and
  $\int_{A\cap\{\tau\le T\}}g_\tau(\Phi)\,dP
    =\sum_{i=0}^T P(A\cap\{\tau=i\})\int g_i\,dQ$.
  Here $\Phi$ is the vector of selected descendant fields and $Q$ is the
  independent product offspring-field law.
* `RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le` bounds
  the same integral by $P(A\cap\{\tau\le T\})b$ when every fresh mean is at most $b$.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Integrate an integrable fresh-field payoff chosen by a bounded
stopping generation, restricted to an event in the stopped domain. -/
theorem RootIndexed.integral_stopped_selectedSubtreeStepFieldVector
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
    (T : ℕ) (g : ℕ → RootIndexed.StepField κ α X → ℝ)
    (hg : ∀ i, Measurable (g i))
    (hi : ∀ i ≤ T, Integrable (g i) (RootIndexed.stepFieldLaw μ)) :
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := κ) μ
    IntegrableOn (fun ω => g ((τ ω).untopD 0)
      (RootIndexed.selectedSubtreeStepFieldVector roots ω)) (A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}) P ∧
    (∫ ω in A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}, g ((τ ω).untopD 0)
      (RootIndexed.selectedSubtreeStepFieldVector roots ω) ∂P) =
      ∑ i ∈ Finset.range (T + 1), P.real (A ∩ {ω | τ ω = (i : WithTop ℕ)}) *
        ∫ f, g i f ∂Q := by
  classical
  intro P Q
  let V := RootIndexed.selectedSubtreeStepFieldVector roots
  let C (i : ℕ) := A ∩ {ω | τ ω = (i : WithTop ℕ)}
  let F := fun ω => g ((τ ω).untopD 0) (V ω)
  have hC (i : ℕ) : MeasurableSet[hτ.measurableSpace] (C i) :=
    hA.inter (hτ.measurable (measurableSet_singleton (i : WithTop ℕ)))
  have hCfull (i : ℕ) : MeasurableSet (C i) := hτ.measurableSpace_le _ (hC i)
  have hV : Measurable V := by
    let S : Set (κ → Root × TreeNode α) := Set.range roots
    let _ : Countable S := Set.countable_coe_iff.mpr hcount
    intro B hB
    have heq : V ⁻¹' B = ⋃ q : S, {ω | roots ω = q.1} ∩
        RootIndexed.subtreeStepFieldVector q.1 ⁻¹' B := by
      ext ω
      constructor
      · intro h
        exact Set.mem_iUnion.mpr ⟨⟨roots ω, Set.mem_range_self ω⟩, rfl, h⟩
      · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
        rintro ⟨q, hq, h⟩
        change RootIndexed.subtreeStepFieldVector (roots ω) ω ∈ B
        rwa [hq]
    rw [heq]
    exact MeasurableSet.iUnion fun q => (hτ.measurableSpace_le _ (hfiber q.1)).inter
      (RootIndexed.subtreeStepFieldVector_measurable q.1 hB)
  have hmap (i : ℕ) : (P.restrict (C i)).map V = P (C i) • Q := by
    ext B hB
    have hfinite : C i ∩ {ω | τ ω ≠ ⊤} = C i :=
      Set.inter_eq_left.mpr fun _ hw => hw.2.trans_ne WithTop.coe_ne_top
    have h := RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots hcount hfiber hdepth hinj (C i) B (hC i) hB
    rw [hfinite] at h
    rw [Measure.map_apply hV hB, Measure.restrict_apply' (hCfull i), smul_apply,
      smul_eq_mul, Set.inter_comm]
    exact h
  have heq (i : ℕ) : F =ᵐ[P.restrict (C i)] fun ω => g i (V ω) := by
    filter_upwards [ae_restrict_mem (hCfull i)] with ω hw
    have ht : τ ω = (i : WithTop ℕ) := hw.2
    change g ((τ ω).untopD 0) (V ω) = _
    rw [ht]
    rfl
  have hint (i : ℕ) (h : i ∈ Finset.range (T + 1)) : IntegrableOn F (C i) P := by
    have hgmap : Integrable (g i) ((P.restrict (C i)).map V) := by
      rw [hmap]
      exact (hi i (Nat.le_of_lt_succ (Finset.mem_range.mp h))).smul_measure
        (measure_ne_top P (C i))
    exact (hgmap.comp_measurable hV).congr (heq i).symm
  have hsum : A ∩ {ω | τ ω ≤ (T : WithTop ℕ)} =
      ⋃ i ∈ Finset.range (T + 1), C i := by
    ext ω
    simp only [C, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨ha, ht⟩
      cases he : τ ω with
      | top => simp [he] at ht
      | coe i => exact ⟨i, Nat.lt_succ_of_le (WithTop.coe_le_coe.mp (he ▸ ht)), ha, rfl⟩
    · rintro ⟨i, hi, ha, he⟩
      exact ⟨ha, he.le.trans (WithTop.coe_le_coe.mpr (Nat.le_of_lt_succ hi))⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (T + 1))) C := by
    intro i _ j _ hij
    exact Set.disjoint_left.mpr fun _ hi hj =>
      hij (WithTop.coe_injective (hi.2.symm.trans hj.2))
  refine ⟨?_, ?_⟩
  · change IntegrableOn F _ P
    rw [hsum]
    generalize Finset.range (T + 1) = J at hint ⊢
    induction J using Finset.induction_on with
    | empty => simp
    | @insert i J hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hint i (Finset.mem_insert_self _ _)).union
        (ih fun j hj => hint j (Finset.mem_insert_of_mem hj))
  change (∫ ω in _, F ω ∂P) = _
  rw [hsum, integral_biUnion_finset _ (fun i _ => hCfull i) hdisj hint]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ ω in C i, g i (V ω) ∂P := integral_congr_ae (heq i)
    _ = ∫ y, g i y ∂(P (C i) • Q) := by
      rw [← hmap, integral_map hV.aemeasurable (hg i).aestronglyMeasurable]
    _ = _ := by simp [integral_smul_measure, measureReal_def, C]

/-- A common upper bound on the fresh means bounds the stopped expectation,
with weight equal to the mass of the event on which the test is performed. -/
theorem RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le
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
    (T : ℕ) (g : ℕ → RootIndexed.StepField κ α X → ℝ)
    (hg : ∀ i, Measurable (g i))
    (hi : ∀ i ≤ T, Integrable (g i) (RootIndexed.stepFieldLaw μ))
    (b : ℝ) (hb : ∀ i ≤ T, (∫ f, g i f ∂RootIndexed.stepFieldLaw μ) ≤ b) :
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    IntegrableOn (fun ω => g ((τ ω).untopD 0)
      (RootIndexed.selectedSubtreeStepFieldVector roots ω)) (A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}) P ∧
    (∫ ω in A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}, g ((τ ω).untopD 0)
      (RootIndexed.selectedSubtreeStepFieldVector roots ω) ∂P) ≤
      P.real (A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}) * b := by
  intro P
  obtain ⟨hint, hintFormula⟩ := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector
    μ τ hτ roots hcount hfiber hdepth hinj A hA T g hg hi
  refine ⟨hint, ?_⟩
  let weight i := P.real (A ∩ {ω | τ ω = (i : WithTop ℕ)})
  have hmass : ∑ i ∈ Finset.range (T + 1), weight i =
      P.real (A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}) := by
    have h := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector μ τ hτ roots hcount
      hfiber hdepth hinj A hA T (fun _ _ => (1 : ℝ))
      (fun _ => measurable_const) (fun _ _ => integrable_const _)
    simpa [weight, integral_const, Measure.restrict_apply_univ] using h.2.symm
  rw [hintFormula]
  change (∑ i ∈ Finset.range (T + 1), weight i * ∫ f, g i f ∂RootIndexed.stepFieldLaw μ) ≤ _
  rw [← hmass, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left
    (hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))) measureReal_nonneg

end ProbabilityTheory.BranchingRandomWalk

end
