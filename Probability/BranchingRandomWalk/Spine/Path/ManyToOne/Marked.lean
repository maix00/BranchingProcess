/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Marked
public import Probability.BranchingRandomWalk.Spine.Generation
public import Probability.Process.Tree.Path.WeightedRecords
public import Probability.Sequence.IID.Basic

/-!
# Many-to-one for complete reproductive records and correlated marks

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `familyPathManyToOne` proves
  `E[∑_(|u|=n) F((ξ_(u|j),uⱼ)_j)] = E_(μ̂ⁿ)[exp(∑ⱼ Xⱼ) F]`,
  with every ancestral offspring family retained.
* `markedPathManyToOne` projects these records to joint increments `(Xⱼ,Bⱼ)`:
  the right side is the existing IID law of `tiltedMarkedPotentialLaw`,
  with weight `exp(∑ⱼ Xⱼ)`. Marks may depend on the whole family and selected slot.

Both statements use the original raw offspring field and its boundary-normalized
joint spine law. They require no moment, nonextinction, finite offspring count,
or independence between the displacement and its mark. Native finite-product
measure transport reads distinct ancestral field coordinates; it introduces no
new branching process or recursive branching-density proof.

These are the marked many-to-one identity used in B. Mallein,
*N-branching random walk with α-stable spine* (2015), §2.1, Proposition 2.1, Lemma 2.2 and proof of Lemma 3.4,
arXiv:1503.03762, and *Necessary and sufficient conditions for the convergence
of the consistent maximal displacement of the branching random walk*,
§2.1, Proposition 2.1 and proof of Lemma 3.4, arXiv:1510.00602v2.
The former article uses the reflected spatial convention; here the bias is `exp(-X)`.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open BranchingProcess (offspringFieldLaw)
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

private lemma product_weight_compensate {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) {n : ℕ} (records : Fin n → Step ι X × ι) :
    (∏ j, realizedPotentialWeight φ (-1) (records j).1 (records j).2) *
      ENNReal.ofReal (Real.exp (∑ j, (records j).1.potentialValue' φ (records j).2)) =
      if ∀ j, survive (records j).1 (records j).2 then 1 else 0 := by
  by_cases hs : ∀ j, survive (records j).1 (records j).2
  · rw [ite_eq_left hs]
    have he : (∏ j, realizedPotentialWeight φ (-1) (records j).1 (records j).2) =
        ENNReal.ofReal (Real.exp (-∑ j, (records j).1.potentialValue' φ (records j).2)) := by
      simp only [realizedPotentialWeight, hs, ↓reduceIte, neg_one_mul]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _),
        ← Real.exp_sum, Finset.sum_neg_distrib]
    rw [he, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  · rw [ite_eq_right hs]
    obtain ⟨j, hj⟩ := not_forall.mp hs
    have hz : (∏ j, realizedPotentialWeight φ (-1) (records j).1 (records j).2) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [realizedPotentialWeight, hj]
    simp [hz]

/-- Complete-record extension of the many-to-one formula in B. Mallein,
*N-branching random walk with α-stable spine*, §2.1, Proposition 2.1 and
Lemma 2.2 (arXiv:1503.03762v2). It retains the entire family at every
strict ancestor and uses the reflected convention with bias `exp(-X)`. -/
theorem familyPathManyToOne {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ)
    {F : (Fin n → Step ι X × ι) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ field, ∑' z : Fin n → ι,
      if surviveAlong field [] (List.ofFn z) then F (Mark.pathRecords field z) else 0
      ∂offspringFieldLaw μ) =
      ∫⁻ records, ENNReal.ofReal (Real.exp
        (∑ j, (records j).1.potentialValue' φ (records j).2)) * F records
        ∂Measure.pi (fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ) := by
  let : IsProbabilityMeasure (tiltedFamilyChildLaw φ (-1) μ) :=
    tiltedFamilyChildLaw_isProbability φ μ hboundary
  let : IsFiniteMeasure (Measure.sum fun i : ι =>
      (μ.withDensity (fun ξ => realizedPotentialWeight φ (-1) ξ i)).map (fun ξ => (ξ, i))) := by
    change IsFiniteMeasure (tiltedFamilyChildLaw φ (-1) μ)
    infer_instance
  have hread : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have hG : Measurable (fun records : Fin n → Step ι X × ι =>
      ENNReal.ofReal (Real.exp
        (∑ j, (records j).1.potentialValue' φ (records j).2)) * F records) := by
    exact (ENNReal.measurable_ofReal.comp
      (Finset.measurable_sum _ (fun j _ => hread.comp (measurable_pi_apply j))).exp).mul hF
  have hi := Tree.lintegral_sum_weighted_pathRecords (ι := ι) μ
    (fun (i : ι) (ξ : Step ι X) => realizedPotentialWeight φ (-1) ξ i)
    (realizedPotentialWeight_measurable φ (-1)) n hG
  refine (lintegral_congr fun field => ?_).trans hi
  apply tsum_congr
  intro z
  have hs : surviveAlong field [] (List.ofFn z) ↔
      ∀ j : Fin n, survive ((Mark.pathRecords field z j).1)
        ((Mark.pathRecords field z j).2) := by
    constructor
    · intro h j
      have hj := (surviveAlong_root_iff_forall_fin field (List.ofFn z)).mp h
        (Fin.cast (show (List.ofFn z).length = n from List.length_ofFn).symm j)
      simpa [Mark.pathRecords, Fin.cast] using hj
    · intro h
      apply (surviveAlong_root_iff_forall_fin field (List.ofFn z)).mpr
      intro j
      have hj := h (Fin.cast (show (List.ofFn z).length = n from List.length_ofFn) j)
      simpa [Mark.pathRecords, Fin.cast] using hj
  change (if surviveAlong field [] (List.ofFn z) then F _ else 0) =
    (∏ j, realizedPotentialWeight φ (-1) (Mark.pathRecords field z j).1
      (Mark.pathRecords field z j).2) *
        (ENNReal.ofReal (Real.exp
          (∑ j, (Mark.pathRecords field z j).1.potentialValue' φ
            (Mark.pathRecords field z j).2)) * F _)
  rw [← mul_assoc, product_weight_compensate]
  by_cases h : surviveAlong field [] (List.ofFn z)
  · simp [h, hs.mp h]
  · simp only [ite_eq_right h, ite_eq_right (mt hs.mpr h), zero_mul]

/-- Projecting the complete records gives the correlated marked-path
many-to-one formula used in B. Mallein, *N-branching random walk with α-stable
spine*, proof of Lemma 3.4 (arXiv:1503.03762v2), and *Necessary and sufficient
conditions for the convergence of the consistent maximal displacement of the
branching random walk*, proof of Lemma 3.4 (arXiv:1510.00602v2).
The scalar displacement marginal is the original boundary-normalized law. -/
theorem markedPathManyToOne {ι X M : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X] [MeasurableSpace M]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {mark : Step ι X × ι → M} (hm : Measurable mark) (n : ℕ)
    {F : (Fin n → ℝ × M) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ field, ∑' z : Fin n → ι, if surviveAlong field [] (List.ofFn z) then
      F (fun j => ((Mark.pathRecords field z j).1.potentialValue' φ
        (Mark.pathRecords field z j).2, mark (Mark.pathRecords field z j))) else 0
      ∂offspringFieldLaw μ) =
      ∫⁻ sequence, ENNReal.ofReal (Real.exp (∑ j : Fin n, (sequence j).1)) *
        F (fun j : Fin n => sequence j)
        ∂iidSequenceLaw (tiltedMarkedPotentialLaw φ (-1) μ mark) := by
  let : IsProbabilityMeasure (tiltedFamilyChildLaw φ (-1) μ) :=
    tiltedFamilyChildLaw_isProbability φ μ hboundary
  let : IsProbabilityMeasure (tiltedMarkedPotentialLaw φ (-1) μ mark) :=
    tiltedMarkedPotentialLaw_isProbability φ μ hboundary hm
  let read (p : Step ι X × ι) : ℝ × M := (p.1.potentialValue' φ p.2, mark p)
  have hr : Measurable read :=
    (measurable_from_prod_countable_left
      (fun i => Step.potentialValue'_measurable φ i)).prodMk hm
  have hread : Measurable (fun records : Fin n → Step ι X × ι => fun j => read (records j)) := by
    fun_prop
  have hi := familyPathManyToOne φ μ hboundary n (hF.comp hread)
  refine hi.trans ?_
  have hg : Measurable (fun records : Fin n → ℝ × M =>
      ENNReal.ofReal (Real.exp (∑ j, (records j).1)) * F records) := by fun_prop
  have hp := Measure.pi_map_pi (μ := fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ)
    (f := fun _ => read) (fun _ => hr.aemeasurable)
  have hh := lintegral_map hg hread
    (μ := Measure.pi (fun _ : Fin n => tiltedFamilyChildLaw φ (-1) μ))
  rw [hp] at hh
  calc
    _ = ∫⁻ records, ENNReal.ofReal (Real.exp (∑ j : Fin n, (records j).1)) * F records
        ∂Measure.pi (fun _ : Fin n => tiltedMarkedPotentialLaw φ (-1) μ mark) := by
      simpa only [Function.comp_def, read, tiltedMarkedPotentialLaw] using hh.symm
    _ = _ := by
      rw [← iidSequenceLaw_map_finPrefix (tiltedMarkedPotentialLaw φ (-1) μ mark) n,
        lintegral_map hg (by fun_prop)]

end ProbabilityTheory.BranchingRandomWalk.Spine
