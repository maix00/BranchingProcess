/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Mark.Path
public import MeasureTheory.Measure.Pi.WeightedPairs

/-!
# Weighted ancestral records of an independent tree field

## Public declarations

In `ProbabilityTheory.Tree`:

* `measurable_pathRecords` proves measurability of the finite ancestral
  record `(field(z|j),zⱼ)_(j<n)`.
* `lintegral_sum_weighted_pathRecords` states
  `E[∑_z (∏ⱼ w(field(z|j),zⱼ)) F((field(z|j),zⱼ)_j)] = ∫ F dγⁿ`,
  where `γ(dx,i)=w(x,i) μ(dx)`.

This is a law transport for independent address coordinates and finite
products of weighted measures. The address field has the native product
law `μ^(List ι)`. No state-tree recursion, branching reproduction,
normalization of `γ`, survival, or harmonic function is assumed.
The observation `x` may retain a whole reproductive family. This supplies
the finite joint-law calculation used by B. Mallein, *N-branching random
walk with α-stable spine* (2015), §2.1, arXiv:1503.03762.
-/

@[expose] public section
namespace ProbabilityTheory.Tree
open MeasureTheory Combinatorics.UlamHarris
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

theorem measurable_pathRecords {ι E : Type*}
    [MeasurableSpace ι] [MeasurableSpace E] {n : ℕ} (z : Fin n → ι) :
    Measurable (fun field : Mark ι E => Mark.pathRecords field z) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (show Measurable (fun field : Mark ι E => field ((List.ofFn z).take j)) from
    measurable_pi_apply _).prodMk (measurable_const : Measurable (fun _ : Mark ι E => z j))

private lemma prefix_injective {ι : Type*} {n : ℕ} (z : Fin n → ι) :
    Function.Injective (fun j : Fin n => (List.ofFn z).take j) := by
  intro i j h
  have hh := congrArg List.length h
  simp only [List.length_take, List.length_ofFn,
    Nat.min_eq_left i.isLt.le, Nat.min_eq_left j.isLt.le] at hh
  exact Fin.ext hh

theorem lintegral_sum_weighted_pathRecords {ι E : Type*}
    [MeasurableSpace ι] [Countable ι] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (w : ι → E → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    [IsFiniteMeasure (Measure.sum fun i => (μ.withDensity (w i)).map (fun x => (x, i)))]
    (n : ℕ) {F : (Fin n → E × ι) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ field : Mark ι E, ∑' z : Fin n → ι,
      (∏ j, w (z j) (field ((List.ofFn z).take j))) * F (Mark.pathRecords field z)
      ∂Measure.infinitePi (fun _ : TreeNode ι => μ)) =
      ∫⁻ records, F records ∂Measure.pi
        (fun _ : Fin n => Measure.sum fun i =>
          (μ.withDensity (w i)).map (fun x => (x, i))) := by
  have hterm (z : Fin n → ι) : Measurable (fun field : Mark ι E =>
      (∏ j, w (z j) (field ((List.ofFn z).take j))) * F (Mark.pathRecords field z)) :=
    (Finset.measurable_prod _ (fun j _ =>
      (hw (z j)).comp (measurable_pi_apply _))).mul
        (hF.comp (measurable_pathRecords z))
  rw [lintegral_tsum (fun z => (hterm z).aemeasurable)]
  rw [Measure.lintegral_pi_sum_map_withDensity
    (fun _ : Fin n => μ) (fun _ i => w i) (fun _ i => hw i) hF]
  apply tsum_congr
  intro z
  have hlaw :
      (Measure.infinitePi (fun _ : TreeNode ι => μ)).map
        (fun (field : Mark ι E) (j : Fin n) => field ((List.ofFn z).take j)) =
      Measure.pi (fun _ : Fin n => μ) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj (prefix_injective z),
      Measure.infinitePi_eq_pi]
  have hg : Measurable (fun x : Fin n → E =>
      (∏ j, w (z j) (x j)) * F (fun j => (x j, z j))) := by
    exact (Finset.measurable_prod _ (fun j _ =>
      (hw (z j)).comp (measurable_pi_apply j))).mul (hF.comp (by fun_prop))
  rw [← hlaw, lintegral_map hg (by fun_prop)]
  rfl

end ProbabilityTheory.Tree
