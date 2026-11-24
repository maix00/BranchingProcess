/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Offspring.Kernel
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Local changes of offspring-family and distinguished-child law

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `LocalBias` specifies a measurable eligible-state domain and a local
  nonnegative density `r(s,ξ,i)` (measurability is recorded in `IsAdmissible`).
* `LocalBias.familyChildKernel` is `Q(s,dξ) r(s,ξ,i)` on families and indices.
* `LocalBias.lintegral_familyChildKernel` gives its weighted integral identity.
* `LocalBias.familyChildKernel_mass` gives `E_Q(s)[∑_i r(s,ξ,i)]`.
* `LocalBias.IsAdmissible` requires measurable data, unit expected total bias
  on eligible parents, and an almost-sure existing eligible selected child.
* `LocalBias.familyChildKernel_isProbabilityMeasure` and
  `LocalBias.ae_familyChildKernel_eligible` give normalization and support.
* `LocalBias.weighted` uses `r=h(child)/normalizer(s)`, and
  `LocalBias.normalizedWeight` takes `normalizer=Mh`.
* `LocalBias.ofWeight` specializes to `D={0<h<∞}`, `r=h(child)/h(parent)`;
  it introduces no second family kernel.

This isolates the local density step in Zhan Shi, *Branching Random Walks*
(2015), Theorem 4.3, (4.12)–(4.13), DOI 10.1007/978-3-319-25372-5.
The density may depend on the whole offspring family. No harmonic function,
finite expected offspring count, or moment condition is imposed here.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

structure LocalBias (S ι : Type*) where
  domain : Set S
  density : S → Step ι S → ι → ℝ≥0∞

namespace LocalBias

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]

/-- Joint local density, expressed with native sum, map and density kernels. -/
noncomputable def familyChildKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) : Kernel S (Step ι S × ι) :=
  Kernel.sum fun i =>
    (Q.withDensity (fun s ξ => B.density s ξ i)).map (fun ξ => (ξ, i))

/-- The exact hypotheses for an indefinitely continuing distinguished lineage. -/
structure IsAdmissible (B : LocalBias S ι) (Q : Kernel S (Step ι S)) : Prop where
  measurableSet_domain : MeasurableSet B.domain
  measurable_density : ∀ i, Measurable (Function.uncurry (fun s ξ => B.density s ξ i))
  normalized : ∀ s ∈ B.domain, (∫⁻ ξ, ∑' i, B.density s ξ i ∂Q s) = 1
  supported : ∀ s ∈ B.domain, ∀ᵐ ξ ∂Q s, ∀ i,
    B.density s ξ i ≠ 0 → ∃ t, ξ i = some t ∧ t ∈ B.domain

/-- Integrating the distinguished family/index is the offspring-weighted sum. -/
theorem lintegral_familyChildKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι)
    (hr : ∀ i, Measurable (Function.uncurry (fun s ξ => B.density s ξ i)))
    {g : Step ι S × ι → ℝ≥0∞} (hg : Measurable g) (s : S) :
    (∫⁻ p, g p ∂familyChildKernel Q B s) =
      ∑' i, ∫⁻ ξ, B.density s ξ i * g (ξ, i) ∂Q s := by
  rw [familyChildKernel, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [Kernel.lintegral_map _ (by fun_prop) s hg]
  exact Kernel.lintegral_withDensity Q (hr i) s (g := fun ξ => g (ξ, i)) (by fun_prop)

theorem familyChildKernel_mass (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι)
    (hr : ∀ i, Measurable (Function.uncurry (fun s ξ => B.density s ξ i))) (s : S) :
    familyChildKernel Q B s Set.univ = ∫⁻ ξ, ∑' i, B.density s ξ i ∂Q s := by
  have hi := lintegral_familyChildKernel Q B hr measurable_const s (g := fun _ => 1)
  simp only [lintegral_one, mul_one] at hi
  rw [hi]
  exact (lintegral_tsum (μ := Q s)
    (fun i => ((hr i).comp (measurable_const.prodMk measurable_id)).aemeasurable)).symm

theorem familyChildKernel_isProbabilityMeasure
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) (s : S) (hs : s ∈ B.domain) :
    IsProbabilityMeasure (familyChildKernel Q B s) := by
  constructor
  rw [familyChildKernel_mass Q B hB.measurable_density, hB.normalized s hs]

/-- Absence and states outside the eligible domain have zero selected mass. -/
theorem ae_familyChildKernel_eligible [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) (s : S) (hs : s ∈ B.domain) :
    ∀ᵐ p ∂familyChildKernel Q B s,
      ∃ t, p.1 p.2 = some t ∧ t ∈ B.domain := by
  have heval : Measurable (fun p : Step ι S × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hgood : MeasurableSet {p : Step ι S × ι |
      ∃ t, p.1 p.2 = some t ∧ t ∈ B.domain} := by
    convert (measurableSet_option_some_image hB.measurableSet_domain).preimage heval using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    aesop
  rw [familyChildKernel, Kernel.sum_apply, Measure.ae_sum_iff]
  intro i
  rw [Kernel.map_apply _ (by fun_prop)]
  apply (ae_map_iff (by fun_prop) hgood).mpr
  rw [Kernel.withDensity_apply Q (hB.measurable_density i)]
  apply (ae_withDensity_iff
    ((hB.measurable_density i).comp (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [hB.supported s hs] with ξ hξ
  exact hξ i

/-- Child weight divided by a measurable state-dependent normalizer. -/
noncomputable def weighted (h normalizer : S → ℝ≥0∞) : LocalBias S ι where
  domain := {s | h s ≠ 0 ∧ h s ≠ ∞}
  density := fun s ξ i => (ξ i).elim 0 h / normalizer s

/-- Local mean normalization; no harmonicity or constant eigenvalue is required. -/
noncomputable def normalizedWeight (Q : Kernel S (Step ι S)) (h : S → ℝ≥0∞) :
    LocalBias S ι :=
  weighted h (fun s => ∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s)

/-- The mean-harmonic specialization uses the parent weight as normalizer. -/
noncomputable def ofWeight (h : S → ℝ≥0∞) : LocalBias S ι := weighted h h

end LocalBias
end ProbabilityTheory.BranchingProcess.Spine
