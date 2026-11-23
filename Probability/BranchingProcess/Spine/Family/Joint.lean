/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Offspring.Kernel
public import Probability.Kernel.DoobTransform.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Joint bias of an offspring family and a distinguished child

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `biasedFamilyChild Q h` is the kernel
  `Q(s,dξ) h(ξ_i)/h(s)` on families paired with a child index. An absent
  child has weight zero. The sum runs over the existing indexed offspring family.
* `lintegral_biasedFamilyChild` states the joint weighted integral formula.
* `biasedFamilyChild_mass` states
  `Q̂(s,univ) = E_Q(s)[∑_i h(ξ_i)]/h(s)`.
* `biasedFamilyChild_isProbabilityMeasure` normalizes this law at any state
  with `0 < h(s) < ∞` and `E[∑_i h(ξ_i)] = h(s)`.

This is the joint form of Zhan Shi, *Branching Random Walks*, Lecture Notes
in Mathematics 2151 (Springer, 2015), Chapter 4, §4.4, (4.8) and the
subsequent biased-family / selected-child construction,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
Here `h` denotes the full reproductive weight. In Shi's additive notation it
is `s ↦ exp(-s) H(s) 1_D(s)`, where `H` is the killed tilted-walk harmonic
function; thus the joint ratio includes the exponential displacement factor.
The state space is arbitrary and weights may vanish away from the spine.
The offspring kernel may be `offspringStateKernel F hF Q`, so mark-valued
laws with a measurable update use this same construction.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]

/-- Bias the family and distinguished child jointly, rather than defining two separate laws. -/
noncomputable def biasedFamilyChild (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (h : S → ℝ≥0∞) : Kernel S (Step ι S × ι) :=
  Kernel.sum fun i =>
    (Q.withDensity (fun s ξ => (ξ i).elim 0 h / h s)).map (fun ξ => (ξ, i))

/-- The integral against the joint kernel is the sum of weighted family integrals. -/
theorem lintegral_biasedFamilyChild (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    {g : Step ι S × ι → ℝ≥0∞} (hg : Measurable g) (s : S) :
    (∫⁻ p, g p ∂biasedFamilyChild Q h s) =
      ∑' i, ∫⁻ ξ, ((ξ i).elim 0 h / h s) * g (ξ, i) ∂Q s := by
  rw [biasedFamilyChild, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [Kernel.lintegral_map _ (by fun_prop) s hg]
  have hw : Measurable (Function.uncurry
      (fun s (ξ : Step ι S) => (ξ i).elim 0 h / h s)) := by
    exact ((measurable_option_elim 0 hh).comp
      ((measurable_pi_apply i).comp measurable_snd)).div (hh.comp measurable_fst)
  exact Kernel.lintegral_withDensity Q hw s (g := fun ξ => g (ξ, i)) (by fun_prop)

/-- The total mass is the normalized expected family weight. -/
theorem biasedFamilyChild_mass (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) (s : S) :
    biasedFamilyChild Q h s Set.univ =
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) / h s := by
  have hi := lintegral_biasedFamilyChild Q hh measurable_const s (g := fun _ => 1)
  simp only [lintegral_one, mul_one] at hi
  rw [hi]
  have hw : ∀ i : ι, Measurable (fun ξ : Step ι S => (ξ i).elim 0 h) :=
    fun i => (measurable_option_elim 0 hh).comp (measurable_pi_apply i)
  simp only [div_eq_mul_inv]
  simp_rw [lintegral_mul_const _ (hw _)]
  rw [ENNReal.tsum_mul_right, lintegral_tsum (fun i => (hw i).aemeasurable)]

/-- Harmonicity normalizes the joint law at a positive finite-weight parent. -/
theorem biasedFamilyChild_isProbabilityMeasure (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) (s : S)
    (hzero : h s ≠ 0) (htop : h s ≠ ∞)
    (harmonic : (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    IsProbabilityMeasure (biasedFamilyChild Q h s) := by
  constructor
  rw [biasedFamilyChild_mass Q hh, harmonic, ENNReal.div_self hzero htop]

end ProbabilityTheory.BranchingProcess.Spine

end
