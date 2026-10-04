/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Comparison
public import Probability.Kernel.Survival.Blocking
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform killed-kernel bounds from finite liminf estimates

Finite pointwise `liminf` estimates with a common finite additive error are
converted into an eventual bound uniform over every initial state covered by
the reference family.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A bound stated for all normalized initial positions is equivalently a
uniform bound on the restricted killed kernel whose state space is the scaled
interval itself. -/
theorem eventually_forall_le_remainingMass_killedIncrementKernelOn_Icc_of_normalized
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (scale : ι → ℝ) (duration : ι → ℕ)
    (lowerBound : ENNReal)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (hnormalized : ∀ᶠ i in l, ∀ x : Set.Icc lower upper,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
        (duration i) (scale i * x)) :
    ∀ᶠ i in l, ∀ x : Set.Icc (scale i * lower) (scale i * upper),
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernelOn ν
          (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
        (duration i) x := by
  filter_upwards [hscale, hnormalized] with i hscalePos hi
  intro x
  let normalized : Set.Icc lower upper :=
    ⟨(x : ℝ) / scale i, by
      constructor
      · exact (le_div_iff₀ hscalePos).2 (by simpa [mul_comm] using x.property.1)
      · exact (div_le_iff₀ hscalePos).2 (by simpa [mul_comm] using x.property.2)⟩
  rw [killedIncrementKernelOn_remainingMass]
  convert hi normalized using 1
  dsimp [normalized]
  field_simp [hscalePos.ne']

/-- An eventual uniform normalized one-block lower bound feeds directly into
the abstract sub-Markov blocking inequality, including the incomplete final
block. -/
theorem eventually_pow_succ_div_le_remainingMass_killedIncrementKernelOn_Icc
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (scale : ι → ℝ)
    (block total : ι → ℕ) (lowerBound : ENNReal)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (hblock : ∀ᶠ i in l, 0 < block i)
    (hnormalized : ∀ᶠ i in l, ∀ x : Set.Icc lower upper,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
        (block i) (scale i * x)) :
    ∀ᶠ i in l, ∀ x : Set.Icc (scale i * lower) (scale i * upper),
      lowerBound ^ (total i / block i + 1) ≤
        Kernel.remainingMass
          (killedIncrementKernelOn ν
            (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
          (total i) x := by
  have hon :=
    eventually_forall_le_remainingMass_killedIncrementKernelOn_Icc_of_normalized
      ν lower upper scale block lowerBound hscale hnormalized
  filter_upwards [hon, hblock] with i hi hblockPos
  intro x
  exact Kernel.pow_succ_div_le_remainingMass
    (killedIncrementKernelOn ν
      (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
    hblockPos (total i) x lowerBound hi

/-- A finite family of strict `liminf` gaps yields an eventual survival bound
uniform over every covered normalized initial position. -/
theorem eventually_forall_le_remainingMass_killedIncrementKernel_Icc_of_finset_liminf
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper margin : ℝ) (references : Finset ℝ)
    (scale : ι → ℝ) (duration : ι → ℕ)
    (lowerBound error : ENNReal) (referenceBound : ℝ → ENNReal)
    (herror : error ≠ ⊤)
    (hscale : ∀ᶠ i in l, 0 ≤ scale i)
    (hcover : ∀ x ∈ Set.Icc lower upper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (hliminf : ∀ y ∈ references,
      referenceBound y ≤ l.liminf (fun i =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale i * (lower + margin))
                (scale i * (upper - margin))) measurableSet_Icc)
            (duration i) (scale i * y) + error))
    (hgap : ∀ y ∈ references,
      lowerBound + error < referenceBound y) :
    ∀ᶠ i in l, ∀ x : Set.Icc lower upper,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * lower) (scale i * upper)) measurableSet_Icc)
        (duration i) (scale i * x) := by
  have href : ∀ y ∈ references, ∀ᶠ i in l,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale i * (lower + margin))
            (scale i * (upper - margin))) measurableSet_Icc)
        (duration i) (scale i * y) := by
    intro y hy
    have hstrict : lowerBound + error < l.liminf (fun i =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale i * (lower + margin))
                (scale i * (upper - margin))) measurableSet_Icc)
            (duration i) (scale i * y) + error) :=
      (hgap y hy).trans_le (hliminf y hy)
    filter_upwards [eventually_lt_of_lt_liminf hstrict]
      with i hi
    exact ((ENNReal.add_lt_add_iff_right herror).1 hi).le
  exact eventually_forall_le_remainingMass_killedIncrementKernel_Icc_of_finset
    ν lower upper margin references scale duration lowerBound
    hscale hcover href

end ProbabilityTheory.RandomWalk
