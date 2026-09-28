import Combinatorics.BranchingWalk.Walk.Path.Scaling
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Algebra.Order.Floor
import Topology.Cadlag.Basic

/-!
# Càdlàg random-walk paths

The normalized step path used in Mogulskii's theorem is a genuine càdlàg
path.  The proof reuses mathlib's `IsCadlag` predicate; no competing path
regularity structure is introduced.
-/

open Filter Set
open scoped Topology

namespace Combinatorics.Branching.Walk

/-- The integer floor function is càdlàg. -/
theorem isCadlag_floor : IsCadlag (fun x : ℝ => ⌊x⌋) where
  isRightContinuous := by
    intro x
    exact ((tendsto_floor_right_pure_floor x).mono_left
      (nhdsWithin_mono x Set.Ioi_subset_Ici_self)).mono_right (pure_le_nhds _)
  tendsto_nhdsLT x := by
    refine ⟨⌈x⌉ - 1, ?_⟩
    exact (tendsto_floor_left_pure_ceil_sub_one x).mono_right
      (pure_le_nhds _)

/-- The truncated natural-valued floor function is càdlàg. -/
theorem isCadlag_natFloor : IsCadlag (fun x : ℝ => ⌊x⌋₊) := by
  have h := isCadlag_floor.continuous_comp
    (continuous_of_discreteTopology : Continuous (Int.toNat : ℤ → ℕ))
  convert h using 1
  funext x
  exact Int.floor_toNat x

/-- Every normalized random-walk step path is càdlàg on real time. -/
theorem normalizedStepPath_isCadlag (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    IsCadlag (normalizedStepPath scale n increment) := by
  have htime : IsCadlag (fun t : ℝ => ⌊(n : ℝ) * t⌋₊) := by
    have hmono : Monotone (fun t : ℝ => (n : ℝ) * t) :=
      fun _ _ h => mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    have h := isCadlag_natFloor.comp_monotone_continuous
      hmono (continuous_const.mul continuous_id)
    change IsCadlag ((fun x : ℝ => ⌊x⌋₊) ∘
      fun t : ℝ => (n : ℝ) * t)
    exact h
  have hsum : IsCadlag (fun t : ℝ =>
      partialSum ⌊(n : ℝ) * t⌋₊ increment) :=
    htime.continuous_comp
      (show Continuous (fun k : ℕ => partialSum k increment) from
        continuous_of_discreteTopology)
  have hscaled := hsum.continuous_comp
    (show Continuous (fun x : ℝ => (scale n)⁻¹ * x) from
      continuous_const.mul continuous_id)
  change IsCadlag ((fun x : ℝ => (scale n)⁻¹ * x) ∘
    fun t : ℝ => partialSum ⌊(n : ℝ) * t⌋₊ increment)
  exact hscaled

/-- The normalized step path as an element of the càdlàg path space. -/
noncomputable def normalizedStepCadlagPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : CadlagPath ℝ ℝ :=
  ⟨normalizedStepPath scale n increment,
    normalizedStepPath_isCadlag scale n increment⟩

@[simp] theorem normalizedStepCadlagPath_apply (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (t : ℝ) :
    normalizedStepCadlagPath scale n increment t =
      normalizedStepPath scale n increment t := rfl

/-- The normalized step path restricted to the compact time interval
`[0, 1]`, the state space used by the Skorokhod functional limit theorem. -/
noncomputable def normalizedStepCadlagPathIcc (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : CadlagPath (Set.Icc (0 : ℝ) 1) ℝ :=
  (normalizedStepCadlagPath scale n increment).compMonotoneContinuous
    Subtype.val (fun _ _ h => h) continuous_subtype_val

@[simp] theorem normalizedStepCadlagPathIcc_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : Set.Icc (0 : ℝ) 1) :
    normalizedStepCadlagPathIcc scale n increment t =
      normalizedStepPath scale n increment t := rfl

end Combinatorics.Branching.Walk
