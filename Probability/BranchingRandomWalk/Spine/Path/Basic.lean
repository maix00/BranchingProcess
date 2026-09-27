import Probability.BranchingRandomWalk.Spine.GenerationBranching
import Probability.BranchingRandomWalk.Spine.IncrementProcess

/-!
# Potential histories along branching and spine paths

A history of length `n` records positions at times `0, ..., n` and therefore
has type `Fin (n + 1) → ℝ`. The construction is independent of any ordering of
offspring slots: a realized address already records its actual successive
slots.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Positions, including the initial position, along the first `n` edges of
an address in a pre-sampled branching field. -/
def pathHistory {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι) :
    Fin (n + 1) → ℝ :=
  fun k => x + pathPotential φ ω (u.take k)

/-- The corresponding history of the canonical tilted increment process. -/
def spineHistory (n : ℕ) (x : ℝ) (increment : ℕ → ℝ) :
    Fin (n + 1) → ℝ :=
  fun k => x + tiltedPosition k increment

@[simp] theorem pathHistory_zero
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι) :
    pathHistory φ n x ω u ⟨0, Nat.zero_lt_succ n⟩ = x := by
  simp [pathHistory]

@[simp] theorem spineHistory_zero (n : ℕ) (x : ℝ) (increment : ℕ → ℝ) :
    spineHistory n x increment ⟨0, Nat.zero_lt_succ n⟩ = x := by
  simp [spineHistory, tiltedPosition]

theorem pathHistory_last
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι)
    (hu : u.length = n) :
    pathHistory φ n x ω u ⟨n, Nat.lt_succ_self n⟩ =
      x + pathPotential φ ω u := by
  simp [pathHistory, ← hu]

theorem spineHistory_last (n : ℕ) (x : ℝ) (increment : ℕ → ℝ) :
    spineHistory n x increment ⟨n, Nat.lt_succ_self n⟩ =
      x + tiltedPosition n increment :=
  rfl

theorem pathHistory_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (u : TreeNode ι) :
    Measurable (fun ω : Combinatorics.Branching.StepField ι X =>
      pathHistory φ n x ω u) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_const.add (pathPotential_measurable φ [] (u.take k))

theorem pathHistory_joint_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (u : TreeNode ι) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathHistory φ n p.1 p.2 u) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.add
    ((pathPotential_measurable φ [] (u.take k)).comp measurable_snd)

theorem spineHistory_measurable (n : ℕ) (x : ℝ) :
    Measurable (spineHistory n x) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_const.add (tiltedPosition_measurable k)

end ProbabilityTheory.BranchingRandomWalk.Spine
