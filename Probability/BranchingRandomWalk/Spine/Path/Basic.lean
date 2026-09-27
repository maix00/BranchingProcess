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

/-- Add a time-zero position in front of a nonempty finite history. -/
def prependHistory {n : ℕ} (x : ℝ) (tail : Fin (n + 1) → ℝ) :
    Fin (n + 2) → ℝ :=
  Fin.cases x tail

/-- Remove the first increment from a discrete increment field. -/
def incrementTail (increment : ℕ → ℝ) : ℕ → ℝ :=
  fun k => increment (k + 1)

@[simp] theorem prependHistory_zero {n : ℕ} (x : ℝ)
    (tail : Fin (n + 1) → ℝ) :
    prependHistory x tail 0 = x :=
  rfl

@[simp] theorem prependHistory_succ {n : ℕ} (x : ℝ)
    (tail : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    prependHistory x tail k.succ = tail k :=
  rfl

theorem prependHistory_joint_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      prependHistory p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact measurable_fst
  · exact measurable_pi_apply j |>.comp measurable_snd

theorem incrementTail_measurable : Measurable incrementTail := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (k + 1)

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

theorem spineHistory_joint_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => spineHistory n p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.add ((tiltedPosition_measurable k).comp measurable_snd)

/-- Partial sums split into the first increment and the partial sums of the
tail increment field. -/
theorem tiltedPosition_succ_eq_head_add_tail (n : ℕ)
    (increment : ℕ → ℝ) :
    tiltedPosition (n + 1) increment =
      increment 0 + tiltedPosition n (incrementTail increment) := by
  induction n with
  | zero => simp [tiltedPosition]
  | succ n ih =>
      rw [tiltedPosition_succ, ih, tiltedPosition_succ]
      simp only [incrementTail]
      ring

/-- A branching history along `i :: v` consists of its initial position and
the descendant history below the actually chosen first slot `i`. -/
theorem pathHistory_cons
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (i : ι) (v : TreeNode ι) :
    pathHistory φ (n + 1) x ω (i :: v) =
      prependHistory x
        (pathHistory φ n (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) v) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [pathHistory]
  · simp [pathHistory, prependHistory, List.take_succ_cons,
      pathPotential_cons, add_assoc]

/-- The canonical spine history has the same first-step decomposition. -/
theorem spineHistory_succ (n : ℕ) (x : ℝ) (increment : ℕ → ℝ) :
    spineHistory (n + 1) x increment =
      prependHistory x
        (spineHistory n (x + increment 0) (incrementTail increment)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [spineHistory, tiltedPosition]
  · simp only [spineHistory, prependHistory_succ]
    change x + tiltedPosition (j.val + 1) increment =
      x + increment 0 + tiltedPosition j.val (incrementTail increment)
    rw [tiltedPosition_succ_eq_head_add_tail]
    ring

end ProbabilityTheory.BranchingRandomWalk.Spine
