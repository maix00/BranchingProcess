/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath
import Probability.Sequence.IID.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Probability.Process.RandomWalk.Path.Representation.Cadlag
import Topology.Cadlag.Skorokhod.Path.Linear
import Probability.Sequence.Block
import Combinatorics.Sequence.Block

/-!
# Finite-path law transfer for the cyclic entrance estimate

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.iidSequenceLaw_measure_linearPathBall_eq_pi`:
  for a finite-path ball $A_n$, its infinite IID law agrees with the finite
  product probability, $\mathbb P_{\nu^{\mathbb N}}(A_n)=\nu^{\otimes n}(A_n)$.

The finite-prefix path identity and measurability steps used in this transfer
are private to this module. This supporting law transfer is specific to the
finite linear-path-ball event in the entrance estimate of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7, used in
the proof of Chapter 3, Lemma 3.5.
-/

open MeasureTheory ProbabilityTheory Fin
open scoped ENNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The finite path depends only on the first `n` coordinates of an infinite
increment sequence. This is the path-level bridge used to transfer Donsker's
linear-ball lower bound to the finite product law. -/
private lemma finiteNormalizedStepPath_prefix_eq {n : ℕ} (scale : ℝ)
    (x : ℕ → ℝ) :
    finiteNormalizedStepPath scale (fun i : Fin n => x i.val) =
      RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x := by
  ext t
  change RandomWalk.normalizedStepPath (fun _ => scale) n
      (Function.extend Fin.val (fun i : Fin n => x i.val) (fun _ => 0)) t =
    RandomWalk.normalizedStepPath (fun _ => scale) n x t
  rw [RandomWalk.normalizedStepPath]
  congr 1
  unfold AdditivePath.displacement
  apply Finset.sum_congr rfl
  intro k hk
  have hkfloor : k < ⌊(n : ℝ) * (t : ℝ)⌋₊ := Finset.mem_range.mp hk
  have hfloor : ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
      _ = n := by ring
  have hkn : k < n := hkfloor.trans_le hfloor
  have hinj : Function.Injective (fun i : Fin n => i.val) :=
    fun i j hij => Fin.ext hij
  have hextend :
      Function.extend Fin.val (fun i : Fin n => x i.val) (fun _ => (0 : ℝ)) k =
        x k := by
    simpa using (Function.Injective.extend_apply hinj
      (fun i : Fin n => x i.val) (fun _ => (0 : ℝ)) ⟨k, hkn⟩)
  rw [hextend]

/-- The finite linear-path-ball event is measurable in the finite product
sigma-algebra. -/
private lemma measurableSet_finiteLinearPathBallEvent
    (scale slope radius : ℝ) {n : ℕ} :
    MeasurableSet (finiteLinearPathBallEvent (n := n) scale slope radius) := by
  have hpath : Measurable (finiteNormalizedStepPath scale :
      (Fin n → ℝ) → CadlagPath unitInterval ℝ) :=
    (RandomWalk.measurable_normalizedStepCadlagPathIcc
      (fun _ => scale) n).comp
        (measurable_function_extend_fin_val n (0 : ℝ))
  exact Metric.isOpen_ball.measurableSet.preimage hpath

/-- The finite product probability of a linear-path-ball event agrees with
the probability of the corresponding event for the canonical IID sequence. -/
lemma iidSequenceLaw_measure_linearPathBall_eq_pi
    {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale slope radius : ℝ) :
    iidSequenceLaw ν
        {x | RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x ∈
          Metric.ball (Skorokhod.linearPath slope) radius} =
      Measure.pi (fun _ : Fin n => ν)
        (finiteLinearPathBallEvent (n := n) scale slope radius) := by
  have hset := measurableSet_finiteLinearPathBallEvent
    (n := n) scale slope radius
  have hpreimage :
      (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          finiteLinearPathBallEvent (n := n) scale slope radius =
        {x | RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x ∈
          Metric.ball (Skorokhod.linearPath slope) radius} := by
    ext x
    have hcoords :
        Combinatorics.Sequence.blockCoordinates 0 n x =
          (fun i : Fin n => x i.val) := by
      funext i
      simp [Combinatorics.Sequence.blockCoordinates]
    change finiteNormalizedStepPath scale ((Combinatorics.Sequence.blockCoordinates 0 n) x) ∈
        Metric.ball (Skorokhod.linearPath slope) radius ↔ _
    rw [hcoords]
    rw [finiteNormalizedStepPath_prefix_eq]
    simp only [Set.mem_ofPred_eq]
  calc
      iidSequenceLaw ν
        {x | RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x ∈
          Metric.ball (Skorokhod.linearPath slope) radius} =
      iidSequenceLaw ν
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          finiteLinearPathBallEvent (n := n) scale slope radius) := by
          rw [hpreimage]
    _ = (iidSequenceLaw ν).map ((Combinatorics.Sequence.blockCoordinates 0 n))
        (finiteLinearPathBallEvent (n := n) scale slope radius) := by
          rw [Measure.map_apply (measurable_blockCoordinates 0 n) hset]
    _ = Measure.pi (fun _ : Fin n => ν)
        (finiteLinearPathBallEvent (n := n) scale slope radius) := by
          rw [Measure.map_apply (measurable_blockCoordinates 0 n) hset]
          exact iidSequenceLaw_measure_blockCoordinates_preimage_eq_pi
            ν 0 n _ hset
end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
