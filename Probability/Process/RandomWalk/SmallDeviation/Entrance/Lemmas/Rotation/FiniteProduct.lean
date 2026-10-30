/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.CyclicCover
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomainEvent
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.PathBallLaw
import MeasureTheory.Measure.Pi.FiniteReindexCover

/-!
# Finite-product probability bounds from cyclic covers

## Internal proof declarations

- `measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets` and
  `measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets_of_normalizationRatio`:
  if $n>0$, $r>0$, $2r+|d|n<1/16$, $u\in[0,1]$, the corridor is measurable,
  and the sequence-law path-ball probability is at least $q$, then the
  $n$-fold product corridor probability is at least $q/n$. The last theorem
  also allows different source and target spatial scales.
- `measure_pi_offsetCorridor_ge_div_of_linearTube`: the same bound $q/n$
  for the centered path ball when $u\in[0,1/10]$.

The main estimate has the form
$q\le\mathbb P(\text{linear path ball})\Longrightarrow
\mathbb P(\text{offset corridor})\ge q/n$.

This finite-product specialization supports Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (master's thesis,
Fudan University, 2026), Appendix A.2, Lemma A.7, used in the proof of
Chapter 3, Lemma 3.5. The generic finite reindex-cover measure estimate
remains at `MeasureTheory.Measure.Pi.FiniteReindexCover`.
-/

section

open MeasureTheory ProbabilityTheory Fin
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- A finite IID prefix has the factor-`n` all-offset entrance estimate. -/
lemma measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets
    {n : ℕ} (hn : 0 < n) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1)
    (hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u))
    {q : ℝ≥0∞}
    (hq : q ≤ iidSequenceLaw ν
      {x | RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x ∈
        Metric.ball (Skorokhod.linearPath (1 / 2 - u)) radius}) :
    q / n ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := by
  have hqPi : q ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius) :=
    hq.trans_eq (iidSequenceLaw_measure_linearPathBall_eq_pi
      (n := n) ν scale (1 / 2 - u) radius)
  have hcover := finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    hn scale drift radius u hradius hsmall hu
  let rotate : Fin n → Fin n ≃ Fin n := fun k => finCycle k
  have hbound := MeasureTheory.measure_pi_event_le_card_smul_of_reindex_cover
    (fun _ : Fin n => ν) (finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius)
    (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u)
    rotate (by intro k i; rfl) hcover hsafe
  have hbound' : Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius) ≤
        n • Measure.pi (fun _ : Fin n => ν)
          (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := by
    simpa using hbound
  have hqbound : q ≤ n • Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) :=
    hqPi.trans hbound'
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hn.ne'))
    (Or.inl (by simp))]
  calc
    q ≤ n • Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := hqbound
    _ = Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) * n := by
          rw [nsmul_eq_mul']

/-- The all-offset cyclic factor-`n` estimate for a source linear ball whose
path normalization differs from the target corridor normalization. -/
lemma measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets_of_normalizationRatio
    {n : ℕ} (hn : 0 < n) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (targetScale sourceScale ratio drift sourceSlope radius u : ℝ)
    (htargetScale : targetScale ≠ 0) (hsourceScale : sourceScale ≠ 0)
    (hratio : ratio = sourceScale / targetScale)
    (hcenter : ratio * sourceSlope = 1 / 2 - u)
    (hradius : 0 < radius)
    (hsmall : 2 * (max 1 |ratio| * radius) +
      |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1)
    (hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u))
    {q : ℝ≥0∞}
    (hq : q ≤ iidSequenceLaw ν
      {x | RandomWalk.normalizedStepCadlagPathIcc
        (fun _ => sourceScale) n x ∈
          Metric.ball (Skorokhod.linearPath sourceSlope) radius}) :
    q / n ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) := by
  have hqPi : q ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) sourceScale sourceSlope radius) :=
    hq.trans_eq (iidSequenceLaw_measure_linearPathBall_eq_pi
      (n := n) ν sourceScale sourceSlope radius)
  have hcover :=
    finiteLinearBall_subset_cyclicOffsetCover_allOffsets_of_normalizationRatio
      hn targetScale sourceScale ratio drift sourceSlope radius u
      htargetScale hsourceScale hratio hcenter hradius hsmall hu
  let rotate : Fin n → Fin n ≃ Fin n := fun k => finCycle k
  have hbound := MeasureTheory.measure_pi_event_le_card_smul_of_reindex_cover
    (fun _ : Fin n => ν) (finiteLinearPathBallEvent (n := n) sourceScale sourceSlope radius)
    (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u)
    rotate (by intro k i; rfl) hcover hsafe
  have hbound' : Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) sourceScale sourceSlope radius) ≤
        n • Measure.pi (fun _ : Fin n => ν)
          (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) := by
    simpa using hbound
  have hqbound : q ≤ n • Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) :=
    hqPi.trans hbound'
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hn.ne'))
    (Or.inl (by simp))]
  calc
    q ≤ n • Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) :=
      hqbound
    _ = Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) * n :=
      by rw [nsmul_eq_mul']

/-- A finite IID prefix has the factor-`n` cyclic-rotation estimate. -/
lemma measure_pi_offsetCorridor_ge_div_of_linearTube
    {n : ℕ} (hn : 0 < n) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 (1 / 10))
    (hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u))
    {q : ℝ≥0∞}
    (hq : q ≤ iidSequenceLaw ν
      {x | RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale) n x ∈
        Metric.ball (Skorokhod.linearPath (1 / 2)) radius}) :
    q / n ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := by
  have hqPi : q ≤ Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) scale (1 / 2) radius) :=
    hq.trans_eq (iidSequenceLaw_measure_linearPathBall_eq_pi
      (n := n) ν scale (1 / 2) radius)
  have hcover := finiteLinearBall_subset_cyclicOffsetCover_lowerEdge
    hn scale drift radius u hradius hsmall hu
  let rotate : Fin n → Fin n ≃ Fin n := fun k => finCycle k
  have hbound := MeasureTheory.measure_pi_event_le_card_smul_of_reindex_cover
    (fun _ : Fin n => ν) (finiteLinearPathBallEvent (n := n) scale (1 / 2) radius)
    (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u)
    rotate (by intro k i; rfl) hcover hsafe
  have hbound' : Measure.pi (fun _ : Fin n => ν)
      (finiteLinearPathBallEvent (n := n) scale (1 / 2) radius) ≤
        n • Measure.pi (fun _ : Fin n => ν)
          (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := by
    simpa using hbound
  have hqbound : q ≤ n • Measure.pi (fun _ : Fin n => ν)
      (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) :=
    hqPi.trans hbound'
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hn.ne'))
    (Or.inl (by simp))]
  calc
    q ≤ n • Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) := hqbound
    _ = Measure.pi (fun _ : Fin n => ν)
        (finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u) * n := by
          rw [nsmul_eq_mul']

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
