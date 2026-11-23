/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Identity
public import Probability.Process.Tree.Line.PathHitting

/-!
# Weighted first-entrance mass and spine hitting probability

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `firstEntranceWeight φ B x` is the exponential mass of particles that
  first enter `B` along their ancestry, summed over all generations,
  including generation zero. The weight is `exp(−(position − x))`.
* `firstEntranceWeight_eq_tsum` identifies this mass with the weighted sum
  over surviving nodes on the existing deterministic `Line.firstEntrance`.
* `lintegral_firstEntranceWeight_eq` proves
  `E[W_B] = P̂(∃ n, S_n ∈ B)` for Borel `B`, an i.i.d. offspring law,
  countably many child slots, and boundary-normalized exponential tilting.
* `lintegral_firstEntranceWeight_le_one` gives `E[W_B] ≤ 1`.
* `lintegral_firstEntranceWeight_eq_one_iff` states that expectation is one
  exactly when the tilted spine enters `B` almost surely.

This is the additive branching-random-walk first-entry specialization of
J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*
(2004), §6, p. 557, Lemma 6.1,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
The proof sums the existing weighted path many-to-one identity over the
pairwise disjoint first-entry generations. It requires no moment condition
or almost-sure finiteness of the spine hitting time. The general-state simple-line identity is proved in
`BranchingProcess/Spine/StoppingLine/ManyToOne.lean`. The independent-field
realization here retains its existing weighted-path-law proof; transporting it
to that canonical state-tree entry remains an explicit migration obligation.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open MeasureTheory Combinatorics.Branching ProbabilityTheory.RandomWalk
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open scoped ENNReal

private def entranceHistory (B : Set ℝ) (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {p | p (Fin.last n) ∈ B ∧ ∀ k : Fin n, p k.castSucc ∉ B}

private theorem measurableSet_entranceHistory {B : Set ℝ} (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (entranceHistory B n) := by
  have heq : entranceHistory B n =
      {p | p (Fin.last n) ∈ B} ∩ ⋂ k : Fin n, {p | p k.castSucc ∉ B} := by
    ext p
    simp [entranceHistory]
  rw [heq]
  exact (hB.preimage (measurable_pi_apply (Fin.last n))).inter
    (MeasurableSet.iInter fun k => (hB.preimage (measurable_pi_apply k.castSucc)).compl)

private theorem entranceHistory_measurable {B : Set ℝ} (hB : MeasurableSet B) (n : ℕ) :
    Measurable ((entranceHistory B n).indicator (fun _ => (1 : ENNReal))) :=
  measurable_const.indicator (measurableSet_entranceHistory hB n)

/-- Total exponentially weighted mass at first entrance, including the initial particle. -/
noncomputable def firstEntranceWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (B : Set ℝ) (x : ℝ) (ω : StepField ι X) : ENNReal :=
  ∑' n : ℕ, weightedPathGeneration φ n
    (({p : Fin (n + 1) → ℝ | p (Fin.last n) ∈ B ∧ ∀ k : Fin n, p k.castSucc ∉ B}).indicator (fun _ => 1)) x ω

private theorem entranceHistory_iff_firstEntrance {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (B : Set ℝ) (x : ℝ) (ω : StepField ι X)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    pathHistory φ u.length x ω u ∈ entranceHistory B u.length ↔
      ((), u) ∈ Combinatorics.UlamHarris.RootIndexed.Line.firstEntrance
        {v : Unit × List ι | x + pathPotential φ ω v.2 ∈ B} := by
  rw [Combinatorics.UlamHarris.RootIndexed.Line.mem_firstEntrance_iff]
  simp only [entranceHistory, Set.mem_ofPred_eq, pathHistory, Fin.val_last, List.take_length,
    Fin.val_castSucc]
  constructor
  · rintro ⟨hu, hp⟩
    exact ⟨hu, fun k hk => hp ⟨k, hk⟩⟩
  · rintro ⟨hu, hp⟩
    exact ⟨hu, fun k => hp k k.isLt⟩

open scoped Classical in
/-- The generation-sum implementation is the mass of the existing first-entrance line. -/
theorem firstEntranceWeight_eq_tsum {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (B : Set ℝ) (x : ℝ) (ω : StepField ι X) :
    firstEntranceWeight φ B x ω = ∑' u : Combinatorics.UlamHarris.TreeNode ι,
      (if surviveAlong ω [] u ∧
          ((), u) ∈ Combinatorics.UlamHarris.RootIndexed.Line.firstEntrance
            {v : Unit × List ι | x + pathPotential φ ω v.2 ∈ B}
        then ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) else 0) := by
  classical
  simp only [firstEntranceWeight, weightedPathGeneration]
  rw [tsum_comm]
  apply tsum_congr
  intro u
  rw [tsum_eq_single u.length (fun n hn => ?_)]
  · have he := entranceHistory_iff_firstEntrance φ B x ω u
    change weightedPathGenerationTerm φ u.length
      ((entranceHistory B u.length).indicator (fun _ => 1)) x u ω = _
    by_cases hs : surviveAlong ω [] u <;>
      by_cases hh : pathHistory φ u.length x ω u ∈ entranceHistory B u.length <;>
      simp [weightedPathGenerationTerm, Set.indicator, hs, hh, ← he]
  · simp [weightedPathGenerationTerm, Ne.symm hn, Set.indicator]

private def entranceEvent (B : Set ℝ) (x : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  (history n x) ⁻¹' entranceHistory B n

private theorem mem_entranceEvent {B : Set ℝ} {x : ℝ} {n : ℕ} {increment : ℕ → ℝ} :
    increment ∈ entranceEvent B x n ↔
      positionProcess x n increment ∈ B ∧
        ∀ k < n, positionProcess x k increment ∉ B := by
  simp only [entranceEvent, Set.mem_preimage, entranceHistory, Set.mem_ofPred_eq,
    history_apply, Fin.val_last, Fin.val_castSucc]
  constructor
  · rintro ⟨hn, hprev⟩
    exact ⟨hn, fun k hk => hprev ⟨k, hk⟩⟩
  · rintro ⟨hn, hprev⟩
    exact ⟨hn, fun k => hprev k k.isLt⟩

private theorem entranceEvent_disjoint (B : Set ℝ) (x : ℝ) :
    Pairwise (fun n m => Disjoint (entranceEvent B x n) (entranceEvent B x m)) := by
  intro n m hne
  apply Set.disjoint_left.mpr
  intro increment hn hm
  rw [mem_entranceEvent] at hn hm
  rcases lt_or_gt_of_ne hne with h | h
  · exact hm.2 n h hn.1
  · exact hn.2 m h hm.1

private theorem iUnion_entranceEvent (B : Set ℝ) (x : ℝ) :
    (⋃ n, entranceEvent B x n) = {increment | ∃ n, positionProcess x n increment ∈ B} := by
  classical
  ext increment
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (mem_entranceEvent.mp hn).1⟩
  · intro hex
    exact ⟨Nat.find hex, mem_entranceEvent.mpr
      ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩⟩

/-- Lemma 6.1 of Biggins–Kyprianou (2004), first-entry BRW specialization. -/
theorem lintegral_firstEntranceWeight_eq {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {B : Set ℝ} (hB : MeasurableSet B) (x : ℝ) :
    (∫⁻ ω, firstEntranceWeight φ B x ω ∂offspringFieldLaw μ) =
      (tiltedIncrementFieldLaw φ μ) {increment | ∃ n, positionProcess x n increment ∈ B} := by
  have hE : ∀ n, MeasurableSet (entranceEvent B x n) := fun n =>
    (measurableSet_entranceHistory hB n).preimage (history_measurable n x)
  calc
    (∫⁻ ω, firstEntranceWeight φ B x ω ∂offspringFieldLaw μ) =
        ∑' n, ∫⁻ ω, weightedPathGeneration φ n
          ((entranceHistory B n).indicator (fun _ => 1)) x ω ∂offspringFieldLaw μ := by
      simp only [firstEntranceWeight]
      apply lintegral_tsum
      intro n
      exact (weightedPathGeneration_measurable φ n (entranceHistory_measurable hB n) x).aemeasurable
    _ = ∑' n, (tiltedIncrementFieldLaw φ μ) (entranceEvent B x n) := by
      apply tsum_congr
      intro n
      rw [weightedPathManyToOneCore φ μ hboundary n (entranceHistory_measurable hB n) x]
      have heq : (fun increment => (entranceHistory B n).indicator (fun _ => (1 : ENNReal))
          (history n x increment)) = (entranceEvent B x n).indicator (fun _ => 1) := by
        ext increment
        rfl
      rw [heq]
      simpa only [Pi.one_def] using lintegral_indicator_one (μ := tiltedIncrementFieldLaw φ μ) (hE n)
    _ = (tiltedIncrementFieldLaw φ μ) (⋃ n, entranceEvent B x n) :=
      (measure_iUnion (entranceEvent_disjoint B x) hE).symm
    _ = _ := by rw [iUnion_entranceEvent]

/-- First-entrance exponential mass has expectation at most one. -/
theorem lintegral_firstEntranceWeight_le_one {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {B : Set ℝ} (hB : MeasurableSet B) (x : ℝ) :
    (∫⁻ ω, firstEntranceWeight φ B x ω ∂offspringFieldLaw μ) ≤ 1 := by
  let : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  rw [lintegral_firstEntranceWeight_eq φ μ hboundary hB x]
  exact prob_le_one

/-- Mean preservation is equivalent to almost-sure entrance of the tilted spine. -/
theorem lintegral_firstEntranceWeight_eq_one_iff {ι X : Type*} [Countable ι]
    [MeasurableSpace X] (φ : Potential X) (μ : Measure (Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    {B : Set ℝ} (hB : MeasurableSet B) (x : ℝ) :
    (∫⁻ ω, firstEntranceWeight φ B x ω ∂offspringFieldLaw μ) = 1 ↔
      ∀ᵐ increment ∂tiltedIncrementFieldLaw φ μ, ∃ n, positionProcess x n increment ∈ B := by
  let : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  rw [lintegral_firstEntranceWeight_eq φ μ hboundary hB x]
  have hm : MeasurableSet {increment | ∃ n, positionProcess x n increment ∈ B} := by
    rw [← iUnion_entranceEvent B x]
    apply MeasurableSet.iUnion
    intro n
    change MeasurableSet ((history n x) ⁻¹' entranceHistory B n)
    exact (measurableSet_entranceHistory hB n).preimage (history_measurable n x)
  exact (mem_ae_iff_prob_eq_one hm).symm

end ProbabilityTheory.BranchingRandomWalk.Spine

end
