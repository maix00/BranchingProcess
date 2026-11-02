/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import MeasureTheory.Measure.Levy.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Small- and large-jump regions of a Lévy measure

These cutoff sets separate jumps at the unit scale and at an arbitrary positive
radius. Their definitions and elementary set properties serve both the
Lévy–Khintchine representation and convergence of Lévy measures.

## Public declarations

- `smallJumpSet` is $\{x\in\mathbb R:|x|<1\}$, the unit region in the
  Lévy-measure integrability condition.
- `largeJumpSet ε` is $\{x\in\mathbb R:ε\le|x|\}$.
- `mem_smallJumpSet` and `mem_largeJumpSet` give the corresponding membership
  characterizations.
- `measurableSet_smallJumpSet` and `measurableSet_largeJumpSet` prove these
  cutoff regions measurable.
- `smallJumpSet_eq_compl_largeJumpSet_one` states that the unit small-jump
  region is the complement of `largeJumpSet 1`.
- `largeJumpSet_antitone` states that $ε₁\le ε₂$ implies
  `largeJumpSet ε₂ ⊆ largeJumpSet ε₁`.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

/-- The unit small-jump region `{x : ℝ | |x| < 1}` used in the
Lévy–Khintchine proof. -/
def smallJumpSet : Set ℝ := {x | |x| < 1}

/-- The large-jump region outside radius `ε`, `{x : ℝ | ε ≤ |x|}`. -/
def largeJumpSet (ε : ℝ) : Set ℝ := {x | ε ≤ |x|}

@[simp]
lemma mem_smallJumpSet {x : ℝ} : x ∈ smallJumpSet ↔ |x| < 1 := Iff.rfl

@[simp]
lemma mem_largeJumpSet {x ε : ℝ} : x ∈ largeJumpSet ε ↔ ε ≤ |x| := Iff.rfl

lemma measurableSet_smallJumpSet : MeasurableSet smallJumpSet :=
  (isOpen_Iio.preimage continuous_abs).measurableSet

lemma measurableSet_largeJumpSet (ε : ℝ) : MeasurableSet (largeJumpSet ε) :=
  (isClosed_Ici.preimage continuous_abs).measurableSet

lemma smallJumpSet_eq_compl_largeJumpSet_one :
    smallJumpSet = (largeJumpSet 1)ᶜ := by
  ext x
  simp [smallJumpSet, largeJumpSet, not_le]

lemma largeJumpSet_antitone {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    largeJumpSet ε₂ ⊆ largeJumpSet ε₁ := by
  intro x hx
  exact mem_largeJumpSet.mpr (h.trans (mem_largeJumpSet.mp hx))

end MeasureTheory

end
