/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Count
public import Combinatorics.BranchingWalk.Step.Selection.Finite

/-!
# Binary-slot encoding of a bounded finite selection

For a finite selection `R` with at most two selected slots, encode its
offspring count as an initial segment of the binary slot set:
\[
  \operatorname{binaryOffspringStep}(R,\xi)(i)=
  \begin{cases}
    \operatorname{some}(\star),&i<\#(R\,\xi),\\
    \operatorname{none},&\#(R\,\xi)\le i.
  \end{cases}
\]
When `R ξ` has cardinality at most two, the encoded step has exactly
`(R ξ).card` surviving slots. The encoding is deterministic and belongs to
the combinatorial branching-step layer; its measurability and induced law are
stated in the corresponding measure-theory and probability modules.

## Public declarations

`Step.FiniteSelection.binaryOffspringStep R ξ` is the two-slot encoding, and
`Step.FiniteSelection.binaryOffspringStep_childCount` proves equality of its
child count with `(R ξ).card` under the capacity-two bound.
-/

@[expose] public section

namespace Combinatorics.Branching.Step.FiniteSelection

/-- Encode the selected-child count as an initial segment of two unmarked
slots. -/
def binaryOffspringStep
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X) :
    Step (Fin 2) PUnit.{1} :=
  fun i => if i.val < (R ξ).card then some PUnit.unit else none

/-- Under a capacity-two bound, the encoding has the same number of children
as the original finite selection. -/
theorem binaryOffspringStep_childCount
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hR : (R ξ).card ≤ 2) :
    (binaryOffspringStep R ξ).childCount = (R ξ).card := by
  classical
  have hsupp : support (binaryOffspringStep R ξ) =
      {i : Fin 2 | i.val < (R ξ).card} := by
    ext i
    change survive (binaryOffspringStep R ξ) i ↔ _
    simp [survive, binaryOffspringStep]
  rw [Step.childCount, hsupp]
  by_cases hzero : (R ξ).card = 0
  · simp [hzero]
  · by_cases hone : (R ξ).card = 1
    · have hsupport : {i : Fin 2 | i.val < (R ξ).card} = {0} := by
        ext i
        fin_cases i <;> simp [hone]
      rw [hsupport]
      simp [hone]
    · have htwo : (R ξ).card = 2 := by omega
      have hsupport : {i : Fin 2 | i.val < (R ξ).card} = Set.univ := by
        rw [htwo]
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_univ]
        exact ⟨fun _ => trivial, fun _ => i.isLt⟩
      rw [hsupport]
      simp [htwo]

end Combinatorics.Branching.Step.FiniteSelection

end
