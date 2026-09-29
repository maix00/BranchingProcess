module

public import Combinatorics.BranchingWalk.Walk.Path.Restart
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

@[expose] public section

/-!
# Positions relative to an ancestral generation

The reference generation may depend deterministically on the observation
generation.  This covers a walk viewed from its root, from a fixed
intermediate generation, or from a piecewise changing restart generation.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Walk

/-- Position of a generation-`n` label relative to its prefix at generation
`anchor`.  Outside the intended depth constraints, `positionAtGeneration`
supplies the same zero-default convention as the rest of the generation API. -/
def relativePositionAtGeneration
    {Root α Mark Position : Type*} [AddCommGroup Position]
    (initial : Root → Position) (d : Mark → Position)
    (anchor n : ℕ) (p : RootIndexed.TreeNode Root α)
    (field : RootIndexed.StepField Root α Mark) : Position :=
  RootIndexed.positionAtGeneration initial d n p.1 p.2 field -
    RootIndexed.positionAtGeneration initial d anchor p.1
      (p.2.take anchor) field

/-- A relative position is observable at generation `n` whenever its anchor
does not lie in the future. -/
theorem relativePositionAtGeneration_measurable
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position]
    (initial : Root → Position) (d : Mark → Position) (hd : Measurable d)
    {anchor n : ℕ} (hanchor : anchor ≤ n)
    (p : RootIndexed.TreeNode Root α) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (relativePositionAtGeneration initial d anchor n p) := by
  have hcurrent := RootIndexed.positionAtGeneration_measurable
    initial d hd n p.1 p.2
  have href : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (RootIndexed.positionAtGeneration initial d anchor p.1
        (p.2.take anchor)) :=
    (RootIndexed.positionAtGeneration_measurable
      initial d hd anchor p.1 (p.2.take anchor)).mono
        ((RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := Mark)).mono hanchor) le_rfl
  exact hcurrent.sub href

/-- Relative position evolves by the mapped mark of the last edge as long as
the reference generation is no later than the parent. -/
theorem relativePositionAtGeneration_child
    {Root α Mark Position : Type*} [AddCommGroup Position]
    (initial : Root → Position) (d : Mark → Position)
    (field : RootIndexed.StepField Root α Mark)
    {anchor n : ℕ} (hanchor : anchor ≤ n)
    (p : RootIndexed.TreeNode Root α) (hp : p.2.length = n) (i : α) :
    relativePositionAtGeneration initial d anchor (n + 1)
        (p.1, p.2 ++ [i]) field =
      relativePositionAtGeneration initial d anchor n p field +
        value' ((field p.1 p.2).map d) i := by
  have hchildDepth : (p.2 ++ [i]).length = n + 1 := by
    simp [hp]
  have hpref : (p.2.take anchor).length = anchor := by
    simp [List.length_take, hp, min_eq_left hanchor]
  have htake : (p.2 ++ [i]).take anchor = p.2.take anchor :=
    List.take_append_of_le_length (by simpa [hp] using hanchor)
  unfold relativePositionAtGeneration
  simp only [positionAtGeneration, hchildDepth, hp, hpref, htake,
    ↓reduceIte]
  rw [RootIndexed.position_append_singleton]
  abel

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
