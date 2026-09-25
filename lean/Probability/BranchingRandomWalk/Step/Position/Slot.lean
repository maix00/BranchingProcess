import Combinatorics.BranchingStep.Slot.Position
import Probability.BranchingRandomWalk.Tree.Filtration

/-!
# Measurability of path positions on the pre-sampled marked tree

The deterministic position and realization vocabulary lives in
`Combinatorics/BranchingStep/Slot/Position.lean`. This file adds the
generation-filtration measurability results: realized nodes, fixed-address
positions, current-generation positions, and the position of a measurably
chosen current-generation address.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


theorem realizedNode_measurable (u : 𝕍) :
    MeasurableSet[generationFiltration (M := NatRealBranchingStep) u.length]
      (realizedNode u) := by
  have hset : realizedNode u =
      ⋂ j ∈ Finset.range u.length,
        {ω : Mark ℕ NatRealBranchingStep |
          ω (u.take j) ∈ childRealized (u[j]!)} := by
    ext ω
    simp [realizedNode]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (mark_measurable_of_depth_lt (u.take j) u.length hprefix)
    (childRealized_measurable (u[j]!))

/-- A fixed address's position is known by its generation. -/
theorem vertexPosition_measurable (u : 𝕍) :
    Measurable[generationFiltration (M := NatRealBranchingStep) u.length]
      (fun ω : Mark ℕ NatRealBranchingStep => vertexPosition ω u) := by
  unfold vertexPosition
  apply Finset.measurable_fun_sum
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (childDisplacement_measurable (u[j]!)).comp
    (mark_measurable_of_depth_lt (u.take j) u.length hprefix)

/-- A current-generation address has an observable position, while addresses
of other depths are assigned a dummy value. -/
def positionAtGeneration (n : ℕ) (u : 𝕍)
    (ω : Mark ℕ NatRealBranchingStep) : ℝ :=
  if u.length = n then vertexPosition ω u else 0

theorem positionAtGeneration_measurable (n : ℕ) (u : 𝕍) :
    Measurable[generationFiltration (M := NatRealBranchingStep) n]
      (positionAtGeneration n u) := by
  change Measurable[generationFiltration (M := NatRealBranchingStep) n]
    (fun ω => if u.length = n then vertexPosition ω u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using (vertexPosition_measurable u)
  · simp only [hu, ite_false]
    exact measurable_const

-- The local measurable-space instance is necessary to form a product with
-- the generation-`n` σ-algebra in `measurable_from_prod_countable_right`.
set_option linter.style.haveILetI false in
theorem selectedPosition_measurable (n : ℕ)
    (chosen : Mark ℕ NatRealBranchingStep → 𝕍)
    (hchosen : Measurable[generationFiltration (M := NatRealBranchingStep) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[generationFiltration (M := NatRealBranchingStep) n]
      (fun ω => vertexPosition ω (chosen ω)) := by
  letI : MeasurableSpace (Mark ℕ NatRealBranchingStep) :=
    generationFiltration (M := NatRealBranchingStep) n
  have hjoint : Measurable
      (fun p : 𝕍 × Mark ℕ NatRealBranchingStep =>
        positionAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (positionAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [positionAtGeneration, hdepth ω]

end ProbabilityTheory.BranchingRandomWalk
