import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Genealogy.Tree
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Path positions on the pre-sampled marked tree

An address specifies child slots along a path. Its position is the sum of
displacements in the marks of its strict ancestors. This total function is
defined even for addresses whose optional child slot is absent; a later
particle-system construction must restrict to realized addresses.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Displacement of child slot `i`, whether or not that slot is realized. -/
def childDisplacement (ξ : WeightedBranchingStep) (i : ℕ) : ℝ :=
  (ξ i).2

theorem offspringStep_eq_childDisplacement (ξ : WeightedBranchingStep) (i : ℕ) :
    offspringStep ξ i = childDisplacement ξ i := rfl

theorem childDisplacement_measurable (i : ℕ) :
    Measurable (fun ξ : WeightedBranchingStep => childDisplacement ξ i) := by
  exact (measurable_pi_apply i).snd

/-- Every child slot follows its presence flag; in particular slot zero may
be absent and the offspring point process may be empty. -/
def childRealized (i : ℕ) : Set WeightedBranchingStep :=
  childPresent i

theorem childRealized_measurable (i : ℕ) :
    MeasurableSet (childRealized i) := by
  exact childPresent_measurable i

/-- The position at a Ulam--Harris address, regardless of its realization. -/
def vertexPosition (ω : PreSampledField WeightedBranchingStep) (u : 𝕍) : ℝ :=
  ∑ j ∈ Finset.range u.length,
    childDisplacement (ω (u.take j)) (u[j]!)

def pathMark (ω : PreSampledField WeightedBranchingStep) (u : 𝕍) : ℝ :=
  vertexPosition ω u

theorem pathMark_eq_vertexPosition (ω : PreSampledField WeightedBranchingStep) (u : 𝕍) :
    pathMark ω u = vertexPosition ω u := rfl

theorem vertexPosition_append_singleton
    (ω : PreSampledField WeightedBranchingStep) (u : 𝕍) (i : ℕ) :
    vertexPosition ω (u ++ [i]) =
      vertexPosition ω u + childDisplacement (ω u) i := by
  simp only [vertexPosition, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  have hlast : (u ++ [i]).take u.length = u := by simp
  have hslot : (u ++ [i])[u.length]! = i := by simp
  rw [hlast, hslot]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  simp [List.take_append_of_le_length (Nat.le_of_lt hjlt),
    List.getElem?_append_left hjlt]

/-- An address is realized exactly when every child slot along its path is
present in the corresponding ancestor mark. -/
def realizedNode (u : 𝕍) : Set (PreSampledField WeightedBranchingStep) :=
  {ω | ∀ j ∈ Finset.range u.length,
    ω (u.take j) ∈ childRealized (u[j]!)}

theorem realizedNode_measurable (u : 𝕍) :
    MeasurableSet[generationFiltration (Mark := WeightedBranchingStep) u.length]
      (realizedNode u) := by
  have hset : realizedNode u =
      ⋂ j ∈ Finset.range u.length,
        {ω : PreSampledField WeightedBranchingStep |
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
    Measurable[generationFiltration (Mark := WeightedBranchingStep) u.length]
      (fun ω : PreSampledField WeightedBranchingStep => vertexPosition ω u) := by
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
    (ω : PreSampledField WeightedBranchingStep) : ℝ :=
  if u.length = n then vertexPosition ω u else 0

theorem positionAtGeneration_measurable (n : ℕ) (u : 𝕍) :
    Measurable[generationFiltration (Mark := WeightedBranchingStep) n]
      (positionAtGeneration n u) := by
  change Measurable[generationFiltration (Mark := WeightedBranchingStep) n]
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
    (chosen : PreSampledField WeightedBranchingStep → 𝕍)
    (hchosen : Measurable[generationFiltration (Mark := WeightedBranchingStep) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[generationFiltration (Mark := WeightedBranchingStep) n]
      (fun ω => vertexPosition ω (chosen ω)) := by
  letI : MeasurableSpace (PreSampledField WeightedBranchingStep) :=
    generationFiltration (Mark := WeightedBranchingStep) n
  have hjoint : Measurable
      (fun p : 𝕍 × PreSampledField WeightedBranchingStep =>
        positionAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (positionAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [positionAtGeneration, hdepth ω]

end ThesisSpeed
