import MeasureTheory.BranchingWalk.Displace.Node
import MeasureTheory.BranchingWalk.Step.Child
import Probability.BranchingRandomWalk.Tree.Filtration

/-!
# Measurability of node displacement on the pre-sampled marked tree

The deterministic displacement and realization vocabulary lives in
`MeasureTheory/BranchingWalk/Displace/Node.lean`. This file adds the
generation-filtration measurability results: realized nodes, fixed-address
displacements, current-generation displacements, and the displacement of a
measurably chosen current-generation address.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


theorem realizedNodeSet_measurable (u : 𝕍) :
    MeasurableSet[generationFiltration (M := NatRealStep) u.length]
      (realizedNodeSet u) := by
  have hset : realizedNodeSet u =
      ⋂ j ∈ Finset.range u.length,
        {ω : Mark ℕ NatRealStep |
          ω (u.take j) ∈ childRealized (u[j]!)} := by
    ext ω
    simp [realizedNodeSet]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (mark_measurable_of_depth_lt (u.take j) u.length hprefix)
    (childRealized_measurable (u[j]!))

/-- A fixed address's displacement is known by its generation. -/
theorem nodeDisplacement_measurable (u : 𝕍) :
    Measurable[generationFiltration (M := NatRealStep) u.length]
      (fun ω : Mark ℕ NatRealStep => nodeDisplacement ω u) := by
  unfold nodeDisplacement
  apply Finset.measurable_fun_sum
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (value'_measurable (u[j]!)).comp
    (mark_measurable_of_depth_lt (u.take j) u.length hprefix)

/-- A current-generation address has an observable displacement, while
addresses of other depths are assigned a dummy value. -/
def displacementAtGeneration (n : ℕ) (u : 𝕍)
    (ω : Mark ℕ NatRealStep) : ℝ :=
  if u.length = n then nodeDisplacement ω u else 0

theorem displacementAtGeneration_measurable (n : ℕ) (u : 𝕍) :
    Measurable[generationFiltration (M := NatRealStep) n]
      (displacementAtGeneration n u) := by
  change Measurable[generationFiltration (M := NatRealStep) n]
    (fun ω => if u.length = n then nodeDisplacement ω u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using (nodeDisplacement_measurable u)
  · simp only [hu, ite_false]
    exact measurable_const

-- The local measurable-space instance is necessary to form a product with
-- the generation-`n` σ-algebra in `measurable_from_prod_countable_right`.
set_option linter.style.haveILetI false in
theorem selectedDisplacement_measurable (n : ℕ)
    (chosen : Mark ℕ NatRealStep → 𝕍)
    (hchosen : Measurable[generationFiltration (M := NatRealStep) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[generationFiltration (M := NatRealStep) n]
      (fun ω => nodeDisplacement ω (chosen ω)) := by
  letI : MeasurableSpace (Mark ℕ NatRealStep) :=
    generationFiltration (M := NatRealStep) n
  have hjoint : Measurable
      (fun p : 𝕍 × Mark ℕ NatRealStep =>
        displacementAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (displacementAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [displacementAtGeneration, hdepth ω]

end ProbabilityTheory.BranchingRandomWalk
