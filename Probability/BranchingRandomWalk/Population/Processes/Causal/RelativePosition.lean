import Probability.BranchingRandomWalk.Population.Processes.Causal.Predicate
import Probability.BranchingRandomWalk.Population.Processes.Causal.Genealogy
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.RelativePosition
import Combinatorics.BranchingWalk.Step.ExponentialWeight

/-!
# Causal killing in ancestral relative-position windows

This is the measurable construction used by moving tubes that restart from
the position of an intermediate ancestor.  The anchor generation may vary
with the current generation but must never lie in the future.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Kill every child whose displacement from its `anchor n` ancestor lies
outside `window n`.  No order or real-valued structure is imposed on the
position space. -/
noncomputable def ofRelativePositionSets
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (anchor : ℕ → ℕ) (hanchor : ∀ n, anchor n ≤ n)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α Mark),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (anchor (n + 1)) (n + 1) q field ∈ window (n + 1)}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofPredicate (Root := Root) (α := α) (X := Mark)
    initial hinitialDepth
    (fun n field q =>
      RootIndexed.relativePositionAtGeneration initialPosition d
        (anchor n) n q field ∈ window n) hfinite
  intro n q
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n
  apply measurableSet_setOfPred.mp
  exact (RootIndexed.relativePositionAtGeneration_measurable
    initialPosition d hd (hanchor n) q) (hwindow n)

/-- Two-stage killed population: positions are viewed from the initial root
through `cutoff`, and from the generation-`cutoff` ancestor afterwards.  The
window function may impose narrower cuts exactly at `cutoff` and at a terminal
generation. -/
noncomputable def ofRestartedPositionSets
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α Mark),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1) q field ∈
            window (n + 1)}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id :=
  ofRelativePositionSets initialPosition d hd initial hinitialDepth
    (RootIndexed.restartAnchor cutoff) (RootIndexed.restartAnchor_le cutoff)
    window hwindow hfinite

/-- Construct the two-stage killed population from directional local
finiteness of each offspring step.  A measurable window only needs a common
upper bound at each generation; the entire offspring set may be uncountable. -/
noncomputable def ofRestartedPositionSetsOfUpperFinite
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position] [LinearOrder Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → Position)
    (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (hlevel : ∀ (n : ℕ) (field : RootIndexed.StepField Root α Mark)
        (p : RootIndexed.TreeNode Root α), p.2.length = n → ∀ (a : Position),
      {i | survive (field p.1 p.2) i ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1)
          (p.1, p.2 ++ [i]) field ≤ a}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofRestartedPositionSets initialPosition d hd initial hinitialDepth
    cutoff window hwindow
  intro n parents field
  apply RootIndexed.childrenAtGeneration_filter_finite_of_upperBound
    n parents field
    (fun q => RootIndexed.relativePositionAtGeneration initialPosition d
      (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1) q field)
    (window (n + 1)) (upper (n + 1)) (hupper (n + 1))
  intro p _ hp a
  exact hlevel n field p hp a

/-- The directional finiteness premise can be checked on each mapped
branching step itself.  Translation from a parent position to its child does
not alter finiteness of lower levels. -/
noncomputable def ofRestartedPositionSetsOfStepLowerFinite
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position] [LinearOrder Position]
    [IsOrderedAddMonoid Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → Position)
    (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (hstep : ∀ (field : RootIndexed.StepField Root α Mark)
        (p : RootIndexed.TreeNode Root α) (a : Position),
      {i | survive ((field p.1 p.2).map d) i ∧
        value' ((field p.1 p.2).map d) i ≤ a}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofRestartedPositionSetsOfUpperFinite initialPosition d hd initial
    hinitialDepth cutoff window hwindow upper hupper
  intro n field p hp a
  let parentRelative := RootIndexed.relativePositionAtGeneration
    initialPosition d (RootIndexed.restartAnchor cutoff (n + 1)) n p field
  apply (hstep field p (a - parentRelative)).subset
  intro i hi
  refine ⟨?_, ?_⟩
  · simpa using hi.1
  · apply le_sub_iff_add_le.mpr
    rw [add_comm]
    rw [← RootIndexed.relativePositionAtGeneration_child initialPosition d field
      (RootIndexed.restartAnchor_succ_le_parent cutoff n) p hp i]
    exact hi.2

/-- Real-valued specialization: finiteness of the usual negative exponential
offspring weight supplies every lower-level finiteness premise required by the
two-stage tube construction. -/
noncomputable def ofRestartedRealPositionSetsOfFiniteWeight
    {Root α Mark : Type*} [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (hweight : ∀ (field : RootIndexed.StepField Root α Mark)
        (p : RootIndexed.TreeNode Root α),
      totalPotentialWeight (⟨d, hd⟩ : Potential Mark) (-1)
        (field p.1 p.2) ≠ ∞) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofRestartedPositionSetsOfStepLowerFinite initialPosition d hd initial
    hinitialDepth cutoff window hwindow upper hupper
  intro field p a
  let ξ := field p.1 p.2
  have hfinite := finite_realized_children_potential_below
    (φ := (⟨d, hd⟩ : Potential Mark)) ξ (hweight field p) a
  have heq :
      {i | survive (ξ.map d) i ∧ value' (ξ.map d) i ≤ a} =
        {i | survive ξ i ∧ ξ.potentialValue' (⟨d, hd⟩ : Potential Mark) i ≤ a} := by
    ext i
    cases hi : ξ i <;>
      simp [Step.map, survive, value', Step.potentialValue',
        Step.potentialAt?, hi]
  rw [heq]
  exact hfinite

/-- A total version of the real-valued restarted tube process.  At a parent
whose negative exponential offspring weight is infinite, all children are
killed.  Hence the construction is finite for every pre-sampled field, while
boundary normalization later shows that this guard is almost surely inactive
simultaneously at all countably labelled coordinates. -/
noncomputable def ofRestartedRealPositionSets
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n)) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  let potential : Potential Mark := ⟨d, hd⟩
  let keep : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Prop := fun n field q =>
    (n = 0 ∨ q.2.length ≠ n ∨ totalPotentialWeight potential (-1)
        (field (parent q).1 (parent q).2) ≠ ∞) ∧
      RootIndexed.relativePositionAtGeneration initialPosition d
        (RootIndexed.restartAnchor cutoff n) n q field ∈ window n
  apply ofPredicate initial hinitialDepth keep
  · intro n parents field
    let goodParents := parents.filter fun p =>
      totalPotentialWeight potential (-1) (field p.1 p.2) ≠ ∞
    have hfinite :
        {q | q ∈ RootIndexed.childrenAtGeneration n goodParents field ∧
          RootIndexed.relativePositionAtGeneration initialPosition d
            (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1) q field ∈
              window (n + 1)}.Finite := by
      apply RootIndexed.childrenAtGeneration_filter_finite_of_upperBound
        n goodParents field
        (fun q => RootIndexed.relativePositionAtGeneration initialPosition d
          (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1) q field)
        (window (n + 1)) (upper (n + 1)) (hupper (n + 1))
      intro p hp hpdepth a
      have hpweight : totalPotentialWeight potential (-1)
          (field p.1 p.2) ≠ ∞ := (Finset.mem_filter.mp hp).2
      let parentRelative := RootIndexed.relativePositionAtGeneration
        initialPosition d (RootIndexed.restartAnchor cutoff (n + 1)) n p field
      have hstep := finite_realized_children_potential_below
        (φ := potential) (field p.1 p.2) hpweight (a - parentRelative)
      apply hstep.subset
      intro i hi
      refine ⟨hi.1, ?_⟩
      have hpotential :
          (field p.1 p.2).potentialValue' potential i =
            value' ((field p.1 p.2).map d) i := by
        cases hslot : field p.1 p.2 i <;>
          simp [Step.map, value', Step.potentialValue', Step.potentialAt?,
            potential, hslot]
      rw [hpotential]
      apply le_sub_iff_add_le.mpr
      rw [add_comm]
      rw [← RootIndexed.relativePositionAtGeneration_child initialPosition d field
        (RootIndexed.restartAnchor_succ_le_parent cutoff n) p hpdepth i]
      exact hi.2
    apply hfinite.subset
    intro q hq
    obtain ⟨p, hp, hpdepth, i, hi, rfl⟩ :=
      (RootIndexed.mem_childrenAtGeneration_iff n parents field q).mp hq.1
    have hpweight : totalPotentialWeight potential (-1)
        (field p.1 p.2) ≠ ∞ := by
      have hguard := hq.2.1
      simp [hpdepth] at hguard
      exact hguard
    refine ⟨RootIndexed.childAddress_mem_childrenAtGeneration n goodParents field
      p (Finset.mem_filter.mpr ⟨hp, hpweight⟩) hpdepth i hi, hq.2.2⟩
  · intro n q
    let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
      RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) n
    have hposition : MeasurableSet
        {field : RootIndexed.StepField Root α Mark |
          RootIndexed.relativePositionAtGeneration initialPosition d
            (RootIndexed.restartAnchor cutoff n) n q field ∈ window n} :=
      (RootIndexed.relativePositionAtGeneration_measurable
        initialPosition d hd (RootIndexed.restartAnchor_le cutoff n) q)
          (hwindow n)
    by_cases hn : n = 0
    · apply measurableSet_setOfPred.mp
      simpa [keep, hn] using hposition
    by_cases hdepth : q.2.length = n
    · have hparent : (parent q).2.length < n := by
        simp [parent]
        omega
      have hweight : MeasurableSet
          {field : RootIndexed.StepField Root α Mark |
            totalPotentialWeight potential (-1)
              (field (parent q).1 (parent q).2) ≠ ∞} :=
        ((totalPotentialWeight_measurable potential (-1)).comp
            (RootIndexed.step_measurable (X := Mark)
              (parent q).1 (parent q).2 hparent))
          (measurableSet_singleton (∞ : ENNReal)) |>.compl
      have hweight' : Measurable fun field : RootIndexed.StepField Root α Mark =>
          totalPotentialWeight potential (-1)
            (field (parent q).1 (parent q).2) ≠ ∞ :=
        measurableSet_setOfPred.mp hweight
      have hposition' : Measurable fun field : RootIndexed.StepField Root α Mark =>
          RootIndexed.relativePositionAtGeneration initialPosition d
            (RootIndexed.restartAnchor cutoff n) n q field ∈ window n :=
        measurableSet_setOfPred.mp hposition
      simpa [keep, hn, hdepth] using hweight'.and hposition'
    · apply measurableSet_setOfPred.mp
      simpa [keep, hn, hdepth] using hposition

/-- The total restarted construction has finite slices, although its public
type is the general set-valued causal population. -/
theorem ofRestartedRealPositionSets_finiteSlices
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n)) :
    (ofRestartedRealPositionSets initialPosition d hd initial hinitialDepth
      cutoff window hwindow upper hupper).FiniteSlices := by
  intro n field
  change (↑(selectedBy initial _ _ n field) :
    Set (RootIndexed.TreeNode Root α)).Finite
  exact (selectedBy initial _ _ n field).finite_toSet

/-- Every retained positive-generation particle lies in its prescribed
relative-position window. -/
theorem mem_ofRestartedRealPositionSets_window
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    {n : ℕ} {field : RootIndexed.StepField Root α Mark}
    {q : RootIndexed.TreeNode Root α}
    (hq : q ∈ ofRestartedRealPositionSets initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper (n + 1) field) :
    RootIndexed.relativePositionAtGeneration initialPosition d
      (RootIndexed.restartAnchor cutoff (n + 1)) (n + 1) q field ∈
        window (n + 1) := by
  let potential : Potential Mark := ⟨d, hd⟩
  let keep : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Prop := fun k sample p =>
    (k = 0 ∨ p.2.length ≠ k ∨ totalPotentialWeight potential (-1)
        (sample (parent p).1 (parent p).2) ≠ ∞) ∧
      RootIndexed.relativePositionAtGeneration initialPosition d
        (RootIndexed.restartAnchor cutoff k) k p sample ∈ window k
  change q ∈ selectedBy initial keep _ (n + 1) field at hq
  exact (keep_of_mem_selectedBy_succ initial keep _ hq).2

/-- Every positive-time prefix of a retained particle satisfies the window
assigned to that time. -/
theorem mem_ofRestartedRealPositionSets_all_windows
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    {n : ℕ} {field : RootIndexed.StepField Root α Mark}
    {q : RootIndexed.TreeNode Root α}
    (hq : q ∈ ofRestartedRealPositionSets initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field)
    {k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n) :
    RootIndexed.relativePositionAtGeneration initialPosition d
      (RootIndexed.restartAnchor cutoff k) k (q.1, q.2.take k) field ∈
        window k := by
  let P := ofRestartedRealPositionSets initialPosition d hd initial
    hinitialDepth cutoff window hwindow upper hupper
  have hprefix : (q.1, q.2.take k) ∈ P k field :=
    P.prefix_mem_of_mem hq (k := k) hkn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  exact mem_ofRestartedRealPositionSets_window initialPosition d hd initial
    hinitialDepth cutoff window hwindow upper hupper hprefix

end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk
