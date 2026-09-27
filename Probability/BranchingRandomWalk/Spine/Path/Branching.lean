import Probability.BranchingRandomWalk.Spine.Path.Generation

/-!
# First-generation decomposition of ancestral-path observables

The first child slot is quantified over.  No slot is distinguished in the
model.  The remaining history is evaluated in the corresponding descendant
field and then prefixed with the initial position.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- The weighted path observable at generation `n + 1` decomposes over every
surviving first-generation child and its descendant field. -/
theorem weightedPathGeneration_succ
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    weightedPathGeneration φ (n + 1) F x ω =
      ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
        weightedPathGeneration φ n
          (fun tail => F (prependHistory x tail))
          (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) := by
  classical
  rw [weightedPathGeneration]
  let generation : Set (TreeNode ι) := {u | u.length = n + 1}
  calc
    (∑' u : TreeNode ι, weightedPathGenerationTerm φ (n + 1) F x u ω) =
        ∑' u : TreeNode ι, generation.indicator
          (fun u => weightedPathGenerationTerm φ (n + 1) F x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = n + 1
      · simp [generation, hu]
      · simp [generation, hu, weightedPathGenerationTerm, Set.indicator]
    _ = ∑' u : generation,
        weightedPathGenerationTerm φ (n + 1) F x u.1 ω := by
      exact (tsum_subtype generation
        (fun u => weightedPathGenerationTerm φ (n + 1) F x u ω)).symm
    _ = ∑' p : ι × {v : TreeNode ι // v.length = n},
        weightedPathGenerationTerm φ (n + 1) F x
          ((generationConsEquiv ι n) p).1 ω := by
      exact (Equiv.tsum_eq (generationConsEquiv ι n)
        (fun u : generation =>
          weightedPathGenerationTerm φ (n + 1) F x u.1 ω)).symm
    _ = ∑' i : ι, ∑' v : {v : TreeNode ι // v.length = n},
        weightedPathGenerationTerm φ (n + 1) F x (i :: v.1) ω := by
      change (∑' p : ι × {v : TreeNode ι // v.length = n},
        weightedPathGenerationTerm φ (n + 1) F x (p.1 :: p.2.1) ω) = _
      exact ENNReal.tsum_prod (f := fun i
          (v : {v : TreeNode ι // v.length = n}) =>
        weightedPathGenerationTerm φ (n + 1) F x (i :: v.1) ω)
    _ = ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
        weightedPathGeneration φ n
          (fun tail => F (prependHistory x tail))
          (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) := by
      apply tsum_congr
      intro i
      rw [weightedPathGeneration, ← ENNReal.tsum_mul_left]
      calc
        (∑' v : {v : TreeNode ι // v.length = n},
            weightedPathGenerationTerm φ (n + 1) F x (i :: v.1) ω) =
            ∑' v : {v : TreeNode ι // v.length = n},
              realizedPotentialWeight φ (-1) (ω []) i *
                weightedPathGenerationTerm φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i) v.1
                  (subtreeStepField [i] ω) := by
          apply tsum_congr
          intro v
          by_cases hi : survive (ω []) i
          · by_cases hv : surviveAlong (subtreeStepField [i] ω) [] v.1
            · have hv' : surviveAlong ω [i] v.1 :=
                (surviveAlong_rebase ω [i] [] v.1).mp hv
              have hpath : surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong] using And.intro hi hv'
              have hmem : (i :: v.1).length = n + 1 ∧
                  surviveAlong ω [] (i :: v.1) :=
                ⟨by simp [v.2], hpath⟩
              have hmemSub : v.1.length = n ∧
                  surviveAlong (subtreeStepField [i] ω) [] v.1 :=
                ⟨v.2, hv⟩
              simp only [weightedPathGenerationTerm, Set.indicator_apply,
                Set.mem_ofPred_eq, hmem, hmemSub]
              rw [pathPotential_cons, pathHistory_cons]
              simp only [realizedPotentialWeight, hi, ite_true, neg_one_mul]
              rw [show -((ω []).potentialValue' φ i +
                    pathPotential φ (subtreeStepField [i] ω) v.1) =
                  -(ω []).potentialValue' φ i +
                    -pathPotential φ (subtreeStepField [i] ω) v.1 by ring]
              rw [Real.exp_add, ENNReal.ofReal_mul
                (Real.exp_nonneg (-(ω []).potentialValue' φ i))]
              simp [mul_assoc]
            · have hv' : ¬ surviveAlong ω [i] v.1 := by
                intro h
                exact hv ((surviveAlong_rebase ω [i] [] v.1).mpr h)
              have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong, hi] using hv'
              simp [weightedPathGenerationTerm, v.2, hpath, hv,
                realizedPotentialWeight, hi]
          · have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
              simp [surviveAlong, hi]
            simp [weightedPathGenerationTerm, v.2, hpath,
              realizedPotentialWeight, hi]
        _ = ∑' v : TreeNode ι, {v | v.length = n}.indicator
              (fun v => realizedPotentialWeight φ (-1) (ω []) i *
                weightedPathGenerationTerm φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω)) v := by
          exact tsum_subtype {v : TreeNode ι | v.length = n}
            (fun v => realizedPotentialWeight φ (-1) (ω []) i *
              weightedPathGenerationTerm φ n
                (fun tail => F (prependHistory x tail))
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω))
        _ = ∑' v : TreeNode ι,
              realizedPotentialWeight φ (-1) (ω []) i *
                weightedPathGenerationTerm φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω) := by
          apply tsum_congr
          intro v
          by_cases hv : v.length = n
          · simp [hv]
          · simp [hv, weightedPathGenerationTerm]

/-- The corresponding first-generation decomposition without exponential
weights. -/
theorem pathGeneration_succ
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    pathGeneration φ (n + 1) F x ω =
      ∑' i : ι, survivingPotentialTest φ
        (fun y => pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i := by
  classical
  rw [pathGeneration]
  let generation : Set (TreeNode ι) := {u | u.length = n + 1}
  calc
    (∑' u : TreeNode ι, pathGenerationTerm φ (n + 1) F x u ω) =
        ∑' u : TreeNode ι, generation.indicator
          (fun u => pathGenerationTerm φ (n + 1) F x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = n + 1
      · simp [generation, hu]
      · simp [generation, hu, pathGenerationTerm, Set.indicator]
    _ = ∑' u : generation,
        pathGenerationTerm φ (n + 1) F x u.1 ω := by
      exact (tsum_subtype generation
        (fun u => pathGenerationTerm φ (n + 1) F x u ω)).symm
    _ = ∑' p : ι × {v : TreeNode ι // v.length = n},
        pathGenerationTerm φ (n + 1) F x
          ((generationConsEquiv ι n) p).1 ω := by
      exact (Equiv.tsum_eq (generationConsEquiv ι n)
        (fun u : generation =>
          pathGenerationTerm φ (n + 1) F x u.1 ω)).symm
    _ = ∑' i : ι, ∑' v : {v : TreeNode ι // v.length = n},
        pathGenerationTerm φ (n + 1) F x (i :: v.1) ω := by
      change (∑' p : ι × {v : TreeNode ι // v.length = n},
        pathGenerationTerm φ (n + 1) F x (p.1 :: p.2.1) ω) = _
      exact ENNReal.tsum_prod (f := fun i
          (v : {v : TreeNode ι // v.length = n}) =>
        pathGenerationTerm φ (n + 1) F x (i :: v.1) ω)
    _ = ∑' i : ι, survivingPotentialTest φ
        (fun y => pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i := by
      apply tsum_congr
      intro i
      unfold survivingPotentialTest
      by_cases hi : survive (ω []) i
      · simp only [hi, ite_true]
        rw [pathGeneration]
        calc
          (∑' v : {v : TreeNode ι // v.length = n},
              pathGenerationTerm φ (n + 1) F x (i :: v.1) ω) =
              ∑' v : {v : TreeNode ι // v.length = n},
                pathGenerationTerm φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i) v.1
                  (subtreeStepField [i] ω) := by
            apply tsum_congr
            intro v
            by_cases hv : surviveAlong (subtreeStepField [i] ω) [] v.1
            · have hv' : surviveAlong ω [i] v.1 :=
                  (surviveAlong_rebase ω [i] [] v.1).mp hv
              have hpath : surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong] using And.intro hi hv'
              simp [pathGenerationTerm, v.2, hpath, hv, pathHistory_cons]
            · have hv' : ¬ surviveAlong ω [i] v.1 := by
                intro h
                exact hv ((surviveAlong_rebase ω [i] [] v.1).mpr h)
              have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong, hi] using hv'
              simp [pathGenerationTerm, v.2, hpath, hv]
          _ = ∑' v : TreeNode ι, {v | v.length = n}.indicator
                (fun v => pathGenerationTerm φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω)) v := by
            exact tsum_subtype {v : TreeNode ι | v.length = n}
              (fun v => pathGenerationTerm φ n
                (fun tail => F (prependHistory x tail))
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω))
          _ = ∑' v : TreeNode ι, pathGenerationTerm φ n
                (fun tail => F (prependHistory x tail))
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω) := by
            apply tsum_congr
            intro v
            by_cases hv : v.length = n
            · simp [hv]
            · simp [hv, pathGenerationTerm]
      · simp only [hi, ite_false]
        apply ENNReal.tsum_eq_zero.mpr
        intro v
        simp [pathGenerationTerm, hi, surviveAlong]

end ProbabilityTheory.BranchingRandomWalk.Spine
