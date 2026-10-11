/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Speed.InitialPopulationFreshField
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position

/-!
# The trajectory rooted at the capacity-hitting population

At the first generation where the smaller-start process has `N` particles,
enumerate those particles in address order and rebase their descendant field.
The rebased field has the exact-`N` product law, and every local descendant
has exactly the same absolute position as its corresponding descendant in the
original pre-sampled forest.  This is the field and path interface needed to
identify the post-hit selected process with the exact-`N` rank process.

The final identification still needs a generation-by-generation theorem that
transports the `IsFirstNBy` selector through the address-prefix embedding.  In
particular, it must verify that rank order and the address tie breaker agree
at every later generation; this module does not assert that trajectory
identity without that proof.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The descendant field obtained by rooting a fresh `N`-particle forest at
the enumerated population at the actual capacity-hitting time. -/
noncomputable def smallInitialPopulationHitSubtreeField
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    RootIndexed.StepField (Fin N) ℕ ℝ :=
  RootIndexed.selectedSubtreeStepFieldVector
    (smallInitialPopulationHitRoots m N hm) field

/-- The hit particles' positions, used as the initial vector for the local
exact-`N` forest. -/
noncomputable def smallInitialPopulationHitInitialPosition
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) : Fin N → ℝ :=
  RootIndexed.selectedSubtreeInitialPosition (fun _ : Fin m => (0 : ℝ)) id
    (smallInitialPopulationHitRoots m N hm) field

/-- The address in the original forest corresponding to a local descendant
of one of the enumerated hit particles. -/
noncomputable def smallInitialPopulationHitAddress
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (q : RootIndexed.TreeNode (Fin N) ℕ) :
    RootIndexed.TreeNode (Fin m) ℕ :=
  let root := smallInitialPopulationHitRoots m N hm field q.1
  (root.1, root.2 ++ q.2)

/-- The local and global candidate sets correspond exactly under prefixing
the enumerated hit-root addresses. This is the deterministic one-generation
transport needed before transporting the first-`N` selector. -/
theorem childrenAtGeneration_image_smallInitialPopulationHitAddress
    (m N j k : ℕ) (hm : 0 < m)
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hdepth : ∀ i : Fin N,
      (smallInitialPopulationHitRoots m N hm field i).2.length = k)
    (parents : Finset (RootIndexed.TreeNode (Fin N) ℕ)) :
    Set.image (smallInitialPopulationHitAddress m N hm field)
        (RootIndexed.childrenAtGeneration j parents
          (smallInitialPopulationHitSubtreeField m N hm field)) =
      RootIndexed.childrenAtGeneration (k + j)
        (parents.image (smallInitialPopulationHitAddress m N hm field)) field := by
  classical
  ext q
  constructor
  · rintro ⟨qLocal, hqLocal, rfl⟩
    obtain ⟨p, hp, hpdepth, i, hi, rfl⟩ :=
      (RootIndexed.mem_childrenAtGeneration_iff j parents
        (smallInitialPopulationHitSubtreeField m N hm field) qLocal).mp hqLocal
    have hsurvive : survive (field
        (smallInitialPopulationHitRoots m N hm field p.1).1
        ((smallInitialPopulationHitRoots m N hm field p.1).2 ++ p.2)) i := by
      simpa [smallInitialPopulationHitSubtreeField,
        RootIndexed.selectedSubtreeStepFieldVector,
        RootIndexed.subtreeStepFieldVector] using hi
    have hpdepth' :
        (smallInitialPopulationHitAddress m N hm field p).2.length = k + j := by
      simp [smallInitialPopulationHitAddress, List.length_append,
        hdepth p.1, hpdepth]
    have hchild := RootIndexed.childAddress_mem_childrenAtGeneration
      (k + j)
      (parents.image (smallInitialPopulationHitAddress m N hm field))
      field (smallInitialPopulationHitAddress m N hm field p)
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩) hpdepth' i hsurvive
    simpa [smallInitialPopulationHitAddress, List.append_assoc] using hchild
  · intro hq
    obtain ⟨pGlobal, hpGlobal, hpGlobalDepth, i, hi, rfl⟩ :=
      (RootIndexed.mem_childrenAtGeneration_iff (k + j)
        (parents.image (smallInitialPopulationHitAddress m N hm field))
        field q).mp hq
    obtain ⟨pLocal, hpLocal, hpEq⟩ := Finset.mem_image.mp hpGlobal
    have hpGlobalDepth' :
        (smallInitialPopulationHitAddress m N hm field pLocal).2.length = k + j := by
      simpa [hpEq] using hpGlobalDepth
    have hpLocalDepth : pLocal.2.length = j := by
      simpa [smallInitialPopulationHitAddress, List.length_append,
        hdepth pLocal.1] using hpGlobalDepth'
    have hsurvive : survive
        ((smallInitialPopulationHitSubtreeField m N hm field)
          pLocal.1 pLocal.2) i := by
      rw [← hpEq] at hi
      simpa [smallInitialPopulationHitAddress,
        smallInitialPopulationHitSubtreeField,
        RootIndexed.selectedSubtreeStepFieldVector,
        RootIndexed.subtreeStepFieldVector] using hi
    have hchild := RootIndexed.childAddress_mem_childrenAtGeneration
      j parents (smallInitialPopulationHitSubtreeField m N hm field)
      pLocal hpLocal hpLocalDepth i hsurvive
    refine ⟨(pLocal.1, pLocal.2 ++ [i]), hchild, ?_⟩
    rw [← hpEq]
    simp [smallInitialPopulationHitAddress, List.append_assoc]

/-- The local exact-`N` forest's position at any descendant address agrees
with the original forest's position at the corresponding prefixed address.
This is a pathwise statement and does not assume the capacity time finite. -/
theorem smallInitialPopulationHitSubtree_position
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) (i : Fin N)
    (v : TreeNode ℕ) :
    RootIndexed.position (smallInitialPopulationHitInitialPosition m N hm field)
        id (smallInitialPopulationHitSubtreeField m N hm field) i v =
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
        (smallInitialPopulationHitRoots m N hm field i).1
        ((smallInitialPopulationHitRoots m N hm field i).2 ++ v) := by
  exact RootIndexed.position_selectedSubtreeStepFieldVector
    (fun _ : Fin m => (0 : ℝ)) id
    (smallInitialPopulationHitRoots m N hm) field i v

/-- On a finite hit, each local initial position is the actual particle
position at that generation. -/
theorem smallInitialPopulationHitInitialPosition_eq_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n)
    (i : Fin N) :
    smallInitialPopulationHitInitialPosition m N hm field i =
      RootIndexed.positionAtGeneration (fun _ : Fin m => (0 : ℝ)) id n
        (smallInitialPopulationHitRoots m N hm field i).1
        (smallInitialPopulationHitRoots m N hm field i).2 field := by
  have hdepth := smallInitialPopulationHitRoots_depth_at_time
    m N n hm field htime i
  simp [smallInitialPopulationHitInitialPosition,
    RootIndexed.selectedSubtreeInitialPosition,
    RootIndexed.subtreeInitialPosition,
    RootIndexed.positionAtGeneration, hdepth]

/-- At a finite hit, the enumerated roots are exactly the actual selected
population at the hitting generation. -/
theorem smallInitialPopulationHitRoots_image_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n) :
    Finset.univ.image (smallInitialPopulationHitRoots m N hm field) =
      smallInitialPopulation m N n field := by
  classical
  have hcard : (smallInitialPopulation m N n field).card = N :=
    (smallInitialPopulationCapacityTime_eq_iff m N n field).1 htime |>.1
  have hinj : Function.Injective (smallInitialPopulationHitRoots m N hm field) :=
    smallInitialPopulationHitRoots_injective_at_time m N n hm field htime
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact smallInitialPopulationHitRoots_mem_at_time
      m N n hm field htime i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
    exact hcard.le

/-- The rebased descendant field at the actual hitting time has the ordinary
exact-`N` root-field law.  The hypotheses are precisely those already used to
prove the hit is finite and to factor fresh marks at the stopping time. -/
theorem smallInitialPopulationHitSubtreeField_law
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ)
    (B : Set (Fin N → TreeNode ℕ → Step ℕ ℝ))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      (smallInitialPopulationHitSubtreeField m N hm ⁻¹' B) =
    finiteRootStepFieldLaw μ N B := by
  exact smallInitialPopulationHitRoots_freshField_law
    m N hm hmN μ hboundary hnonempty hsupercritical B hB

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
