/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Speed.InitialPopulationFreshField
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
import Combinatorics.UlamHarris.Order

/-!
# The trajectory rooted at the capacity-hitting population

At the first generation where the smaller-start process has `N` particles,
enumerate those particles in address order and rebase their descendant field.
The rebased field has the exact-`N` product law, and every local descendant
has exactly the same absolute position as its corresponding descendant in the
original pre-sampled forest.  This is the field and path interface needed to
identify the post-hit selected process with the exact-`N` rank process.

The generation-by-generation identification transports the `IsFirstNBy`
selector through the address-prefix embedding. Its pathwise recurrence uses
the lower-finiteness conditions already proved almost surely from boundary
normalization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem list_lt_append_of_length_eq
    {α : Type*} [LinearOrder α] {p q u v : List α}
    (hlen : p.length = q.length) (hpq : p < q) :
    p ++ u < q ++ v := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => simp at hpq
      | cons b q => simp at hlen
  | cons a p ih =>
      cases q with
      | nil => simp at hlen
      | cons b q =>
          have hlen' : p.length = q.length := by simpa using hlen
          have hlex : List.Lex (· < ·) (a :: p) (b :: q) :=
            (List.lt_iff_lex_lt (a :: p) (b :: q)).mp hpq
          have hlex' : List.Lex (· < ·) ((a :: p) ++ u) ((b :: q) ++ v) := by
            cases hlex with
            | rel hab => exact .rel hab
            | cons htail =>
                exact .cons (ih hlen' ((List.lt_iff_lex_lt p q).mpr htail))
          exact (List.lt_iff_lex_lt ((a :: p) ++ u) ((b :: q) ++ v)).mpr hlex'

private theorem rootedAddress_append_lt
    {Root α : Type*} [LinearOrder Root] [LinearOrder α]
    (x y : RootIndexed.TreeNode Root α) (u v : List α)
    (hlen : x.2.length = y.2.length)
    (hxy : @LT.lt (RootIndexed.TreeNode Root α)
      ((RootIndexed.addressLinearOrder Root α).toPartialOrder.toPreorder.toLT) x y) :
    @LT.lt (RootIndexed.TreeNode Root α)
      ((RootIndexed.addressLinearOrder Root α).toPartialOrder.toPreorder.toLT)
      (x.1, x.2 ++ u) (y.1, y.2 ++ v) := by
  have hxy' := (RootIndexed.addressLinearOrder_lt_iff Root α x y).mp hxy
  apply (RootIndexed.addressLinearOrder_lt_iff Root α
    (x.1, x.2 ++ u) (y.1, y.2 ++ v)).mpr
  rcases hxy' with hroot | ⟨hroot, hpath⟩
  · exact Or.inl hroot
  · exact Or.inr ⟨hroot,
      list_lt_append_of_length_eq hlen hpath⟩

private theorem isFirstNBy_image
    {ι κ Value : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder Value]
    [DecidableEq κ]
    (N : ℕ) (f : ι → κ) (hf : Function.Injective f)
    (value : ι → Value) (targetValue : κ → Value)
    (keyOrder : ∀ p q,
      Combinatorics.Branching.Selection.NSelection.valueKey value p <
          Combinatorics.Branching.Selection.NSelection.valueKey value q ↔
        Combinatorics.Branching.Selection.NSelection.valueKey targetValue (f p) <
          Combinatorics.Branching.Selection.NSelection.valueKey targetValue (f q))
    (candidates : Set ι) (selected : Finset ι)
    (hselected : Combinatorics.Branching.Selection.NSelection.IsFirstNBy
      N value candidates selected) :
    Combinatorics.Branching.Selection.NSelection.IsFirstNBy N targetValue
      (f '' candidates) (selected.image f) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Set.mem_image_of_mem f (hselected.subset hp)
  · intro hfiniteImage
    have hfinite : candidates.Finite :=
      hfiniteImage.of_finite_image (by
        intro p hp q hq hpq
        exact hf hpq)
    have hcard : hfiniteImage.toFinset.card = hfinite.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card _ hfiniteImage,
        ← Set.ncard_eq_toFinset_card _ hfinite]
      exact Set.ncard_image_of_injective candidates hf
    rw [Finset.card_image_of_injective _ hf,
      hselected.card_finite hfinite, hcard]
  · intro hinfiniteImage
    have hinfinite : candidates.Infinite :=
      (Set.infinite_image_iff (by
        intro p hp q hq hpq
        exact hf hpq)).mp hinfiniteImage
    rw [Finset.card_image_of_injective _ hf, hselected.card_infinite hinfinite]
  · intro p hp q hq hqp
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := (Set.mem_image f candidates q).mp hq
    exact Finset.mem_image.mpr ⟨q₀,
      hselected.lower p₀ hp₀ q₀ hq₀
        ((keyOrder q₀ p₀).2 hqp), rfl⟩

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

private theorem smallInitialPopulationHitAddress_strictMono_at_time
    (m N n : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (q r : RootIndexed.TreeNode (Fin N) ℕ)
    (hqr : @LT.lt (RootIndexed.TreeNode (Fin N) ℕ)
      ((RootIndexed.addressLinearOrder (Fin N) ℕ).toPartialOrder.toPreorder.toLT)
      q r) :
    @LT.lt (RootIndexed.TreeNode (Fin m) ℕ)
      ((RootIndexed.addressLinearOrder (Fin m) ℕ).toPartialOrder.toPreorder.toLT)
      (@smallInitialPopulationHitAddress m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field q)
      (@smallInitialPopulationHitAddress m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field r) := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  letI : Preorder (Fin N) := (inferInstance : LinearOrder (Fin N)).toPreorder
  letI : Preorder (RootIndexed.TreeNode (Fin m) ℕ) :=
    (RootIndexed.addressLinearOrder (Fin m) ℕ).toPartialOrder.toPreorder
  have hdepth (i : Fin N) :
      (@smallInitialPopulationHitRoots m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field i).2.length = n :=
    @smallInitialPopulationHitRoots_depth_at_time m N n hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime i
  have hqr' := (RootIndexed.addressLinearOrder_lt_iff (Fin N) ℕ q r).mp hqr
  rcases hqr' with hij | ⟨hij, hword⟩
  · have hroot : @LT.lt (RootIndexed.TreeNode (Fin m) ℕ)
        ((RootIndexed.addressLinearOrder (Fin m) ℕ).toPartialOrder.toPreorder.toLT)
        (@smallInitialPopulationHitRoots m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field q.1)
        (@smallInitialPopulationHitRoots m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field r.1) := by
      rw [@smallInitialPopulationHitRoots_eq_at_time m N n hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime]
      have hcard : (smallInitialPopulation m N n field).card = N :=
        (@smallInitialPopulationCapacityTime_eq_iff m N n
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field).1 htime |>.1
      simp only [smallInitialPopulationRootsAt,
        smallInitialPopulationRootsOfFinset, dif_pos hcard]
      exact (smallInitialPopulation m N n field).orderEmbOfFin hcard |>.strictMono hij
    exact rootedAddress_append_lt
      (@smallInitialPopulationHitRoots m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field q.1)
      (@smallInitialPopulationHitRoots m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field r.1)
      q.2 r.2 ((hdepth q.1).trans (hdepth r.1).symm) hroot
  · have hword' :
        (@smallInitialPopulationHitRoots m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field q.1).2 ++ q.2 <
        (@smallInitialPopulationHitRoots m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field r.1).2 ++ r.2 := by
      rw [hij]
      exact (List.lt_iff_lex_lt _ _).mpr <| List.Lex.append_left (· < ·)
        ((List.lt_iff_lex_lt _ _).mp hword) _
    apply (RootIndexed.addressLinearOrder_lt_iff (Fin m) ℕ _ _).mpr
    exact Or.inr ⟨congrArg
      (fun i : Fin N =>
        (@smallInitialPopulationHitRoots m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field i).1) hij,
      hword'⟩

private theorem smallInitialPopulationHitAddress_injective_at_time
    (m N n : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (q r : RootIndexed.TreeNode (Fin N) ℕ)
    (hqr : @smallInitialPopulationHitAddress m N hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field q =
        @smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field r) :
    q = r := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  have hroots := @smallInitialPopulationHitRoots_injective_at_time m N n hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime
  have hrootLabel := congrArg Prod.fst hqr
  have hconcat := congrArg Prod.snd hqr
  have hrootLabel' :
      (smallInitialPopulationHitRoots m N hm field q.1).1 =
        (smallInitialPopulationHitRoots m N hm field r.1).1 := by
    simpa [smallInitialPopulationHitAddress] using hrootLabel
  have hconcat' :
      (smallInitialPopulationHitRoots m N hm field q.1).2 ++ q.2 =
        (smallInitialPopulationHitRoots m N hm field r.1).2 ++ r.2 := by
    simpa [smallInitialPopulationHitAddress] using hconcat
  have hdepthq := @smallInitialPopulationHitRoots_depth_at_time m N n hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime q.1
  have hdepthr := @smallInitialPopulationHitRoots_depth_at_time m N n hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime r.1
  have hrootPath :
      (smallInitialPopulationHitRoots m N hm field q.1).2 =
        (smallInitialPopulationHitRoots m N hm field r.1).2 := by
    have htake := congrArg (List.take n) hconcat'
    simpa [List.take_append, hdepthq, hdepthr] using htake
  have hroot : smallInitialPopulationHitRoots m N hm field q.1 =
      smallInitialPopulationHitRoots m N hm field r.1 := by
    exact Prod.ext hrootLabel' hrootPath
  have hlocalRoot : q.1 = r.1 := hroots hroot
  have hpath : q.2 = r.2 := by
    have hpathEq :
        (smallInitialPopulationHitRoots m N hm field q.1).2 ++ q.2 =
          (smallInitialPopulationHitRoots m N hm field q.1).2 ++ r.2 := by
      simpa [hroot] using hconcat'
    exact List.append_right_injective _ hpathEq
  apply Prod.ext
  · exact hlocalRoot
  · exact hpath

/-- The exact-`N` selected process on the re-rooted field, started from the
positions of the capacity-hitting particles. -/
noncomputable def smallInitialPopulationHitSubtreePopulation
    (m N : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ) :
    ℕ → Finset (RootIndexed.TreeNode (Fin N) ℕ) := by
  classical
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  exact fun j => RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin N))
    (@smallInitialPopulationHitInitialPosition m N hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field) id id j
    (@smallInitialPopulationHitSubtreeField m N hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field)

private theorem smallInitialPopulationHitAddress_observedPosition_eq
    (m N n j : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (p : RootIndexed.TreeNode (Fin N) ℕ) :
    RootIndexed.observedPositionAtGeneration
        (@smallInitialPopulationHitInitialPosition m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field)
        id id (j + 1)
        (@smallInitialPopulationHitSubtreeField m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field) p =
      RootIndexed.observedPositionAtGeneration
        (fun _ : Fin m => (0 : ℝ)) id id (n + j + 1) field
        (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field p) := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  have hrootDepth (i : Fin N) :
      (@smallInitialPopulationHitRoots m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field i).2.length = n :=
    @smallInitialPopulationHitRoots_depth_at_time m N n hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime i
  by_cases hp : p.2.length = j + 1
  · have haddressDepth :
        (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field p).2.length = n + j + 1 := by
      simp [smallInitialPopulationHitAddress, List.length_append,
        hrootDepth, hp]
      omega
    simp only [RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration, if_pos hp, if_pos haddressDepth]
    have hposition := RootIndexed.position_selectedSubtreeStepFieldVector
      (fun _ : Fin m => (0 : ℝ)) id
      (@smallInitialPopulationHitRoots m N hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ))
      field p.1 p.2
    simpa [smallInitialPopulationHitAddress,
      smallInitialPopulationHitInitialPosition,
      smallInitialPopulationHitSubtreeField] using
      hposition
  · have haddressDepth :
        ¬ (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field p).2.length = n + j + 1 := by
      intro h
      have hlen : n + p.2.length = n + j + 1 := by
        simpa [smallInitialPopulationHitAddress, List.length_append,
          hrootDepth] using h
      omega
    simp [RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration, hp, haddressDepth]

/-- One generation of the post-hit trajectory is identified with the
corresponding original population whenever both selector specifications hold.
The comparison uses positions first and the transported address order for
the deterministic tie break. -/
theorem smallInitialPopulationHitSubtreePopulation_image_succ
    (m N n j : ℕ) (hm : 0 < m)
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (parents : Finset (RootIndexed.TreeNode (Fin N) ℕ))
    (hparents : parents.image
        (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field) =
      @smallInitialPopulation m N (n + j)
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field)
    (hcandidateImage : Set.image
        (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field)
        (RootIndexed.childrenAtGeneration j parents
          (@smallInitialPopulationHitSubtreeField m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field)) =
      RootIndexed.childrenAtGeneration (n + j)
        (parents.image (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field)) field)
    (hlocal : @Combinatorics.Branching.Selection.NSelection.IsFirstNBy
      (RootIndexed.TreeNode (Fin N) ℕ) ℝ
      (RootIndexed.addressLinearOrder (Fin N) ℕ) inferInstance N
      (RootIndexed.observedPositionAtGeneration
        (@smallInitialPopulationHitInitialPosition m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field)
        id id (j + 1)
        (@smallInitialPopulationHitSubtreeField m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field))
      (RootIndexed.childrenAtGeneration j parents
        (@smallInitialPopulationHitSubtreeField m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field))
      (smallInitialPopulationHitSubtreePopulation m N hm field (j + 1)))
    (hglobal : @Combinatorics.Branching.Selection.NSelection.IsFirstNBy
      (RootIndexed.TreeNode (Fin m) ℕ) ℝ
      (RootIndexed.addressLinearOrder (Fin m) ℕ) inferInstance N
      (RootIndexed.observedPositionAtGeneration
        (fun _ : Fin m => (0 : ℝ)) id id (n + j + 1) field)
      (RootIndexed.childrenAtGeneration (n + j)
        (@smallInitialPopulation m N (n + j)
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field) field)
      (@smallInitialPopulation m N (n + j + 1)
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field)) :
    (smallInitialPopulationHitSubtreePopulation m N hm field (j + 1)).image
        (@smallInitialPopulationHitAddress m N hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field) =
      @smallInitialPopulation m N (n + j + 1)
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  letI : Preorder (RootIndexed.TreeNode (Fin m) ℕ) :=
    (RootIndexed.addressLinearOrder (Fin m) ℕ).toPartialOrder.toPreorder
  letI : Preorder (RootIndexed.TreeNode (Fin N) ℕ) :=
    (RootIndexed.addressLinearOrder (Fin N) ℕ).toPartialOrder.toPreorder
  let address := @smallInitialPopulationHitAddress m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localField := @smallInitialPopulationHitSubtreeField m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localInitial := @smallInitialPopulationHitInitialPosition m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localValue := RootIndexed.observedPositionAtGeneration
    localInitial id id (j + 1) localField
  let globalValue := RootIndexed.observedPositionAtGeneration
    (fun _ : Fin m => (0 : ℝ)) id id (n + j + 1) field
  let candidates := RootIndexed.childrenAtGeneration j parents localField
  have hdepth (i : Fin N) : (smallInitialPopulationHitRoots m N hm field i).2.length = n :=
    @smallInitialPopulationHitRoots_depth_at_time m N n hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime i
  have haddressStrict :
      @StrictMono (RootIndexed.TreeNode (Fin N) ℕ)
        (RootIndexed.TreeNode (Fin m) ℕ)
        ((RootIndexed.addressLinearOrder (Fin N) ℕ).toPartialOrder.toPreorder)
        ((RootIndexed.addressLinearOrder (Fin m) ℕ).toPartialOrder.toPreorder)
        address := by
    intro q r hqr
    exact smallInitialPopulationHitAddress_strictMono_at_time
      m N n hm field htime q r hqr
  have haddressInjective : Function.Injective address := by
    intro q r hqr
    exact smallInitialPopulationHitAddress_injective_at_time
      m N n hm field htime q r hqr
  have hkeyOrder (p q : RootIndexed.TreeNode (Fin N) ℕ) :
      Combinatorics.Branching.Selection.NSelection.valueKey localValue p <
          Combinatorics.Branching.Selection.NSelection.valueKey localValue q ↔
        Combinatorics.Branching.Selection.NSelection.valueKey globalValue (address p) <
          Combinatorics.Branching.Selection.NSelection.valueKey globalValue (address q) := by
    have hp := smallInitialPopulationHitAddress_observedPosition_eq
      m N n j hm field htime p
    have hq := smallInitialPopulationHitAddress_observedPosition_eq
      m N n j hm field htime q
    have hp' : localValue p = globalValue (address p) := by
      simpa [localValue, globalValue, address] using hp
    have hq' : localValue q = globalValue (address q) := by
      simpa [localValue, globalValue, address] using hq
    have hlabel : p < q ↔ address p < address q :=
      haddressStrict.lt_iff_lt.symm
    change toLex (localValue p, p) < toLex (localValue q, q) ↔
      toLex (globalValue (address p), address p) <
        toLex (globalValue (address q), address q)
    rw [hp', hq']
    simp only [Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro (hvalue | ⟨heq, hlt⟩)
      · exact Or.inl hvalue
      · exact Or.inr ⟨heq, hlabel.mp hlt⟩
    · rintro (hvalue | ⟨heq, hlt⟩)
      · exact Or.inl hvalue
      · exact Or.inr ⟨heq, hlabel.mpr hlt⟩
  have hcandidateImage' : Set.image address candidates =
      RootIndexed.childrenAtGeneration (n + j)
        (@smallInitialPopulation m N (n + j)
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field) field := by
    rw [hcandidateImage, hparents]
  have htransport := isFirstNBy_image N address haddressInjective
    localValue globalValue hkeyOrder candidates
    (smallInitialPopulationHitSubtreePopulation m N hm field (j + 1)) hlocal
  rw [hcandidateImage'] at htransport
  exact hglobal.unique htransport |>.symm

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

/-- After a finite capacity hit, the re-rooted exact-`N` selected process
agrees generation by generation with the original selected process. The
lower-finiteness hypotheses are the pathwise admissibility conditions for
the two totalized selectors; they hold simultaneously almost surely under
the boundary-normalized offspring law. -/
theorem smallInitialPopulationHitSubtreePopulation_image
    (m N n : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (hlocalGood : ∀ j,
      @Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
        (RootIndexed.TreeNode (Fin N) ℕ) ℝ
        (RootIndexed.addressLinearOrder (Fin N) ℕ) inferInstance
        (RootIndexed.observedPositionAtGeneration
          (@smallInitialPopulationHitInitialPosition m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field)
          id id (j + 1)
          (@smallInitialPopulationHitSubtreeField m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field))
        (RootIndexed.childrenAtGeneration j
          (smallInitialPopulationHitSubtreePopulation m N hm field j)
          (@smallInitialPopulationHitSubtreeField m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field)))
    (hglobalGood : ∀ j,
      @Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
        (RootIndexed.TreeNode (Fin m) ℕ) ℝ
        (RootIndexed.addressLinearOrder (Fin m) ℕ) inferInstance
        (RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (n + j + 1) field)
        (RootIndexed.childrenAtGeneration (n + j)
          (@smallInitialPopulation m N (n + j)
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field) field)) :
    ∀ j,
      (smallInitialPopulationHitSubtreePopulation m N hm field j).image
          (@smallInitialPopulationHitAddress m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field) =
        @smallInitialPopulation m N (n + j)
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
  classical
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  let localField := @smallInitialPopulationHitSubtreeField m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localInitial := @smallInitialPopulationHitInitialPosition m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let address := @smallInitialPopulationHitAddress m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localPopulation := smallInitialPopulationHitSubtreePopulation m N hm field
  have hlocalZero : localPopulation 0 =
      Finset.univ.image (fun i : Fin N => ((i, []) : RootIndexed.TreeNode (Fin N) ℕ)) := by
    ext q
    change q ∈ RootIndexed.initialPopulation (α := ℕ) Finset.univ ↔
      q ∈ Finset.univ.image
        (fun i : Fin N => ((i, []) : RootIndexed.TreeNode (Fin N) ℕ))
    rw [RootIndexed.mem_initialPopulation_iff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩
  have haddressZero :
      (localPopulation 0).image address =
        Finset.univ.image (smallInitialPopulationHitRoots m N hm field) := by
    rw [hlocalZero]
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro i hi
    simp [address, smallInitialPopulationHitAddress]
  have hcard : (@smallInitialPopulation m N n
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field).card = N :=
    (@smallInitialPopulationCapacityTime_eq_iff m N n
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field).1 htime |>.1
  have hinj : Function.Injective (@smallInitialPopulationHitRoots m N hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field) :=
    @smallInitialPopulationHitRoots_injective_at_time m N n hm
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime
  have hroots : Finset.univ.image (smallInitialPopulationHitRoots m N hm field) =
      @smallInitialPopulation m N n
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact @smallInitialPopulationHitRoots_mem_at_time m N n hm
        (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin]
      exact hcard.le
  have hzero :
      (localPopulation 0).image address =
        @smallInitialPopulation m N n
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
    rw [haddressZero, hroots]
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hdepth (i : Fin N) :
          (smallInitialPopulationHitRoots m N hm field i).2.length = n :=
        @smallInitialPopulationHitRoots_depth_at_time m N n hm
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field htime i
      have hcandidate := childrenAtGeneration_image_smallInitialPopulationHitAddress
        m N j n hm field hdepth (localPopulation j)
      have hlocalGood' := hlocalGood j
      change Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration localInitial id id
          (j + 1) localField)
        (RootIndexed.childrenAtGeneration j (localPopulation j) localField)
        at hlocalGood'
      have hlocalSpec :
          Combinatorics.Branching.Selection.NSelection.IsFirstNBy N
            (RootIndexed.observedPositionAtGeneration localInitial id id
              (j + 1) localField)
            (RootIndexed.childrenAtGeneration j (localPopulation j) localField)
            (localPopulation (j + 1)) := by
        simpa [localPopulation, localInitial, localField,
          smallInitialPopulationHitSubtreePopulation] using
          (RootIndexed.selectedPopulationTotalized_succ_spec N Finset.univ
            localInitial id id j localField hlocalGood')
      have hglobalSpec :
          Combinatorics.Branching.Selection.NSelection.IsFirstNBy N
            (RootIndexed.observedPositionAtGeneration
              (fun _ : Fin m => (0 : ℝ)) id id (n + j + 1) field)
            (RootIndexed.childrenAtGeneration (n + j)
              (@smallInitialPopulation m N (n + j)
                (RootIndexed.addressLinearOrder (Fin m) ℕ) field) field)
            (@smallInitialPopulation m N (n + j + 1)
              (RootIndexed.addressLinearOrder (Fin m) ℕ) field) := by
        simpa [smallInitialPopulation] using
          (RootIndexed.selectedPopulationTotalized_succ_spec N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + j) field
            (hglobalGood j))
      simpa [localPopulation, Nat.add_assoc] using
        smallInitialPopulationHitSubtreePopulation_image_succ
          m N n j hm field htime (localPopulation j) ih hcandidate
          hlocalSpec hglobalSpec

/-- Boundary admissibility is enough to discharge the pathwise selector
conditions in the post-hit trajectory comparison.  This version exposes only
the one-step finite negative exponential weight property of the pre-sampled
field; the almost-everywhere theorem below derives it from the paper's
boundary normalization assumption. -/
theorem smallInitialPopulationHitSubtreePopulation_image_of_weight
    (m N n : ℕ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : @smallInitialPopulationCapacityTime m N
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n)
    (hweight : ∀ r : Fin m, ∀ u : TreeNode ℕ,
      totalPotentialWeight realPotential (-1) (field r u) ≠ ∞) :
    ∀ j,
      (smallInitialPopulationHitSubtreePopulation m N hm field j).image
          (@smallInitialPopulationHitAddress m N hm
            (RootIndexed.addressLinearOrder (Fin m) ℕ) field) =
        @smallInitialPopulation m N (n + j)
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
  classical
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) :=
    RootIndexed.addressLinearOrder (Fin N) ℕ
  let localField := @smallInitialPopulationHitSubtreeField m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localInitial := @smallInitialPopulationHitInitialPosition m N hm
    (RootIndexed.addressLinearOrder (Fin m) ℕ) field
  let localPopulation := smallInitialPopulationHitSubtreePopulation m N hm field
  apply smallInitialPopulationHitSubtreePopulation_image m N n hm field htime
  · intro j
    apply RootIndexed.childrenAtGeneration_isLowerFiniteBy_real j
      (localPopulation j) localField localInitial
    · intro p hp
      have hdepth := RootIndexed.selectedPopulationTotalized_depth
        N Finset.univ localInitial id id j localField p (by
          simpa [localPopulation, localInitial, localField,
            smallInitialPopulationHitSubtreePopulation] using hp)
      simpa [localPopulation, localInitial, localField,
        smallInitialPopulationHitSubtreePopulation] using hdepth
    · intro p hp
      have hweight' := hweight
        (smallInitialPopulationHitRoots m N hm field p.1).1
        ((smallInitialPopulationHitRoots m N hm field p.1).2 ++ p.2)
      simpa [localField, smallInitialPopulationHitSubtreeField,
        RootIndexed.selectedSubtreeStepFieldVector,
        RootIndexed.subtreeStepFieldVector] using hweight'
  · intro j
    apply RootIndexed.childrenAtGeneration_isLowerFiniteBy_real (n + j)
      (smallInitialPopulation m N (n + j) field) field
      (fun _ : Fin m => (0 : ℝ))
    · intro p hp
      exact RootIndexed.selectedPopulationTotalized_depth
        N Finset.univ (fun _ : Fin m => (0 : ℝ)) id id (n + j) field p
        (by simpa [smallInitialPopulation] using hp)
    · intro p hp
      exact hweight p.1 p.2

/-- Almost surely, once the smaller initial population reaches capacity, its
subsequent selected populations are exactly the descendants of the
capacity-hitting roots, generation by generation.  Boundary normalization
supplies all lower-finiteness conditions simultaneously. -/
theorem finiteRootStepFieldLaw_ae_smallInitialPopulationHitSubtreePopulation_image
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∃ n : ℕ,
        @smallInitialPopulationCapacityTime m N
          (RootIndexed.addressLinearOrder (Fin m) ℕ) field = n ∧
        ∀ j,
          (smallInitialPopulationHitSubtreePopulation m N hm field j).image
              (@smallInitialPopulationHitAddress m N hm
                (RootIndexed.addressLinearOrder (Fin m) ℕ) field) =
            @smallInitialPopulation m N (n + j)
              (RootIndexed.addressLinearOrder (Fin m) ℕ) field := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  have hweightAE := RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots
    μ hboundary (Finset.univ : Finset (Fin m))
  have htimeAE := ae_smallInitialPopulationCapacityTime_ne_top
    m N hm hmN μ hboundary hnonempty hsupercritical
  filter_upwards [hweightAE, htimeAE] with field hweight htime
  obtain ⟨n, htime⟩ := WithTop.ne_top_iff_exists.mp htime
  have htime' : smallInitialPopulationCapacityTime m N field = n := htime.symm
  refine ⟨n, htime', ?_⟩
  exact smallInitialPopulationHitSubtreePopulation_image_of_weight
    m N n hm field htime'
    (fun r _ => hweight r (Finset.mem_univ r) _)

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
