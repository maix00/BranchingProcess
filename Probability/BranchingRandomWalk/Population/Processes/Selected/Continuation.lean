/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
import Combinatorics.UlamHarris.Generation

/-!
# Continuing a selected branching walk from a generation

## Public declarations

* `RootIndexed.selectedPopulationTotalized_eq_image_subtrees`: let
  (u_i=(r_i,v_i)) enumerate every selected particle at generation (n).
  Give root (i) its position at (u_i) and its descendant field
  (omega(r_i,v_imathbin{++}cdot)). When the new label order is induced
  by the address embedding (e(i,w)=(r_i,v_imathbin{++}w)), the selected
  populations satisfy (P_{n+k}=e(P_k^{\mathrm{sub}})) for every (k).
-/

public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

private lemma lowerFinite_image_iff
    {ι κ V : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder V]
    (f : ι → κ) (hf : Function.Injective f) (C : Set ι)
    (key : ι → V) (key' : κ → V)
    (hkey : ∀ p ∈ C, ∀ q ∈ C, valueKey key p ≤ valueKey key q ↔
      valueKey key' (f p) ≤ valueKey key' (f q)) :
    IsLowerFiniteBy key' (f '' C) ↔ IsLowerFiniteBy key C := by
  have hsection (p : ι) (hp : p ∈ C) :
      {q | q ∈ f '' C ∧ valueKey key' q ≤ valueKey key' (f p)} =
        f '' {q | q ∈ C ∧ valueKey key q ≤ valueKey key p} := by
    ext q
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzp⟩
      exact ⟨z, ⟨hz, (hkey z hz p hp).mpr hzp⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzp⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hkey z hz p hp).mp hzp⟩
  constructor
  · intro h p hp
    have hfinite := h (f p) (Set.mem_image_of_mem f hp)
    rw [hsection p hp] at hfinite
    exact hfinite.of_finite_image hf.injOn
  · rintro h _ ⟨p, hp, rfl⟩
    rw [hsection p hp]
    exact (h p hp).image f

/-- Restart the selected walk from the full population at generation `n`.
The descendant addresses use the original tie order and retain their
absolute positions. -/
theorem RootIndexed.selectedPopulationTotalized_eq_image_subtrees
    {Root κ α Mark Position Value : Type*} [Fintype κ]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode κ α)] [LinearOrder Value] [AddCommMonoid Position]
    (N : ℕ) (initialRoots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value) (ω : RootIndexed.StepField Root α Mark)
    (n : ℕ) (roots : κ → RootIndexed.TreeNode Root α)
    (hdepth : ∀ i, (roots i).2.length = n) (hroots : Function.Injective roots)
    (hcover : Finset.univ.image roots =
      RootIndexed.selectedPopulationTotalized N initialRoots initial d φ n ω)
    (horder : ∀ p q : RootIndexed.TreeNode κ α, p < q ↔
      ((roots p.1).1, (roots p.1).2 ++ p.2) < ((roots q.1).1, (roots q.1).2 ++ q.2)) :
    ∀ k : ℕ, RootIndexed.selectedPopulationTotalized N initialRoots initial d φ (n + k) ω =
      (RootIndexed.selectedPopulationTotalized N Finset.univ
        (RootIndexed.subtreeInitialPosition initial d ω roots) d φ k
        (RootIndexed.subtreeStepFieldVector roots ω)).image
        (fun p => ((roots p.1).1, (roots p.1).2 ++ p.2)) := by
  let embed (p : RootIndexed.TreeNode κ α) : RootIndexed.TreeNode Root α :=
    ((roots p.1).1, (roots p.1).2 ++ p.2)
  have hinj : Function.Injective embed :=
    Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective roots hdepth hroots
  let localPosition := RootIndexed.subtreeInitialPosition initial d ω roots
  let subtrees := RootIndexed.subtreeStepFieldVector roots ω
  let original := fun k => RootIndexed.selectedPopulationTotalized N initialRoots initial d φ k ω
  let restarted := fun k =>
    RootIndexed.selectedPopulationTotalized N Finset.univ localPosition d φ k subtrees
  change ∀ k, original (n + k) = (restarted k).image embed
  intro k
  induction k with
  | zero =>
    rw [Nat.add_zero, ← show Finset.univ.image roots = original n from hcover]
    ext p
    simp [restarted, RootIndexed.selectedPopulationTotalized, RootIndexed.mem_initialPopulation_iff,
      Finset.mem_image, embed]
  | succ k ih =>
    let C := Combinatorics.Branching.Population.childrenAtGeneration k (restarted k) subtrees
    let D := Combinatorics.Branching.Population.childrenAtGeneration (n + k) (original (n + k)) ω
    have hchildren : embed '' C = D := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨a, ha, hlen, j, hj, rfl⟩ :=
          (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff _ _ _ _).mp hp
        apply (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff _ _ _ _).mpr
        exact ⟨embed a, ih ▸ Finset.mem_image_of_mem embed ha,
          by simp [embed, hdepth, hlen], j, hj,
          by simp [embed, Combinatorics.UlamHarris.RootIndexed.childAddress, List.append_assoc]⟩
      · intro hq
        obtain ⟨a, ha, hlen, j, hj, rfl⟩ :=
          (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff _ _ _ _).mp hq
        rw [ih] at ha
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        have hpdepth := RootIndexed.selectedPopulationTotalized_depth N Finset.univ localPosition
          d φ k subtrees p hp
        refine ⟨Combinatorics.UlamHarris.RootIndexed.childAddress p j, ?_, ?_⟩
        · exact (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff _ _ _ _).mpr
            ⟨p, hp, hpdepth, j, hj, rfl⟩
        · simp [embed, Combinatorics.UlamHarris.RootIndexed.childAddress, List.append_assoc]
    let key := RootIndexed.observedPositionAtGeneration localPosition d φ (k + 1) subtrees
    let originalKey :=
      RootIndexed.observedPositionAtGeneration initial d φ (n + k + 1) ω
    have hvalue (p : RootIndexed.TreeNode κ α) (hp : p ∈ C) : key p = originalKey (embed p) := by
      have hlen := Combinatorics.Branching.Population.childrenAtGeneration_depth k
        (restarted k) subtrees p hp
      have hembed : (embed p).2.length = n + k + 1 := by
        simp [embed, hdepth, hlen, Nat.add_assoc]
      dsimp only [key, originalKey]
      rw [RootIndexed.observedPositionAtGeneration_eq _ _ _ _ _ _ hlen,
        RootIndexed.observedPositionAtGeneration_eq _ _ _ _ _ _ hembed]
      exact congrArg φ (RootIndexed.position_subtreeStepFieldVector initial d ω roots p.1 p.2)
    have hlt (p : RootIndexed.TreeNode κ α) (hp : p ∈ C)
        (q : RootIndexed.TreeNode κ α) (hq : q ∈ C) :
        valueKey key p < valueKey key q ↔
          valueKey originalKey (embed p) < valueKey originalKey (embed q) := by
      simp only [valueKey, Prod.Lex.lt_iff, ofLex_toLex, hvalue p hp, hvalue q hq]
      rw [show p < q ↔ embed p < embed q from horder p q]
    have hfinite : IsLowerFiniteBy originalKey D ↔ IsLowerFiniteBy key C := by
      rw [← hchildren]
      exact lowerFinite_image_iff embed hinj C key originalKey
        (fun p hp q hq => by simpa only [not_lt] using (not_congr (hlt q hq p hp)))
    by_cases hgood : IsLowerFiniteBy key C
    · have hlocal : IsFirstNBy N key C (restarted (k + 1)) :=
        RootIndexed.selectedPopulationTotalized_succ_spec N Finset.univ localPosition
          d φ k subtrees hgood
      have hglobal : IsFirstNBy N originalKey D (original (n + k + 1)) :=
        RootIndexed.selectedPopulationTotalized_succ_spec N initialRoots initial d φ (n + k)
          ω (hfinite.mpr hgood)
      -- Extend key agreement off the candidate set, where the selector never reads it.
      let extended := fun p => originalKey (embed p)
      have hlocal' := hlocal.congr_value (fun p hp => hvalue p hp)
      have horderKey (p q : RootIndexed.TreeNode κ α) :
          valueKey extended p < valueKey extended q ↔
            valueKey originalKey (embed p) < valueKey originalKey (embed q) := by
        simp only [valueKey, extended, Prod.Lex.lt_iff, ofLex_toLex]
        rw [show p < q ↔ embed p < embed q from horder p q]
      have himage := IsFirstNBy.image N embed hinj extended originalKey horderKey C _ hlocal'
      rw [hchildren] at himage
      exact hglobal.unique himage
    · have hglobal : ¬ IsLowerFiniteBy originalKey D := fun h => hgood (hfinite.mp h)
      have hl := selectFirstNFromSetTotalized_empty_of_not_lowerFinite N
        (RootIndexed.observedPositionAtGeneration localPosition d φ (k + 1))
        (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N Finset.univ localPosition d φ k field) field)
        subtrees hgood
      have hg := selectFirstNFromSetTotalized_empty_of_not_lowerFinite N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + k + 1))
        (fun field => Combinatorics.Branching.Population.childrenAtGeneration (n + k)
          (RootIndexed.selectedPopulationTotalized N initialRoots initial d φ (n + k) field) field)
        ω hglobal
      change original (n + k + 1) = (restarted (k + 1)).image embed
      have heq₁ : original (n + k + 1) = ∅ := hg
      have heq₂ : restarted (k + 1) = ∅ := hl
      simp [heq₁, heq₂]

/-- Common spatial translation preserves the first-`N` genealogy. -/
theorem RootIndexed.selectedPopulationTotalized_add_initial
    {Root α Mark : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initial : Root → ℝ)
    (d : Mark → ℝ) (ω : RootIndexed.StepField Root α Mark) (c : ℝ) :
    ∀ k, RootIndexed.selectedPopulationTotalized N roots (fun r => initial r + c) d id k ω =
      RootIndexed.selectedPopulationTotalized N roots initial d id k ω := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    let parents := RootIndexed.selectedPopulationTotalized N roots initial d id k ω
    let C := Combinatorics.Branching.Population.childrenAtGeneration k parents ω
    let key := RootIndexed.observedPositionAtGeneration initial d id (k + 1) ω
    let shifted := RootIndexed.observedPositionAtGeneration (fun r => initial r + c) d id (k + 1) ω
    let translated := fun p => key p + c
    have hkey (p : RootIndexed.TreeNode Root α) (hp : p ∈ C) :
        shifted p = translated p := by
      have hdepth := Combinatorics.Branching.Population.childrenAtGeneration_depth k parents ω p hp
      simp only [shifted, key, translated, RootIndexed.observedPositionAtGeneration, id_eq,
        RootIndexed.positionAtGeneration, RootIndexed.position, hdepth, ↓reduceIte]
      ac_rfl
    have hlt (p q : RootIndexed.TreeNode Root α) :
        valueKey key p < valueKey key q ↔ valueKey translated p < valueKey translated q := by
      simp [valueKey, Prod.Lex.lt_iff, translated]
    have hfinite : IsLowerFiniteBy shifted C ↔ IsLowerFiniteBy key C := by
      simpa using lowerFinite_image_iff id Function.injective_id C key shifted
        (fun p hp q hq => by
          have heq (r : RootIndexed.TreeNode Root α) (hr : r ∈ C) :
              valueKey shifted r = valueKey translated r := by simp [valueKey, hkey r hr]
          simpa only [id_eq, not_lt, heq p hp, heq q hq] using not_congr (hlt q p))
    have hC : Combinatorics.Branching.Population.childrenAtGeneration k
        (RootIndexed.selectedPopulationTotalized N roots (fun r => initial r + c) d id k ω) ω = C :=
      congrArg (fun pop => Combinatorics.Branching.Population.childrenAtGeneration k pop ω) ih
    by_cases hgood : IsLowerFiniteBy key C
    · have hplain := RootIndexed.selectedPopulationTotalized_succ_spec N roots initial d id k ω hgood
      have hshifted := RootIndexed.selectedPopulationTotalized_succ_spec N roots
        (fun r => initial r + c) d id k ω
        (show IsLowerFiniteBy shifted _ from hC.symm ▸ hfinite.mpr hgood)
      rw [hC] at hshifted
      have hsame := IsFirstNBy.image N id Function.injective_id key translated hlt C _ hplain
      have hsame' : IsFirstNBy N translated C
          (RootIndexed.selectedPopulationTotalized N roots initial d id (k + 1) ω) := by
        simpa using hsame
      exact hshifted.unique (hsame'.congr_value fun p hp => (hkey p hp).symm)
    · have hshift : ¬ IsLowerFiniteBy shifted C := fun h => hgood (hfinite.mp h)
      have hnil₁ := selectFirstNFromSetTotalized_empty_of_not_lowerFinite N
        (RootIndexed.observedPositionAtGeneration (fun r => initial r + c) d id (k + 1))
        (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots (fun r => initial r + c) d id k field)
          field)
        ω (show ¬ IsLowerFiniteBy shifted _ from hC.symm ▸ hshift)
      have hnil₂ := selectFirstNFromSetTotalized_empty_of_not_lowerFinite N
        (RootIndexed.observedPositionAtGeneration initial d id (k + 1))
        (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initial d id k field) field)
        ω hgood
      exact hnil₁.trans hnil₂.symm

end ProbabilityTheory.BranchingRandomWalk

end
