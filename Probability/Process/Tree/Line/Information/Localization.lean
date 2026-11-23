/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Information.Stopped
public import Combinatorics.UlamHarris.Line.FirstEntrance

/-!
# Localizing optional-line information at a deterministic cut

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine.measurableSet_subset_stopped`: for countable `ℓ`,
  `{ω | ℓ ⊆ L ω} ∈ F_L`.
* `IsOptionalLine.measurable_stopped`: `L` is measurable in `F_L`, without
  countability of its range or of the node space.
* `IsOptionalLine.measurableSet_inter_subset`: if `A ∈ F_L` and `ℓ` is a
  countable deterministic line, then `A ∩ {ω | ℓ ⊆ L ω} ∈ past ℓ`, provided
  deterministic-line information increases in ancestral order.
* `IsOptionalLine.measurableSet_subset`: under the same assumptions,
  `{ω | ℓ ⊆ L ω} ∈ past ℓ`.

There is no finite-depth bound, countable-range condition on `L`, or hypothesis
that generation truncations of `L` are optional. Countability is imposed only
on the tested deterministic cut. Initial and reproduction information are
explicit in the supplied `past`, which may be instantiated with `linePast`.

These localization identities support the extension from deterministic-line
branching to the strong branching property at optional lines in P. Jagers,
*General branching processes as Markov fields* (1989), Theorem 4.14,
DOI 10.1016/0304-4149(89)90075-6. The deterministic and optional conditional
product identities are restated in P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching
processes* (2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419.
This module proves information identities, without assuming any branching law.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]
  {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
  {L : Ω → Set (RootIndexed.TreeNode Root α)}

private lemma subset_and_precedes_iff
    {C : Set (RootIndexed.TreeNode Root α)} (hC : RootIndexed.IsLine C)
    (ℓ q : Set (RootIndexed.TreeNode Root α)) :
    (ℓ ⊆ C ∧ RootIndexed.Line.Precedes C q) ↔
      RootIndexed.Line.Precedes C (RootIndexed.Line.firstEntrance (q ∪ ℓ)) ∧
      ∀ u ∈ ℓ, ∀ n < u.2.length,
        ¬ RootIndexed.Line.Precedes C
          (RootIndexed.Line.firstEntrance ((q ∪ ℓ) ∪ {(u.1, u.2.take n)})) := by
  constructor
  · rintro ⟨h, hpq⟩
    refine ⟨RootIndexed.Line.precedes_firstEntrance_iff.mpr ?_, ?_⟩
    · intro u hu
      rcases hu with hu | hu
      · exact hpq u hu
      · exact ⟨u, h hu, RootIndexed.IsAncestor.refl u⟩
    · intro u hu n hn hp
      have hp' := RootIndexed.Line.precedes_firstEntrance_iff.mp hp
      obtain ⟨v, hv, hvp⟩ := hp' (u.1, u.2.take n)
        (Set.mem_union_right _ (Set.mem_singleton _))
      have heq := hC.eq hv (h hu) (hvp.trans ⟨rfl, List.take_prefix n u.2⟩)
      have hlen := hvp.2.length_le
      rw [heq] at hlen
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hlen
      omega
  · rintro ⟨hp, hstrict⟩
    have hp' := RootIndexed.Line.precedes_firstEntrance_iff.mp hp
    refine ⟨?_, fun u hu => hp' u (Set.mem_union_left _ hu)⟩
    intro u hu
    obtain ⟨v, hv, hvu⟩ := hp' u (Set.mem_union_right _ hu)
    have heq : v = u := by
      by_contra hne
      have hlt : v.2.length < u.2.length := by
        have hle := hvu.2.length_le
        have hlen : v.2.length ≠ u.2.length := by
          intro hlen
          exact hne (Prod.ext hvu.1 (hvu.2.eq_of_length hlen))
        omega
      apply hstrict u hu v.2.length hlt
      apply RootIndexed.Line.precedes_firstEntrance_iff.mpr
      intro w hw
      rcases hw with hw | hw
      · exact hp' w hw
      · have hw' : w = (u.1, u.2.take v.2.length) := Set.mem_singleton_iff.mp hw
        subst w
        have he : (u.1, u.2.take v.2.length) = v :=
          Prod.ext hvu.1.symm (List.prefix_iff_eq_take.mp hvu.2).symm
        exact ⟨v, hv, he.symm ▸ RootIndexed.IsAncestor.refl v⟩
    exact heq ▸ hv

private lemma measurableSet_subset_inter_precedes
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    (ℓ : Set (RootIndexed.TreeNode Root α)) (hcount : ℓ.Countable)
    (q : Set (RootIndexed.TreeNode Root α)) (hq : RootIndexed.IsLine q) :
    MeasurableSet[past q] ({ω | ℓ ⊆ L ω} ∩
      {ω | RootIndexed.Line.Precedes (L ω) q}) := by
  have htest (B : Set (RootIndexed.TreeNode Root α)) :
      MeasurableSet[past q] {ω | RootIndexed.Line.Precedes (L ω)
        (RootIndexed.Line.firstEntrance (q ∪ B))} := by
    have hcut := RootIndexed.Line.isLine_firstEntrance (q ∪ B)
    have hp : RootIndexed.Line.Precedes
        (RootIndexed.Line.firstEntrance (q ∪ B)) q :=
      fun v hv => RootIndexed.Line.firstEntrance_precedes _ v (Set.mem_union_left _ hv)
    exact hmono hcut hq hp _ (h.measurableSet_precedes _ hcut)
  have heq : {ω | ℓ ⊆ L ω} ∩ {ω | RootIndexed.Line.Precedes (L ω) q} =
      {ω | RootIndexed.Line.Precedes (L ω) (RootIndexed.Line.firstEntrance (q ∪ ℓ))} \
        ⋃ u ∈ ℓ, ⋃ n : ℕ, {ω | n < u.2.length ∧
          RootIndexed.Line.Precedes (L ω)
            (RootIndexed.Line.firstEntrance ((q ∪ ℓ) ∪ {(u.1, u.2.take n)}))} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_iUnion,
      subset_and_precedes_iff (h.isLine ω) ℓ q, not_exists, not_and]
  rw [heq]
  apply (htest ℓ).diff
  apply MeasurableSet.biUnion hcount
  intro u hu
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n < u.2.length
  · simpa only [hn, true_and, Set.union_assoc] using htest (ℓ ∪ {(u.1, u.2.take n)})
  · simp only [hn, false_and, Set.ofPred_false]
    exact @MeasurableSet.empty Ω (past q)

/-- Containment of any countable node set is observable at the optional line itself. -/
theorem IsOptionalLine.measurableSet_subset_stopped
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    (ℓ : Set (RootIndexed.TreeNode Root α)) (hcount : ℓ.Countable) :
    MeasurableSet[h.measurableSpace] {ω | ℓ ⊆ L ω} := by
  refine ⟨?_, fun q hq => measurableSet_subset_inter_precedes h hmono ℓ hcount q hq⟩
  have heq : {ω | ℓ ⊆ L ω} = ⋂ u ∈ ℓ, {ω | u ∈ L ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [heq]
  exact MeasurableSet.biInter hcount (fun u _ => h.toIsRandomLine.measurableSet_mem u)

/-- The optional line, as a membership-valued random set, is known at its stopped information. -/
theorem IsOptionalLine.measurable_stopped
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b) :
    Measurable[h.measurableSpace] L := by
  have hm (u : RootIndexed.TreeNode Root α) :
      MeasurableSet[h.measurableSpace] {ω | u ∈ L ω} := by
    simpa only [Set.singleton_subset_iff] using
      h.measurableSet_subset_stopped hmono {u} (Set.countable_singleton u)
  let : MeasurableSpace Ω := h.measurableSpace
  exact measurable_set_iff.mpr (fun u => measurableSet_setOfPred.mp (hm u))

/-- The event that the optional cut contains a prescribed countable line is known
before any member of that deterministic line reproduces. -/
theorem IsOptionalLine.measurableSet_subset
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    {ℓ : Set (RootIndexed.TreeNode Root α)}
    (hℓ : RootIndexed.IsLine ℓ) (hcount : ℓ.Countable) :
    MeasurableSet[past ℓ] {ω | ℓ ⊆ L ω} := by
  have heq : {ω | ℓ ⊆ L ω} ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ} =
      {ω | ℓ ⊆ L ω} := by
    apply Set.inter_eq_left.mpr
    intro ω hω u hu
    exact ⟨u, hω hu, RootIndexed.IsAncestor.refl u⟩
  rw [← heq]
  exact measurableSet_subset_inter_precedes h hmono ℓ hcount ℓ hℓ

/-- Localizing stopped information to a fixed subset of the optional cut uses only
that deterministic cut's past, even when the optional cut has unbounded depth. -/
theorem IsOptionalLine.measurableSet_inter_subset
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    {ℓ : Set (RootIndexed.TreeNode Root α)}
    (hℓ : RootIndexed.IsLine ℓ) (hcount : ℓ.Countable)
    {A : Set Ω} (hA : MeasurableSet[h.measurableSpace] A) :
    MeasurableSet[past ℓ] (A ∩ {ω | ℓ ⊆ L ω}) := by
  have heq : A ∩ {ω | ℓ ⊆ L ω} =
      (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) ∩ {ω | ℓ ⊆ L ω} := by
    ext ω
    constructor
    · rintro ⟨hA, hℓL⟩
      exact ⟨⟨hA, fun u hu => ⟨u, hℓL hu, RootIndexed.IsAncestor.refl u⟩⟩, hℓL⟩
    · exact fun hω => ⟨hω.1.1, hω.2⟩
  rw [heq]
  exact (hA.2 ℓ hℓ).inter (h.measurableSet_subset hmono hℓ hcount)

end ProbabilityTheory.Tree

end
