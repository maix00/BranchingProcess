import Combinatorics.BranchingWalk.Cloud.SliceMeasure
import Combinatorics.BranchingWalk.Cloud.Rank.Slice

/-!
# Domination on one time slice

Two populations at a fixed time are compared through their counting measures:
`μ` is dominated by `ν` when, at every threshold, `μ` has no more mass on the left
half-line than `ν` does. This is the order B\'erard and Gou\'er\'e use on counting
measures (`Brunet-Derrida behavior of branching-selection particle systems on the
line`, arXiv:0811.2782, Section 2), stated there in the upper-tail form, and it is
the order the thesis states on finite counting measures
(`contents/n-brw/intro.tex`): the leftmost comparison of the atoms together with
`M(μ) ≤ M(ν)`, both with multiplicity.

The two directions of the line are the *same* relation read in the two orders, so
this file defines one relation and `Cloud/Order/Basic.lean` obtains the second
direction from it at `OrderDual`. It is *not* the relation with the two arguments
exchanged: both directions keep the atom count of the first population below that
of the second.

The definition is a condition on measures, so it needs nothing on the particle
index of a cloud; only the half-lines of the value space have to be measurable for
the statements that move between thresholds.
-/

open MeasureTheory

open Combinatorics.UlamHarris

namespace Combinatorics

namespace Branching

variable {X : Type*}

/-- The slice domination order read on counting measures: at every threshold the
first measure has no more mass on the left half-line than the second. -/
def SliceDominatesMeasure [MeasurableSpace X] [Preorder X] (μ ν : Measure X) : Prop :=
  ∀ a : X, μ (Set.Iic a) ≤ ν (Set.Iic a)

theorem sliceDominatesMeasure_refl [MeasurableSpace X] [Preorder X] (μ : Measure X) :
    SliceDominatesMeasure μ μ :=
  fun _ => le_rfl

theorem sliceDominatesMeasure_trans [MeasurableSpace X] [Preorder X]
    {μ ν ρ : Measure X} (h₁ : SliceDominatesMeasure μ ν)
    (h₂ : SliceDominatesMeasure ν ρ) :
    SliceDominatesMeasure μ ρ :=
  fun a => le_trans (h₁ a) (h₂ a)

/-- The rankwise form of the slice order: the particle of rank `k` of `C`, whenever it
exists, has a counterpart of rank `k` in `D` lying weakly to its left. The rank is read
in the index order of the cloud (`Cloud.sliceRank`), which is the order the selection
layer uses, and a rank present in `C` has to be present in `D`, so the particle-count
comparison `M(C) ≤ M(D)` is built in. This is the thesis's `xᵢ ≥ yᵢ` read along the
index enumeration.

The rank is read in the index order of the cloud (`Cloud.sliceRank`), which is the order
the selection layer uses, and it counts *particles*, not positions: `particles` is a set
of particles (a root together with an address), so several particles of one slice may sit
at the same position, and every one of them has its own rank. Multiplicity is therefore
kept, and the particle-count comparison `M(C) ≤ M(D)` is built into the statement, since a
rank present in `C` has to be present in `D`.

Which enumeration is meant is decided by the index order, not by the definition: at the
position-increasing order the particle of rank `0` is the leftmost one, which is the
thesis's lower-tail form, while at the reversed order (`OrderDual`, cf.
`Cloud.mapOrderDual`) the particle of rank `0` is the rightmost one, which is the
upper-tail form of Bérard–Gouéré; the two sides are mirror images and neither is obtained
by exchanging the two clouds. The agreement with the thesis's sorted-list definition,
ties included, is a statement about finite slices and is proved on the finite layer. -/
def Cloud.RankwiseDominates [LT (RootIndexed.TreeNode Root α)] [Preorder X]
    (C D : Cloud Time Root α X) (t : Time) : Prop :=
  ∀ k : ℕ∞, ∀ q, q ∈ C.particles t → C.sliceRank t q = k →
    ∃ q', q' ∈ D.particles t ∧ D.sliceRank t q' = k ∧
      D.position q'.1 q'.2 ≤ C.position q.1 q.2

/-- The rankwise form of the slice order is reflexive. -/
theorem Cloud.rankwiseDominates_refl [LT (RootIndexed.TreeNode Root α)] [Preorder X]
    (C : Cloud Time Root α X) (t : Time) : C.RankwiseDominates C t :=
  fun _ q hq h => ⟨q, hq, h, le_rfl⟩

/-- The rankwise form of the slice order is transitive, since the last cloud's particle of
rank `k` lies weakly to the left of the first cloud's particle of rank `k`. -/
theorem Cloud.rankwiseDominates_trans [LT (RootIndexed.TreeNode Root α)] [Preorder X]
    {C D E : Cloud Time Root α X} (t : Time)
    (h₁ : C.RankwiseDominates D t) (h₂ : D.RankwiseDominates E t) :
    C.RankwiseDominates E t := by
  intro k q hq hk
  obtain ⟨q', hq', hk', hle⟩ := h₁ k q hq hk
  obtain ⟨q'', hq'', hk'', hle'⟩ := h₂ k q' hq' hk'
  exact ⟨q'', hq'', hk'', hle'.trans hle⟩

/-- Half of the equivalence between the rankwise form and the threshold counts, on a finite
slice: if the particle of rank `k` of `C` has a counterpart of rank `k` in `D`, then no
threshold holds more particles of `C` than of `D`. The counterpart of a particle below the
threshold lies below the threshold as well, ranks are injective on a finite slice, and equal
ranks can only come from one particle, so the counterparts are an injection from the
particles of `C` below the threshold into those of `D`. -/
theorem Cloud.rankwiseDominates_encard_Iic_le [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder X]
    {C D : Cloud Time Root α X} (t : Time) [Fintype (C.particles t)]
    [Fintype (D.particles t)]
    (h : C.RankwiseDominates D t) (a : X) :
    {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}.encard ≤
      {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}.encard := by
  classical
  set SC : Set (RootIndexed.TreeNode Root α) := {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}
  set SD : Set (RootIndexed.TreeNode Root α) := {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}
  have hSCfin : SC.Finite := (Set.toFinite (C.particles t)).subset fun p hp => hp.1
  have hSDfin : SD.Finite := (Set.toFinite (D.particles t)).subset fun q hq => hq.1
  let g : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α := fun p =>
    if hp : p ∈ SC then Classical.choose (h (C.sliceRank t p) p hp.1 rfl) else p
  have hgMem : ∀ p (hp : p ∈ SC), g p ∈ D.particles t := by
    intro p hp
    simp only [g, dite_eq_left hp]
    exact (Classical.choose_spec (h (C.sliceRank t p) p hp.1 rfl)).1
  have hgRank : ∀ p (hp : p ∈ SC), D.sliceRank t (g p) = C.sliceRank t p := by
    intro p hp
    simp only [g, dite_eq_left hp]
    exact (Classical.choose_spec (h (C.sliceRank t p) p hp.1 rfl)).2.1
  have hgPos : ∀ p (hp : p ∈ SC), D.position (g p).1 (g p).2 ≤ C.position p.1 p.2 := by
    intro p hp
    simp only [g, dite_eq_left hp]
    exact (Classical.choose_spec (h (C.sliceRank t p) p hp.1 rfl)).2.2
  have hgSD : ∀ p ∈ SC, g p ∈ SD := fun p hp =>
    ⟨hgMem p hp, le_trans (hgPos p hp) hp.2⟩
  have hinj : Set.InjOn g SC := by
    intro p hp p' hp' hgg
    have h1 : C.sliceRank t p = C.sliceRank t p' := by
      rw [← hgRank p hp, hgg, hgRank p' hp']
    exact Cloud.sliceRank_injOn_of_finite C t hp.1 hp'.1 h1
  have hle : SC.ncard ≤ SD.ncard := Set.ncard_le_ncard_of_injOn g hgSD hinj hSDfin
  rw [Set.Finite.encard_eq_coe_toFinset_card hSCfin,
    Set.Finite.encard_eq_coe_toFinset_card hSDfin]
  have h : (hSCfin.toFinset.card : ℕ∞) ≤ (hSDfin.toFinset.card : ℕ∞) := by
    rw [← Set.ncard_eq_toFinset_card (s := SC) (hs := hSCfin),
      ← Set.ncard_eq_toFinset_card (s := SD) (hs := hSDfin)]
    exact_mod_cast hle
  exact h

/-- The rankwise form bounds the threshold counts on any slice whose ranks tell its particles
apart. Each particle of `C` below the threshold has a counterpart in `D` of the same rank,
which lies below the threshold too, and the correspondence is injective because two particles
of a slice with the same rank are the same particle. No finiteness of the slices is needed:
what is needed is that the ranks separate the particles of `C`, which on a finite slice is
`Cloud.sliceRank_injOn_of_finite` and on a slice with finitely many particles below each of
its particles is the same statement read through `Cloud.sliceRank_lt_sliceRank_of_lt`. -/
theorem Cloud.rankwiseDominates_encard_le [LT (RootIndexed.TreeNode Root α)] [Preorder X]
    {C D : Cloud Time Root α X} (t : Time)
    (hinj : Set.InjOn (C.sliceRank t) (C.particles t))
    (h : C.RankwiseDominates D t) (a : X) :
    {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}.encard ≤
      {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}.encard := by
  classical
  set SC : Set (RootIndexed.TreeNode Root α) := {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}
  set SD : Set (RootIndexed.TreeNode Root α) := {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}
  let g : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α := fun p =>
    if hp : p ∈ SC then Classical.choose (h (C.sliceRank t p) p hp.1 rfl) else p
  have hgSD : ∀ p ∈ SC, g p ∈ SD := by
    intro p hp
    simp only [g, dite_eq_left hp]
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (h (C.sliceRank t p) p hp.1 rfl)
    exact ⟨h1, le_trans h3 hp.2⟩
  have hinj' : Set.InjOn g SC := by
    intro p hp p' hp' hgg
    have key : ∀ r (hr : r ∈ SC), D.sliceRank t (g r) = C.sliceRank t r := by
      intro r hr
      simp only [g, dite_eq_left hr]
      exact (Classical.choose_spec (h (C.sliceRank t r) r hr.1 rfl)).2.1
    have h1 : C.sliceRank t p = C.sliceRank t p' :=
      calc C.sliceRank t p = D.sliceRank t (g p) := (key p hp).symm
        _ = D.sliceRank t (g p') := by rw [hgg]
        _ = C.sliceRank t p' := key p' hp'
    exact hinj hp.1 hp'.1 h1
  exact Set.encard_le_encard_of_injOn (fun p hp => hgSD p hp) hinj'

/-- The converse of the threshold count bound, on a finite slice: if no threshold holds more
particles of `C` than of `D`, then the particle of rank `k` of `C`, whenever it exists, has a
counterpart of rank `k` in `D` lying weakly to its left. The particles of `D` below the position
of that particle are closed downwards in the index order and number at least `k + 1`, so one of
them has rank `k` and lies below the threshold as well. -/
theorem Cloud.rankwiseDominates_of_encard_Iic_le [LinearOrder (RootIndexed.TreeNode Root α)]
    [Preorder X] {C D : Cloud Time Root α X} (t : Time)
    [Fintype (C.particles t)] [Fintype (D.particles t)]
    (hmono : ∀ p ∈ C.particles t, ∀ q ∈ C.particles t,
      p < q → C.position p.1 p.2 ≤ C.position q.1 q.2)
    (hDmono : ∀ p ∈ D.particles t, ∀ q ∈ D.particles t,
      p < q → D.position p.1 p.2 ≤ D.position q.1 q.2)
    (hcount : ∀ a, {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}.encard ≤
      {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}.encard) :
    C.RankwiseDominates D t := by
  classical
  intro k q hq hk
  have hcast : ∀ S : Set (RootIndexed.TreeNode Root α), S.Finite → S.encard = (((S.ncard : ℕ)) : ℕ∞) := by
    intro S hS
    rw [Set.ncard_eq_toFinset_card (s := S) (hs := hS),
      Set.Finite.encard_eq_coe_toFinset_card hS]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℕ∞) :=
    ⟨_, hk.symm.trans (Cloud.sliceRank_eq_coe_ncard_of_finite C t
      (Set.toFinite (C.particles t)) q)⟩
  subst hm
  set a : X := C.position q.1 q.2
  set TD : Finset (RootIndexed.TreeNode Root α) :=
    (D.particles t).toFinset.filter fun w => D.position w.1 w.2 ≤ a
  have hTD : (↑TD : Set (RootIndexed.TreeNode Root α)) =
      {w | w ∈ D.particles t ∧ D.position w.1 w.2 ≤ a} := by
    ext w
    simp [TD, Set.mem_toFinset]
  have hlow : ((m + 1 : ℕ) : ℕ∞) ≤
      ({p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a} : Set _).encard := by
    have hins : (insert q {p | p ∈ C.particles t ∧ p < q} : Set _) ⊆
        ({p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a} : Set _) := by
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨hq, le_rfl⟩
      · exact ⟨hp.1, hmono p hp.1 q hq hp.2⟩
    have hfin : ({p | p ∈ C.particles t ∧ p < q} : Set _).Finite :=
      (Set.toFinite (C.particles t)).subset fun p hp => hp.1
    have hb : (insert q {p | p ∈ C.particles t ∧ p < q} : Set _).ncard = m + 1 := by
      rw [Set.ncard_insert_of_notMem (fun h => lt_irrefl q h.2) hfin]
      congr 1
      have hsq := Cloud.sliceRank_eq_coe_ncard_of_finite C t (Set.toFinite (C.particles t)) q
      rw [hk] at hsq
      exact ENat.natCast_inj.mp hsq.symm
    calc ((m + 1 : ℕ) : ℕ∞)
        = (((insert q {p | p ∈ C.particles t ∧ p < q} : Set _).ncard : ℕ) : ℕ∞) := by rw [hb]
      _ = (insert q {p | p ∈ C.particles t ∧ p < q} : Set _).encard :=
          (hcast _ (hfin.insert q)).symm
      _ ≤ _ := Set.encard_le_encard hins
  have hchain : ({p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a} : Set _).encard ≤
      ((TD.card : ℕ) : ℕ∞) := by
    refine le_of_le_of_eq (hcount a) ?_
    rw [← hTD, Set.encard_coe_eq_coe_finsetCard]
  have hle : m + 1 ≤ TD.card :=
    Nat.cast_le.mp (le_trans hlow hchain)
  have hm_lt : m < TD.card := Nat.lt_of_succ_le hle
  obtain ⟨v, hv, hvk⟩ := Cloud.exists_sliceRank_eq_of_downClosed D t (T := TD)
    (fun w hw => by rw [hTD] at hw; exact hw.1)
    (fun u hu v hv huv => by
      obtain ⟨hvf, hvle⟩ := Finset.mem_filter.mp hv
      have hvD : v ∈ D.particles t := by
        rwa [Set.mem_toFinset] at hvf
      exact Finset.mem_filter.mpr
        ⟨by rwa [Set.mem_toFinset], le_trans (hDmono u hu v hvD huv) hvle⟩)
    hm_lt
  have hvD : v ∈ ({w | w ∈ D.particles t ∧ D.position w.1 w.2 ≤ a} : Set _) := by
    rw [← hTD]
    exact Finset.mem_coe.mpr hv
  exact ⟨v, hvD.1, hvk, hvD.2⟩

/-- The two forms of the slice order agree on a finite slice: the rankwise comparison of the
particles is the comparison of the threshold counts. The forward direction needs the ranks to
separate the particles of `C`, which finiteness provides, and the converse needs the particles
of `D` below each position to be finite, which finiteness provides as well. -/
theorem Cloud.rankwiseDominates_iff_encard_Iic_le [LinearOrder (RootIndexed.TreeNode Root α)]
    [Preorder X] {C D : Cloud Time Root α X} (t : Time)
    [Fintype (C.particles t)] [Fintype (D.particles t)]
    (hmono : ∀ p ∈ C.particles t, ∀ q ∈ C.particles t,
      p < q → C.position p.1 p.2 ≤ C.position q.1 q.2)
    (hDmono : ∀ p ∈ D.particles t, ∀ q ∈ D.particles t,
      p < q → D.position p.1 p.2 ≤ D.position q.1 q.2) :
    C.RankwiseDominates D t ↔ ∀ a,
      {p | p ∈ C.particles t ∧ C.position p.1 p.2 ≤ a}.encard ≤
        {q | q ∈ D.particles t ∧ D.position q.1 q.2 ≤ a}.encard :=
  ⟨fun h a => Cloud.rankwiseDominates_encard_le t
      (Cloud.sliceRank_injOn_of_finite C t) h a,
    fun h => Cloud.rankwiseDominates_of_encard_Iic_le t hmono hDmono h⟩

/-- The mirror of the rankwise form: the same statement read at the reversed order compares the
right tails instead of the left ones, which is the upper-tail form of Bérard–Gouéré. The
particles are the same and the ranks are read in the index order, so `Cloud.mapOrderDual`
reverses only the position comparison: "the particle of rank `k` of `C` has a counterpart at
most as far left in `D`" becomes "a counterpart at least as far left". -/
theorem Cloud.rankwiseDominates_mapOrderDual_iff [LT (RootIndexed.TreeNode Root α)] [Preorder X]
    (C D : Cloud Time Root α X) (t : Time) :
    (C.mapOrderDual).RankwiseDominates (D.mapOrderDual) t ↔
      ∀ k : ℕ∞, ∀ q, q ∈ C.particles t → C.sliceRank t q = k →
        ∃ q', q' ∈ D.particles t ∧ D.sliceRank t q' = k ∧
          C.position q.1 q.2 ≤ D.position q'.1 q'.2 := by
  simp only [Cloud.RankwiseDominates, Cloud.mapOrderDual]
  constructor
  · intro h k q hq hk
    obtain ⟨q', h1, h2, h3⟩ := h k q hq hk
    exact ⟨q', h1, h2, OrderDual.toDual_le_toDual.mp h3⟩
  · intro h k q hq hk
    obtain ⟨q', h1, h2, h3⟩ := h k q hq hk
    exact ⟨q', h1, h2, OrderDual.toDual_le_toDual.mpr h3⟩

/-- Counting the particles of a slice that satisfy a predicate does not depend on whether the
slice is read as a set of particles or as its own type: the two sets correspond under the
identity on the underlying particles. -/
theorem Cloud.encard_subtype_eq_encard {Time Root α X : Type*} {C : Cloud Time Root α X}
    (t : Time) (P : RootIndexed.TreeNode Root α → Prop) :
    ({p : (C.particles t : Set (RootIndexed.TreeNode Root α)) | P p.1} : Set _).encard =
      {p | p ∈ C.particles t ∧ P p}.encard :=
  Set.encard_congr
    { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      invFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }

/-- On a countable slice whose ranks separate its particles, the rankwise form implies the slice
order on the Dirac sums: the countable evaluation of the slice measure turns the threshold
counts into the values of the Dirac sums at the thresholds. -/
theorem Cloud.rankwiseDominates_diracSum_of_countable [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable (RootIndexed.TreeNode Root α)] [LT (RootIndexed.TreeNode Root α)]
    [Preorder X] {C D : Cloud Time Root α X} (t : Time)
    (hinj : Set.InjOn (C.sliceRank t) (C.particles t))
    (h : C.RankwiseDominates D t) :
    SliceDominatesMeasure (C.diracSum t) (D.diracSum t) := by
  intro a
  rw [Cloud.diracSum_Iic_eq_encard_of_countable C t a,
    Cloud.diracSum_Iic_eq_encard_of_countable D t a,
    Cloud.encard_subtype_eq_encard (C := C) t (fun w => C.position w.1 w.2 ≤ a),
    Cloud.encard_subtype_eq_encard (C := D) t (fun w => D.position w.1 w.2 ≤ a)]
  exact ENat.toENNReal_le.mpr (Cloud.rankwiseDominates_encard_le t hinj h a)

end Branching
