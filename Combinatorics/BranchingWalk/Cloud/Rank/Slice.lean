import Combinatorics.BranchingWalk.Cloud.Rank.Basic

/-!
# Rank of a particle in one time slice

A particle of the cloud is an initial root together with an address, so a rank
counts particles below a fixed particle of `Root × TreeNode α`. The order on
that type is not yet fixed by the cloud (the walk's selection compares
positions), so it is an explicit hypothesis here. -/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- Cardinal rank of a particle in a complete time slice: the number of
particles of the slice that lie strictly below it. -/
noncomputable def Cloud.sliceRank [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) (q : Root × TreeNode α) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ p < q}.encard

@[simp] theorem Cloud.sliceRank_def [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) (q : Root × TreeNode α) :
    C.sliceRank t q = {p | p ∈ C.particles t ∧ p < q}.encard := rfl

/-- The rank respects the index order: a particle of a slice that lies below another
particle of the same slice has the smaller rank. Particles at the same position are
still separated by their index, hence by their rank. -/
theorem Cloud.sliceRank_mono [Preorder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) {p q : Root × TreeNode α} (hpq : p < q) :
    C.sliceRank t p ≤ C.sliceRank t q :=
  Set.encard_le_encard fun _ hr => ⟨hr.1, lt_trans hr.2 hpq⟩


/-- On a finite slice of a linearly ordered cloud the rank separates the particles: two
particles of the slice with the same rank are the same particle, so the ranks enumerate the
slice and several particles at one position stay distinct. -/
theorem Cloud.sliceRank_injOn_of_finite [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] :
    Set.InjOn (C.sliceRank t) (C.particles t) := by
  have hfinC : (C.particles t).Finite := Set.toFinite (C.particles t)
  intro p hp q hq hpq
  by_contra hne
  have hcast : ∀ r : Root × TreeNode α,
      ({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).encard =
        (({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).ncard : ℕ∞) := by
    intro r
    have hf : ({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    rw [Set.ncard_eq_toFinset_card _ hf, Set.Finite.encard_eq_coe_toFinset_card hf]
  simp only [Cloud.sliceRank_def] at hpq
  have he : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)).ncard =
      ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)).ncard := by
    have h := hpq
    rw [hcast p, hcast q] at h
    exact ENat.natCast_inj.mp h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hss : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)) ⊂
        {s | s ∈ C.particles t ∧ s < q} := by
      refine ⟨fun s hs => ⟨hs.1, lt_trans hs.2 hlt⟩, fun hsub => ?_⟩
      exact absurd (hsub ⟨hp, hlt⟩).2 (lt_irrefl p)
    have hfq : ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    exact (ne_of_lt (Set.ncard_lt_ncard hss hfq)) he
  · have hss : ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)) ⊂
        {s | s ∈ C.particles t ∧ s < p} := by
      refine ⟨fun s hs => ⟨hs.1, lt_trans hs.2 hgt⟩, fun hsub => ?_⟩
      exact absurd (hsub ⟨hq, hgt⟩).2 (lt_irrefl q)
    have hfp : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    exact (ne_of_lt (Set.ncard_lt_ncard hss hfp)) he.symm

theorem Cloud.sliceRank_eq_finsetRank [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    (s : Finset (Root × TreeNode α))
    (hs : C.particles t = (s : Set (Root × TreeNode α)))
    (q : Root × TreeNode α) :
    C.sliceRank t q = (finsetRank s q : ℕ∞) := by
  rw [Cloud.sliceRank, hs]
  rw [Set.encard_eq_coe_toFinset_card]
  simp [finsetRank]

/-- The rank of a particle is at most the number of particles of the slice lying weakly
below it in position. This is the first half of the link between the rankwise order and the
threshold counts: with positions increasing along the index order, everything strictly below
a particle in the index order is below it in position as well. -/
theorem Cloud.sliceRank_le_encard_position_of_mono [Preorder X]
    [Preorder (Root × TreeNode α)] (C : Cloud Time Root α X) (t : Time)
    (hmono : ∀ p, p ∈ C.particles t → ∀ q, q ∈ C.particles t →
      p < q → C.position p.1 p.2 ≤ C.position q.1 q.2)
    {p : Root × TreeNode α} (hp : p ∈ C.particles t) :
    C.sliceRank t p ≤
      {q | q ∈ C.particles t ∧ C.position q.1 q.2 ≤ C.position p.1 p.2}.encard :=
  Set.encard_le_encard fun _ hq => ⟨hq.1, hmono _ hq.1 _ hp hq.2⟩

set_option linter.style.haveILetI false in
/-- A particle below another particle of a slice has the strictly smaller rank, provided the
particles below the upper one are finite: those below the lower particle are a subset of those
below the upper one and miss the lower particle itself, so the two ranks differ. Two particles
of a slice hence have different ranks as soon as the ranks are finite, which is what makes the
ranks an enumeration of the slice. -/
theorem Cloud.sliceRank_lt_sliceRank_of_lt [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) {p q : Root × TreeNode α}
    (hp : p ∈ C.particles t) (hpq : p < q)
    (hfin : ({r | r ∈ C.particles t ∧ r < q} : Set _).Finite) :
    C.sliceRank t p < C.sliceRank t q := by
  set sp : Set (Root × TreeNode α) := {r | r ∈ C.particles t ∧ r < p}
  set sq : Set (Root × TreeNode α) := {r | r ∈ C.particles t ∧ r < q}
  have hsub : sp ⊆ sq := fun r hr => ⟨hr.1, lt_trans hr.2 hpq⟩
  have hfinsp : sp.Finite := hfin.subset hsub
  haveI hsp : Fintype ↑sp := hfinsp.fintype
  haveI hsq : Fintype ↑sq := hfin.fintype
  have hmem : p ∈ sq := ⟨hp, hpq⟩
  have hnotmem : p ∉ sp := fun h => lt_irrefl p h.2
  have hcard : sp.ncard + 1 ≤ sq.ncard := by
    calc sp.ncard + 1 = (insert p sp).ncard := (Set.ncard_insert_of_notMem hnotmem).symm
      _ ≤ sq.ncard := Set.ncard_le_ncard (fun r hr => by
          rcases hr with h | h
          · exact h.symm ▸ hmem
          · exact hsub h) hfin
  have h1 : C.sliceRank t p = (sp.ncard : ℕ∞) := by
    rw [Cloud.sliceRank, show {r | r ∈ C.particles t ∧ r < p} = sp from rfl,
      Set.Finite.encard_eq_coe_toFinset_card hfinsp,
      Set.ncard_eq_toFinset_card (s := sp) (hs := hfinsp)]
  have h2 : C.sliceRank t q = (sq.ncard : ℕ∞) := by
    rw [Cloud.sliceRank, show {r | r ∈ C.particles t ∧ r < q} = sq from rfl,
      Set.Finite.encard_eq_coe_toFinset_card hfin,
      Set.ncard_eq_toFinset_card (s := sq) (hs := hfin)]
  rw [h1, h2]
  exact_mod_cast Nat.lt_of_succ_le hcard

/-- On a finite slice the rank of a particle is the number of particles of the slice below
it, as a finite natural number. -/
theorem Cloud.sliceRank_eq_coe_ncard_of_finite [Preorder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) (hfin : (C.particles t).Finite)
    (q : Root × TreeNode α) :
    C.sliceRank t q = ↑({p | p ∈ C.particles t ∧ p < q}.ncard) := by
  rw [Cloud.sliceRank]
  show {p | p ∈ C.particles t ∧ p < q}.encard = ↑({p | p ∈ C.particles t ∧ p < q}.ncard)
  rw [Set.Finite.encard_eq_coe_toFinset_card (hfin.subset fun p hp => hp.1),
    Set.ncard_eq_toFinset_card (hs := hfin.subset fun p hp => hp.1)]

/-- If a finite set of particles of a slice is closed downwards in the index order, then its
largest element has rank one less than the size of the set: everything of the slice below that
largest element is in the set, and it is everything of the set but the largest element. -/
theorem Cloud.sliceRank_max'_of_downClosed [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    {T : Finset (Root × TreeNode α)} (hT : ↑T ⊆ C.particles t) (hne : T.Nonempty)
    (hdown : ∀ u ∈ C.particles t, ∀ v ∈ T, u < v → u ∈ T) :
    C.sliceRank t (T.max' hne) = ((T.card - 1 : ℕ) : ℕ∞) := by
  have hmemT : T.max' hne ∈ T := Finset.max'_mem T hne
  have hset : {u | u ∈ C.particles t ∧ u < T.max' hne} = ↑(T.erase (T.max' hne)) := by
    ext u
    constructor
    · intro hu
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨ne_of_lt hu.2, hdown u hu.1 _ hmemT hu.2⟩)
    · intro hu
      obtain ⟨hne', hmem⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hu)
      exact ⟨hT hmem, lt_of_le_of_ne (Finset.le_max' T u hmem) hne'⟩
  rw [Cloud.sliceRank, hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_erase_of_mem hmemT]

/-- In a finite set of particles of a slice that is closed downwards in the index order, every
number below the size of the set is the rank of one of its elements: the rank of an element is
the number of its elements below it, those ranks are distinct, and each of them is smaller than
the size, so the ranks fill the whole interval below the size. -/
theorem Cloud.exists_sliceRank_eq_of_downClosed [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    {T : Finset (Root × TreeNode α)} (hT : ↑T ⊆ C.particles t)
    (hdown : ∀ u ∈ C.particles t, ∀ v ∈ T, u < v → u ∈ T)
    {k : ℕ} (hk : k < T.card) :
    ∃ v ∈ T, C.sliceRank t v = (k : ℕ∞) := by
  classical
  have hrank : ∀ v ∈ T, C.sliceRank t v = ((T.filter fun w => w < v).card : ℕ∞) := by
    intro v hv
    have hset : {u | u ∈ C.particles t ∧ u < v} = ↑(T.filter fun w => w < v) := by
      ext u
      constructor
      · intro hu
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hdown u hu.1 v hv hu.2, hu.2⟩)
      · intro hu
        obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu)
        exact ⟨hT hmem, hlt⟩
    rw [Cloud.sliceRank, hset, Set.encard_coe_eq_coe_finsetCard]
  have hinj : Set.InjOn (fun v => (T.filter fun w => w < v).card) ↑T := by
    intro u hu v hv huv
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hss : T.filter (fun w => w < u) ⊂ T.filter (fun w => w < v) := by
        refine ⟨fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.trans hlt⟩, fun hsub => ?_⟩
        exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hu, hlt⟩))).2 (lt_irrefl u)
      exact (ne_of_lt (Finset.card_lt_card hss)) huv
    · have hss : T.filter (fun w => w < v) ⊂ T.filter (fun w => w < u) := by
        refine ⟨fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.trans hlt⟩, fun hsub => ?_⟩
        exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hv, hlt⟩))).2 (lt_irrefl v)
      exact (ne_of_lt (Finset.card_lt_card hss)) huv.symm
  have hbdd : ∀ v ∈ T, (T.filter fun w => w < v).card < T.card := fun v hv =>
    Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub =>
      absurd (Finset.mem_filter.mp (hsub hv)).2 (lt_irrefl v)⟩
  have hsub : T.image (fun v => (T.filter fun w => w < v).card) ⊆ Finset.range T.card := by
    intro j hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hbdd v hv)
  have heq : T.image (fun v => (T.filter fun w => w < v).card) = Finset.range T.card :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range])
  obtain ⟨v, hv, hvk⟩ := Finset.mem_image.mp (by
    rw [heq]; exact Finset.mem_range.mpr hk)
  exact ⟨v, hv, by rw [hrank v hv, hvk]⟩

end Combinatorics.Branching
