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

The rankwise form and the threshold count form agree when the index order enumerates
each slice increasingly by position without ties. Tied positions (`p < q` at equal
positions) are counted twice by the threshold count but separated by the rank, and a
slice whose index order does not follow its positions enumerates it in the wrong
order; in both cases the count clause is what the thesis adds on top of `xᵢ ≥ yᵢ`. -/
def Cloud.RankwiseDominates [LT (Root × TreeNode α)] [Preorder X]
    (C D : Cloud Time Root α X) (t : Time) : Prop :=
  ∀ k : ℕ∞, ∀ q, q ∈ C.particles t → C.sliceRank t q = k →
    ∃ q', q' ∈ D.particles t ∧ D.sliceRank t q' = k ∧
      D.position q'.1 q'.2 ≤ C.position q.1 q.2

end Branching

end Combinatorics
