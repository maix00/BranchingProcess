import Combinatorics.BranchingWalk.Cloud.SliceMeasure

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

end Branching

end Combinatorics
