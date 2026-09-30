module

public import Mathlib.Probability.Independence.Basic

/-!
# Independent events over a finite partition

If each cell of a finite measurable partition is paired with an independent
future event of probability at least `c`, the union of the paired events has
probability at least `c` times the mass of the partition. The future event may
depend on the cell. This is the finite endpoint-binning step used in block
lower estimates.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem measure_iUnion_inter_ge_mul_of_finite_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (A B : ι → Set Ω) (c : ENNReal)
    (hA : ∀ i, NullMeasurableSet (A i) P)
    (hB : ∀ i, NullMeasurableSet (B i) P)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfactor : ∀ i, P (A i ∩ B i) = P (A i) * P (B i))
    (hlower : ∀ i, c ≤ P (B i)) :
    c * P (⋃ i, A i) ≤ P (⋃ i, A i ∩ B i) := by
  have hdisj' : Pairwise (fun i j => Disjoint (A i ∩ B i) (A j ∩ B j)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas' : ∀ i, NullMeasurableSet (A i ∩ B i) P :=
    fun i => (hA i).inter (hB i)
  have hdisj₀ : Pairwise (fun i j => AEDisjoint P (A i) (A j)) :=
    hdisj.mono fun _ _ hij => hij.aedisjoint
  have hdisj'₀ : Pairwise (fun i j => AEDisjoint P (A i ∩ B i) (A j ∩ B j)) :=
    hdisj'.mono fun _ _ hij => hij.aedisjoint
  rw [measure_iUnion₀ hdisj₀ hA, measure_iUnion₀ hdisj'₀ hmeas']
  simp_rw [hfactor]
  calc
    c * (∑' i, P (A i)) = ∑' i, P (A i) * c := by
      rw [mul_comm, ENNReal.tsum_mul_right]
    _ ≤ ∑' i, P (A i) * P (B i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      simpa only [mul_comm] using mul_le_mul_left (hlower i) (P (A i))

end ProbabilityTheory
