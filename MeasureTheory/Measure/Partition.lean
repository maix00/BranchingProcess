/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Measure identities for disjoint partitions

The countable identity transfers a fixed measure factor from each cell to the
union. The finite-partition inequality derives a lower bound when each paired
event has mass at least `c`. These statements use measure additivity and do not
require independence or a probability measure.

## Public declarations

- `measure_iUnion_eq_mul_of_disjoint_factor`: for countable pairwise-disjoint
  families $(A_i)$ and $(B_i)$ with
  $\mu(B_i)=\mu(A_i)\,c$, one has
  $\mu(\bigcup_i B_i)=\mu(\bigcup_i A_i)\,c$.
- `measure_iUnion_inter_ge_mul_of_finite_partition`: for a finite pairwise
  disjoint family $(A_i)$ with
  $\mu(A_i\cap B_i)=\mu(A_i)\mu(B_i)$ and $\mu(B_i)\ge c$, one has
  $c\,\mu(\bigcup_i A_i)\le\mu(\bigcup_i(A_i\cap B_i))$.
-/

@[expose] public section

namespace MeasureTheory

theorem measure_iUnion_eq_mul_of_disjoint_factor
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (A B : ι → Set Ω) (c : ENNReal)
    (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ i, MeasurableSet (B i))
    (hAdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hBdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hfactor : ∀ i, P (B i) = P (A i) * c) :
    P (⋃ i, B i) = P (⋃ i, A i) * c := by
  calc
    P (⋃ i, B i) = ∑' i, P (B i) := measure_iUnion hBdisj hB
    _ = ∑' i, P (A i) * c := tsum_congr hfactor
    _ = (∑' i, P (A i)) * c := ENNReal.tsum_mul_right
    _ = P (⋃ i, A i) * c := by rw [measure_iUnion hAdisj hA]

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

end MeasureTheory
