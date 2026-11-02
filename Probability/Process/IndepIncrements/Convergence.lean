/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.ConvergenceInDistribution.Independence
public import Topology.Algebra.BigOperators.PartialSum

/-!
# Finite-dimensional convergence from independent increments

## Public declarations

- `ProbabilityTheory.HasIndepIncrements.tendstoInDistribution_positions_of_increment_convergence`:
  if each consecutive increment of a sequence of zero-start processes
  converges in distribution and each process has independent increments, then
  the position vector on the same finite grid converges to the partial sums of
  independent increments with the limiting marginal laws. For a finite grid
  $t_0\le t_1\le\cdots\le t_n$ with $X^{(m)}_{t_0}=0$ almost surely, the
  conclusion has the form
  \[
    (X^{(m)}_{t_j})_{j=0}^n\;\Rightarrow\;
    \left(\sum_{k<j} Z_k\right)_{j=0}^n,
  \]
  where the $Z_k$ are independent and each has the limiting law of
  $X^{(m)}_{t_{k+1}}-X^{(m)}_{t_k}$.

This is the process-level finite-grid assembly step. A source-specific scalar
limit theorem supplies the convergence of the individual increments.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- Finite-dimensional position laws converge when the successive increment
laws converge and the source processes have independent increments. The
limiting position vector is formed by partial sums of independent coordinates
with the prescribed limiting increment laws. -/
theorem HasIndepIncrements.tendstoInDistribution_positions_of_increment_convergence
    {ι Time : Type*} [Preorder Time]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {X : (i : ι) → Time → Ω i → ℝ} {l : Filter ι}
    {n : ℕ} {limitIncrementLaw : Fin n → Measure ℝ}
    [∀ j, IsProbabilityMeasure (limitIncrementLaw j)]
    (grid : Fin (n + 1) → Time)
    (hgrid : Monotone grid)
    (hstart : ∀ i, ∀ᵐ ω ∂P i, X i (grid 0) ω = 0)
    (hindep : ∀ i, HasIndepIncrements (X i) (P i))
    (hinc : ∀ j : Fin n,
      TendstoInDistribution
        (fun i ω => X i (grid j.succ) ω - X i (grid j.castSucc) ω)
        l id P (limitIncrementLaw j)) :
    TendstoInDistribution
      (fun i ω j => X i (grid j) ω) l
      (fun z j => Fin.partialSum z j) P (Measure.pi limitIncrementLaw) := by
  let increment : (i : ι) → Fin n → Ω i → ℝ := fun i j ω =>
    X i (grid j.succ) ω - X i (grid j.castSucc) ω
  have hindependent (i : ι) : iIndepFun (increment i) (P i) := by
    simpa [increment] using hindep i n grid hgrid
  have hincrements : TendstoInDistribution
      (fun i ω j => increment i j ω) l id P (Measure.pi limitIncrementLaw) := by
    exact TendstoInDistribution.pi_of_iIndepFun hinc
      (fun _ => measurable_id) hindependent
  let partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ := Fin.partialSum
  have hsum := hincrements.continuous_comp (Fin.continuous_partialSum n)
  have hpositions (i : ι) :
      (partialSum ∘ (fun ω j => increment i j ω)) =ᵐ[P i]
        fun ω j => X i (grid j) ω := by
    filter_upwards [hstart i] with ω hω
    funext j
    have htel := Fin.partialSum_differences
      (fun k : Fin (n + 1) => X i (grid k) ω) j
    simpa [partialSum, increment, hω] using htel
  have hpositionsMeasurable (i : ι) :
      AEMeasurable (fun ω j => X i (grid j) ω) (P i) :=
    (hsum.forall_aemeasurable i).congr (hpositions i)
  exact hsum.congr_eventually
    (Filter.Eventually.of_forall hpositions) hpositionsMeasurable

end ProbabilityTheory

end
