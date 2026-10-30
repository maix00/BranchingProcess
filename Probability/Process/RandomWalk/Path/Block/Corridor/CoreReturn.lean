/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
import all Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Representation.Cadlag

/-!
# Finite-block corridor core returns

For a finite increment block \(z\), let \(S_k(z)=\sum_{j<k}z_j\). Given a
corridor \((a,b)\), an incoming core \([c_0-r_0,c_0+r_0]\), and an outgoing
core \([c_1-r_1,c_1+r_1]\), the event below contracts the corridor by the
incoming radius and requires the final displacement to land in the open band
of radius \((r_1-r_0)/2\) about \(c_1-c_0\). It is defined for arbitrary real
increments and has no moment, scaling, or distribution assumptions.

This finite-block event is used in the finite-partition lower argument of
A. A. Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081. The same block event also supplies endpoint bridges in
finite-variance entrance estimates.

## Public declarations

- `InOpenPartialSumCoreReturn a b c₀ r₀ c₁ r₁ z` means
  \[
    a+r_0-c_0 < S_k(z) < b-r_0-c_0\quad(0\le k\le \ell),
    \qquad
    c_1-c_0-\frac{r_1-r_0}{2}<S_\ell(z)<c_1-c_0+\frac{r_1-r_0}{2}.
  \]
- `measurableSet_inOpenPartialSumCoreReturn` proves measurability in the
  finite product sigma algebra.
- `inOpenPartialSumCoreReturn_positions_mem` places every translated partial
  sum in \((a,b)\) when the initial value lies in the incoming core.
- `inOpenPartialSumCoreReturn_endpoint_mem` places the translated terminal
  value in the outgoing core when \(r_0<r_1\).
- `inOpenPartialSumCoreReturn_of_staysIn_endsIn` converts a scaled corridor
  path with an endpoint bridge into the finite-block event.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The local event for one finite-partition cell. Relative partial sums stay
inside the corridor contracted by the incoming core; the endpoint band
connects the incoming core center to the outgoing core center. The band
radius is half the increase in core radius, matching the source lower
construction and leaving strict room inside the outgoing core. -/
def InOpenPartialSumCoreReturn {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ)
    (block : Fin length → ℝ) : Prop :=
  InOpenPartialSumCorridorEndsIn
    (innerLower + startRadius - startCenter)
    (innerUpper - startRadius - startCenter)
    (endCenter - startCenter - (endRadius - startRadius) / 2)
    (endCenter - startCenter + (endRadius - startRadius) / 2)
    block

/-- A finite endpoint-core cell event is measurable in the product sigma
algebra on its IID increment coordinates. -/
theorem measurableSet_inOpenPartialSumCoreReturn {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ) :
    MeasurableSet {block : Fin length → ℝ |
      InOpenPartialSumCoreReturn innerLower innerUpper startCenter
        startRadius endCenter endRadius block} := by
  exact measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _

/-- If the starting position is in the incoming core, every partial-sum
position of a core-return block lies in the prescribed inner cell corridor. -/
theorem inOpenPartialSumCoreReturn_positions_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : InOpenPartialSumCoreReturn innerLower innerUpper startCenter
      startRadius endCenter endRadius block) :
    ∀ k : Fin (length + 1),
      innerLower < x + Fin.partialSum block k ∧
        x + Fin.partialSum block k < innerUpper := by
  intro k
  have hsum := hevent.1 k
  change innerLower + startRadius - startCenter < Fin.partialSum block k ∧
      Fin.partialSum block k < innerUpper - startRadius - startCenter at hsum
  constructor <;> nlinarith [hstart.1, hstart.2]

/-- The open endpoint band in a core-return block lands strictly inside the
outgoing core, uniformly over every starting point in the incoming core. -/
theorem inOpenPartialSumCoreReturn_endpoint_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hradius : startRadius < endRadius)
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : InOpenPartialSumCoreReturn innerLower innerUpper
      startCenter startRadius endCenter endRadius block) :
    x + Fin.partialSum block (Fin.last length) ∈
      Set.Ioo (endCenter - endRadius) (endCenter + endRadius) := by
  have hend := hevent.2
  change Fin.partialSum block (Fin.last length) ∈
    Set.Ioo (endCenter - startCenter - (endRadius - startRadius) / 2)
      (endCenter - startCenter + (endRadius - startRadius) / 2) at hend
  rcases hend with ⟨hendLower, hendUpper⟩
  rcases hstart with ⟨hstartLower, hstartUpper⟩
  constructor <;> nlinarith [hradius]

/-- A killed walk started at the core center, with a strict spatial margin,
produces the robust block event used to pass from one endpoint core to the
next. The terminal window is allowed to be strictly smaller than the core
radius increment. -/
theorem inOpenPartialSumCoreReturn_of_staysIn_endsIn
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter
      endRadius margin bridgeRadius scale : ℝ} {increment : ℕ → ℝ}
    (hscale : 0 < scale) (hmargin : 0 < margin)
    (hzeroLower : innerLower + startRadius - startCenter < 0)
    (hzeroUpper : 0 < innerUpper - startRadius - startCenter)
    (hbridgeRadius : bridgeRadius < (endRadius - startRadius) / 2)
    (hpath : StaysIn
      (Set.Icc (scale * (innerLower + startRadius + margin))
        (scale * (innerUpper - startRadius - margin)))
      length (scale * startCenter) increment)
    (hend : scale * startCenter + AdditivePath.displacement length increment ∈
      Set.Icc (scale * (endCenter - bridgeRadius))
        (scale * (endCenter + bridgeRadius))) :
    InOpenPartialSumCoreReturn
      (scale * innerLower) (scale * innerUpper)
      (scale * startCenter) (scale * startRadius)
      (scale * endCenter) (scale * endRadius)
      (Combinatorics.Sequence.blockCoordinates 0 length increment) := by
  let block := Combinatorics.Sequence.blockCoordinates 0 length increment
  have hsum (k : Fin (length + 1)) :
      Fin.partialSum block k = AdditivePath.displacement (k : ℕ) increment := by
    rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
  change InOpenPartialSumCorridor
      (scale * innerLower + scale * startRadius - scale * startCenter)
      (scale * innerUpper - scale * startRadius - scale * startCenter) block ∧
    Fin.partialSum block (Fin.last length) ∈
      Set.Ioo
        (scale * endCenter - scale * startCenter -
          (scale * endRadius - scale * startRadius) / 2)
        (scale * endCenter - scale * startCenter +
          (scale * endRadius - scale * startRadius) / 2)
  constructor
  · intro k
    refine Fin.cases ?_ ?_ k
    · change
        (scale * innerLower + scale * startRadius - scale * startCenter <
          AdditivePath.displacement 0 increment) ∧
        (AdditivePath.displacement 0 increment <
          scale * innerUpper - scale * startRadius - scale * startCenter)
      rw [AdditivePath.displacement_zero]
      constructor
      · have hpos := mul_pos hscale (neg_pos.mpr hzeroLower)
        nlinarith
      · have hpos := mul_pos hscale hzeroUpper
        nlinarith
    · intro j
      have hstay := hpath j
      have hsumSucc : Fin.partialSum block j.succ =
          AdditivePath.displacement ((j : ℕ) + 1) increment := by
        simpa [Fin.val_succ] using hsum j.succ
      rcases hstay with ⟨hlo, hhi⟩
      constructor
      · rw [hsumSucc]
        have hmargin' := mul_pos hscale hmargin
        nlinarith
      · rw [hsumSucc]
        have hmargin' := mul_pos hscale hmargin
        nlinarith
  · have hsumLast : Fin.partialSum block (Fin.last length) =
        AdditivePath.displacement length increment := by
      simpa using hsum (Fin.last length)
    rw [hsumLast]
    rcases hend with ⟨hlo, hhi⟩
    constructor
    · have hgap := mul_pos hscale
        (sub_pos.mpr (by linarith : (endRadius - startRadius) / 2 - bridgeRadius > 0))
      nlinarith
    · have hgap := mul_pos hscale
        (sub_pos.mpr (by linarith : (endRadius - startRadius) / 2 - bridgeRadius > 0))
      nlinarith


end ProbabilityTheory.RandomWalk

end
