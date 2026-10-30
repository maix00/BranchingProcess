/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.CoreReturn.Endpoint
public import Probability.Process.RandomWalk.Path.Block.Partition.CoreReturn.Geometry
public import Probability.Process.RandomWalk.Path.Block.Partition.CoreReturn.Probability

/-!
# Partitioned endpoint-core bounds

This entry point collects the endpoint-core path propagation, corridor
gluing, and IID product lower-bound interfaces for finite step-boundary
partitions.

## Public declarations

- `normalizedStepCadlagPathIcc_commonPartitionGrid_mem_core_of_blockEvents`:
  if every cell has the prescribed `InOpenPartialSumCoreReturn` event and
  the endpoint-core radii increase from the initial value zero, then every
  partition-knot value lies in its assigned core interval
  $[c_j-r_j,c_j+r_j]$.
- `normalizedStepCadlagPathIcc_mem_corridorSet_of_coreReturnBlockEvents`:
  under the endpoint-core and strict cell-interior hypotheses, the normalized
  step path belongs to the global strict corridor
  $\operatorname{corridorSet}(U,L)$.
- `iidSequenceLaw_partitionCellCoreReturnBlocks_ge_of_subset`:
  for consecutive IID blocks with local events $E_i$, if
  $\bigcap_i E_i\subseteq A$, then
  $\prod_i\mathbb P_\nu(E_i)\leq\mathbb P_\nu(A)$.
- `iidSequenceLaw_normalizedStepCorridor_ge_prod_partitionCellCoreReturnProbability`:
  the product of local endpoint-core probabilities is a lower bound for the
  probability that the normalized step path lies in the strict corridor.
- `eventually_iidSequenceLaw_normalizedStepCorridor_ge_prod_of_partitionCellCoreReturnBounds`:
  eventual lower bounds for the finitely many local probabilities yield the
  corresponding eventual product lower bound for the corridor probability.
-/
