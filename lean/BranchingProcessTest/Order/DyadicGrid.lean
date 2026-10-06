import Topology.Order.DyadicUnitInterval

open UniformGrid

example (k : ℕ) :
    UniformGrid.IsRefinement
      (DyadicGrid.grid (-3 : ℚ) 5 (by norm_num) k)
      (DyadicGrid.grid (-3 : ℚ) 5 (by norm_num) (k + 1)) :=
  DyadicGrid.isRefinement_succ (-3 : ℚ) 5 (by norm_num) k

example : Dense DyadicGrid.unitPoints :=
  DyadicGrid.dense_unitPoints

#print axioms DyadicGrid.isRefinement_succ
#print axioms DyadicGrid.point_lift
#print axioms DyadicGrid.unitPoint_lift
#print axioms DyadicGrid.unitGrid_point
#print axioms DyadicGrid.dense_unitPoints
