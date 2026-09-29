import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The unit interval

`UnitInterval` is the compact time interval `[0, 1]` of the real line, the time domain of the paths of
`D(0, 1)` used for the Skorokhod `J₁` topology and for the stable Lévy process. It is a plain set of reals,
carrying no topology of its own and belonging to no particular path space.

It is the real case of the interval of an ordered type: for general `a b : α` that interval is Mathlib's
`Set.Icc a b`, and naming `Set.Icc (0 : ℝ) 1` as `UnitInterval` follows Mathlib's
`Mathlib/Topology/Instances/UnitInterval.lean`.
-/

/-- The compact unit time interval `[0, 1]` of the real line. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1
