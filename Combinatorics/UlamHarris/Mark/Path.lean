/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic
public import Mathlib.Data.List.OfFn

/-!
# Complete ancestral records in an address field

## Public declarations

* `Combinatorics.UlamHarris.Mark.pathRecords field z` reads
  `(field(z|j), zⱼ)` for `j < n` along a finite address `z : Fin n → ι`.
  It retains both the mark of the parent and the chosen child label.

The field is the existing `Mark ι E = List ι → E`, rather than a new
marked-tree object. There is no survival, probability, ordering, or spatial
assumption. When a field mark is a complete offspring family, this reads
the reproductive families with their selected children, without discarding
siblings or replacing them by independent observations.
-/

@[expose] public section
namespace Combinatorics.UlamHarris.Mark

/-- The parent mark and chosen child at each strict ancestor of a finite address. -/
def pathRecords {ι E : Type*} {n : ℕ} (field : Mark ι E) (z : Fin n → ι) :
    Fin n → E × ι :=
  fun j => (field ((List.ofFn z).take j), z j)

end Combinatorics.UlamHarris.Mark
