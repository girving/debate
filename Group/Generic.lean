import Comp.Defs
import DComp.Defs

/-!
# Generic algorithms over groups

A generic algorithm over a group `G` is an algorithm which manipulates elements of `G` only via
an oracle for group operations. Some references:

1. Victor Shoup (1997), Lower bounds for discrete logarithms and related problems.
2. Minki Hhan (2024), A New Approach to Generic Lower Bounds, https://eprint.iacr.org/2024/268.

For some reason papers often describe the oracle as doing (1) multiplication, (2) inversion, and
(3) equality testing. However, equality testing isn't counted as a query, so (3) is silly to
include. Instead, we give the algorithm access to some other type `α` equivalent to `G`.
-/

open Set
noncomputable section

variable {G : Type} [Group G]
variable {α : Type}

/-- An oracle call either multiplies two elements, or inverts one -/
inductive Op (α : Type) where
| mul : α → α → Op α
| inv : α → Op α

/-- A generic group algorithm operates on a type `α`, treating it as a group via oracle calls -/
abbrev GComp (α β : Type) := Comp (fun _ => Op α) (fun _ ↦ α) u β

/-- A generic group algorithm operates on a type `α`, treating it as a group via oracle calls -/
abbrev GDComp (α β : Type) := DComp (fun _ => Op α) (fun _ ↦ α) u β
