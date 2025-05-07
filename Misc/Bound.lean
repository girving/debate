import Mathlib.Tactic.Bound
import Mathlib.Data.Real.Sqrt

/-!
# Extra `bound` lemmas

These should be upstreamed to Mathlib.
-/

@[bound] private alias ⟨_, Bound.nat_cast_le⟩ := Nat.cast_le
attribute [bound] Real.sqrt_pos_of_pos
