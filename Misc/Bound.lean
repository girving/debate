import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Bound

/-!
# Extra `bound` lemmas

These should be upstreamed to Mathlib.
-/

variable {α ι : Type}

@[bound] private alias ⟨_, Bound.nat_cast_le⟩ := Nat.cast_le
attribute [bound] Real.sqrt_pos_of_pos
attribute [bound] Finset.sum_nonneg Finset.prod_nonneg
attribute [bound] Fintype.card_pos
@[bound] private alias ⟨_, Bound.finsupp_single_nonneg_of_nonneg⟩ := Finsupp.single_nonneg
@[bound] private alias ⟨_, Bound.nat_ceil_pos_of_pos⟩ := Nat.ceil_pos

@[bound] lemma Finsupp.single_apply_nonneg {i j : ι} {x : α} [Zero α] [Preorder α] (x0 : 0 ≤ x) :
    0 ≤ Finsupp.single i x j := by
  rw [@Finsupp.single_apply _ _ _ _ _ _ (Classical.dec _)]
  bound

@[bound] lemma exp_le_quadratic {x : ℝ} (x1 : x ≤ 1) : x.exp ≤ 1 + x + x ^ 2 := by
  by_cases n : -1 ≤ x
  · replace x1 : |x| ≤ 1 := by simp [abs_le, x1, n]
    linarith [(abs_le.mp (Real.abs_exp_sub_one_sub_id_le x1)).2]
  · trans 1
    · simp; linarith
    · nlinarith

@[bound] lemma log_one_add_le_self {x : ℝ} (x1 : -1 < x) : (1 + x).log ≤ x :=
  le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by simp)
