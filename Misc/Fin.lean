import Mathlib.Data.Fin.Tuple.Basic

/-!
# `Fin` facts
-/

variable {n : ℕ}
variable {α : Type}

lemma Fin.snoc_eq_iff {x : Fin n → α} {y : α} {z : Fin (n + 1) → α} :
    Fin.snoc x y = z ↔ x = Fin.init z ∧ y = z (last n) := by
  simp [Fin.init_def, funext_iff, snoc, Fin.forall_iff_castSucc, and_comm]
