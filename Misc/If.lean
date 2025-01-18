import Mathlib.Data.Real.Basic

/-!
# A few `if` utilities
-/

universe u
variable {α β : Type u}
variable {m : Type u → Type u} [Monad m]

/-- ↑x ≤ ↑y ↔ y → x -/
lemma ite_le_ite_iff (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    (@ite _ x dx (1:ℝ) 0) ≤ (@ite _ y dy 1 0) ↔ x → y := by
  by_cases h : x
  repeat { by_cases l : y; repeat { simp only [h, l, ite_true, ite_false]; norm_num }}

lemma ite_one_zero_congr (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    @ite _ x dx (1:ℝ) 0 = @ite _ y dy (1:ℝ) 0 ↔ (x ↔ y) := by
  by_cases h : x
  repeat { by_cases l : y; repeat simp [h, l] }

lemma ite_one_zero_ne_zero (x : Prop) {dx : Decidable x} : @ite _ x dx (1:ℝ) 0 ≠ 0 ↔ x := by
  by_cases h : x; repeat { simp only [h, if_true, if_false]; norm_num }

lemma ite_and_one_zero (x y : Prop) {d : Decidable (x ∧ y)} :
    @ite _ (x ∧ y) d (1:ℝ) 0 =
      (@ite _ x (Classical.dec _) (1:ℝ) 0) * (@ite _ y (Classical.dec _) 1 0) := by
  rw [ite_zero_mul_ite_zero, one_mul]
  congr

lemma ite_one_zero_nonneg {x : Prop} {d : Decidable x} : 0 ≤ @ite _ x d (1:ℝ) 0 := by
  split_ifs; repeat norm_num

/-- Change `bif` to `if` -/
lemma bif_eq_if {b : Bool} {x y : α} : (bif b then x else y) = if b then x else y := by
  induction b
  · simp only [cond_false, Bool.false_eq_true, ↓reduceIte]
  · simp only [cond_true, ↓reduceIte]

/-- Push a bind inside an `if` -/
lemma if_bind (c : Prop) (x y : m α) (z : α → m β) {h : Decidable c} :
    ite c (h := h) x y >>= z = ite c (h := h) (x >>= z) (y >>= z) := by
  by_cases p : c
  all_goals simp only [p, ↓reduceIte]

/-!
### Kronecker delta

This is nice notation, but it also makes lets us reason without worrying about particular
decidable instances.
-/

variable {α β : Type}
open Classical

/-- Kronecker delta function -/
noncomputable def delta (x y : α) : ℝ := if x = y then 1 else 0

-- Basic properties of `delta`
@[simp] lemma delta_self (x : α) : delta x x = 1 := by simp [delta]
@[simp] lemma delta_ne {x y : α} (ne : x ≠ y) : delta x y = 0 := by simp [delta, ne]
@[simp] lemma delta_ne' {x y : α} (ne : y ≠ x) : delta x y = 0 := by simp [delta, ne.symm]
lemma delta_comm (x y : α) : delta x y = delta y x := by simp [delta, eq_comm]

/-- Turn `if` into `delta` -/
lemma ite_eq_delta (x y : α) {d : Decidable (x = y)} : @ite _ (x = y) d 1 0 = delta x y := by
  simp only [delta]; split_ifs; all_goals rfl

/-- `delta` splits for pairs -/
@[simp] lemma delta_pair (x y : α) (z w : β) : delta (x, z) (y, w) = delta x y * delta z w := by
  simp only [delta, Prod.mk.inj_iff, ite_and_one_zero]
