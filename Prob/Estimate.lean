import Prob.Arith

/-!
# Estimate the probability of a `Prob Bool` by sampling
-/

open Classical
open Prob
open Set
open scoped Real
noncomputable section

-- We allow an arbitrary monad to support both `Prob` and `Comp s`
universe u
variable {m : Type → Type u} [Monad m]

/-- `count f n` is the distribution of the number of `true` of `f` after `n` samples. -/
def count (f : m Bool) : ℕ → m ℕ
| 0 => pure 0
| n+1 => do
  let x := bif ← f then 1 else 0
  let y ← count f n
  return x + y

-- Facts about count
@[simp] lemma count_zero (f : m Bool) : count f 0 = pure 0 := by simp only [count]
lemma count_le (f : Prob Bool) {n k : ℕ} : n < k → (count f n).prob k = 0 := by
  induction' n with n lo generalizing k
  · intro h; simp only [count, prob_pure, Nat.le_zero] at h ⊢
    by_cases k0 : k = 0
    · simp only [k0, lt_self_iff_false] at h
    · simp only [k0, ↓reduceIte, one_ne_zero]
  · intro h; simp only [count, prob_bind, prob_pure] at h ⊢
    refine exp_eq_zero fun x _ ↦ exp_eq_zero fun l m ↦ ?_
    generalize hy : (bif x then 1 else 0) = y
    have y1 : y ≤ 1 := by rw [← hy]; induction x; all_goals simp
    have ln : l ≤ n := by contrapose m; simp only [not_not, not_le] at m ⊢; exact lo m
    have kl : k ≠ y + l := by omega
    simp only [kl, ↓reduceIte]
lemma count_le' (f : Prob Bool) {n k : ℕ} : (count f n).prob k ≠ 0 → k ≤ n := by
  intro h; contrapose h; simp only [not_le, not_not] at h ⊢; exact count_le _ h

/-- Estimate a probability via sample mean -/
def estimate (f : m Bool) (n : ℕ) : m ℝ := (fun x : ℕ ↦ (x : ℝ) / n) <$> count f n

/-- count.mean = n * f.prob true -/
lemma mean_count (f : Prob Bool) (n : ℕ) : (count f n).exp (fun x ↦ ↑x) = n * f.prob true := by
  induction' n with k h
  · simp only [count, mean, pure_bind, exp_pure, id, Nat.cast_zero, zero_mul]
  · simp only [count, exp_bind, exp_pure, Nat.cast_add, exp_add, exp_const, h, exp_bool,
      cond_false, CharP.cast_eq_zero, smul_eq_mul, mul_zero, cond_true, Nat.cast_succ, zero_add,
      mul_one]
    ring

/-- count of the negative of f -/
lemma count_not (f : Prob Bool) (n : ℕ) :
    (count (not <$> f) n) = (fun x ↦ n - x) <$> count f n := by
  induction' n with k h
  · simp only [Nat.zero_eq, ge_iff_le, zero_le, tsub_eq_zero_of_le, Prob.map_const, count_zero]
  · simp only [count, h, seq_bind_eq, Function.comp, map_bind, map_pure]
    apply Prob.bind_congr; intro x _; apply Prob.bind_congr; intro n m; induction x
    · simp only [Bool.not_false, cond_true, cond_false, zero_add]
      by_cases nk : n ≤ k
      · simp only [Function.comp_apply, ← Nat.add_sub_assoc nk, Nat.add_comm 1 k]
      · contrapose m; clear m; simp only [not_le, not_not] at nk ⊢; exact count_le f nk
    · simp only [Bool.not_true, cond_false, zero_add, Function.comp_apply, cond_true, add_comm 1 n,
        Nat.succ_sub_succ_eq_sub]

/-- estimate.mean = f.prob true -/
lemma mean_estimate (f : Prob Bool) {n : ℕ} (n0 : n ≠ 0) : (estimate f n).mean = f.prob true := by
  simp only [mean, estimate, exp_map, CompTriple.comp_eq, exp_div, mean_count]
  field_simp [n0]
