import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Misc.Bound

/-!
# Online gradient descent

We formalise the online gradient descent algorithm as described in

* Elad Hazan, "Introduction to Online Convex Optimization", https://arxiv.org/abs/1909.05207

Online gradient descent works even the losses are chosen adversarially after our hero moves.
-/

open Real (sqrt)
open Set
noncomputable section
namespace OGD

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {d g : ℝ} {s : Set V} {proj : V → V} {η : ℕ → ℝ} {n : ℕ} {x y : V}

/-- A subgradient of a convex function represents a tangent plane below the function. -/
def Subgrad (f : V → ℝ) (x : V) (g : V) : Prop :=
  ∀ y, inner ℝ g (y - x) ≤ f y - f x

/-- A projection to a set picks out a closest point in the set. -/
structure Proj (proj : V → V) (s : Set V) : Prop where
  mem : ∀ x, proj x ∈ s
  dist_le : ∀ x {y}, y ∈ s → dist (proj x) y ≤ dist x y

/-- At each point in online gradient descent, our adversary picks a loss and a subgradient -/
structure Move (g : ℝ) (s : Set V) (x : V) where
  loss : V → ℝ
  grad : V
  sub : Subgrad loss x grad
  norm : ‖grad‖ ≤ g

attribute [bound_forward] Move.norm

/-- One gradient descent step -/
def step (proj : V → V) (η : ℝ) (x : V) (m : Move g s x) : V :=
  proj (x - η • m.grad)

/-- An adversary observes the current time and time, and chooses a loss -/
def Adversary (g : ℝ) (s : Set V) :=
  ℕ → (x : V) → Move g s x

variable {eve : Adversary g s}

/-- Online gradient descent (algorithm 8 in section 3.1) -/
def ogd (proj : V → V) (η : ℕ → ℝ) (eve : Adversary g s) (x : V) (xs : x ∈ s) : ℕ → V
  | 0 => x
  | n + 1 =>
    let x := ogd proj η eve x xs n
    step proj (η n) x (eve n x)

/-- Regret relative to a fixed loss `y`. We don't use the optimal loss, as plugging in a particular
loss and proving quantified theorems lets us avoid suprema over possibly unbounded sets. -/
def regret (eve : Adversary g s) (x : ℕ → V) (y : V) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    let m := eve k (x k)
    m.loss (x k) - m.loss y

/-- The step size that achieves good regret -/
def good_η (d g : ℝ) (n : ℕ) : ℝ := d / g / sqrt (n + 1)

@[bound] lemma good_η_pos (d0 : 0 < d) (g0 : 0 < g) : 0 < good_η d g n := by rw [good_η]; bound
@[bound] lemma good_η_nonneg (d0 : 0 ≤ d) (g0 : 0 ≤ g) : 0 ≤ good_η d g n := by rw [good_η]; bound

/-- Online gradient descent stays in the set -/
lemma ogd_mem (p : Proj proj s) (xs : x ∈ s) : ogd proj η eve x xs n ∈ s := by
  induction' n with n
  all_goals simp [ogd, step, xs, p.mem]

/-- A bound on the sum of inverse sqrts -/
@[bound] lemma sum_inv_sqrt_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (sqrt (k + 1) : ℝ)⁻¹ ≤ 2 * sqrt n := by
  induction' n with n h
  · simp
  · simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    refine le_trans (add_le_add_right h _) ?_
    rw [← mul_le_mul_iff_of_pos_right (a := sqrt (n + 1)), add_mul, inv_mul_cancel₀ (by positivity),
      mul_assoc, mul_assoc, Real.mul_self_sqrt, ← Real.sqrt_mul, ← le_sub_iff_add_le,
      ← le_div_iff₀', Real.sqrt_le_iff]
    all_goals bound

/-- Regret bound for online gradient descent (theorem 3.1 in section 3.1) -/
theorem regret_le (sd : EMetric.diam s ≤ .ofReal d) (p : Proj proj s) (eve : Adversary g s)
    (d0 : 0 ≤ d) (g0 : 0 ≤ g) (xs : x ∈ s) (ys : y ∈ s) :
    regret eve (ogd proj (good_η d g) eve x xs) y n ≤ 3 / 2 * g * d * sqrt n := by
  set η : ℕ → ℝ := good_η d g
  set z := ogd proj η eve x xs
  set m := fun n ↦ eve n (z n)
  have hm : ∀ n, eve n (z n) = m n := by intro; rfl
  set Δ := fun n ↦ z n - y
  -- If the set is empty, regret is zero
  by_cases empty : d = 0
  · simp only [empty, ENNReal.ofReal_zero, nonpos_iff_eq_zero, EMetric.diam_eq_zero_iff, mul_zero,
      zero_mul] at sd ⊢
    have e : ∀ n, z n = y := fun _ ↦ sd (ogd_mem p xs) ys
    simp only [regret, e, sub_self, Finset.sum_const_zero, le_refl]
  replace d0 : 0 < d := (Ne.symm empty).lt_of_le d0
  have Δd : ∀ n, ‖Δ n‖ ≤ d := by
    intro n
    simp only [Δ, ← dist_eq_norm_sub, ← ENNReal.ofReal_le_ofReal_iff d0.le, ← edist_dist]
    exact EMetric.edist_le_of_diam_le (ogd_mem p xs) ys sd
  -- Apply convexity to express regret in terms of subgradient inner products
  simp only [regret, hm]
  have le0 : ∀ {n}, (m n).loss (z n) - (m n).loss y ≤ inner ℝ (m n).grad (Δ n) := by
    intro n
    rw [← neg_le_neg_iff, neg_sub, ← inner_neg_right, neg_sub]
    apply (m n).sub
  refine le_trans (Finset.sum_le_sum (fun _ _ ↦ le0)) ?_
  -- If subgradients are zero, regret is zero
  by_cases flat : g = 0
  · have e : ∀ n, (m n).grad = 0 := by intro n; simpa [flat] using (m n).norm
    simp [e, flat]
  replace g0 : 0 < g := (Ne.symm flat).lt_of_le g0
  have η0 : ∀ n, 0 < η n := by bound
  -- Regret subgradient inner products as an almost telescoping sum
  have le1 : ∀ {n}, inner ℝ (m n).grad (Δ n) ≤
      2⁻¹ * ((η n)⁻¹ * (‖Δ n‖^2 - ‖Δ (n + 1)‖^2) + η n * g^2) := by
    intro n
    rw [← mul_le_mul_left (η0 n), mul_left_comm (η n), le_inv_mul_iff₀ (by norm_num)]
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ (η0 n).ne', one_mul, ← pow_two,
      sub_add_eq_add_sub, le_sub_iff_add_le]
    rw [add_comm, ← le_sub_iff_add_le, ← sub_add_eq_add_sub, real_inner_comm, mul_assoc,
      ← smul_eq_mul (η _), ← inner_smul_right_eq_smul]
    have gg : ‖η n • (m n).grad‖^2 ≤ η n ^ 2 * g ^ 2 := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (η0 n), mul_pow]
      bound [(m n).norm]
    refine le_trans ?_ (add_le_add_left gg _)
    rw [← norm_sub_sq_real, sub_right_comm, ← dist_eq_norm_sub, ← dist_eq_norm_sub]
    bound [p.dist_le (z n - η n • (m n).grad) ys]
  refine le_trans (Finset.sum_le_sum (fun _ _ ↦ le1)) ?_
  simp only [mul_add, Finset.sum_add_distrib, mul_comm _ (g ^ 2), ← Finset.mul_sum, ← mul_assoc,
    mul_sub, Finset.sum_sub_distrib]
  -- Make the telescoping sum clearer
  set δ : ℕ → ℝ := fun n ↦ if n = 0 then 0 else η (n - 1)
  have δ1 : ∀ n, η n = δ (n + 1) := by simp [η, δ]
  have ηδ : ∀ n, (δ n)⁻¹ ≤ (η n)⁻¹ := by
    intro n
    induction' n
    all_goals { simp [δ, η, good_η]; bound }
  have le2 : ∑ k ∈ Finset.range n, 2⁻¹ * (η k)⁻¹ * ‖Δ (k + 1)‖ ^ 2 ≥
      ∑ k ∈ Finset.range n, 2⁻¹ * (δ k)⁻¹ * ‖Δ k‖ ^ 2 := by
    induction' n with n h
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp [δ, if_true, η]
      bound
  refine le_trans (add_le_add_right (sub_le_sub_left le2 _) _) ?_
  -- Split into telescoping sum and error term
  trans 2⁻¹ * g * d * √n + g * d * √n
  · apply add_le_add
    · -- Telescope the sum
      simp only [← Finset.sum_sub_distrib, ← sub_mul, ← mul_sub]
      trans ∑ k ∈ Finset.range n, 2⁻¹ * ((η k)⁻¹ - (δ k)⁻¹) * d ^ 2
      · exact Finset.sum_le_sum fun k _ ↦ by bound [Δd k, ηδ k]
      · simp only [← Finset.mul_sum, mul_comm _ (d ^ 2), δ1,
          Finset.sum_range_sub (f := fun k ↦ (δ k)⁻¹)]
        simp only [δ, if_true, inv_zero, sub_zero]
        induction' n with n
        · simp
        · simp [η, good_η, div_eq_mul_inv, ← mul_assoc, mul_comm _ d⁻¹, pow_two]
          apply le_of_eq
          ring
    · -- Bound the error term
      simp only [η, good_η, div_eq_mul_inv, ← Finset.mul_sum, ← mul_assoc, mul_comm _ g⁻¹, pow_two,
        inv_mul_cancel₀ g0.ne', one_mul]
      rw [mul_comm _ (2⁻¹ : ℝ), mul_assoc, mul_assoc, inv_mul_le_iff₀ (by norm_num)]
      simp only [mul_comm _ (g * d), ← mul_assoc]
      rw [mul_assoc _ 2]
      bound
  · linarith
