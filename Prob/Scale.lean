import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Bound
import Prob.Argmax

/-!
# Exponentially scale and normalise a probability distribution
-/

open Set
noncomputable section
namespace Prob

variable {α : Type}

/-- The partition function of an exponentially scaled distribution -/
def partition (p : Prob α) (η : α → ℝ) : ℝ :=
  p.exp fun x ↦ (η x).exp

@[bound] lemma partition_pos (p : Prob α) {η : α → ℝ} : 0 < p.partition η := by
  simp only [partition, Prob.exp, smul_eq_mul]
  exact Finset.sum_pos' (by bound) ⟨p.argmax, p.argmax_mem_supp, by bound⟩

@[simp] lemma partition_zero (p : Prob α) : p.partition (fun _ ↦ 0) = 1 := by
  simp only [partition, Real.exp_zero, exp_const]

@[bound] lemma partition_nonneg (p : Prob α) {η : α → ℝ} : 0 ≤ p.partition η :=
  p.partition_pos.le

/-- Exponentially scale a probability distribution, then renormalise -/
def scale (p : Prob α) (η : α → ℝ) : Prob α where
  prob := (p.partition η)⁻¹ • (fun x ↦ Real.exp (η x)) • p.prob
  prob_nonneg := by intro; simp; bound
  total := by
    rw [Finsupp.sum, Finsupp.support_smul_eq, Finsupp.support_pointwise_smul_eq]
    · simp only [Prob.partition, Finsupp.sum, Finsupp.coe_smul, Finsupp.coe_pointwise_smul,
        smul_eq_mul, Pi.smul_apply, Pi.mul_apply, ← Finset.mul_sum, Prob.exp, mul_comm _ (p.prob _)]
      exact inv_mul_cancel₀ p.partition_pos.ne'
    · simp
    · exact inv_ne_zero p.partition_pos.ne'

/-- Scaled, reweighted probabilities -/
lemma prob_scale (p : Prob α) (η : α → ℝ) (x : α) :
    (p.scale η).prob x = Real.exp (η x) * p.prob x / p.partition η := by
  simp [Prob.scale, inv_mul_eq_div]
