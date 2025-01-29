import Prob.Basic

/-!
# Uniform distribution on a `Finset`
-/

open Classical
open Set
open scoped Real
noncomputable section

namespace Prob

variable {α : Type}

/-- The uniform probability function on a nonempty finset -/
def uniform_finsupp (s : Finset α) (n : s.Nonempty) : α →₀ ℝ where
  support := s
  toFun := fun x ↦ if x ∈ s then s.card⁻¹ else 0
  mem_support_toFun := by
    intro x
    by_cases m : x ∈ s
    all_goals simp [m, n.ne_empty]

/-- The uniform distribution on a nonempty finset -/
def uniform (s : Finset α) (n : s.Nonempty) : Prob α where
  prob := uniform_finsupp s n
  prob_nonneg := by
    intro x
    simp only [uniform_finsupp, Finsupp.coe_mk]
    split_ifs
    all_goals simp
  total := by
    simp only [Finsupp.sum, uniform_finsupp, Finsupp.coe_mk, Finset.sum_ite_mem, Finset.inter_self,
      Finset.sum_const, nsmul_eq_mul]
    apply mul_inv_cancel₀
    simp [n.ne_empty]

/-- The support is the original set -/
@[simp] lemma supp_uniform {s : Finset α} {n : s.Nonempty} : (uniform s n).supp = s := by
  simp only [supp, uniform, uniform_finsupp]

/-- The support is the original set -/
@[simp] lemma support_uniform {s : Finset α} {n : s.Nonempty} : (uniform s n).prob.support = s := by
  simp only [uniform, uniform_finsupp]

/-- Nonzero uniform probabilities are `card⁻¹` -/
lemma prob_uniform {s : Finset α} {n : s.Nonempty} {x : α} (px : (uniform s n).prob x ≠ 0) :
    (uniform s n).prob x = (s.card : ℝ)⁻¹ := by
  rw [← Finsupp.mem_support_iff, ← supp, supp_uniform] at px
  simp only [uniform, uniform_finsupp, Finsupp.coe_mk, px, ↓reduceIte]

/-!
### The uniform distribution on a `Fintype`
-/

variable [Fintype α] [Nonempty α]

/-- The uniform distribution on a `Fintype` -/
def uniform_univ (α : Type) [Fintype α] [Nonempty α] : Prob α :=
  uniform Finset.univ Finset.univ_nonempty

@[simp] lemma supp_uniform_univ : (uniform_univ α).supp = Finset.univ := by
  simp only [supp, uniform_univ, support_uniform]

@[simp] lemma support_uniform_univ : (uniform_univ α).prob.support = Finset.univ := by
  simp only [uniform_univ, support_uniform]

@[simp] lemma prob_uniform_univ {x : α} : (uniform_univ α).prob x = (Fintype.card α : ℝ)⁻¹ := by
  rw [uniform_univ, prob_uniform, Finset.card_univ]
  rw [← mem_iff, supp_uniform]
  apply Finset.mem_univ
