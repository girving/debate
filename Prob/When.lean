import Prob.Argmax
import Prob.Arith
import Prob.ArithPi
import Misc.If

/-!
# `when`: machinery to commute binds

We construct an operator `p.when q` which allows flipping the order of `p` and `q` in a bind.
-/

open Classical
open Prod (fst)
open Set
open scoped Real
noncomputable section

variable {α β γ : Type}
variable (p : Prob α) (q : α → Prob β)
variable {V : Type} [AddCommGroup V] [Module ℝ V]

namespace Prob

def when_prob_fn (y : β) (x : α) : ℝ :=
    if (p >>= q).prob y = 0 then if x = p.argmax then 1 else 0 else
      ((p >>= q).prob y)⁻¹ * p.prob x * (q x).prob y

def when_support (y : β) : Finset α :=
  if (p >>= q).prob y = 0 then {p.argmax}
  else p.prob.support.filter fun x ↦ (q x).prob y ≠ 0

def when_finsupp (y : β) : α →₀ ℝ where
  support := when_support p q y
  toFun := when_prob_fn p q y
  mem_support_toFun := by
    intro x
    simp only [when_prob_fn, when_support]
    by_cases py : (p >>= q).prob y = 0
    all_goals simp [py]

lemma when_finsupp_nonneg (y : β) (x : α) : 0 ≤ (p.when_finsupp q y) x := by
  simp only [when_finsupp, Finsupp.coe_mk, when_prob_fn]
  split_ifs
  · norm_num
  · norm_num
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (prob_nonneg _)) (prob_nonneg _)) (prob_nonneg _)

lemma when_finsupp_total (y : β) : ((p.when_finsupp q y).sum fun _ p ↦ p) = 1 := by
  simp only [Finsupp.sum, when_finsupp, Finsupp.coe_mk, when_support, when_prob_fn]
  by_cases py : (p >>= q).prob y = 0
  · simp only [py, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_singleton]
  · simp only [py, ↓reduceIte, ne_eq, Finset.sum_filter, ite_not]
    trans ∑ x ∈ p.prob.support, ((p >>= q).prob y)⁻¹ * p.prob x * (q x).prob y
    · apply Finset.sum_congr rfl; intro x hx
      simp only [Finsupp.mem_support_iff] at hx
      simp only [ite_eq_right_iff, zero_eq_mul, mul_eq_zero, inv_eq_zero, py, hx, or_self,
        false_or, imp_self]
    · simp only [← Finset.mul_sum, mul_assoc, inv_mul_eq_one₀ py]
      simp only [prob_bind, exp, Finsupp.sum, smul_eq_mul]

/-- `p.when q` is a function that composes on the right of `p >>= q` to recover `p` -/
def when (y : β) : Prob α where
  prob := p.when_finsupp q y
  prob_nonneg := when_finsupp_nonneg _ _ _ _
  total := when_finsupp_total _ _ _

/-- Unconditional `when` probability -/
lemma when_prob_eq' (y : β) (x : α) : (p.when q y).prob x =
    if (p >>= q).prob y = 0 then if x = p.argmax then 1 else 0 else
      ((p >>= q).prob y)⁻¹ * p.prob x * (q x).prob y := by
  simp only [when, when_finsupp, Finsupp.coe_mk, when_prob_fn]

/-- Conditional `when` probability -/
lemma when_prob_eq {p} {q : α → Prob β} {y : β} {x : α} (h : (p >>= q).prob y ≠ 0) :
    (p.when q y).prob x = ((p >>= q).prob y)⁻¹ * p.prob x * (q x).prob y := by
   simp only [when_prob_eq', h, ↓reduceIte]

/-- The key property of `when`, special case `(x,y)` version -/
lemma bind_when_pure :
    (do let y ← p >>= q; let x ← p.when q y; return (x,y)) =
      (do let x ← p; let y ← q x; return (x,y)) := by
  ext ⟨s,t⟩
  simp only [bind_assoc, prob_bind, prob_pure, Prod.mk.injEq, ite_and_one_zero, ite_eq_delta,
    exp_delta_mul', exp_mul_delta', exp_mul_const]
  simp only [← prob_bind]
  by_cases z : (p >>= q).prob t = 0
  · simp only [z, zero_mul, zero_eq_mul]
    contrapose z
    simp only [not_or, prob_bind] at z ⊢
    refine ne_of_gt (exp_pos (by simp) ?_)
    use s, z.1; exact (Ne.symm z.2).lt_of_le (prob_nonneg _)
  · simp only [when_prob_eq z, ← mul_assoc, mul_inv_cancel₀ z, one_mul]

/-- The key property of `when` -/
lemma bind_when (r : α → β → Prob γ) :
    (do let y ← p >>= q; let x ← p.when q y; r x y) = (do let x ← p; let y ← q x; r x y) := by
  trans (do let x ← p; let y ← q x; return (x,y)) >>= fun s ↦ r s.1 s.2
  · simp only [← bind_when_pure, bind_assoc, pure_bind]
  · simp only [bind_assoc, pure_bind]

/-- Binding `p >>= q` with `p.when q` recovers `p` -/
lemma bind_bind_when : p >>= q >>= p.when q = p := by
  trans fst <$> (do let y ← p >>= q; let x ← p.when q y; return (x,y))
  · simp only [map_eq, bind_assoc, pure_bind, bind_pure]
  · trans fst <$> (do let x ← p; let y ← q x; return (x,y))
    · simp only [bind_when_pure]
    · simp only [map_eq, bind_assoc, pure_bind, bind_const, bind_pure]

/-- The key property of `when`, in terms of `exp` -/
lemma exp_when (r : α → β → V) :
    (p.exp fun x ↦ (q x).exp fun y ↦ r x y) =
      (p >>= q).exp fun y ↦ (p.when q y).exp fun x ↦ r x y := by
  trans (do let x ← p; let y ← q x; return (x,y)).exp (fun s ↦ r s.1 s.2)
  · simp only [exp_bind, exp_pure]
  · simp only [← bind_when_pure, exp_bind, exp_pure]
