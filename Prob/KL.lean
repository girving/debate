import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Bound
import Misc.Bool
import Misc.Bound
import Misc.Finset
import Misc.If
import Prob.Basic
import Prob.Jensen

/-!
# KL-divergence
-/

open Classical
open Real (log)
open Set
open scoped Real
open scoped ENNReal
noncomputable section
namespace Prob

variable {α β : Type}
variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-!
### Definitions

We define a real version that ignores division by zero, then an `ℝ≥0∞` version that fills in `∞`
correctly.
-/

def reKL (p q : Prob α) : ℝ :=
  p.exp fun x ↦ log (p.prob x / q.prob x)

def KL (p q : Prob α) : ℝ≥0∞ :=
  if ∀ x, p.prob x ≠ 0 → q.prob x ≠ 0 then .ofReal (p.reKL q) else ∞

/-!
### Positivity and nonnegativity
-/

/-- A function for showing KL is positive-/
def gibbs (t : ℝ) : ℝ :=
  t * log t - (t - 1)

lemma gibbs_pos (t : ℝ) (t0 : 0 ≤ t) (t1 : t ≠ 1) : 0 < gibbs t := by
  by_cases z : t = 0
  · simp [gibbs, z]
  replace t0 : 0 < t := (Ne.symm z).lt_of_le t0
  have e : log t = -log t⁻¹ := by simp
  simp only [gibbs, sub_pos, mul_comm t, ← div_lt_iff₀ t0, sub_div, div_self t0.ne', one_div, e,
    lt_neg, neg_sub]
  exact Real.log_lt_sub_one_of_pos (by bound) (by simp [t1])

@[bound] lemma gibbs_nonneg (t : ℝ) (t0 : 0 ≤ t) : 0 ≤ gibbs t := by
  by_cases t1 : t = 1
  · simp [gibbs, t1]
  · exact (gibbs_pos t t0 t1).le

/-- KL is positive unless the distributions are equal -/
lemma reKL_pos (p q : Prob α) (h : ∀ x, p.prob x ≠ 0 → q.prob x ≠ 0) (ne : p ≠ q) :
    0 < reKL p q := by
  have g : 0 < q.exp fun x ↦ gibbs (p.prob x / q.prob x) := by
    obtain ⟨x, ne⟩ := ne_iff.mp ne
    refine exp_pos (by bound) ⟨x, ?_⟩
    by_cases q0 : q.prob x = 0
    · have p0 := h x
      simp only [not_imp_not, q0, true_implies] at p0
      simp only [p0, q0, ne_eq, not_true_eq_false] at ne
    · use q0
      apply gibbs_pos _ (by bound)
      simp [q0, div_eq_iff, ne]
  simpa only [gibbs, exp_sub, exp_const, exp_div_eq_one h, sub_self, sub_zero, ← smul_eq_mul,
    exp_div_smul h] using g

/-- `KL(p,p) = 0` -/
@[simp] lemma reKL_self (p : Prob α) : p.reKL p = 0 := by
  trans p.exp 0
  · exact p.exp_congr fun x px ↦ by simp
  · apply exp_const

/-- KL is nonnegative -/
lemma reKL_nonneg (p q : Prob α) (h : ∀ x, p.prob x ≠ 0 → q.prob x ≠ 0) : 0 ≤ reKL p q := by
  by_cases e : p = q
  · simp only [e, reKL_self, le_refl]
  · exact (reKL_pos p q h e).le

/-- KL is zero only if the distributions are equal -/
@[simp] lemma reKL_eq_zero_iff (p q : Prob α) (h : ∀ x, p.prob x ≠ 0 → q.prob x ≠ 0) :
    reKL p q = 0 ↔ p = q := by
  constructor
  · rw [← not_imp_not]
    exact fun ne ↦ (reKL_pos p q h ne).ne'
  · aesop

/-!
### Useful lemmas for manipulating KLs
-/

/-- Expand the log division given denominator safety -/
lemma exp_log_div_eq_sub {p q : Prob α} (h : ∀ x, p.prob x ≠ 0 → q.prob x ≠ 0) :
    p.exp (fun x ↦ log (p.prob x / q.prob x)) = p.exp fun x ↦ log (p.prob x) - log (q.prob x) :=
  exp_congr fun _ px ↦ Real.log_div px (h _ px)
