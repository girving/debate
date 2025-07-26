import Prob.Basic
import Misc.If

/-!
# Facts about expectations of functions
-/

open Classical
open Set
open scoped Real
noncomputable section

variable {α β : Type}
variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {W : Type} [AddCommGroup W] [Module ℝ W]

namespace Prob

/-- Expectation commutes with function application -/
lemma exp_apply (p : Prob α) (u : α → β → V) (y : β) : (p.exp u) y = p.exp fun x ↦ u x y := by
  simp only [exp, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

/-- Expectation commutes with function application, Finsupp version -/
lemma exp_finsupp_apply (p : Prob α) (u : α → β →₀ V) (y : β) :
    (p.exp u) y = p.exp fun x ↦ u x y := by
  simp only [exp, Finsupp.sum]
  generalize p.prob.support = s
  induction' s using Finset.induction with x s m h
  · simp
  · simp [Finset.sum_insert m]

/-- Commute a linear operator inside an exp -/
lemma apply_exp (p : Prob α) (u : α → V) (f : V → W) (f0 : f 0 = 0)
    (fa : ∀ a b, f (a + b) = f a + f b) (fs : ∀ (s : ℝ) a, f (s • a) = s • f a):
    f (p.exp u) = p.exp fun x ↦ f (u x) := by
  simp only [exp, Finsupp.sum]
  generalize p.prob.support = s
  induction' s using Finset.induction with x s m h
  · simp only [Finset.sum_empty, f0]
  · simp only [Finset.sum_insert m, fa, fs, h]
