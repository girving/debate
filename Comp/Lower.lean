import Comp.Basic
import Prob.Entropy

/-!
# Lower bounds on query complexity via information theory

We can only learn one bit per query about an oracle.
-/

open Real (logb)
open Set
noncomputable section

variable {α β : Type}

/-- We can only learn one bit per query about our oracle -/
theorem Comp.I_le_cost (p : Prob (BOracle α)) (f : BComp α (univ : Set Unit) β) :
    (do let o ← p; let r ← f.prob' o; return (o, r)).I ≤ p.exp fun o ↦ f.cost' o () := by
  induction' f with x β f g' h j m y f h generalizing p
  · simp only [prob', prob_pure', pure_bind, Prob.I_const, cost'_pure', Prob.exp_const, le_refl]
  · simp only [prob', prob_sample', bind_assoc, cost'_sample]
    refine le_trans (Prob.I_bind_le_exp' _ _ _) ?_
    rw [Prob.exp_comm]
    exact Prob.exp_mono fun _ _ ↦ h _ _
  · simp only [prob', prob_query', bind_assoc, cost', cost_query', if_true, Prob.exp_const_add]
    refine le_trans (Prob.I_bind_le₂ _ _ _) ?_
    refine add_le_add (Prob.H_le_one _) ?_
    simp only [Prob.exp_when p (fun o ↦ o y)]
    refine Prob.exp_mono fun b _ ↦ ?_
    simp only [bind_pure_comp, Prob.exp_const]
    apply h
