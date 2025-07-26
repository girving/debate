import Prob.Arith

/-!
# Conditional probabilities
-/

open Classical
open Prob
open Set
open scoped Real
noncomputable section

namespace Prob

variable {α β γ : Type}
variable {f g : Prob α}
variable {p q r s : α → Prop}
variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {u : α → V}
variable {v : α → ℝ}

/-- cexp and cond are related -/
lemma cond_eq_cexp : f.cond p q = f.cexp (fun x ↦ if p x then 1 else 0) q := by
  simp only [cexp, cond]
  -- rw [pr, exp_congr]
  rw [pr, div_eq_inv_mul, smul_eq_mul]
  refine congr_arg₂ _ rfl (exp_congr fun x _ ↦ ?_)
  by_cases qx : q x
  repeat simp only [qx, and_true, if_true, if_false, and_false]

/-- cexp is monotonic -/
lemma cexp_mono {u v : α → ℝ} (uv : ∀ x, f.prob x ≠ 0 → q x → u x ≤ v x) :
    f.cexp u q ≤ f.cexp v q := by
  simp only [cexp, smul_eq_mul, ← div_eq_inv_mul]
  refine div_le_div_of_nonneg_right (exp_mono ?_) pr_nonneg
  intro x m; by_cases qx : q x
  repeat simp only [qx, if_true, if_false, uv x m, le_refl]

/-- cond is monotonic -/
lemma cond_mono (pq : ∀ x, f.prob x ≠ 0 → r x → p x → q x) : f.cond p r ≤ f.cond q r := by
  simp only [cond_eq_cexp]; apply cexp_mono; intro x m; rw [ite_le_ite_iff]; exact pq x m

-- cond is between 0 and 1
@[bound] lemma cond_nonneg : 0 ≤ f.cond p q := div_nonneg pr_nonneg pr_nonneg
@[bound] lemma cond_le_one : f.cond p q ≤ 1 := by
  refine div_le_one_of_le₀ (pr_mono ?_) pr_nonneg; intro x _; exact And.right
lemma cond_mem_Icc : f.cond p q ∈ Icc 0 1 := ⟨cond_nonneg, cond_le_one⟩

/-- cexp is nonneg if the inside is -/
lemma cexp_nonneg (h : ∀ x, f.prob x ≠ 0 → q x → 0 ≤ v x) : 0 ≤ f.cexp v q := by
  simp only [cexp, smul_eq_mul, ← div_eq_inv_mul]
  refine div_nonneg (exp_nonneg ?_) pr_nonneg
  intro x p; by_cases qx : q x
  · simp only [qx, if_true, h x p qx]
  · simp only [qx, if_false, le_refl]

/-- If something is true with probability 1, conditioning on it does nothing -/
lemma cexp_eq_exp (q1 : f.pr q = 1) : f.cexp u q = f.exp u := by
  simp only [cexp, q1, inv_one, one_smul]; simp only [pr_eq_one] at q1
  apply exp_congr; intro x m; simp only [q1 x m, if_true]

/-- If something is true with probability 1, conditioning on it does nothing -/
lemma cond_eq_pr (q1 : f.pr q = 1) : f.cond p q = f.pr p := by
  simp only [cond, q1, div_one]; simp only [pr_eq_one] at q1
  apply pr_congr; intro x m; simp only [q1 x m, and_true]

/-- Conditioning on true is just `pr` -/
@[simp] lemma cond_true : f.cond p (fun _ ↦ True) = f.pr p := by
  apply cond_eq_pr; simp only [pr_true]

/-- cexp = 0 if the event never occurs for nonzero `u` -/
lemma cexp_eq_zero (h : ∀ x, f.prob x ≠ 0 → q x → u x = 0) : f.cexp u q = 0 := by
  have z : (f.exp fun x => if q x then u x else 0) = 0 := by
    apply exp_eq_zero; intro _ m; split_ifs; apply h _ m; assumption; rfl
  simp only [cexp, z, smul_zero]

/-- cond = 0 if the event never occurs -/
lemma cond_eq_zero (h : ∀ x, f.prob x ≠ 0 → q x → ¬p x) : f.cond p q = 0 := by
  have z : f.pr (fun x ↦ p x ∧ q x) = 0 := by rw [pr_eq_zero]; simp only [ne_eq, not_and']; exact h
  rw [cond, z, zero_div]

-- If the conditioning event has probability zero, cond and pr = 0
lemma cexp_on_zero (q0 : f.pr q = 0) : f.cexp u q = 0 := by
  simp only [cexp, q0, inv_zero, zero_smul]
lemma cond_on_zero (q0 : f.pr q = 0) : f.cond p q = 0 := by simp only [cond, q0, div_zero]

/-- cexp depends only on the conditional supp -/
lemma cexp_congr {u v : α → V} (uv : ∀ x, f.prob x ≠ 0 → q x → u x = v x) :
    f.cexp u q = f.cexp v q := by
  have uvq : ∀ x, f.prob x ≠ 0 → (if q x then u x else 0) = (if q x then v x else 0) := by
    intro x m; by_cases qx : q x
    · simp only [qx, uv x m qx]
    · simp only [qx, if_false]
  simp only [cexp, exp_congr uvq]

/-- We can bound a cond bind uniformly in the first argument -/
lemma cond_bind_le_of_forall_le {f : Prob α} {g : α → Prob β} {p q : β → Prop} {b : ℝ}
    (b0 : 0 ≤ b) (le : ∀ x, f.prob x ≠ 0 → (g x).cond p q ≤ b) : (f >>= g).cond p q ≤ b := by
  simp only [cond]
  by_cases fg0 : 0 < (f >>= g).pr q
  · simp only [div_le_iff₀ fg0]; simp only [pr, ←exp_const_mul, exp_bind]
    apply exp_mono; intro x px; specialize le x px; simp only [exp_const_mul]
    by_cases g0 : 0 < (g x).pr q
    · simp only [cond, div_le_iff₀ g0] at le; exact le
    · replace g0 := le_antisymm (not_lt.mp g0) pr_nonneg; simp only [pr] at g0
      simp only [g0, mul_zero]; nth_rewrite 2 [←g0]
      apply exp_mono; intro y _; simp only [ite_le_ite_iff]; exact And.right
  · replace fg0 := le_antisymm (not_lt.mp fg0) pr_nonneg
    simp only [fg0, div_zero, b0]

/-- exp can be decomposed as positive and negative cexps, even if there are zeros -/
lemma exp_eq_cexp_add_cexp (q : α → Prop) :
    f.exp u = f.pr q • f.cexp u q + (1 - f.pr q) • f.cexp u (fun x ↦ ¬q x) := by
  by_cases q0 : f.pr q = 0
  · simp only [q0, cexp, inv_zero, zero_smul, smul_zero, sub_zero, pr_neg, inv_one, one_smul,
      zero_add]
    simp only [pr_eq_zero] at q0; apply exp_congr; intro x m
    simp only [q0 x m, not_false_eq_true, ↓reduceIte]
  by_cases q1 : f.pr q = 1
  · simp only [q1, cexp, inv_one, one_smul, sub_self, zero_smul, add_zero]
    simp only [pr_eq_one] at q1; apply exp_congr; intro x m; simp only [q1 x m, if_true]
  replace q1 : 1 - f.pr q ≠ 0 := by rw [sub_ne_zero]; exact Ne.symm q1
  simp only [cexp, pr_neg, smul_smul, mul_inv_cancel₀ q0, mul_inv_cancel₀ q1, one_smul]
  simp only [← exp_add]; apply exp_congr; intro x _
  by_cases qx : q x; repeat { simp only [qx, if_true, if_false]; norm_num }

/-- exp can be decomposed as a expectation over cexp's w.r.t. a function -/
lemma exp_eq_exp_cexp (g : α → β) :
    f.exp u = (g <$> f).exp (fun k ↦ f.cexp u (fun y ↦ g y = k)) := by
  simp only [map_eq, exp_bind, exp_pure, cexp, ← exp_const_smul]
  rw [exp_comm]
  refine exp_congr fun x p ↦ ?_
  have e : ∀ y, (f.pr fun z => g z = g y)⁻¹ • (if g x = g y then u x else 0) =
      (f.pr fun z ↦ g x = g z)⁻¹ • (if g x = g y then (1:ℝ) else 0) • u x := by
    intro y; by_cases gxy : g x = g y
    · simp only [gxy, ↓reduceIte, one_smul, eq_comm (a := g y)]
    · simp only [gxy, ↓reduceIte, smul_zero, zero_smul]
  rw [exp_congr fun _ _ ↦ e _, exp_const_smul, exp_smul_const, ← pr, smul_smul, inv_mul_cancel₀,
    one_smul]
  rw [pr_ne_zero]
  use x

/-- cexp can be decomposed as a expectation over cexp's w.r.t. a function -/
lemma cexp_eq_cexp_cexp (g : α → β) (h : ∀ x y, f.prob x ≠ 0 → g x = g y → (q x ↔ q y)) :
    f.cexp u q = (g <$> f).cexp (fun k ↦ f.cexp u (fun y ↦ g y = k))
      (fun k ↦ ∃ x, g x = k ∧ q x) := by
  rw [cexp, cexp]
  refine congr_arg₂ _ (congr_arg _ ?_) ?_
  · simp only [pr_map]
    refine pr_congr fun x m ↦ ⟨?_,?_⟩
    · intro _; use x
    · intro ⟨y,gyx,qy⟩; rwa [h x y m gyx.symm]
  · rw [exp_eq_exp_cexp g]
    refine exp_congr fun k _ ↦ ?_
    by_cases qk : ∃ z, g z = k ∧ q z
    · simp only [qk, ite_true]
      rcases qk with ⟨z,zk,qz⟩
      refine cexp_congr fun w m e ↦ ?_
      simp only [(h w z m (e.trans zk.symm)).mpr qz, ite_true]
    · simp only [qk, ite_false]
      refine cexp_eq_zero fun _ _ e ↦ ?_
      simp only [not_exists, not_and] at qk
      simp only [qk _ e, ite_false]

/-- Probabilities can be decomposed as positive and negative conditional probabilities,
    even if there are zeros -/
lemma pr_eq_cond_add_cond (q : α → Prop) :
    f.pr p = f.cond p q * f.pr q + f.cond p (fun x ↦ ¬q x) * (1 - f.pr q) := by
  rw [pr]
  simp only [cond_eq_cexp, exp_eq_cexp_add_cexp q, smul_eq_mul]
  ring

/-- The no-ratio version of Bayes' theorem holds unconditionally -/
lemma bayes' (f : Prob α) (a b : α → Prop) : f.cond a b * f.pr b = f.cond b a * f.pr a := by
  simp only [cond]
  by_cases a0 : f.pr a = 0
  · have ab0 : f.pr (fun x ↦ a x ∧ b x) = 0 := by
      apply le_antisymm _ pr_nonneg; rw [←a0]; apply pr_mono; intro x _; exact And.left
    simp only [a0, ab0, div_zero, mul_zero, zero_div, zero_mul]
  by_cases b0 : f.pr b = 0
  · have ab0 : f.pr (fun x ↦ b x ∧ a x) = 0 := by
      apply le_antisymm _ pr_nonneg; rw [←b0]; apply pr_mono; intro x _; exact And.left
    simp only [b0, ab0, div_zero, mul_zero, zero_div, zero_mul]
  simp only [div_mul_cancel₀ _ a0, div_mul_cancel₀ _ b0, and_comm]

/-- Bayes' theorem, ratio version -/
theorem bayes (f : Prob α) (a b : α → Prop) (b0 : f.pr b ≠ 0) :
    f.cond a b = f.cond b a * f.pr a / f.pr b := by
  rw [←bayes']; field_simp [b0]

/-- Pure cexps are simple -/
lemma cexp_pure {x : α} : (pure x : Prob α).cexp u q = if q x then u x else 0 := by
  simp only [cexp, exp_pure, pr_pure]; by_cases qx : q x
  repeat simp only [qx, if_true, if_false, inv_zero, inv_one, one_smul, zero_smul]

/-- Pure conditional probabilities are just p ∧ q booleans -/
lemma cond_pure {x : α} : (pure x : Prob α).cond p q = if p x ∧ q x then 1 else 0 := by
  simp only [cond, pr_pure]; by_cases qx : q x
  repeat simp only [qx, and_true, if_true, div_one, and_false, if_false, zero_div]

-- cexp is linear
lemma cexp_zero : f.cexp (fun _ ↦ (0 : V)) q = 0 := by
  simp only [cexp, ite_self, exp_const, smul_zero]
lemma cexp_add {u v : α → V} : f.cexp (fun x ↦ u x + v x) q = f.cexp u q + f.cexp v q := by
  simp only [cexp, ite_add_zero, exp_add, smul_add]
lemma cexp_sum {s : Finset β} {u : β → α → V} :
    f.cexp (fun y ↦ s.sum (fun x ↦ u x y)) q = s.sum (fun x ↦ f.cexp (u x) q) := by
  induction' s using Finset.induction with _ s m h
  · simp only [Finset.sum_empty, cexp_zero]
  · simp only [Finset.sum_insert m, cexp_add, h]
lemma cexp_const_mul {s : ℝ} : f.cexp (fun x ↦ s • u x) q = s • f.cexp u q := by
  simp only [cexp, smul_ite_zero, ← exp_const_smul, smul_comm s]

/-- cond depends only on the conditional supp -/
lemma cond_congr {p q r : α → Prop} (pq : ∀ x, f.prob x ≠ 0 → r x → (p x ↔ q x)) :
    f.cond p r = f.cond q r := by
  simp only [cond_eq_cexp]; apply cexp_congr; simp only [ite_one_zero_congr]; exact pq

/-- Congruence for `cond` if both arguments change -/
lemma cond_congr' (rs : ∀ x, f.prob x ≠ 0 → (r x ↔ s x))
    (pq : ∀ x, f.prob x ≠ 0 → r x → (p x ↔ q x)) : f.cond p r = f.cond q s := by
  rw [cond]
  refine congr_arg₂ _ ?_ ?_
  all_goals { apply pr_congr; aesop }

/-- f.cond ¬p q = 1 - f.cond p q if f.pr q ≠ 0 -/
lemma cond_neg (q0 : f.pr q ≠ 0) : f.cond (fun x ↦ ¬p x) q = 1 - f.cond p q := by
  simp only [cond, eq_sub_iff_add_eq, ←add_div, div_eq_one_iff_eq q0]
  simp only [pr, ←exp_add]; apply exp_congr; intro x _
  by_cases qx : q x
  repeat { by_cases px : p x; repeat { simp only [px,qx, if_true, if_false]; norm_num }}

/-- Rewrite cexp of an if into a more conditional cexp -/
lemma cexp_if :
    f.cexp (fun x ↦ if p x then u x else 0) q = f.cond p q • f.cexp u (fun x ↦ p x ∧ q x) := by
  simp only [cexp, cond, ←ite_and, @and_comm _ (p _)]
  by_cases z : f.pr (fun x ↦ p x ∧ q x) = 0
  · simp only [z, zero_div, inv_zero, zero_smul, smul_zero, smul_eq_zero, inv_eq_zero]
    right
    refine exp_eq_zero fun x m ↦ ?_
    simp only [pr_eq_zero] at z
    simp only [z x m, if_false]
  · simp only [smul_smul, div_eq_inv_mul, mul_assoc, mul_inv_cancel₀ z, mul_one]
    refine congr_arg₂ _ rfl (exp_congr ?_); intro x _; split_ifs; repeat rfl

/-- cexp can be decomposed as positive and negative cexps, even if there are zeros -/
lemma cexp_eq_cexp_add_cexp (r : α → Prop) :
    f.cexp u q = f.cond r q • f.cexp u (fun x ↦ q x ∧ r x) +
       (1 - f.cond r q) • f.cexp u (fun x ↦ q x ∧ ¬r x) := by
  by_cases q0 : f.pr q = 0
  · simp only [cexp_on_zero q0, cond_on_zero q0, zero_smul, sub_zero, one_smul, zero_add]
    simp only [pr_eq_zero] at q0
    rw [cexp, pr_eq_zero.mpr _, inv_zero, zero_smul]
    intro x m; simp only [q0 x m, false_and, not_false_eq_true]
  have e : ∀ s, 1 - (f.pr q)⁻¹ • s = (f.pr q)⁻¹ • (f.pr q - s) := by
    intro s; simp only [smul_eq_mul, mul_sub, inv_mul_cancel₀ q0]
  rw [cexp, exp_eq_cexp_add_cexp r]
  simp only [cond, div_eq_inv_mul, ← smul_eq_mul, e, ← smul_add, smul_assoc]
  refine congr_arg₂ _ rfl (congr_arg₂ _ ?_ ?_)
  · simp only [cexp_if, smul_smul, mul_comm (f.pr r), bayes' f q r]
    simp only [cond, div_mul_cancel₀ _ q0]
  · simp only [cexp_if, ← pr_neg, smul_smul, mul_comm (f.pr fun x ↦ ¬r x),
      bayes' f q (fun x ↦ ¬r x)]
    simp only [cond, div_mul_cancel₀ _ q0]
    refine congr_arg₂ _ ?_ rfl
    simp only [pr, ← exp_sub]
    refine exp_congr fun x _ ↦ ?_
    by_cases qx : q x
    all_goals { by_cases rx : r x; all_goals simp [qx, rx] }

/-- Weighted averages are ≤ max -/
lemma average_le_max {p x y : ℝ} (m : p ∈ Icc 0 1) : p • x + (1-p) • y ≤ max x y := by
  have p0 : 0 ≤ p := m.1; have p1 : p ≤ 1 := m.2
  by_cases xy : x ≤ y
  · simp only [max_eq_right xy, smul_eq_mul]; nlinarith
  · simp only [max_eq_left (le_of_lt (not_le.mp xy)), smul_eq_mul]; nlinarith

/-- We can bound a cexp bind in terms of an intermediate event occuring or not -/
lemma cexp_bind_le_of_cut {f : Prob α} {g : α → Prob β} {u : β → ℝ} {q : β → Prop} (i : α → Prop) :
    (f >>= g).cexp u q ≤
      max ((f >>= fun x ↦ Prod.mk x <$> g x).cexp (fun y ↦ u y.2) (fun y ↦ q y.2 ∧ i y.1))
           ((f >>= fun x ↦ Prod.mk x <$> g x).cexp (fun y ↦ u y.2) (fun y ↦ q y.2 ∧ ¬i y.1)) := by
  rw [cexp_enrich, cexp_eq_cexp_add_cexp (fun y ↦ i y.1)]
  generalize hp : (f >>= fun x ↦ Prod.mk x <$> g x).cond (fun y ↦ i y.1) (fun y ↦ q y.2) = p
  have m : p ∈ Icc 0 1 := by rw [←hp]; exact cond_mem_Icc
  exact average_le_max m

/-- We can bound a cond bind in terms of an intermediate event occuring or not -/
lemma cond_bind_le_of_cut {f : Prob α} {g : α → Prob β} {p q : β → Prop} (i : α → Prop) :
    (f >>= g).cond p q ≤
      max ((f >>= fun x ↦ Prod.mk x <$> g x).cond (fun y ↦ p y.2) (fun y ↦ q y.2 ∧ i y.1))
          ((f >>= fun x ↦ Prod.mk x <$> g x).cond (fun y ↦ p y.2) (fun y ↦ q y.2 ∧ ¬i y.1)) := by
  simp only [cond_eq_cexp]; apply cexp_bind_le_of_cut

/-- pr_mono when the left side is enriched -/
lemma pr_enrich_le_pr {f : Prob α} {g : α → Prob β} {p : α × β → Prop} {i : α → Prop}
    (pi : ∀ x y, f.prob x ≠ 0 → (g x).prob y ≠ 0 → p (x,y) → i x) :
    (f >>= fun x ↦ Prod.mk x <$> g x).pr p ≤ f.pr i := by
  simp only [pr_bind]; apply exp_mono; intro x fx; by_cases ix : i x
  · simp only [ix, if_true]; apply pr_le_one
  · apply le_of_eq; simp only [ix, if_false, pr_eq_zero, prob_map]; intro ⟨x',y⟩ pxy
    contrapose pxy; simp only [not_not] at pxy ⊢; rw [pr_eq_zero]; intro y' n
    contrapose ix; simp only [not_not]
    simp only [Prod.mk.injEq, not_and, not_forall, not_not, exists_prop] at ix
    simp only [←ix.1, ix.2] at n pxy; exact pi x y fx n pxy

/-- pr_mono when the right side is enriched -/
lemma pr_le_pr_enrich {f : Prob α} {g : α → Prob β} {p : α × β → Prop} {i : α → Prop}
    (ip : ∀ x y, f.prob x ≠ 0 → (g x).prob y ≠ 0 → i x → p (x,y)) :
    f.pr i ≤ (f >>= fun x ↦ Prod.mk x <$> g x).pr p := by
  simp only [pr_bind]; apply exp_mono; intro x fx; by_cases ix : i x
  · apply le_of_eq; simp only [ix, if_true]; refine (pr_eq_one.mpr ?_).symm; intro ⟨x',y⟩ pxy
    contrapose pxy; simp only [not_not, prob_map]; rw [pr_eq_zero]; intro y' n
    contrapose pxy; simp only [Prod.mk.injEq, not_and, not_forall, not_not, exists_prop] at pxy ⊢
    simp only [←pxy.1, pxy.2] at n ⊢; apply ip x y fx n ix
  · simp only [ix, if_false]; exact pr_nonneg

/-- Bound an enriched cond by bounding the first half
    if first half props relate to second half props -/
lemma cond_bind_le_first {f : Prob α} {g : α → Prob β} (p q : β → Prop) (i j : α → Prop)
    (pi : ∀ x y, f.prob x ≠ 0 → (g x).prob y ≠ 0 → j x → p y → q y → i x)
    (jq : ∀ x y, f.prob x ≠ 0 → (g x).prob y ≠ 0 → j x → q y) :
    (f >>= fun x ↦ Prod.mk x <$> g x).cond (fun y ↦ p y.snd) (fun y ↦ q y.snd ∧ j y.fst) ≤
      f.cond i j := by
  simp only [cond]; by_cases fj : f.pr j = 0
  · have qj : (f >>= fun x ↦ Prod.mk x <$> g x).pr (fun y ↦ q y.2 ∧ j y.1) = 0 := by
      refine le_antisymm ?_ pr_nonneg; rw [←fj]
      apply pr_enrich_le_pr; intro x y _ _ ⟨_,jx⟩; exact jx
    simp only [fj, qj, div_zero, le_refl]
  refine div_le_div₀ pr_nonneg ?_ ((Ne.symm fj).lt_of_le pr_nonneg) ?_
  · apply pr_enrich_le_pr; intro x y fx gy ⟨py,qy,jx⟩; exact ⟨pi x y fx gy jx py qy, jx⟩
  · apply pr_le_pr_enrich; intro x y fx gy jx; exact ⟨jq x y fx gy jx,jx⟩

/-- Bound an enriched cond by bounding the second half uniformly in the first half -/
lemma cond_bind_le_second {f : Prob α} {g : α → Prob β} (p q : β → Prop) (i : α → Prop) {b : ℝ}
    (b0 : 0 ≤ b) (gb : ∀ x, f.prob x ≠ 0 → i x → (g x).cond p q ≤ b) :
    (f >>= fun x ↦ Prod.mk x <$> g x).cond (fun y ↦ p y.snd) (fun y ↦ q y.snd ∧ i y.fst) ≤ b := by
  simp only [cond]
  by_cases d0 : (f >>= fun x ↦ Prod.mk x <$> g x).pr (fun y ↦ q y.2 ∧ i y.1) = 0
  · simp only [d0, div_zero, b0]
  simp only [div_le_iff₀ ((Ne.symm d0).lt_of_le pr_nonneg)]
  simp only [pr, ←exp_const_mul, exp_bind]; apply exp_mono; intro x m
  simp only [exp_map]
  by_cases ix : i x
  · simp only [Function.comp_def, ix, and_true, mul_ite, mul_one, mul_zero]
    specialize gb x m ix
    simp only [cond] at gb
    by_cases gq : (g x).pr q = 0
    · rw [exp_eq_zero]
      · apply exp_nonneg; intro y _; by_cases qy : q y
        repeat simp only [qy, if_true, if_false, b0, le_refl]
      · intro y n; rw [pr_eq_zero] at gq; simp only [gq y n, and_false, if_false]
    · simp only [div_le_iff₀ ((Ne.symm gq).lt_of_le pr_nonneg)] at gb
      simp only [pr, ← exp_const_mul, mul_ite, mul_one, mul_zero] at gb
      convert gb
  · simp only [ix, and_false, ite_false, mul_zero, le_refl, Function.comp_def]

/-- Bound a cexp uniformly -/
lemma cexp_le_of_forall {b : ℝ} (h : ∀ x, f.prob x ≠ 0 → q x → v x ≤ b) (b0 : 0 ≤ b) :
    f.cexp v q ≤ b := by
  simp only [cexp, smul_eq_mul, ← div_eq_inv_mul]
  apply div_le_of_le_mul₀ pr_nonneg b0
  simp only [pr, ←exp_const_mul]
  refine exp_mono fun x m ↦ ?_
  by_cases qx : q x
  · simp only [qx, ite_true, mul_one, h _ m qx]
  · simp only [qx, ite_false, mul_zero, le_refl]

lemma cond_map {f : α → β} {g : Prob α} {p : β → Prop} {q : β → Prop} :
    (f <$> g).cond p q = g.cond (fun y ↦ p (f y)) (fun y ↦ q (f y)) := by
  simp only [cond, pr_map]
