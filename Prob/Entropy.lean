import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Functor
import Prob.Cond
import Prob.Uniform
import Prob.When

/-!
# Basic information theory for finite probability distributions
-/

open Classical
open Prod (fst snd)
open Real (log logb)
open Set
open scoped Real
noncomputable section
namespace Prob

variable {α β γ δ : Type}

/-!
### Definitions
-/

/-- The Shannon entropy of a probability distribution -/
def H (p : Prob α) : ℝ := p.exp fun x ↦ -logb 2 (p.prob x)

/-- Conditional entropy of a probability distribution: `H(X | Y)` -/
def Hc (p : Prob (α × β)) : ℝ :=
  p.exp fun x ↦ logb 2 ((p.pr fun y ↦ y.2 = x.2) / p.prob x)

/-- The inside of the `I` expectation -/
def I_inner (p : Prob (α × β)) (x : α × β) : ℝ :=
  logb 2 (p.prob x / p.pr (fun y ↦ y.1 = x.1) / p.pr (fun y ↦ y.2 = x.2))

/-- Mutual information of a distribution of pairs: `I(X,Y)` -/
def I (p : Prob (α × β)) : ℝ := p.exp fun x ↦ p.I_inner x

/-- The inside of the `Ic` expectation.
See https://en.wikipedia.org/wiki/Conditional_mutual_information.-/
def Ic_inner (p : Prob (α × β × γ)) (x : α × β × γ) : ℝ :=
  logb 2 (p.prob x * p.pr (fun y ↦ y.2.2 = x.2.2) / p.pr (fun y ↦ y.1 = x.1 ∧ y.2.2 = x.2.2) /
    p.pr (fun y ↦ y.2 = x.2))

/-- Conditional mutual information: `I(X,Y | Z)` -/
def Ic (p : Prob (α × β × γ)) : ℝ := p.exp fun x ↦ p.Ic_inner x

/-!
### Basic properties of `H`
-/

/-- Constants have no entropy -/
@[simp] lemma H_pure (x : α) : (pure x : Prob α).H = 0 := by
  simp [H, prob_pure]

/-- Maps reduce entropy -/
lemma H_map_le (f : α → β) (p : Prob α) : (f <$> p).H ≤ p.H := by
  simp only [H, map_eq, prob_bind, prob_pure, bind_assoc, pure_bind, exp_bind,
    exp_pure, id_eq]
  refine exp_mono fun x px ↦ ?_
  apply neg_le_neg
  apply Real.logb_le_logb_of_le
  · norm_num
  · exact px.symm.lt_of_le p.prob_nonneg
  · trans p.exp fun y ↦ if y = x then 1 else 0
    · rw [exp_eq_prob]
    · apply exp_mono fun y _ ↦ ?_
      by_cases xy : x = y
      · simp only [xy, ↓reduceIte, le_refl]
      · simp only [Ne.symm xy, ↓reduceIte]
        split_ifs; all_goals norm_num

/-- Injective maps preserve entropy -/
lemma H_map_eq (f : α → β) (p : Prob α) (fi : f.Injective) : (f <$> p).H = p.H := by
  simp only [H, map_eq, prob_bind, prob_pure, bind_assoc, pure_bind, exp_bind, exp_pure, id_eq]
  apply congr_arg₂ _ rfl
  funext x
  apply congr_arg
  apply congr_arg
  rw [← exp_eq_prob (d := fun y ↦ inferInstance)]
  apply congr_arg₂ _ rfl
  funext y
  by_cases xy : x = y
  · simp only [xy, ↓reduceIte]
  · simp only [Ne.symm xy, ↓reduceIte, ite_eq_right_iff, one_ne_zero, imp_false]
    rwa [← ne_eq, fi.ne_iff]

/-- The information of a pair is `fst.H + exp snd.H` -/
lemma H_pair (p : Prob α) (q : α → Prob β) :
    (do let x ← p; let y ← q x; return (x, y)).H = p.H + p.exp fun x ↦ (q x).H := by
  simp only [H, exp_map, CompTriple.comp_eq, exp_bind, exp_pure, ← exp_add, exp_neg, ← neg_add,
    neg_inj, prob_bind, prob_pure, Prod.mk.injEq, ite_and_one_zero, exp_const_mul, exp_eq_prob']
  simp only [ite_zero_mul, one_mul]
  refine exp_congr fun x px ↦ ?_
  simp only [← exp_const_add]
  refine exp_congr fun y py ↦ ?_
  rw [exp_eq_single p _ x]
  · simp only [↓reduceIte, Real.logb_mul px py, smul_eq_mul]
  · intro z _ zx; simp only [zx.symm, ↓reduceIte]

/-- Expected entropy as a difference of entropies -/
lemma exp_H_eq_H (p : Prob α) (q : α → Prob β) :
    p.exp (fun x ↦ (q x).H) = (do let x ← p; let y ← q x; return (x, y)).H - p.H := by
  simp only [H_pair]; abel

/-- The entropy of independent variables adds -/
@[simp] lemma H_bind_eq_add (p : Prob α) (q : Prob β) :
    (do let x ← p; let y ← q; return (x,y)).H = p.H + q.H := by
  simp only [H, prob_bind, prob_pure, ite_eq_delta, exp_bind, exp_pure, delta_pair, exp_mul_delta']
  trans p.exp fun x ↦ q.exp fun y ↦ -(logb 2 (p.prob x) + logb 2 (q.prob y))
  · refine exp_congr fun x px ↦ exp_congr fun y py ↦ ?_
    simp only [← neg_add, neg_inj, Real.logb_mul px py, smul_eq_mul]
  · simp only [neg_add_rev, exp_add, exp_neg, exp_const]; ring

/-- The entropy of independent variables adds -/
@[simp] lemma H_bind_eq_add' (p : Prob α) (q : Prob β) :
    (do let x ← p; let y ← q; return (y,x)).H = p.H + q.H := by
  rw [bind_comm, add_comm]; apply H_bind_eq_add

/-!
### Information is nonnegative
-/

/-- Reversed version of `Real.log_le_sub_one_of_pos` -/
lemma Real.one_sub_inv_le_log {x : ℝ} (x0 : 0 < x) : 1 - x⁻¹ ≤ log x := by
  rw [← neg_le_neg_iff, ← Real.log_inv, neg_sub]
  exact Real.log_le_sub_one_of_pos (by positivity)

/-- Conditional information is nonnegative (the building block for Shannon-type inequalities).
Proof follows https://mathweb.ucsd.edu/~lrothsch/information.pdf. -/
lemma Ic_nonneg (p : Prob (α × β × γ)) : 0 ≤ p.Ic := by
  simp only [Ic, Prob.Ic_inner]
  trans p.exp fun x ↦ (log 2)⁻¹ * (1 - (
    ((p.prob x * p.pr fun y ↦ y.2.2 = x.2.2) / p.pr fun y ↦ y.1 = x.1 ∧ y.2.2 = x.2.2) /
    p.pr fun y ↦ y.2 = x.2)⁻¹)
  · simp only [exp_const_mul]
    refine mul_nonneg (by positivity) ?_
    simp only [exp_sub, exp_const, sub_nonneg]
    rw [exp_eq_exp_cexp fun y ↦ y.2.2]
    refine exp_le_of_forall_le fun z pz ↦ ?_
    simp only [cexp, smul_eq_mul]
    apply inv_mul_le_one_of_le₀
    · trans p.exp fun x ↦ if x.2.2 = z then (((p.prob x * p.pr fun y ↦ y.2.2 = z) /
        p.pr fun y ↦ y.1 = x.1 ∧ y.2.2 = z) / p.pr fun y ↦ y.2.1 = x.2.1 ∧ y.2.2 = z)⁻¹ else 0
      · refine le_of_eq (congr_arg₂ _ rfl ?_)
        ext x
        split_ifs with e
        · simp only [e, Prod.ext_iff]
        · rfl
      · generalize hzp : (p.pr fun y ↦ y.2.2 = z) = zp
        simp only [inv_div, ← div_mul, div_mul_eq_mul_div, exp, Finsupp.sum]
        simp only [div_eq_inv_mul, mul_inv, ← mul_ite_zero, ← mul_assoc]
        set sx := p.prob.support.image (fun y ↦ y.1)
        set sy := p.prob.support.image (fun y ↦ y.2.1)
        set sz := p.prob.support.image (fun y ↦ y.2.2)
        rw [Finset.sum_subset_zero_on_sdiff (s₂ := sx ×ˢ sy ×ˢ sz) (hfg := fun _ _ ↦ rfl)]
        · have zm : z ∈ sz := by simpa [sz, prob_map, pr_eq_zero] using pz
          simp only [prob_map, hzp] at pz
          have pz' : 0 < zp := by simp only [← hzp] at pz ⊢; exact pr_nonneg.lt_of_ne pz.symm
          simp only [mul_comm _ zp⁻¹, ← mul_assoc, smul_eq_mul]
          simp only [mul_assoc, mul_ite, mul_zero, Finset.sum_product,
            Finset.sum_ite_eq', zm, ↓reduceIte, ← Finset.mul_sum, inv_mul_le_iff₀ pz', smul_eq_mul]
          trans ∑ x ∈ sx, ∑ y ∈ sy, ((p.pr fun a ↦ a.2.1 = y ∧ a.2.2 = z) *
            p.pr fun a ↦ a.1 = x ∧ a.2.2 = z)
          · refine Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ ?_
            rw [← mul_assoc]
            apply mul_le_of_le_one_left
            · exact mul_nonneg pr_nonneg pr_nonneg
            · exact mul_inv_le_one_of_le₀ (le_refl _) (prob_nonneg _)
          · simp only [← Finset.sum_mul, ← Finset.mul_sum]
            apply mul_le_mul
            · rw [sum_pr_eq_pr_and, ← hzp]
              · exact pr_mono fun _ _ ⟨_,_,_,e⟩ ↦ e
              · intro _ _ _ _ _ ⟨xy0,_⟩ ⟨xy1,_⟩
                exact xy0.symm.trans xy1
            · rw [sum_pr_eq_pr_and, ← hzp]
              · exact pr_mono fun _ _ ⟨_,_,_,e⟩ ↦ e
              · intro _ _ _ _ _ ⟨xy0,_⟩ ⟨xy1,_⟩
                exact xy0.symm.trans xy1
            · exact Finset.sum_nonneg fun _ _ ↦ pr_nonneg
            · exact pz'.le
        · intro x px
          simp only [Finsupp.mem_support_iff] at px
          simp only [Finset.mem_product, Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
            Prod.exists, exists_and_right, exists_eq_right, sx, sy, sz]
          exact ⟨⟨x.2.1, x.2.2, px⟩, ⟨x.1, x.2.2, px⟩, ⟨x.1, x.2.1, px⟩⟩
        · intro x px
          simp only [Finset.mem_sdiff, Finset.mem_product, Finsupp.mem_support_iff, ne_eq,
            Decidable.not_not] at px
          simp only [px, inv_zero, smul_zero, zero_mul, mul_ite, ite_self]
    · apply pr_nonneg
  · refine exp_mono fun x px ↦ ?_
    simp only [logb, div_eq_inv_mul _ (log 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.one_sub_inv_le_log
    refine div_pos (div_pos (mul_pos ?_ ?_) ?_) ?_
    · exact px.symm.lt_of_le p.prob_nonneg
    · rw [pr_pos]; use x
    · rw [pr_pos]; use x
    · rw [pr_pos]; use x

/-- Information is degenerate conditional information -/
lemma I_eq_Ic (p : Prob (α × β)) (z : γ) : p.I = ((fun x ↦ (x.1, x.2, z)) <$> p).Ic := by
  simp only [I, I_inner, Ic, Ic_inner, prob_map, pr_map, exp_map, Function.comp_def, Prod.mk.injEq,
    and_true, pr_true, mul_one, ← Prod.ext_iff, pr_eq_prob]

/-- Information is nonnegative -/
lemma I_nonneg (p : Prob (α × β)) : 0 ≤ p.I := by
  rw [p.I_eq_Ic ()]; apply Ic_nonneg

/-!
### `I` and `Ic` in terms of `H`
-/

/-- Alternate expression of `I` in terms of `H` -/
lemma I_eq_H (p : Prob (α × β)) : p.I = (fst <$> p).H + (snd <$> p).H - p.H := by
  simp only [I, H, exp_map, CompTriple.comp_eq, exp_neg, Function.comp, add_assoc,
    ← exp_add, ← exp_sub, I_inner, sub_neg_eq_add, ← sub_eq_neg_add, ← neg_add, neg_sub_left]
  refine exp_congr fun x px ↦ ?_
  have z1 : (p.pr fun y ↦ y.1 = x.1) ≠ 0 := by rw [pr_ne_zero]; use x
  have z2 : (p.pr fun y ↦ y.2 = x.2) ≠ 0 := by rw [pr_ne_zero]; use x
  rw [Real.logb_div (by positivity) z2, Real.logb_div px z1]
  simp only [prob_map]
  ring

/-- Alternate expression of `Ic` in terms of `I, H`.
See https://en.wikipedia.org/wiki/Conditional_mutual_information#Some_identities. -/
lemma Ic_eq_I_sub_H (p : Prob (α × β × γ)) :
    p.Ic = ((fun ⟨x,y,z⟩ ↦ ((x,z),(y,z))) <$> p).I - ((fun ⟨_,_,z⟩ ↦ z) <$> p).H := by
  simp only [Ic, Ic_inner, I, Prod.mk.eta, I_inner, exp_map, H, ← exp_sub, Function.comp_apply,
    sub_neg_eq_add, prob_map, pr_map, ← Prod.ext_iff, Prod.mk.injEq]
  refine exp_congr fun x px ↦ ?_
  have e0 : (p.pr fun y ↦ (y.1 = x.1 ∧ y.2.2 = x.2.2) ∧ y.2 = x.2) = p.prob x := by
    simp only [← pr_eq_prob]
    refine pr_congr fun y _ ↦ ?_
    by_cases e : y.2 = x.2
    repeat simp only [Prod.ext_iff, e, and_true, and_false]
  rw [← Real.logb_mul, e0]
  · exact congr_arg₂ _ rfl (by field_simp)
  refine mul_ne_zero (mul_ne_zero ?_ (inv_ne_zero ?_)) (inv_ne_zero ?_)
  all_goals rw [pr_ne_zero]; use x

/-- Alternate expression of `Ic` in terms of `H` -/
lemma Ic_eq_H (p : Prob (α × β × γ)) :
    p.Ic = ((fun ⟨x,_,z⟩ ↦ (x,z)) <$> p).H + ((fun ⟨_,y,z⟩ ↦ (y,z)) <$> p).H -
      ((fun ⟨x,y,z⟩ ↦ ((x,z),(y,z))) <$> p).H - ((fun ⟨_,_,z⟩ ↦ z) <$> p).H := by
  simp only [Ic_eq_I_sub_H, I_eq_H, Functor.map_map, Function.comp]

/-- Expected information is conditional information -/
lemma exp_I_eq_Ic (p : Prob α) (q : α → Prob (β × γ)) :
    p.exp (fun x ↦ (q x).I) = (do let z ← p; let (x,y) ← q z; return (x,y,z)).Ic := by
  simp only [I_eq_H, map_eq, exp_sub, exp_add, exp_H_eq_H, bind_assoc, pure_bind, Ic_eq_H,
    Prod.mk.eta, bind_const, bind_pure]
  generalize ha : (do let z ← p; let xy ← q z; pure (z, xy.1)) = a
  generalize hb : (do let z ← p; let xy ← q z; pure (z, xy.2)) = b
  generalize hc : (do let z ← p; let xy ← q z; pure (z, xy)) = c
  have ha' : (do let z ← p; let xy ← q z; pure (xy.1, z)).H = a.H := by
    trans (Prod.swap <$> a).H
    · rw [← ha]; apply congr_arg; simp only [map_bind, map_pure, Prod.swap_prod_mk]
    · rw [H_map_eq]; exact Prod.swap_injective
  have hb' : (do let z ← p; let xy ← q z; pure (xy.2, z)).H = b.H := by
    trans (Prod.swap <$> b).H
    · rw [← hb]; apply congr_arg; simp only [map_bind, map_pure, Prod.swap_prod_mk]
    · rw [H_map_eq]; exact Prod.swap_injective
  have hc' : (do let z ← p; let xy ← q z; pure ((xy.1, z), (xy.2, z))).H = c.H := by
    trans ((fun ⟨z,⟨x,y⟩⟩ ↦ ((x,z),(y,z))) <$> c).H
    · rw [← hc]; apply congr_arg; simp only [map_bind, map_pure]
    · rw [H_map_eq]; intro ⟨z,x,y⟩ ⟨z',x',y'⟩ e; simp only [Prod.mk.injEq] at e; simp only [e]
  simp only [ha', hb', hc']
  abel

/-- `I(X,Y) = I(Y,X)` -/
lemma I_swap (p : Prob (α × β)) : (Prod.swap <$> p).I = p.I := by
  simp only [I_eq_H, Functor.map_map, Function.comp, Prod.swap_prod_mk]
  refine congr_arg₂ _ ?_ ?_
  · nth_rw 1 [add_comm]; rfl
  · rw [H_map_eq]; exact Prod.swap_injective

/-- Information is preserved under injective maps -/
lemma I_map_eq_I (p : Prob (α × β)) (f : β → γ) (fi : f.Injective) :
    ((fun s ↦ (s.1, f s.2)) <$> p).I = p.I := by
  simp only [I_eq_H, Functor.map_map, Function.comp]
  refine congr_arg₂ _ (congr_arg₂ _ rfl ?_) ?_
  · trans (f <$> (snd <$> p)).H
    · simp only [Functor.map_map, Function.comp]
    · rw [H_map_eq _ _ fi]
  · rw [H_map_eq]
    intro ⟨_,_⟩ ⟨_,_⟩ e
    simp only [Prod.mk.injEq] at e
    simp only [e, Prod.mk.injEq, true_and, fi e.2]

/-- Information is preserved under injective maps -/
lemma map_I_eq_I (p : Prob (α × β)) (f : α → γ) (fi : f.Injective) :
    ((fun s ↦ (f s.1, s.2)) <$> p).I = p.I := by
  nth_rw 1 [← I_swap]
  nth_rw 2 [← I_swap]
  simp only [Functor.map_map, Function.comp, Prod.swap_prod_mk]
  have e : (fun s ↦ (s.2, f s.1)) <$> p = (fun s ↦ (s.1, f s.2)) <$> Prod.swap <$> p := by
    simp only [Functor.map_map, Function.comp, Prod.swap]
  rw [e, I_map_eq_I _ _ fi]

/-- Mutual self information is entropy -/
@[simp] lemma I_self (p : Prob α) : (p >>= fun x ↦ pure (x,x)).I = p.H := by
  simp only [I_eq_H, map_eq, bind_assoc, pure_bind, bind_pure]
  rw [← map_eq, H_map_eq]
  · ring
  · intro x y; simp

/-!
### Independent mutual information is zero
-/

/-- Mutual information w.r.t. a constant is zero -/
@[simp] lemma I_const (p : Prob α) (y : β) : (p >>= fun x ↦ pure (x,y)).I = 0 := by
  simp only [I_eq_H, map_bind, map_pure, bind_pure, bind_const, H_pure, add_zero, sub_eq_zero]
  rw [← map_eq_pure_bind, H_map_eq]
  apply Prod.mk_left_injective

/-- Mutual information is zero for independent variables -/
@[simp] lemma I_bind_eq_zero (p : Prob α) (q : Prob β) :
    (do let x ← p; let y ← q; return (x,y)).I = 0 := by
  simp only [I_eq_H, map_bind, map_pure, bind_const, bind_pure, H_bind_eq_add, sub_self]

/-- Mutual information is zero for independent variables -/
@[simp] lemma I_bind_eq_zero' (p : Prob α) (q : Prob β) :
    (do let x ← p; let y ← q; return (y,x)).I = 0 := by
  simp only [I_eq_H, map_bind, map_pure, bind_pure, bind_const, H_bind_eq_add']
  ring

/-!
### The chain rule for mutual information
-/

/-- The chain rule for mutual information: `I(X,(Y,Z)) = I(X,Z) + I(X,Y|Z)` -/
lemma I_eq_I_add_Ic (p : Prob (α × β × γ)) :
    p.I = ((fun ⟨x,_,z⟩ ↦ (x,z)) <$> p).I + p.Ic := by
  simp only [I_eq_H, Functor.map_map, Function.comp, Ic_eq_H, Prod.mk.eta]
  ring_nf
  simp only [add_right_inj, sub_right_inj]
  rw [H_map_eq]
  intro ⟨_,_,_⟩ ⟨_,_,_⟩ e
  simp only [Prod.mk.injEq] at e
  simp only [e]

/-- The chain rule for mutual information: `I(X,Y|Z) = I(X,(Y,Z)) - I(X,Z)` -/
lemma Ic_eq_I_sub_I (p : Prob (α × β × γ)) :
    p.Ic = p.I - ((fun ⟨x,_,z⟩ ↦ (x,z)) <$> p).I := by
  simp only [I_eq_I_add_Ic]; ring

/-!
### The data processing inequality

In full generality, this says

  `I(X,Z) ≤ I(X,Y)`, where `Z` is conditionally independent of `X` given `Y`

Our proof follows https://en.wikipedia.org/wiki/Data_processing_inequality.

We prove only the special case where `Z` is a random function of `Y`.
-/

/-- Conditional information is zero if we have conditional independence -/
lemma Ic_eq_zero (p : Prob (α × β)) (q : β → Prob γ) :
    (do let (x,z) ← p; let y ← q z; return (x,y,z)).Ic = 0 := by
  simp only [Ic, Ic_inner, prob_bind, prob_pure, pr_bind, pr_pure, exp_bind, exp_pure,
    Prod.mk.injEq]
  refine exp_eq_zero fun ⟨x,z⟩ pxz ↦ ?_
  refine exp_eq_zero fun y qy ↦ ?_
  simp only [Real.logb_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, div_eq_zero_iff,
    mul_eq_zero, false_or, eq_comm (a := x), eq_comm (a := z)]
  norm_num; right; left
  set ix : α  → ℝ := fun x' ↦ if x' = x then 1 else 0
  set iz : β → ℝ := fun z' ↦ if z' = z then 1 else 0
  have ex : ∀ x' (d : Decidable (x' = x)), @ite _ (x' = x) d 1 0 = ix x' := by
    intro x' d; simp only [ix]; by_cases e : x' = x; simp [e]; simp [e]
  have ez : ∀ z' (d : Decidable (z' = z)), @ite _ (z' = z) d 1 0 = iz z' := by
    intro z' d; simp only [iz]; by_cases e : z' = z; simp [e]; simp [e]
  have eq : ∀ x : α × β, (q x.2).prob y * iz x.2 = (q z).prob y * iz x.2 := by
    intro ⟨x',z'⟩
    by_cases zz : z' = z
    · simp only [zz]
    · simp only [zz, ↓reduceIte, mul_zero, iz]
  simp only [ite_and_one_zero, exp_const_mul, exp_mul_const, exp_eq_prob, exp_eq_prob', exp_const,
    ex, ez, eq]
  simp only [← mul_assoc, mul_comm ((q z).prob y), exp_mul_const]
  have z0 : p.exp (fun x ↦ ix x.1 * iz x.2) ≠ 0 := by
    refine ne_of_gt (exp_pos ?_ ?_)
    · intro _ _; simp only [mul_ite, mul_one, mul_zero, ix, iz]; split_ifs; all_goals norm_num
    · use ⟨x,z⟩, pxz; simp only [↓reduceIte, mul_one, zero_lt_one, ix, iz]
  have z1 : p.exp (fun x ↦ iz x.2) ≠ 0 := by
    refine ne_of_gt (exp_pos ?_ ?_)
    · intro _ _; simp only [iz]; split_ifs; all_goals norm_num
    · use ⟨x,z⟩, pxz; simp only [iz, one_pos, if_true]
  field_simp [z0, z1]
  ring

/-- The data processing inequality -/
lemma I_bind_le_I (p : Prob (α × β)) (q : β → Prob γ) :
    (do let (x,y) ← p; let z ← q y; return (x,z)).I ≤ p.I := by
  set r : Prob (α × β × γ) := do let (x,y) ← p; let z ← q y; return (x,y,z)
  set s : Prob (α × γ × β) := do let (x,y) ← p; let z ← q y; return (x,z,y)
  have rs : r.I = s.I := by
    refine Eq.trans ?_ (s.I_map_eq_I Prod.swap Prod.swap_injective)
    simp only [map_bind, map_pure, Prod.swap_prod_mk, r, s]
  have rd : r.I = (do let (x,y) ← p; let z ← q y; return (x,z)).I + r.Ic := by
    simp only [I_eq_I_add_Ic, map_eq, bind_assoc, pure_bind, r]
  have rp : r.I = p.I := by
    simp only [I_eq_I_add_Ic, map_eq, bind_assoc, pure_bind, Prod.mk.eta, bind_const, bind_pure, s,
      Ic_eq_zero, add_zero, rs]
  simp only [← rp, rd, le_add_iff_nonneg_right, Ic_nonneg]

/-- The data processing inequality -/
lemma bind_I_le_I (p : Prob (α × β)) (q : α → Prob γ) :
    (do let (x,y) ← p; let z ← q x; return (z,y)).I ≤ p.I := by
  set q := Prod.swap <$> p
  have pq : p = Prod.swap <$> q := by
    simp only [Functor.map_map, Function.comp, Prod.swap_swap, q, id_map']
  simp only [pq, I_swap q]
  nth_rw 1 [← I_swap]
  simp only [map_eq, bind_assoc, pure_bind, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk]
  apply I_bind_le_I

/-- Maps decrease information (data processing inequality with deterministic maps) -/
lemma map_I_le_I (p : Prob (α × β)) (f : α → γ) : ((fun s ↦ (f s.1, s.2)) <$> p).I ≤ p.I := by
  trans (do let (x,y) ← p; let z ← pure (f x); return (z, y)).I
  · refine le_of_eq (congr_arg _ ?_)
    simp only [map_eq, pure_bind]
  · exact bind_I_le_I p (fun x ↦ pure (f x))

/-- Maps decrease information (data processing inequality with deterministic maps) -/
lemma I_map_le_I (p : Prob (α × β)) (f : β → γ) : ((fun s ↦ (s.1, f s.2)) <$> p).I ≤ p.I := by
  trans (do let (x,y) ← p; let z ← pure (f y); return (x, z)).I
  · refine le_of_eq (congr_arg _ ?_)
    simp only [map_eq, pure_bind]
  · exact I_bind_le_I p (fun x ↦ pure (f x))

/-- Maps decrease information (data processing inequality with deterministic maps) -/
lemma map_I_map_le_I (p : Prob (α × β)) (f : α → γ) (g : β → δ) :
    ((fun s ↦ (f s.1, g s.2)) <$> p).I ≤ p.I := by
  refine le_trans (le_of_eq ?_) (le_trans (map_I_le_I _ f) (I_map_le_I _ g))
  simp only [map_eq, bind_assoc, pure_bind]

/-!
### The most information that can be added by branching
-/

/-- The most information that can be added by branching -/
lemma I_bind_le (p : Prob α) (q : α → Prob (β × γ)) :
    (p >>= q).I ≤ p.H + p.exp fun x ↦ (q x).I := by
  -- In terms of random variables, let p = Z, q = (X,Y). Then our inequality is
  --   I(X,Y) ≤ H(Z) + I(X,Y|Z)
  --   I(X,Y) ≤ H(Z) + H(X,Z) + H(Y,Z) - H(X,Y,Z) - H(Z)
  --   I(X,Y) ≤ H(X,Z) + H(Y,Z) - H(X,Y,Z)
  --   I(X,Y) ≤ I((X,Z),(Y,Z))
  set r : Prob ((β × α) × (γ × α)) := do let z ← p; let (x,y) ← q z; return ((x,z),(y,z))
  have e0 : p.H + p.exp (fun x ↦ (q x).I) = r.I := by
    simp only [exp_I_eq_Ic]
    simp only [I_eq_H, Ic_eq_H, map_bind, map_pure, r, bind_const, bind_pure, add_sub_cancel]
  have e1 : p >>= q = (fun s ↦ (s.1.1, s.2.1)) <$> r := by
    simp only [r, map_eq, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
  rw [e0, e1]
  apply map_I_map_le_I

/-- The most information that can be added by branching, under an outer bind -/
lemma I_bind_le₂ (o : Prob α) (p : α → Prob β) (q : α → β → Prob (γ × δ)) :
    (do let x ← o; let y ← p x; q x y).I ≤
      (o >>= p).H + o.exp fun x ↦ (p x).exp fun y ↦ (do let x ← o.when p y; q x y).I := by
  simp only [← bind_when o p]
  refine le_trans (I_bind_le _ _) ?_
  simp only [exp_bind, add_le_add_iff_left, le_refl]

/-!
### Independent branching adds no information
-/

/-- Independent branching adds no information: I(X,Y) = I(X,Y|Z) if I(X,Z) = 0 -/
lemma I_bind_le_exp (p : Prob α) (q : Prob β) (r : α → β → Prob γ) :
    (do let z ← p; let x ← q; let y ← r z x; return (x,y)).I ≤
      p.exp fun z ↦ (do let x ← q; let y ← r z x; return (x,y)).I := by
  simp only [exp_I_eq_Ic, bind_assoc, pure_bind, Ic_eq_I_sub_I, map_eq, bind_const, I_bind_eq_zero',
    sub_zero]
  refine le_trans (le_of_eq ?_) (I_map_le_I _ fst)
  simp only [map_eq, bind_assoc, pure_bind]

/-- Independent branching adds no information: I(X,Y) = I(X,Y|Z) if I(X,Z) = 0 -/
lemma I_bind_le_exp' (p : Prob α) (q : Prob β) (r : α → β → Prob γ) :
    (do let x ← p; let z ← q; let y ← r x z; return (x,y)).I ≤
      q.exp fun z ↦ (do let x ← p; let y ← r x z; return (x,y)).I := by
  simp only [bind_comm p]
  apply I_bind_le_exp

/-!
### Entropy is at most `log #states`
-/

/-- Abbreviation for `-p * logb 2 p` -/
def Hp (p : ℝ) : ℝ := -(p * logb 2 p)

lemma Hp_def (p : ℝ) : Hp p = -(p * logb 2 p) := rfl
lemma Hp_inv (x : ℝ) : Hp x⁻¹ = x⁻¹ * logb 2 x := by simp [Hp_def]
lemma Hp_of_negMulLog (p : ℝ) : Hp p = (Real.log 2)⁻¹ * Real.negMulLog p := by
  simp only [Hp, logb, div_eq_inv_mul, Real.negMulLog, neg_mul, mul_neg, neg_inj]
  ring

/-- `Hp` is concave down -/
lemma concaveOn_Hp : ConcaveOn ℝ (Icc 0 1) Hp := by
  have e : Hp = fun p ↦ (Real.log 2)⁻¹ * Real.negMulLog p := by ext p; simp only [Hp_of_negMulLog]
  simp only [e]
  apply ConcaveOn.mul
  · exact concaveOn_const _ (convex_Icc _ _)
  · exact Real.concaveOn_negMulLog.subset Icc_subset_Ici_self (convex_Icc 0 1)
  · intro _ _; simp only [inv_nonneg]; apply Real.log_nonneg; norm_num
  · intro _ ⟨a,b⟩; apply Real.negMulLog_nonneg a b
  · intro _ _ _ _; simp only [le_refl, implies_true]

/-- Entropy is at most `log #states` -/
lemma H_le_log (p : Prob α) : p.H ≤ logb 2 p.supp.card := by
  generalize hn : p.supp.card = n
  have np : 0 < (n : ℝ) := by simp only [← hn, Nat.cast_pos, p.card_supp_pos]
  have n0 : (n : ℝ) ≠ 0 := np.ne'
  simp only [H, exp, Finsupp.sum, smul_eq_mul, mul_neg, ← Hp_def]
  trans n * ∑ x ∈ p.prob.support, (n : ℝ)⁻¹ • Hp (p.prob x)
  · simp only [smul_eq_mul, ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ n0, one_mul, le_refl]
  · rw [mul_comm, ← le_div_iff₀ np, div_eq_inv_mul, ← Hp_inv]
    refine le_trans (concaveOn_Hp.le_map_sum ?_ ?_ ?_) ?_
    · intro _ _; positivity
    · simp only [supp] at hn
      simp only [Finset.sum_const, hn, nsmul_eq_mul, mul_inv_cancel₀ n0]
    · intro _ _; apply prob_mem_Icc
    · have t := p.total
      simp only [Finsupp.sum] at t
      simp only [smul_eq_mul, ← Finset.mul_sum, t, mul_one, le_refl]

/-- Bools have at one most bit of entropy -/
lemma H_le_one (p : Prob Bool) : p.H ≤ 1 := by
  refine le_trans (H_le_log p) ?_
  refine le_trans ?_ (le_trans (Real.logb_self_eq_one (b := 2) (by norm_num)).le (by norm_num))
  apply Real.logb_le_logb_of_le (by norm_num)
  · simp only [Nat.cast_pos, card_supp_pos]
  · simp only [supp, Nat.cast_le_ofNat]
    trans (Finset.univ : Finset Bool).card
    · exact Finset.card_le_card (Finset.subset_univ _)
    · simp only [Finset.card_univ, Fintype.card_bool, le_refl]

/-!
### The entropy of a uniform distribution
-/

/-- Uniform distributions have `H = log supp.card` -/
@[simp] lemma H_uniform (s : Finset α) (n : s.Nonempty) : (uniform s n).H = logb 2 s.card := by
  trans (uniform s n).exp fun _ ↦ -logb 2 s.card⁻¹
  · exact exp_congr fun _ px ↦ by rw [prob_uniform px]
  · simp only [Real.logb_inv, neg_neg, exp_const]
