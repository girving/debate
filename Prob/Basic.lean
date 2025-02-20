import Mathlib.LinearAlgebra.Finsupp.LSum
import Misc.Finsupp
import Prob.Defs

/-!
## Basic properties of `Prob`
-/

open Classical
open Prob
open Set
noncomputable section

variable {α β γ : Type}
variable {V : Type} [AddCommGroup V] [Module ℝ V]

namespace Prob

-- Monad details
lemma prob_pure' (x : α) : (pure x : Prob α).prob = Finsupp.single x 1 := rfl
lemma prob_bind' (f : Prob α) (g : α → Prob β) :
    (f >>= g).prob = f.prob.sum (λ x p ↦ p • (g x).prob) := rfl

/-- (pure x).prob is the indicator function on {x} -/
lemma prob_pure (x y : α) : (pure x : Prob α).prob y = if y = x then 1 else 0 := by
  simp only [Prob.prob, prob_pure', Finsupp.single_apply, eq_comm]

/-- pure.exp is function application -/
@[simp] lemma exp_pure (x : α) (f : α → V) : (pure x : Prob α).exp f = f x := by
  simp only [exp, prob_pure', zero_smul, Finsupp.sum_single_index, one_smul]

-- Basic definitions
lemma map_eq (f : α → β) (x : Prob α) : f <$> x = x >>= (λ x ↦ pure (f x)) := rfl
lemma seq_eq (f : Prob (α → β)) (x : Prob α) : f <*> x = f >>= (λ f ↦ f <$> x) := rfl
lemma seqLeft_eq (x : Prob α) (y : Prob β) : x <* y = x >>= (λ x ↦ y >>= λ _ ↦ pure x) := rfl
lemma seqRight_eq (x : Prob α) (y : Prob β) : x *> y = x >>= (λ _ ↦ y) := rfl

/-- (f >>= g).prob as an exp -/
lemma prob_bind (f : Prob α) (g : α → Prob β) (y : β) :
    (f >>= g).prob y = f.exp (λ x ↦ (g x).prob y) := by
  simp only [Prob.prob, prob_bind', Prob.exp, Finsupp.sum_apply]
  apply Finsupp.sum_congr; intro x _; rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- bind.exp is iterated exp -/
lemma exp_bind (f : Prob α) (g : α → Prob β) (h : β → V) :
    (f >>= g).exp h = f.exp (λ x ↦ (g x).exp h) := by
  simp only [exp, prob_bind']
  rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr; intro x _; rw [Finsupp.sum_smul_index]
    · simp only [← smul_smul, ← Finsupp.smul_sum]
    · intro _; simp only [zero_smul]
  · intro _; simp only [zero_smul]
  · intro _ _ _; simp only [add_smul]

-- Monad laws for Prob
lemma left_id (f : Prob α) : f >>= pure = f := by
  ext x; simp only [prob_bind, prob_pure, exp, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq,
    Finsupp.mem_support_iff, ne_eq, ite_not, smul_eq_mul]
  split_ifs; exact Eq.symm (by assumption); rfl
lemma right_id (x : α) (f : α → Prob β) : pure x >>= f = f x := by
  ext y; simp only [prob_bind, prob_pure, exp_pure]
lemma assoc (f : Prob α) (g : α → Prob β) (h : β → Prob γ) :
    f >>= g >>= h = f >>= (λ x ↦ g x >>= h) := by
  ext z; simp only [prob_bind, exp_bind, Finsupp.sum_apply]

/-- Prob is a lawful monad -/
instance : LawfulMonad Prob := LawfulMonad.mk'
  (id_map := by intro α x; simp only [map_eq, id, left_id])
  (pure_bind := by intro α β x f; simp only [right_id])
  (bind_assoc := assoc)

/-- Independent expectations can be reordered -/
lemma exp_comm (f : Prob α) (g : Prob β) (h : α → β → V) :
    f.exp (λ x ↦ g.exp (λ y ↦ h x y)) = g.exp (λ y ↦ f.exp (λ x ↦ h x y)) := by
  simp only [exp, Finsupp.smul_sum]
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun _ _ ↦ ?_
  refine Finsupp.sum_congr fun _ _ ↦ ?_
  simp only [smul_smul]
  ring_nf

/-- Independent computations can be reordered -/
lemma bind_comm (f : Prob α) (g : Prob β) (h : α → β → Prob γ) :
    f >>= (λ x ↦ g >>= (λ y ↦ h x y)) = g >>= (λ y ↦ f >>= (λ x ↦ h x y)) := by
  ext z; simp only [prob_bind]; rw [exp_comm]

/-- Variant of bind_comm when h's are not obviously equal -/
lemma bind_comm_of_eq (f : Prob α) (g : Prob β) (h0 h1 : α → β → Prob γ) (e : h0 = h1) :
    f >>= (λ x ↦ g >>= (λ y ↦ h0 x y)) = g >>= (λ y ↦ f >>= (λ x ↦ h1 x y)) := by
  rw [e]; apply bind_comm

/-- Constants are their own expectation -/
@[simp] lemma exp_const (f : Prob α) (x : V) : f.exp (λ _ ↦ x) = x := by
  simp only [exp, ← Finsupp.sum_smul, total, one_smul]

/-- We can drop the left side of a bind if it's unused -/
@[simp] lemma bind_const (f : Prob α) (g : Prob β) : f >>= (λ _ ↦ g) = g := by
  ext x; simp only [prob_bind, exp_const]

/-- Map of a constant is pure -/
lemma map_const (y : β) (x : Prob α) : (λ _ ↦ y) <$> x = pure y := bind_const _ _

/-- map sums probabilities -/
lemma prob_map (f : α → β) (x : Prob α) (z : β) : (f <$> x).prob z = x.pr (λ y ↦ f y = z) := by
  simp only [map_eq, prob_bind, pr, prob_pure, eq_comm]

/-- injective map preserves probabilities -/
lemma map_prob_of_inj {f : α → β} (inj : f.Injective) (x : Prob α) (y : α) :
    (f <$> x).prob (f y) = x.prob y := by
  simp only [prob_map, pr, exp, Finsupp.sum]; rw [Finset.sum_eq_single y]
  · simp only [↓reduceIte, smul_eq_mul, mul_one]
  · intro z m zy
    simp only [Finsupp.mem_support_iff, ne_eq] at m
    simp only [inj.ne zy, ↓reduceIte, smul_eq_mul, mul_zero]
  · intro m
    simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m
    simp only [m, ↓reduceIte, smul_eq_mul, mul_one]

/-- prob is in [0,1] -/
@[bound] lemma prob_le_one (f : Prob α) (x : α) : f.prob x ≤ 1 := by
  by_cases m : x ∈ f.supp
  · rw [←f.total, ←Finset.sum_singleton f.prob]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp only [supp, Finsupp.mem_support_iff, ne_eq] at m
      simp only [Finset.singleton_subset_iff, Finsupp.mem_support_iff, ne_eq, m, not_false_eq_true]
    · intro _ _ _; apply prob_nonneg
  · simp only [f.zero m, zero_le_one]
lemma prob_mem_Icc (f : Prob α) (x : α) : f.prob x ∈ Icc 0 1 := ⟨prob_nonneg _, prob_le_one f x⟩

/-- Congruence for exp -/
lemma exp_congr {f : Prob α} {g h : α → V} (e : ∀ x, f.prob x ≠ 0 → (g x = h x)) :
    f.exp g = f.exp h := by
  simp only [exp]; apply Finsupp.sum_congr; intro x m
  simp only [Finsupp.mem_support_iff] at m; simp only [e _ m]

/-- General congruence for exp, allowing the probabilities to be different -/
lemma exp_congr' {f g : Prob α} {u v : α → V} (h : ∀ x, f.prob x • u x = g.prob x • v x) :
    f.exp u = g.exp v := by
  simp only [exp, Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := f.prob.support) (s₂ := g.prob.support)),
    Finset.sum_subset (Finset.subset_union_right (s₁ := f.prob.support) (s₂ := g.prob.support))]
  · exact Finset.sum_congr rfl (λ _ _ ↦ h _)
  · intro x _ m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_smul]
  · intro x _ m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_smul]

/-- Congruence for pr -/
lemma pr_congr {f : Prob α} {p q : α → Prop} (e : ∀ x, f.prob x ≠ 0 → (p x ↔ q x)) :
    f.pr p = f.pr q := by
  simp only [pr]; apply exp_congr; intro x m; simp only [eq_iff_iff.mpr (e x m)]

/-- bind_congr but restricted to support -/
lemma bind_congr (f : Prob α) (g h : α → Prob β) (e : ∀ x, f.prob x ≠ 0 → g x = h x) :
    f >>= g = f >>= h := by
  ext y; simp only [prob_bind]; apply exp_congr; intro x m
  simp only [f.mem_iff] at m; simp only [e _ m]

/-- total for Fintypes -/
lemma fintype_total (f : Prob α) [Fintype α] : (Finset.univ : Finset α).sum f.prob = 1 := by
  rw [←Finset.sum_subset (Finset.subset_univ f.supp)]; exact f.total
  intro x _ m; simp only [mem_iff, not_not] at m; exact m

-- Boolean probabilities are complements
@[simp] lemma bool_total (f : Prob Bool) : f.prob true + f.prob false = 1 := by
  simpa only [Fintype.sum_bool] using f.fintype_total
@[simp] lemma bool_total' (f : Prob Bool) : f.prob false + f.prob true = 1 := by
  rw [add_comm, bool_total]
lemma bool_prob_false_of_true {f : Prob Bool} : f.prob false = 1 - f.prob true := by
  apply eq_sub_of_add_eq; rw [add_comm]; exact f.bool_total
lemma bool_prob_true_of_false {f : Prob Bool} : f.prob true = 1 - f.prob false :=
  eq_sub_of_add_eq f.bool_total
lemma not_bool_prob {f : Prob Bool} {x : Bool} : (not <$> f).prob x = f.prob (not x) := by
  rw [←Bool.not_not x, map_prob_of_inj, Bool.not_not]; rw [Bool.injective_iff]; simp

/-- The difference in probabilities between two boolean distributions is a constant -/
lemma bool_abs_prob_diff {f g : Prob Bool} {x : Bool} (y : Bool) :
    |f.prob x - g.prob x| = |f.prob y - g.prob y| := by
  induction' x
  all_goals induction' y
  all_goals simp only [bool_prob_false_of_true]; try ring_nf
  all_goals nth_rw 1 [← abs_neg]; ring_nf

/-- Bound a prob bind in terms of an intermediate event -/
lemma le_prob_bind_of_cut {f : Prob α} {g : α → Prob β} (x : α) {y : β} :
    f.prob x * (g x).prob y ≤ (f >>= g).prob y := by
  simp only [prob_bind]
  have p : ∀ x, 0 ≤ f.prob x * (g x).prob y := λ _ ↦ mul_nonneg (prob_nonneg _) (prob_nonneg _)
  by_cases m : x ∈ f.supp
  · exact @Finset.single_le_sum _ _ _ (λ x ↦ f.prob x * (g x).prob y) _ (λ _ _ ↦ p _) _ m
  · simp only [mem_iff, not_not] at m
    simp only [m, zero_mul]
    exact Finset.sum_nonneg (λ _ _ ↦ p _)

/-- `p.supp` is never empty -/
lemma card_supp_ne_zero (p : Prob α) : p.supp.card ≠ 0 := by
  have t := p.total
  contrapose t
  simp only [supp, ne_eq, Finset.card_eq_zero, Finsupp.support_eq_empty, not_not] at t
  simp only [t, Finsupp.sum_zero_index, zero_ne_one, not_false_eq_true]

/-- `p.supp` is never empty -/
lemma card_supp_pos (p : Prob α) : 0 < p.supp.card := by
  have h := p.card_supp_ne_zero
  omega

/-- `(pure x).supp` is a singleton -/
@[simp] lemma supp_pure (x : α) : (pure x : Prob α).supp = {x} := by
  ext y
  simp [supp, prob_pure]

/-- Pull a bind in the first part of an `if` to the outside -/
lemma if_bind_comm {c : Prop} {h : Decidable c} (x : Prob α) (y : α → Prob β) (z : Prob β) :
    ite c (h := h) (x >>= y) z = x >>= fun x ↦ ite c (h := h) (y x) z := by
  by_cases p : c
  all_goals simp only [p, ↓reduceIte, bind_const]

/-- All probabilities are 1 over subsingleton spaces -/
@[simp] lemma prob_eq_one [s : Subsingleton α] (p : Prob α) (x : α) : p.prob x = 1 := by
  have t := p.total
  have f := Fintype.ofSubsingleton x
  rwa [Finsupp.sum_fintype, Fintype.sum_subsingleton _ x] at t
  simp only [implies_true]

/-- `Prob` over singleton spaces is singleton -/
instance [Subsingleton α] : Subsingleton (Prob α) where
  allEq p q := by
    ext x
    simp only [prob_eq_one]

/-- `Prob` over unique spaces is unique -/
instance [Unique α] : Unique (Prob α) where
  default := pure default
  uniq p := by
    ext x
    simp only [prob_eq_one]

/-!
### Tactics
-/

/-- Move a `Prob` term to the front of a bind -/
macro "lift" f:term : tactic =>
  `(tactic| simp only [bind_comm _ $f, if_bind_comm $f])

/-- Strip off a bind term -/
macro "strip" x:term : tactic =>
  `(tactic|
  focus
    refine congr_arg₂ _ rfl ?_
    funext $x)
