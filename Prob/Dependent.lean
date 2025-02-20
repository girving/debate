import Mathlib.Tactic.Bound
import Prob.Arith

/-!
## Dependently typed operations on `Prob`

We define the `Prob` analogues of `Π` and `Σ`:

1. `Prob.pi`: Given a finite map `(x : α) → Prob (β x)`, sample all the `Prob`s in parallel
2. `Prob.dbind`: Turn `p : Prob α` and `q : (x : α) → Prob (β x)` into `Prob (Σ x, β x)`

`Prob.dbind` is an extension of `Prob.bind` (normal monadic bind), since normal bind requires a
fixed return type independent of the intermediate value.
-/

open Classical
open scoped Real
noncomputable section
namespace Prob

variable {n : ℕ}
variable {α β γ : Type}
variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-!
### `Prob.pi`: Sample from a bunch of `Prob`s in parallel

We also define a `Finset`-restricted version, `Prob.set_pi`. This is also needed to prove things
about `pi` via induction down from `Finset.univ`.
-/

/-- The `prob` for `pi` below -/
def pi_prob [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x)) : (Π x, β x) →₀ ℝ where
  toFun g := ∏ x, (f x).prob (g x)
  support := Fintype.piFinset fun x ↦ (f x).supp
  mem_support_toFun g := by simp [mem_iff, Finset.prod_eq_zero_iff]

/-- The `prob` for `set_pi` below -/
def set_pi_prob {β : α → Type} (s : Finset α) (f : (x : α) → Prob (β x)) : (Π x ∈ s, β x) →₀ ℝ where
  toFun g := ∏ x ∈ s.attach, (f x).prob (g x x.2)
  support := Finset.pi s fun x ↦ (f x).supp
  mem_support_toFun g := by simp [mem_iff, Finset.prod_eq_zero_iff]

/-- Sample from a bunch of `Prob`s in parallel -/
def pi [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x)) : Prob (Π x, β x) where
  prob := pi_prob f
  prob_nonneg := by
    simp only [pi_prob, Finsupp.coe_mk]
    bound
  total := by
    have e : ∀ x, ∑ j ∈ (f x).supp, (f x).prob j = 1 := fun x ↦ (f x).total
    simp [pi_prob, Finsupp.sum, ← Finset.prod_univ_sum, e]

/-- Sample from a bunch of `Prob`s in parallel, restricting to a `Finset` -/
def set_pi {β : α → Type} (s : Finset α) (f : (x : α) → Prob (β x)) : Prob (Π x ∈ s, β x) where
  prob := set_pi_prob s f
  prob_nonneg := by
    simp only [set_pi_prob, Finsupp.coe_mk]
    bound
  total := by
    have e : ∀ x, ∑ j ∈ (f x).supp, (f x).prob j = 1 := fun x ↦ (f x).total
    simp [set_pi_prob, Finsupp.sum, e, ← Finset.prod_sum (f := fun x (y : β x) ↦ (f x).prob y)]

/-- `pi` probs are products of probs -/
lemma prob_pi [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x)) (g : Π x, β x) :
    (pi f).prob g = ∏ x, (f x).prob (g x) := rfl

/-- `set_pi` probs are products of probs -/
lemma prob_set_pi {β : α → Type} (s : Finset α) (f : (x : α) → Prob (β x)) (g : Π x ∈ s, β x) :
    (set_pi s f).prob g = ∏ x : s, (f x).prob (g x x.2) := rfl

/-- Convert an expectation over `pi` to one over `set_pi` -/
lemma exp_pi_eq_exp_set_pi [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x))
    (g : (Π x, β x) → V) : (Prob.pi f).exp g =
      (Prob.set_pi .univ f).exp fun h ↦ g fun x ↦ h x (Finset.mem_univ x) := by
  simp only [exp, Finsupp.sum]
  apply Finset.sum_of_injOn (e := fun g ↦ fun x _ ↦ g x)
  · intro _ _ _ _ e
    simpa [funext_iff] using e
  · intro g m
    simpa [prob_pi, prob_set_pi] using m
  · intro g m n
    simp only [Finsupp.mem_support_iff, prob_set_pi, Finset.univ_eq_attach, Finset.prod_attach_univ,
      ne_eq, Set.mem_image, Finset.mem_coe, prob_pi, not_exists, not_and, smul_eq_zero] at m n ⊢
    specialize n (fun x ↦ g x (Finset.mem_univ x)) m
    simp at n
  · intros
    simp [prob_pi, prob_set_pi]

/-- Unravel an expectation over `set_pi (insert x s)` -/
lemma exp_set_pi_insert {β : α → Type} {a : α} {s : Finset α} (m : a ∉ s)
    (f : (x : α) → Prob (β x)) (g : (Π x ∈ insert a s, β x) → V) :
    (set_pi (insert a s) f).exp g = (f a).exp fun y ↦ (set_pi s f).exp fun z ↦
      g (Finset.Pi.cons s a y z) := by
  simp only [exp, Finsupp.sum, prob_set_pi]
  simp only [set_pi, set_pi_prob]
  simp only [Finset.univ_eq_attach, Finset.prod_attach_insert m, Finset.sum_pi_insert m, Prob.supp,
    Finset.Pi.cons_same, ← smul_smul, ← Finset.smul_sum, Finset.Pi.cons_mem m]

/-- Peel off the first element of `pi` over `Fin (n + 1)` -/
lemma exp_pi_fin_succ {n : ℕ} {β : Fin (n + 1) → Type} (f : (x : Fin (n + 1)) → Prob (β x))
    (g : (Π x, β x) → V) :
    (Prob.pi f).exp g = (f 0).exp fun y ↦ (Prob.pi (Fin.tail f)).exp fun z ↦ g (Fin.cons y z) := by
  simp only [exp, Finsupp.sum, prob_pi, Fin.prod_univ_succ, ← smul_smul]
  have e : (pi f).prob.support = Finset.image (fun ⟨x,y⟩ ↦ Fin.cons x y)
      ((f 0).prob.support ×ˢ (pi (Fin.tail f)).prob.support) := by
    ext g
    simp only [Finsupp.mem_support_iff, Finset.mem_image, Finset.mem_product, Prod.exists, prob_pi,
      Fin.prod_univ_succ, mul_ne_zero_iff]
    constructor
    · intro ⟨a,b⟩
      exact ⟨g 0, Fin.tail g, ⟨a,b⟩, Fin.cons_self_tail _⟩
    · intro ⟨x,y,⟨px,py⟩,e⟩
      simp only [← e, Fin.cons_zero, ne_eq, Fin.cons_succ]
      exact ⟨px, py⟩
  rw [e, Finset.sum_image, Finset.sum_product]
  · simp only [Fin.cons_zero, Fin.cons_succ, ← Finset.smul_sum]
    rfl
  · aesop

/-- Induction principle for `x ∈ Finset.insert a s`, to make dependent-typed situations easier -/
lemma Finset.induction_mem_insert (a : α) (s : Finset α) {p : (x : α) → x ∈ insert a s → Prop}
    (same : p a (Finset.mem_insert_self a s))
    (diff : ∀ x (m : x ∈ s), p x (Finset.mem_insert_of_mem m))
    (x : α) (m : x ∈ insert a s) : p x m := by
  cases' Finset.mem_insert.mp m with e m
  · exact e ▸ same
  · exact diff x m

/-- Sampling everything and then picking is equivalent to picking and then sampling the right one -/
@[simp] lemma set_pi_exp {β : α → Type} (s : Finset α) (f : (x : α) → Prob (β x)) (x : α)
    (m : x ∈ s) (g : β x → V) : ((Prob.set_pi s f).exp fun y ↦ g (y x m)) = (f x).exp g := by
  induction' s using Finset.induction_on with a s n h
  · simp at m
  · simp only [exp_set_pi_insert n]
    induction' x, m using Finset.induction_mem_insert with x m generalising g h
    · simp
    · have ax : a ≠ x := by aesop
      simp [Finset.Pi.cons_ne ax, h]

/-- Sampling everything and then picking is equivalent to picking and then sampling the right one -/
@[simp] lemma pi_exp [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x))
    (x : α) (g : β x → V) : ((Prob.pi f).exp fun y ↦ g (y x)) = (f x).exp g := by
  simp only [exp_pi_eq_exp_set_pi, set_pi_exp]

/-- Sampling everything and then picking is equivalent to picking and then sampling the right one -/
@[simp] lemma pi_bind [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x))
    (x : α) (g : β x → Prob γ) : (Prob.pi f >>= fun y ↦ g (y x)) = f x >>= g := by
  ext z
  simp only [prob_bind]
  apply pi_exp (g := fun y ↦ (g y).prob z)

/-!
### Dependent bind for `Prob`
-/

/-- Version of `bind` that supports dependently typed results -/
def dbind (p : Prob α) {β : α → Type} (q : (x : α) → Prob (β x)) : Prob (Σ x, β x) where
  prob := p.prob.sum fun x p ↦ p • (q x).prob.mapDomain fun y ↦ ⟨x,y⟩
  prob_nonneg := by
    intro x
    simp only [Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.mapDomain]
    refine Finset.sum_nonneg fun _ _ ↦ mul_nonneg p.prob_nonneg (Finset.sum_nonneg fun _ _ ↦ ?_)
    simp only [Finsupp.single_apply, apply_ite, prob_nonneg, le_refl, ite_self]
  total := by
    have e : ∀ (p : ℝ) (x : α), (p • (q x).prob.mapDomain fun y ↦ (⟨x,y⟩ : Σ x, β x)).sum
        (fun _ q ↦ q) = p := by
      intro p x
      rw [Finsupp.sum_smul_index, ← Finsupp.mul_sum, Finsupp.mapDomain, Finsupp.sum_sum_index]
      all_goals simp only [Finsupp.sum_single_index, total, mul_one, implies_true]
    rw [Finsupp.sum_sum_index]
    all_goals simp only [e, Prob.total, implies_true]

/-- `dbind` probabilities are easy, so we know both elements -/
lemma prob_dbind (p : Prob α) {β : α → Type} (q : (x : α) → Prob (β x)) (z : Σ x, β x) :
    (p.dbind q).prob z = p.prob z.1 * (q z.1).prob z.2 := by
  simp only [Prob.dbind, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.coe_smul, Finsupp.coe_sum,
    Pi.smul_apply, Finsupp.sum_apply', Finsupp.single_apply, Sigma.ext_iff, smul_eq_mul]
  rw [Finsupp.sum_eq_single (a := z.1)]
  all_goals aesop

/-- `dbind` expectations look like normal expectations -/
lemma exp_dbind (p : Prob α) {β : α → Type} (q : (x : α) → Prob (β x)) (h : (Σ x, β x) → V) :
    (p.dbind q).exp h = p.exp fun x ↦ (q x).exp fun y ↦ h ⟨x,y⟩ := by
  simp only [Prob.exp, dbind, Finsupp.mapDomain]
  rw [Finsupp.sum_sum_index]
  refine Finsupp.sum_congr fun x _ ↦ ?_
  simp only [Finsupp.smul_sum, Finsupp.smul_single, smul_eq_mul]
  rw [Finsupp.sum_sum_index]
  refine Finsupp.sum_congr fun y _ ↦ ?_
  all_goals simp only [add_smul, zero_smul, implies_true, smul_smul, Finsupp.sum_single_index]

/-- Reassociate `dbind` and `bind` into two `bind`s -/
lemma dbind_bind_assoc (p : Prob α) {β : α → Type} (q : (x : α) → Prob (β x))
    (r : (Σ x, β x) → Prob γ) : p.dbind q >>= r = p >>= fun x ↦ (q x) >>= fun y ↦ r ⟨x,y⟩ := by
  ext z
  simp only [prob_bind, exp_dbind]
