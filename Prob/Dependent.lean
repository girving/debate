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
-/

/-- Sample from a bunch of `Prob`s in parallel (`Fin n` version) -/
def fin_pi : {n : ℕ} → {α : Fin n → Type} → ((x : Fin n) → Prob (α x)) → Prob (Π x, α x)
  | 0, _, _ => pure fun x ↦ x.elim0
  | _ + 1, _, f => do
    let p ← f 0
    let q ← fin_pi fun i ↦ f i.succ
    return Fin.cons p q

/-- Sample from a bunch of `Prob`s in parallel -/
def pi [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x)) : Prob (Π x, β x) := do
  let g ← fin_pi fun x ↦ f ((Fintype.equivFin α).symm x)
  return fun x ↦ (Fintype.equivFin α).symm_apply_apply x ▸ g ((Fintype.equivFin α) x)

/-- Sampling everything and then picking is equivalent to picking and then sampling the right one -/
@[simp] lemma fin_pi_exp {α : Fin n → Type} (f : (x : Fin n) → Prob (α x))
    (x : Fin n) (g : α x → V) : ((fin_pi f).exp fun y ↦ g (y x)) = (f x).exp g := by
  induction' n with n h
  · apply x.elim0
  · induction' x using Fin.induction
    all_goals simp only [h, Fin.cons_zero, Fin.cons_succ,  exp_const, fin_pi, exp_bind, exp_pure]

/-- Sampling everything and then picking is equivalent to picking and then sampling the right one -/
@[simp] lemma pi_exp [Fintype α] {β : α → Type} (f : (x : α) → Prob (β x))
    (x : α) (g : β x → V) : ((Prob.pi f).exp fun y ↦ g (y x)) = (f x).exp g := by
  simp only [Prob.pi, exp_bind, exp_pure]
  refine Eq.trans (fin_pi_exp (α := fun x ↦ β ((Fintype.equivFin α).symm x))
    (f := fun y ↦ f ((Fintype.equivFin α).symm y)) (x := Fintype.equivFin α x)
    (g := fun y ↦ g ((Fintype.equivFin α).symm_apply_apply x ▸ y))) ?_
  set e : (β ((Fintype.equivFin α).symm ((Fintype.equivFin α) x))) → β x :=
    fun y ↦ (Fintype.equivFin α).symm_apply_apply x ▸ y
  apply Finset.sum_of_injOn (e := e)
  · intro x _ y _; simp only [eq_rec_inj, imp_self, e]
  · intro y m
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq, e] at m ⊢
    convert m
    all_goals simp only [e, Equiv.symm_apply_apply, eqRec_heq_iff_heq, heq_eq_eq]
  · intro y m n
    contrapose n
    simp [e] at m ⊢
    use (Fintype.equivFin α).symm_apply_apply _ ▸ y
    constructor
    · convert m
      all_goals simp only [e, Equiv.symm_apply_apply, eqRec_heq_iff_heq, heq_eq_eq]
    · apply eq_of_heq
      simp only [eqRec_heq_iff_heq, heq_self_iff_true]
  · intro y m
    apply congr_arg₂
    · convert rfl
      all_goals simp only [e, Equiv.symm_apply_apply, eqRec_heq_iff_heq, heq_eq_eq]
    · all_goals simp only [e, Equiv.symm_apply_apply, eqRec_heq_iff_heq, heq_eq_eq]

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
