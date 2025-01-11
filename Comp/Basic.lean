import Comp.Oracle
import Comp.Defs
import Prob.Arith
import Prob.Estimate

/-!
## Basic properties of `Comp`
-/

open Classical
open Prob
open Option (some none)
open scoped Real
noncomputable section

variable {n : ℕ}
variable {ι I : Type}
variable {s t u : Set I}
variable {α β γ : Type}

namespace Comp

lemma map_eq (f : α → β) (x : Comp ι s α) : f <$> x = x >>= (λ x ↦ pure (f x)) := rfl

/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp ι s) := LawfulMonad.mk'
  (id_map := by
    intro α f
    simp only [map_eq, id, bind, bind']
    induction' f with x β f g h o m y f0 f1 h0 h1
    · rfl
    · simp only [bind', sample'.injEq, heq_eq_eq, true_and]; ext y; apply h
    · simp only [bind', h0, h1])
  (pure_bind := by intro α β x f; simp only [bind, bind'])
  (bind_assoc := by
    intro α β β f g h
    simp only [bind]
    induction' f with x β f g h o m y f0 f1 h0 h1
    · rfl
    · simp only [bind', sample'.injEq, heq_eq_eq, true_and, h]
    · simp only [bind', h0, h1])

/-- Running a `pure'` is `pure` -/
@[simp] lemma prob_pure' (x : α) (o : I → Oracle ι) : (pure' x : Comp ι s α).prob o = pure x := by
  simp only [prob, run, map_pure]

-- The definition of `Comp.bind` as `simp` lemmas
@[simp] lemma pure'_bind (x : α) (f : α → Comp ι s β) : (pure' x : Comp ι s α) >>= f = f x := rfl
@[simp] lemma sample'_bind (f : Prob (Fin n)) (g : Fin n → Comp ι s β) (h : β → Comp ι s γ) :
    sample' f g >>= h = .sample' f fun x ↦ g x >>= h := rfl
@[simp] lemma sample_bind (f : Prob α) (g : α → Comp ι s β) (h : β → Comp ι s γ) :
    sample f g >>= h = .sample f fun x ↦ g x >>= h := rfl
@[simp] lemma query'_bind (o : I) (m : o ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (g : α → Comp ι s β) : query' o m y f0 f1 >>= g = .query' o m y (f0 >>= g) (f1 >>= g) := rfl

-- The definition of `Comp.allow` as `simp` lemmas
@[simp] lemma allow_pure' (x : α) (st : s ⊆ t) : (pure' x : Comp ι s α).allow st = pure x := rfl
@[simp] lemma allow_sample' (f : Prob (Fin n)) (g : Fin n → Comp ι s α) (st : s ⊆ t) :
    (sample' f g).allow st = sample' f fun x ↦ (g x).allow st := rfl
@[simp] lemma allow_query' (i : I) (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α) (st : s ⊆ t) :
    (query' i m y f0 f1).allow st = query' i (st m) y (f0.allow st) (f1.allow st) := rfl

/-- Cost is nonnegative -/
@[simp] lemma cost_nonneg {f : Comp ι s α} {o : I → Oracle ι} {i : I} : 0 ≤ f.cost o i := by
  apply exp_nonneg; simp only [ne_eq, Nat.cast_nonneg, implies_true, Prod.forall, forall_const]

/-!
## `Comp.run` commutes with various things
-/

@[simp] lemma run_pure' (x : α) (o : I → Oracle ι) :
    (Comp.pure' x : Comp ι s α).run o = pure (x, fun _ ↦ 0) := by
  simp only [Comp.run]

@[simp] lemma run_pure (x : α) (o : I → Oracle ι) :
    (pure x : Comp ι s α).run o = pure (x, fun _ ↦ 0) := by
  simp only [pure, Comp.run]

@[simp] lemma run_sample' (f : Prob (Fin n)) (g : Fin n → Comp ι s β) (o : I → Oracle ι) :
    (sample' f g).run o = f >>= fun x ↦ (g x).run o := by
  simp only [pure, Comp.run]

@[simp] lemma run_sample (f : Prob α) (g : α → Comp ι s β) (o : I → Oracle ι) :
    (Comp.sample f g).run o = f >>= fun x ↦ (g x).run o := by
  simp only [sample, run, Function.comp_apply, bind_fin f fun x ↦ (g x).run o]

lemma run_query' {i : I} (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) : (Comp.query' i m y f0 f1).run o = do
      let x ← (o i) y
      let (z,c) ← if x then f0.run o else f1.run o
      return (z, c + fun j => if j = i then 1 else 0) := by
  rfl

/-- Coersion of `Prob` matches `run` -/
@[simp] lemma run_coe (f : Prob α) (o : I → Oracle ι) : (f : Comp ι s α).prob o = f := by
  simp only [prob, run, bind_pure_comp, Functor.map_map, map_fin, run_sample, id_map']

@[simp] lemma run_bind (f : Comp ι s α) (g : α → Comp ι s β) (o : I → Oracle ι) :
    (f >>= g).run o = f.run o >>= fun (x,c) ↦ (fun (y,c') ↦ (y, c + c')) <$> (g x).run o := by
  induction' f with x β f g' h j m y f0 f1 h0 h1
  · simp only [pure'_bind, run_pure', Pi.add_def, pure_bind, zero_add, Prod.mk.eta, id_map']
  · have e : ∀ x, bind' (g' x) g = g' x >>= g := fun _ ↦ rfl
    simp only [sample'_bind, run_sample', h, bind_assoc]
  · have e : ∀ h, bind' h g = h >>= g := fun _ ↦ rfl
    simp only [run_query', query'_bind, e, h0, bind_assoc, h1, Prob.map_eq]
    refine congr_arg₂ _ rfl ?_
    funext b
    induction b
    all_goals simp only [ite_false, ite_true, bind_assoc, pure_bind, Pi.add_def, add_comm,
      add_assoc, Bool.false_eq_true]

@[simp] lemma run_allow (f : Comp ι s α) (st : s ⊆ t) (o : I → Oracle ι) :
    (f.allow st).run o = f.run o := by
  induction' f with x β f g h j _ y f0 f1 h0 h1
  · simp only [allow, run_pure, run_pure']
  · simp only [run_sample', allow_sample', bind', h, Prob.bind_fin f (fun x ↦ (g x).run o)]
  · simp only [allow_query', run_query', h0, h1]

@[simp] lemma run_allow_all (f : Comp ι s α) (o : I → Oracle ι) : f.allow_all.run o = f.run o := by
  apply run_allow

@[simp] lemma prob_sample' (f : Prob (Fin n)) (g : Fin n → Comp ι s β) (o : I → Oracle ι) :
    (Comp.sample' f g).prob o = f >>= fun x ↦ (g x).prob o  := by
  simp only [prob, run, map_bind, map_pure, bind_pure]

/-!
## `Comp.cost` commutes with various things
-/

/-- `pure` is free -/
@[simp] lemma cost_pure (x : α) (o : I → Oracle ι) (i : I) : (pure x : Comp ι s α).cost o i = 0 := by
  simp only [cost, run, exp_pure, Nat.cast_zero]

/-- `pure` is free -/
@[simp] lemma cost'_pure (x : α) (o : Oracle ι) (i : I) : (pure x : Comp ι s α).cost' o i = 0 := by
  simp only [cost', cost_pure]

/-- `pure'` is free -/
@[simp] lemma cost_pure' (x : α) (o : I → Oracle ι) (i : I) :
    (Comp.pure' x : Comp ι s α).cost o i = 0 := by
  simp only [cost, run, exp_pure, Nat.cast_zero]

/-- `pure'` is free -/
@[simp] lemma cost'_pure' (x : α) (o : Oracle ι) (i : I) :
    (Comp.pure' x : Comp ι s α).cost' o i = 0 := by
  simp only [cost', cost_pure']

/-- `sample'` cost's is the expected follow-on cost -/
@[simp] lemma cost_sample' (f : Prob (Fin n)) (g : Fin n → Comp ι s β) (o : I → Oracle ι) (i : I) :
    (Comp.sample' f g).cost o i = f.exp (fun x ↦ (g x).cost o i) := by
  simp only [cost, run, exp_bind, Nat.cast_zero]

/-- `sample'` cost's is the expected follow-on cost -/
@[simp] lemma cost_sample (f : Prob (Fin n)) (g : Fin n → Comp ι s β) (o : I → Oracle ι) (i : I) :
    (Comp.sample f g).cost o i = f.exp (fun x ↦ (g x).cost o i) := by
  simp only [cost, run_sample, exp_bind, Nat.cast_zero, Prob.fin, exp_map, Function.comp_def]

/-- `sample'` cost's is the expected follow-on cost -/
@[simp] lemma cost'_sample (f : Prob (Fin n)) (g : (Fin n) → Comp ι s β) (o : Oracle ι) (i : I) :
    (Comp.sample' f g).cost' o i = f.exp (fun x ↦ (g x).cost' o i) := by
  simp only [cost', cost_sample']

/-- `query'` costs one query, plus the rest -/
@[simp] lemma cost_query' {i : I} (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) (j : I) :
    (Comp.query' i m y f0 f1).cost o j =
      (if j = i then 1 else 0) +
      (o i y).exp (fun x ↦ if x then f0.cost o j else f1.cost o j) := by
  simp only [cost, run, exp_bind, Nat.cast_zero]
  rw [←exp_const_add]
  refine exp_congr fun x _ ↦ ?_
  induction x
  all_goals simp only [ite_false, ite_true, exp_bind, exp_pure, Pi.add_apply, Nat.cast_add,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, exp_add, exp_const, add_comm, Bool.false_eq_true]

/-- `query` makes one query -/
@[simp] lemma cost_query (i : I) (y : ι) (o : I → Oracle ι) :
    (query i y).cost o i = 1 := by
  simp only [query, cost_query', ite_true, cost_pure, ite_self, exp_const, add_zero]

/-- Non-oracle computations are free -/
@[simp] lemma cost_coe (f : Prob α) (o : I → Oracle ι) (i : I) : (f : Comp ι s α).cost o i = 0 := by
  simp only [cost_sample', Function.comp_apply, cost_pure, exp_const, sample]

/-- Oracles we can't query don't get queried -/
lemma cost_of_not_mem (f : Comp ι s α) (o : I → Oracle ι) {i : I} (is : i ∉ s) :
    f.cost o i = 0 := by
  induction' f with x β f g h j js y f0 f1 h0 h1
  · simp only [cost_pure']
  · simp only [cost_sample', h, exp_const]
  · simp only [cost_query', h0, h1, ite_self, exp_const, add_zero]
    by_cases ij : i = j
    · simp only [ij] at is; simp only [js, not_true_eq_false] at is
    · simp only [ij, if_false]

/-- The cost of `f >>= g` is roughly `f.cost + g.cost` -/
lemma cost_bind (f : Comp ι s α) (g : α → Comp ι s β) (o : I → Oracle ι) (i : I) :
    (f >>= g).cost o i = f.cost o i + (f.prob o).exp (fun x ↦ (g x).cost o i) := by
  induction' f with x β f g h j m y f0 f1 h0 h1
  · simp only [cost_pure', zero_add, prob_pure, exp_pure, prob_pure', bind, bind']
  · simp only [bind, bind'] at h
    simp only [cost_sample', bind, bind', h, exp_add]
    apply congr_arg₂ _ rfl
    simp only [prob_sample', exp_bind]
  · simp only [bind, bind'] at h0 h1
    simp only [cost_query', bind, bind', prob, add_assoc, h0, h1]
    apply congr_arg₂ _ rfl
    simp only [run_query', bind_pure_comp, map_bind, exp_bind, ← exp_add]
    refine exp_congr fun x _ ↦ ?_
    induction x
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, exp_map, Function.comp_def,
      Functor.map_map]

/-- Map doesn't change `cost` -/
@[simp] lemma cost_map (f : α → β) (g : Comp ι s α) (o : I → Oracle ι) (i : I) :
    (f <$> g).cost o i = g.cost o i := by
  simp only [map_eq, cost_bind, cost_pure, exp_const, add_zero]

/-- If an oracle isn't allowed, its cost is zero -/
lemma cost_eq_zero {f : Comp ι s α} {i : I} (m : i ∉ s) (o : I → Oracle ι) : f.cost o i = 0 := by
  induction' f with x β f g h j mj y f0 f1 h0 h1
  · simp only [cost_pure']
  · simp only [cost_sample', h, exp_const]
  · simp only [cost_query', h0, h1, ite_self, exp_const, add_zero, ite_eq_right_iff, one_ne_zero]
    intro e; rw [e] at m; exact m mj

/-- `count` multiplies cost by `n` -/
@[simp] lemma cost_count (f : Comp ι s Bool) (n : ℕ) (o : I → Oracle ι) (i : I) :
    (count f n).cost o i = n * (f.cost o i) := by
  induction' n with n h
  · simp only [Nat.zero_eq, count_zero, cost_pure, Nat.cast_zero, zero_mul]
  · simp only [count, add_comm, cost_bind, h, cost_pure, exp_const, add_zero, Nat.cast_succ,
      add_mul, one_mul]

/-- `estimate` multiplies cost by `n` -/
@[simp] lemma cost_estimate (f : Comp ι s Bool) (n : ℕ) (o : I → Oracle ι) (i : I) :
    (estimate f n).cost o i = n * (f.cost o i) := by
  simp only [estimate, cost_map, cost_count]

/-!
## `Comp.prob` commutes with various things
-/

@[simp] lemma prob_pure (x : α) (o : I → Oracle ι) : (pure x : Comp ι s α).prob o = pure x := by
  simp only [pure, prob_pure']

@[simp] lemma prob_query' (i : I) (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) :
    (query' i m y f0 f1).prob o = (do if ←o i y then f0.prob o else f1.prob o) := by
  simp only [prob, Prob.map_eq, run, bind_assoc]
  apply congr_arg₂ _ rfl; funext y; induction y
  all_goals simp only [ite_false, ite_true, bind_assoc, pure_bind, Bool.false_eq_true]

@[simp] lemma prob_query (i : I) (y : ι) (o : I → Oracle ι) :
    (query i y).prob o = o i y := by
  have e : ∀ y : Bool, (if y = true then pure true else pure false) = (pure y : Prob Bool) := by
    intro y; induction y; simp only [ite_false, Bool.false_eq_true]; simp only [ite_true]
  simp only [query, prob_query', prob_pure, e, bind_pure]

@[simp] lemma prob_bind (f : Comp ι s α) (g : α → Comp ι s β) (o : I → Oracle ι) :
    (f >>= g).prob o = f.prob o >>= fun x ↦ (g x).prob o := by
  induction' f with x β f g h j m y f0 f1 h0 h1
  · simp only [pure'_bind, prob_pure', pure_bind]
  · simp only [sample'_bind, prob_sample', h, bind_assoc]
  · simp only [query'_bind, prob_query', h0, h1, bind_assoc]
    apply congr_arg₂ _ rfl; funext y; induction y
    all_goals simp only [ite_false, ite_true, Bool.false_eq_true]

@[simp] lemma prob_map (f : α → β) (g : Comp ι s α) (o : I → Oracle ι) :
    (f <$> g).prob o = f <$> g.prob o := by
  simp only [Comp.map_eq, prob_bind, prob_pure, Prob.map_eq]

@[simp] lemma prob_sample (f : Prob α) (g : α → Comp ι s β) (o : I → Oracle ι) :
    (Comp.sample f g).prob o = f >>= fun x ↦ (g x).prob o  := by
  simp only [prob, run, Function.comp_apply, map_bind, bind_fin f fun x ↦ Prod.fst <$> (g x).run o,
    run_sample]

@[simp] lemma prob_count (f : Comp ι s Bool) (n : ℕ) (o : I → Oracle ι) :
    (count f n).prob o = count (f.prob o) n := by
  induction' n with n h
  · simp only [count, prob_pure]
  · simp only [count, prob_bind, h, prob_pure]

@[simp] lemma prob_estimate (f : Comp ι s Bool) (n : ℕ) (o : I → Oracle ι) :
    (estimate f n).prob o = estimate (f.prob o) n := by
  simp only [estimate, prob_map, prob_count]

/-!
## `allow` and `allow_all` don't change `.prob` or `.cost`
-/

@[simp] lemma prob_allow (f : Comp ι s α) (st : s ⊆ t) (o : I → Oracle ι) :
    (f.allow st).prob o = f.prob o := by
  induction' f with x β f g h j m y f0 f1 h0 h1
  · simp only [prob_pure', allow, prob_pure]
  · simp only [allow, sample_bind, pure_bind, prob_sample, prob_sample', h]
  · simp only [allow, prob_query', h0, h1]

@[simp] lemma prob_allow_all (f : Comp ι s α) (o : I → Oracle ι) :
    f.allow_all.prob o = f.prob o := by
  apply prob_allow

@[simp] lemma cost_allow (f : Comp ι s α) (st : s ⊆ t) (o : I → Oracle ι) (i : I) :
    (f.allow st).cost o i = f.cost o i := by
  induction' f with x β f g h j m y f0 f1 h0 h1
  · simp only [allow, cost_pure, cost_pure']
  · simp only [allow, sample_bind, pure_bind, cost_sample, h, cost_sample']
  · simp only [allow, cost_query', h0, h1]

@[simp] lemma cost_allow_all (f : Comp ι s α) (o : I → Oracle ι) (i : I) :
    f.allow_all.cost o i = f.cost o i := by
  apply cost_allow

@[simp] lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : Comp ι s α).allow st = pure x := by
  simp only [allow]

@[simp] lemma allow_all_pure (x : α) : (pure x : Comp ι s α).allow_all = pure x := by
  simp only [allow_all, allow_pure]

@[simp] lemma allow_bind (f : Comp ι s α) (g : α → Comp ι s β) (st : s ⊆ t) :
    (f >>= g).allow st = f.allow st >>= fun x ↦ (g x).allow st := by
  have e : ∀ v, bind' v g = v >>= g := fun _ ↦ rfl
  induction' f with x β u v h j m y f0 f1 h0 h1
  · simp only [pure'_bind, allow, pure_bind]
  · simp only [allow, e, h, sample'_bind]
  · simp only [allow, e, h0, h1, query'_bind]

@[simp] lemma allow_sample (p : Prob α) (f : α → Comp ι s β) (st : s ⊆ t) :
    (sample p f).allow st = sample p (fun x ↦ (f x).allow st) := rfl

@[simp] lemma allow_all_bind (f : Comp ι s α) (g : α → Comp ι s β) :
    (f >>= g).allow_all = f.allow_all >>= fun x ↦ (g x).allow_all :=
  allow_bind f g _

@[simp] lemma allow_allow (f : Comp ι s α) (st : s ⊆ t) (tu : t ⊆ u) :
    (f.allow st).allow tu = f.allow (st.trans tu) := by
  induction' f with x β u v h j m y f0 f1 h0 h1
  · simp only [allow]
  · simp only [allow, bind', h, sample'_bind, pure_bind]
  · simp only [allow, h0, h1]

@[simp] lemma allow_all_allow (f : Comp ι s α) (st : s ⊆ t) :
    (f.allow st).allow_all = f.allow_all := by
  simp only [allow_all, allow_allow]

end Comp

/-!
### `Comp` tactics
-/

/-- Show `i ∉ s` via `simp` -/
macro "not_mem" : tactic =>
  `(tactic| simp only [Set.mem_singleton_iff, Set.mem_insert_iff, or_self, not_false_eq_true,
    not_false, reduceCtorEq])

/-- Show `s ⊆ t` via `simp` -/
macro "subset" : tactic =>
  `(tactic| simp only [Set.mem_singleton_iff, Set.singleton_subset_iff, Set.mem_insert_iff,
    or_false, false_or, true_or, or_true])

/-- Show a cost is zero via `i : I` not being in `s` -/
macro "zero_cost" : tactic =>
  `(tactic|
  focus
    try simp only [Comp.cost_allow_all]
    rw [Comp.cost_eq_zero]
    not_mem)
