import DComp.Basic
import Prob.Estimate

/-!
## Basic properties of `DComp`
-/

open Classical
open Option (some none)
open scoped Real
noncomputable section

variable {n : ℕ}
variable {ι I : Type}
variable {ω : ι → Type}
variable {s t u : Set I}
variable {α β γ : Type}

namespace DComp

lemma map_eq (f : α → β) (x : DComp ι ω s α) : f <$> x = x >>= (fun x ↦ pure (f x)) := rfl

/-- `DComp` is a lawful monad -/
instance : LawfulMonad (DComp ι ω s) := LawfulMonad.mk'
  (id_map := by
    intro α f
    simp only [map_eq, id, bind, bind']
    induction' f with x o m y f h
    · rfl
    · simp only [bind', h])
  (pure_bind := by intro α β x f; simp only [bind, bind'])
  (bind_assoc := by
    intro α β β f g h
    simp only [bind]
    induction' f with x o m y f h
    · rfl
    · simp only [bind', h])

/-- Running a `pure'` unwraps it` -/
@[simp] lemma value_pure' (x : α) (o : I → (x : ι) → ω x) :
    (pure' x : DComp ι ω s α).value o = x := by
  simp only [value, run, map_pure]

-- The definition of `DComp.bind` as `simp` lemmas
@[simp] lemma pure'_bind (x : α) (f : α → DComp ι ω s β) : (pure' x : DComp ι ω s α) >>= f = f x :=
  rfl
@[simp] lemma query'_bind (o : I) (m : o ∈ s) (y : ι) (f : ω y → DComp ι ω s α)
    (g : α → DComp ι ω s β) : query' o m y f >>= g = .query' o m y fun x ↦ (f x) >>= g := rfl

-- Basic facts about map
@[simp] lemma map_query' (f : α → β) (i : I) (m : i ∈ s) (y : ι) (g : ω y → DComp ι ω s α) :
    f <$> query' i m y g = query' i m y fun x ↦ f <$> (g x) := rfl

-- The definition of `DComp.allow` as `simp` lemmas
@[simp] lemma allow_pure' (x : α) (st : s ⊆ t) : (pure' x : DComp ι ω s α).allow st = pure x := rfl
@[simp] lemma allow_query' (i : I) (m : i ∈ s) (y : ι) (f : ω y → DComp ι ω s α) (st : s ⊆ t) :
    (query' i m y f).allow st = query' i (st m) y fun x ↦ (f x).allow st := rfl

/-!
## `DComp.run` commutes with various things
-/

@[simp] lemma run_pure' (x : α) (o : I → (x : ι) → ω x) :
    (.pure' x : DComp ι ω s α).run o = (x, fun _ ↦ 0) := by
  simp only [run, map_pure]

@[simp] lemma run_pure (x : α) (o : I → (x : ι) → ω x) :
    (pure x : DComp ι ω s α).run o = (x, fun _ ↦ 0) := by
  simp only [run, map_pure]

lemma run_query' {i : I} (m : i ∈ s) (y : ι) (f : ω y → DComp ι ω s α)
    (o : I → (x : ι) → ω x) : (query' i m y f).run o =
      let x := o i y
      let (z,c) := (f x).run o
      (z, c + fun j => if j = i then 1 else 0) := by
  rfl

@[simp] lemma run_bind (f : DComp ι ω s α) (g : α → DComp ι ω s β) (o : I → (x : ι) → ω x) :
    (f >>= g).run o = let (x,c) := f.run o; let (y,c') := (g x).run o; (y, c + c') := by
  induction' f with x j m y f h
  · simp only [pure'_bind, run_pure', Pi.add_def, zero_add, Prod.mk.eta]
  · have e : ∀ h, bind' h g = h >>= g := fun _ ↦ rfl
    simp only [run_query', query'_bind, e, h, bind_assoc, Prob.map_eq]
    refine congr_arg₂ _ rfl ?_
    funext b
    simp only [Pi.add_def, Pi.add_apply, add_comm, add_assoc]

@[simp] lemma run_allow (f : DComp ι ω s α) (st : s ⊆ t) (o : I → (x : ι) → ω x) :
    (f.allow st).run o = f.run o := by
  induction' f with x j _ y f h
  · simp only [allow, run_pure, run_pure']
  · simp only [allow_query', run_query', h]

@[simp] lemma run_allow_all (f : DComp ι ω s α) (o : I → (x : ι) → ω x) :
    (f.allow_all).run o = f.run o := by
  apply run_allow

/-!
## `DComp.cost` commutes with various things
-/

/-- `pure` is free -/
@[simp] lemma cost_pure (x : α) (o : I → (x : ι) → ω x) (i : I) :
    (pure x : DComp ι ω s α).cost o i = 0 := by
  simp only [cost, run]

/-- `pure` is free -/
@[simp] lemma cost'_pure (x : α) (o : I → (x : ι) → ω x) (i : I) :
    (pure x : DComp ι ω s α).cost' o i = 0 := by
  simp only [cost', run_pure]

/-- `pure'` is free -/
@[simp] lemma cost_pure' (x : α) (o : I → (x : ι) → ω x) (i : I) :
    (pure' x : DComp ι ω s α).cost o i = 0 := by
  simp only [cost, run]

/-- `pure'` is free -/
@[simp] lemma cost'_pure' (x : α) (o : I → (x : ι) → ω x) (i : I) :
    (pure' x : DComp ι ω s α).cost' o i = 0 := by
  simp only [cost', run_pure']

/-- `query'` costs one query, plus the rest -/
@[simp] lemma cost_query' {i : I} (m : i ∈ s) (y : ι) (f : ω y → DComp ι ω s α)
    (o : I → (x : ι) → ω x) (j : I) :
    (query' i m y f).cost o j = (if j = i then 1 else 0) + (f (o i y)).cost o j := by
  simp only [cost, run, Pi.add_apply, add_comm]

/-- `query` makes one query -/
@[simp] lemma cost_query (i : I) (y : ι) (o : I → (x : ι) → ω x) :
    (query i y).cost o i = 1 := by
  simp only [query, cost_query', ite_true, cost_pure, ite_self, add_zero]

/-- Oracles we can't query don't get queried -/
lemma cost_of_not_mem (f : DComp ι ω s α) (o : I → (x : ι) → ω x) {i : I} (is : i ∉ s) :
    f.cost o i = 0 := by
  induction' f with x j js y f h
  · simp only [cost_pure']
  · simp only [cost_query', h, ite_self, add_zero]
    by_cases ij : i = j
    · simp only [ij] at is; simp only [js, not_true_eq_false] at is
    · simp only [ij, if_false]

/-- The cost of `f >>= g` is `f.cost + g.cost` -/
lemma cost_bind (f : DComp ι ω s α) (g : α → DComp ι ω s β) (o : I → (x : ι) → ω x) (i : I) :
    (f >>= g).cost o i = f.cost o i + (g (f.value o)).cost o i := by
  induction' f with x j m y f h
  · simp only [bind, bind', cost_pure', value_pure', zero_add]
  · simp only [bind, bind'] at h
    simp only [bind, bind', cost_query', h, value, add_assoc, add_right_inj]
    apply congr_arg₂ _ rfl
    simp only [run_query', bind_pure_comp, map_bind]

/-- Map doesn't change `cost` -/
@[simp] lemma cost_map (f : α → β) (g : DComp ι ω s α) (o : I → (x : ι) → ω x) (i : I) :
    (f <$> g).cost o i = g.cost o i := by
  simp only [map_eq, cost_bind, cost_pure, add_zero]

/-- If an oracle isn't allowed, its cost is zero -/
@[simp] lemma cost_eq_zero {f : DComp ι ω s α} {i : I} (m : i ∉ s) (o : I → (x : ι) → ω x) :
    f.cost o i = 0 := by
  induction' f with x j mj y f h
  · simp only [cost_pure']
  · simp only [cost_query', h, add_zero, ite_eq_right_iff, one_ne_zero, imp_false]
    intro e; rw [e] at m; exact m mj

/-- `count` multiplies cost by `n` -/
@[simp] lemma cost_count (f : DComp ι ω s Bool) (n : ℕ) (o : I → (x : ι) → ω x) (i : I) :
    (count f n).cost o i = n * (f.cost o i) := by
  induction' n with n h
  · simp only [count_zero, cost_pure, zero_mul]
  · simp only [count, add_comm, bind_pure_comp, cost_bind, cost_map, h, add_mul, one_mul]

/-- `estimate` multiplies cost by `n` -/
@[simp] lemma cost_estimate (f : DComp ι ω s Bool) (n : ℕ) (o : I → (x : ι) → ω x) (i : I) :
    (estimate f n).cost o i = n * (f.cost o i) := by
  simp only [estimate, cost_map, cost_count]

/-!
## `DComp.value` commutes with various things
-/

@[simp] lemma value_pure (x : α) (o : I → (x : ι) → ω x) : (pure x : DComp ι ω s α).value o = x := by
  simp only [pure, value_pure']

@[simp] lemma value_query' (i : I) (m : i ∈ s) (y : ι) (f : ω y → DComp ι ω s α)
    (o : I → (x : ι) → ω x) : (query' i m y f).value o = (f (o i y)).value o := by
  simp only [value, run, bind_assoc]

@[simp] lemma value_query (i : I) (y : ι) (o : I → (x : ι) → ω x) :
    (query i y).value o = o i y := by
  simp only [query, value_query', value_pure, bind_pure]

@[simp] lemma value_bind (f : DComp ι ω s α) (g : α → DComp ι ω s β) (o : I → (x : ι) → ω x) :
    (f >>= g).value o = (g (f.value o)).value o := by
  induction' f with x j m y f h
  · simp only [pure'_bind, value_pure', pure_bind]
  · simp only [query'_bind, value_query', h, bind_assoc]

@[simp] lemma value_map (f : α → β) (g : DComp ι ω s α) (o : I → (x : ι) → ω x) :
    (f <$> g).value o = f (g.value o) := by
  simp only [map_eq, value_bind, value_pure, bind_pure]

/-!
## `allow` and `allow_all` don't change `.value` or `.cost`
-/

@[simp] lemma value_allow (f : DComp ι ω s α) (st : s ⊆ t) (o : I → (x : ι) → ω x) :
    (f.allow st).value o = f.value o := by
  induction' f with x j m y f h
  · simp only [allow, value_pure', value_pure]
  · simp only [allow, value_query', h]

@[simp] lemma value_allow_all (f : DComp ι ω s α) (o : I → (x : ι) → ω x) :
    (f.allow_all).value o = f.value o := by
  apply value_allow

@[simp] lemma cost_allow (f : DComp ι ω s α) (st : s ⊆ t) (o : I → (x : ι) → ω x) (i : I) :
    (f.allow st).cost o i = f.cost o i := by
  induction' f with x j m y f h
  · simp only [allow, cost_pure, cost_pure']
  · simp only [allow, cost_query', h]

@[simp] lemma cost_allow_all (f : DComp ι ω s α) (o : I → (x : ι) → ω x) (i : I) :
    (f.allow_all).cost o i = f.cost o i := by
  apply cost_allow

@[simp] lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : DComp ι ω s α).allow st = pure x := by
  simp only [allow]

@[simp] lemma allow_all_pure (x : α) : (pure x : DComp ι ω s α).allow_all = pure x := by
  simp only [allow_all, allow_pure]

@[simp] lemma allow_bind (f : DComp ι ω s α) (g : α → DComp ι ω s β) (st : s ⊆ t) :
    (f >>= g).allow st = f.allow st >>= fun x ↦ (g x).allow st := by
  have e : ∀ v, bind' v g = v >>= g := fun _ ↦ rfl
  induction' f with x j m y f h
  · simp only [pure'_bind, allow, pure_bind]
  · simp only [allow, e, h, query'_bind]

@[simp] lemma allow_all_bind (f : DComp ι ω s α) (g : α → DComp ι ω s β) :
    (f >>= g).allow_all = f.allow_all >>= fun x ↦ (g x).allow_all :=
  allow_bind f g _

@[simp] lemma allow_all_map (f : α → β) (g : DComp ι ω s α) :
    (f <$> g).allow_all = f <$> g.allow_all := by
  simp only [map_eq]; apply allow_all_bind

@[simp] lemma allow_allow (f : DComp ι ω s α) (st : s ⊆ t) (tu : t ⊆ u) :
    (f.allow st).allow tu = f.allow (st.trans tu) := by
  induction' f with x j m y f h
  · simp only [allow]
  · simp only [allow, h]

@[simp] lemma allow_all_allow (f : DComp ι ω s α) (st : s ⊆ t) :
    (f.allow st).allow_all = f.allow_all := by
  simp only [allow_all, allow_allow]
