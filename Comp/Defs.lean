import Comp.Oracle
import Prob.Defs

/-!
## Oracle-relative probabilitistic computations

`Prob α` represents the result of a probabilistic computation, but has no information about
how long the computation took.  `Comp ι s α` is a computation that is allowed to consult any
oracle `o ∈ s`, and produces a distribution over results and calls to each oracle.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {ι I : Type}
variable {s t : Set I}
variable {α β γ : Type}

/-- A stochastic computation that can make oracle queries.
    Importantly, the computation does not know the oracle, so we can model query complexity.
    The `Comp` constructors are not very user friendly due to kernel restrictions on inductive,
    but we replace them with clean ones below. -/
inductive Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type 1 where
  /-- Return a result with no computation -/
  | pure' : α → Comp ι s α
  /-- Sample a value with some probability distribution, then continue -/
  | sample' : {β : Type} → Prob β → (β → Comp ι s α) → Comp ι s α
  /-- Query an oracle `o ∈ s`, and branch on the result -/
  | query' : (o : I) → o ∈ s → ι → Comp ι s α → Comp ι s α → Comp ι s α

namespace Comp

/-- Bind two `Comp`s together -/
def bind' (f : Comp ι s α) (g : α → Comp ι s β) : Comp ι s β := match f with
  | .pure' x => g x
  | .sample' p f => .sample' p (fun y ↦ (f y).bind' g)
  | .query' o m y f0 f1 => .query' o m y (f0.bind' g) (f1.bind' g)

/-- `Comp` is a monad -/
instance : Monad (Comp ι s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- `Prob`s are `Comp ι s` for any `s` -/
instance : Coe (Prob α) (Comp ι s α) where
  coe f := .sample' f pure

/-- The simplest case of `Comp.query'` -/
def query (i : I) (y : ι) : Comp ι {i} Bool :=
  Comp.query' i (mem_singleton _) y (pure true) (pure false)

/-- The value and query counts of a `Comp ι s`, once we supply oracles -/
def run (f : Comp ι s α) (o : I → Oracle ι) : Prob (α × (I → ℕ)) := match f with
  | .pure' x => pure (x, fun _ => 0)
  | .sample' f g => f >>= fun x ↦ (g x).run o
  | .query' i _ y f0 f1 => do
    let x ← (o i) y
    let (z,c) ← if x then f0.run o else f1.run o
    return (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp ι s` -/
def prob (f : Comp ι s α) (o : I → Oracle ι) : Prob α :=
  Prod.fst <$> f.run o

/-- The value of a `Comp ι s` when all oracles are the same -/
@[simp] def prob' (f : Comp ι s α) (o : Oracle ι) : Prob α :=
  f.prob fun _ ↦ o

/-- The expected query cost of a `Comp ι α`.
    There is a design decision here to make the theory about expected cost.  My guess is that
    will make the downstream theory slightly easier. -/
def cost (f : Comp ι s α) (o : I → Oracle ι) (i : I) : ℝ :=
  (f.run o).exp fun (_,c) ↦ c i

/-- The expected query cost of a `Comp ι α` when all oracles are the same. -/
def cost' (f : Comp ι s α) (o : Oracle ι) : I → ℝ :=
  f.cost fun _ ↦ o

/-- Allow more oracles in a computation -/
def allow (f : Comp ι s α) (st : s ⊆ t) : Comp ι t α := match f with
  | .pure' x => pure x
  | .sample' f g => f >>= fun x ↦ (g x).allow st
  | .query' i m y f0 f1 => .query' i (st m) y (f0.allow st) (f1.allow st)

/-- Allow all oracles in a computation -/
def allow_all (f : Comp ι s α) : Comp ι (@univ I) α :=
  f.allow (subset_univ s)

end Comp
