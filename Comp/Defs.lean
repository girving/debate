import Comp.Oracle
import Prob.Defs
import Prob.Fin

/-!
## Oracle-relative probabilistic computations

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

variable {n : ℕ}
variable {ι I : Type}
variable {s t : Set I}
variable {α β γ : Type}

/-- A stochastic computation that can make oracle queries.
    Importantly, the computation does not know the oracle, so we can model query complexity.
    The `Comp` constructors are not very user friendly due to kernel restrictions on inductive,
    but we replace them with clean ones below. -/
inductive Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type where
  /-- Return a result with no computation -/
  | pure' : α → Comp ι s α
  /-- Sample a value with some probability distribution, then continue -/
  | sample' : {n : ℕ} → Prob (Fin n) → (Fin n → Comp ι s α) → Comp ι s α
  /-- Query an oracle `o ∈ s`, and branch on the result -/
  | query' : (o : I) → o ∈ s → ι → (Bool → Comp ι s α) → Comp ι s α

namespace Comp

/-- Bind two `Comp`s together -/
def bind' (f : Comp ι s α) (g : α → Comp ι s β) : Comp ι s β := match f with
  | .pure' x => g x
  | .sample' p f => .sample' p (fun y ↦ (f y).bind' g)
  | .query' o m y f => .query' o m y fun x ↦ (f x).bind' g

/-- `Comp` is a monad -/
instance : Monad (Comp ι s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- `sample'` with a general `α` instead of `Fin n` -/
def sample (p : Prob α) (f : α → Comp ι s β) : Comp ι s β :=
  .sample' p.fin (f ∘ p.fromfin)

/-- `Prob`s are `Comp`s -/
instance : Coe (Prob α) (Comp ι s α) where
  coe p := .sample p pure

/-- The simplest case of `Comp.query'` -/
def query (i : I) (y : ι) : Comp ι {i} Bool :=
  Comp.query' i (mem_singleton _) y pure

/-- The value and query counts of a `Comp ι s`, once we supply oracles -/
def run (f : Comp ι s α) (o : I → Oracle ι) : Prob (α × (I → ℕ)) := match f with
  | .pure' x => pure (x, fun _ => 0)
  | .sample' f g => f >>= fun x ↦ (g x).run o
  | .query' i _ y f => do
    let x ← (o i) y
    let (z,c) ← (f x).run o
    return (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp` -/
def prob (f : Comp ι s α) (o : I → Oracle ι) : Prob α :=
  Prod.fst <$> f.run o

/-- The value of a `Comp` when all oracles are the same -/
@[simp] def prob' (f : Comp ι s α) (o : Oracle ι) : Prob α :=
  f.prob fun _ ↦ o

/-- The expected query cost of a `Comp` -/
def cost (f : Comp ι s α) (o : I → Oracle ι) (i : I) : ℝ :=
  (f.run o).exp fun (_,c) ↦ c i

/-- The expected query cost of a `Comp` when all oracles are the same. -/
def cost' (f : Comp ι s α) (o : Oracle ι) : I → ℝ :=
  f.cost fun _ ↦ o

/-- Allow more oracles in a computation -/
def allow (f : Comp ι s α) (st : s ⊆ t) : Comp ι t α := match f with
  | .pure' x => pure x
  | .sample' f g => sample' f fun x ↦ (g x).allow st
  | .query' i m y f => .query' i (st m) y fun x ↦ (f x).allow st

/-- Allow all oracles in a computation -/
def allow_all (f : Comp ι s α) : Comp ι (@univ I) α :=
  f.allow (subset_univ s)

/-- The worst-case query cost of a `Comp`.
    For simplicity, we do not check for zero probabilities, so it is sometimes an overestimate. -/
def worst (f : Comp ι s α) : ℕ := match f with
| .pure' _ => 0
| .sample' _ f => Finset.univ.sup fun x ↦ (f x).worst
| .query' _ _ _ f => 1 + Finset.univ.sup fun x ↦ (f x).worst
