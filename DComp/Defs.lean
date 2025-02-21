import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Basic

/-!
## Oracle-relative deterministic computations

Overall in this repo we view stochastic computations `Comp` as the central object. These can consult
oracles and draw random bits. However, it is sometimes useful to refactor a stochastic computation
into a single random draw followed by a deterministic computation.

Here we define `DComp ι ω s α` as a deterministic computation that is allowed to consult any
oracle `o ∈ s`.
-/

open Classical
open Option (some none)
open Set
noncomputable section

variable {n : ℕ}
variable {I : Type} {ι : I → Type} {ω : {o : I} → ι o → Type}
variable {s t : Set I}
variable {α β γ : Type}

/-- A deterministic computation that can make oracle queries.
    Importantly, the computation does not know the oracle, so we can model query complexity.
    The `DComp` constructors are not very user friendly due to kernel restrictions on inductive,
    but we replace them with clean ones below. -/
inductive DComp (ι : I → Type) (ω : {o : I} → ι o → Type) (s : Set I) (α : Type) : Type where
  /-- Return a result with no computation -/
  | pure' : α → DComp ι ω s α
  /-- Query an oracle `o ∈ s`, and branch on the result -/
  | query' : (o : I) → o ∈ s → (y : ι o) → ((ω y) → DComp ι ω s α) → DComp ι ω s α

namespace DComp

variable {ι : I → Type} {ω : {o : I} → ι o → Type}
/-- Bind two `DComp`s together -/
def bind' (f : DComp ι ω s α) (g : α → DComp ι ω s β) : DComp ι ω s β := match f with
  | .pure' x => g x
  | .query' o m y f => .query' o m y fun x ↦ (f x).bind' g

/-- `DComp` is a monad -/
instance : Monad (DComp ι ω s) where
  pure := DComp.pure'
  bind := DComp.bind'

/-- The simplest case of `DComp.query'` -/
def query (i : I) (y : ι i) : DComp ι ω {i} (ω y) :=
  DComp.query' i (mem_singleton _) y pure

/-- The value and query counts of a `DComp ι s`, once we supply monadic oracles -/
def runM {m : Type → Type} [Monad m] (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → m (ω x)) :
    m (α × (I → ℕ)) :=
  match f with
  | .pure' x => pure (x, fun _ => 0)
  | .query' i _ y f => do
    let x ← o i y
    let (z, c) ← (f x).runM o
    pure (z, c + fun j => if j = i then 1 else 0)

/-- The value and query counts of a `DComp ι s`, once we supply oracles -/
def run (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → ω x) : α × (I → ℕ) :=
  f.runM (m := Id) o

/-- The value of a `DComp` -/
def value (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → ω x) : α :=
  (f.run o).1

/-- The value of a `DComp` when all oracles are the same -/
@[simp] def value' (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → ω x) : α :=
  (f.run o).1

/-- The query cost of a `DComp` -/
def cost (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → ω x) : I → ℕ :=
  (f.run o).2

/-- The expected query cost of a `Comp` when all oracles are the same. -/
def cost' (f : DComp ι ω s α) (o : (o : I) → (x : ι o) → ω x) : I → ℕ :=
  (f.run o).2

/-- Allow more oracles in a computation -/
def allow (f : DComp ι ω s α) (st : s ⊆ t) : DComp ι ω t α := match f with
  | .pure' x => pure x
  | .query' i m y f => .query' i (st m) y fun x ↦ (f x).allow st

/-- Allow all oracles in a computation -/
def allow_all (f : DComp ι ω s α) : DComp ι ω (@univ I) α :=
  f.allow (subset_univ s)
