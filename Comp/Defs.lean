import Comp.Oracle
import Prob.Defs
import Prob.Fin
import DComp.Defs

/-!
## Oracle-relative probabilistic computations

`Prob α` represents the result of a probabilistic computation, but has no information about
how long the computation took.  `Comp ι ω s α` is a computation that is allowed to consult any
oracle `o ∈ s`, and produces a distribution over results and calls to each oracle.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {n : ℕ}
variable {I : Type} {ι : I → Type} {ω : {o : I} → ι o → Type}
variable {s t : Set I}
variable {α β γ : Type}


/-- A stochastic computation that can make oracle queries.
    Importantly, the computation does not know the oracle, so we can model query complexity.
    The `Comp` constructors are not very user friendly due to kernel restrictions on inductive,
    but we replace them with clean ones below. -/
def Comp (ι : I → Type) (ω : {o : I} → ι o → Type) (s : Set I) (α : Type) : Type :=
  DComp
    (I := Option I)
    (ι := fun | some i => ι i | none => Σ n, Prob (Fin n))
    (ω := @fun | some _ => ω | none => fun s => Fin s.1)
    (some '' s ∪ {none})
    α

/-- `Comp` where all oracles accept `ι` and return `Bool` -/
abbrev BComp (ι : Type) {I : Type} (s : Set I) (α : Type) := Comp (fun _ => ι) (fun _ ↦ Bool) s α

namespace Comp

/-- Bind two `Comp`s together -/
nonrec def bind' (f : Comp ι ω s α) (g : α → Comp ι ω s β) : Comp ι ω s β := f.bind' g


/-- `Comp` is a monad -/
instance : Monad (Comp ι ω s) where
  pure := DComp.pure'
  bind := Comp.bind'

nonrec def query'' (o : I) : o ∈ s → (y : ι o) → ((ω y) → Comp ι ω s α) → Comp ι ω s α :=
  fun h y f => .query' (some o) (by simp [h]) y f

@[match_pattern]
def sample' {n} (p : Prob (Fin n)) (f : Fin n → Comp ι ω s β) : Comp ι ω s β :=
  DComp.query' none (by simp) ⟨n, p⟩ f

/-- `sample'` with a general `α` instead of `Fin n` -/
def sample (p : Prob α) (f : α → Comp ι ω s β) : Comp ι ω s β :=
  .sample' p.fin (f ∘ p.fromfin)

/-- `Prob`s are `Comp`s -/
instance : Coe (Prob α) (Comp ι ω s α) where
  coe p := .sample p pure

/-- The simplest case of `Comp.query'` -/
def query (i : I) (y : ι i) : Comp ι ω {i} (ω y) :=
  Comp.query'' i (mem_singleton _) y pure

/-- The value and query counts of a `Comp ι s`, once we supply oracles -/
def run (f : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) : Prob (α × (I → ℕ)) := match f with
  | .pure' x => pure (x, fun _ => 0)
  | .sample' f g => f >>= fun x ↦ (g x).run o
  | .query'' i _ y f => do
    let x ← o i y
    let (z,c) ← (f x).run o
    return (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp` -/
def prob (f : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) : Prob α :=
  Prod.fst <$> f.run o


/-- The expected query cost of a `Comp` -/
def cost (f : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) (i : I) : ℝ :=
  (f.run o).exp fun (_,c) ↦ c i


/-- Allow more oracles in a computation -/
def allow (f : Comp ι ω s α) (st : s ⊆ t) : Comp ι ω t α := match f with
  | .pure' x => pure x
  | .sample' f g => sample' f fun x ↦ (g x).allow st
  | .query' i m y f => .query' i (st m) y fun x ↦ (f x).allow st

/-- Allow all oracles in a computation -/
def allow_all (f : Comp ι ω s α) : Comp ι ω (@univ I) α :=
  f.allow (subset_univ s)

/-- The worst-case query cost of a `Comp`.
    For simplicity, we do not check for zero probabilities, so it is sometimes an overestimate. -/
def worst [∀ (i) (x : ι i), Fintype (ω x)] (f : Comp ι ω s α) : ℕ := match f with
| .pure' _ => 0
| .sample' _ f => Finset.univ.sup fun x ↦ (f x).worst
| .query' _ _ _ f => 1 + Finset.univ.sup fun x ↦ (f x).worst

section
variable {ι : Type} {ω : ι → Type}

/-- The value of a `Comp` when all oracles are the same -/
@[simp] def prob' (f : Comp (fun _ => ι) ω s α) (o : Oracle ι ω) : Prob α :=
  f.prob fun _ ↦ o

/-- The expected query cost of a `Comp` when all oracles are the same. -/
def cost' (f : Comp (fun _ => ι) ω s α) (o : Oracle ι ω) : I → ℝ :=
  f.cost fun _ ↦ o

end
