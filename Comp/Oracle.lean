import Prob.Argmax
import Prob.Bernoulli
import Prob.IsPure

/-!
# Stochastic oracle for use in randomized computations

We formalize debate w.r.t. randomized computations allowed to query a stochastic oracle.
-/

open Classical
open Prob
open Option (some none)
open scoped Real
noncomputable section

variable {α : Type}
variable {β : α → Type}

/-- A stochastic oracle is a random map from `α → Bool` -/
def Oracle (α : Type) (β : α → Type) := (x : α) → Prob (β x)

/-- An `Oracle` that always returns `Bool` -/
abbrev BOracle (α : Type) := Oracle α fun _ ↦ Bool

/-- The probability of true for an oracle -/
def Oracle.prob (o : BOracle α) (x : α) : ℝ :=
  (o x).prob true

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as `o` can behave differently based on input length. -/
def Oracle.fold (o : BOracle (List Bool)) : (n : ℕ) → Prob (List.Vector Bool n)
| 0 => pure .nil
| n+1 => do
  let y ← o.fold n
  let x ← o y.toList
  return y.cons x

/-- The (n+1)th bit of o.fold -/
def Oracle.final (o : BOracle (List Bool)) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- The distance between two oracles is the sup of their probability differences -/
instance : Dist (Oracle α β) where
  dist o0 o1 := ⨆ y, ⨆ x, |(o0 y).prob x - (o1 y).prob x|

/-- Pure oracles have probability 0 or 1, always -/
def Oracle.IsPure (o : Oracle α β) : Prop :=
  ∀ y, (o y).IsPure

/-- `pure` is pure -/
@[simp] lemma Oracle.isPure_pure (f : (x : α) → β x) : IsPure (fun x ↦ pure (f x)) := by
  intro x z
  simp [Prob.prob_pure, ne_or_eq]

/-- Pure oracles are `pure` -/
lemma Oracle.IsPure.eq_pure {o : Oracle α β} (d : o.IsPure) (x : α) :
    o x = pure ((o x).argmax) :=
  (d x).eq_pure
