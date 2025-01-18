import Prob.Argmax
import Prob.Bernoulli

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

/-- A stochastic oracle is a random map from `α → Bool` -/
def Oracle (α : Type) := α → Prob Bool

/-- The probability of true for an oracle -/
def Oracle.prob (o : Oracle α) (x : α) : ℝ :=
  (o x).prob true

/-- n random bits from an oracle, each given by feeding the oracle the previous result.
    This models an arbitrary computation, as `o` can behave differently based on input length. -/
def Oracle.fold (o : Oracle (List Bool)) : (n : ℕ) → Prob (List.Vector Bool n)
| 0 => pure .nil
| n+1 => do
  let y ← o.fold n
  let x ← o y.toList
  return y.cons x

/-- The (n+1)th bit of o.fold -/
def Oracle.final (o : Oracle (List Bool)) (t : ℕ) : Prob Bool := do
  let x ← o.fold (t+1)
  return x.head

/-- The distance between two oracles is the sup of their probability differences -/
instance : Dist (Oracle α) where
  dist o0 o1 := ⨆ y, |(o0 y).prob true - (o1 y).prob true|

/-- Deterministic oracles have probability 0 or 1, always -/
def Oracle.Deterministic (o : Oracle α) : Prop :=
  ∀ y, (o y).prob true = 0 ∨ (o y).prob true = 1

/-- `pure` is deterministic -/
@[simp] lemma Oracle.deterministic_pure (f : α → Bool) : Deterministic (fun x ↦ pure (f x)) := by
  intro x
  induction f x
  all_goals simp [Prob.prob_pure]

/-- Deterministic oracles are pure -/
lemma Oracle.Deterministic.eq_pure {o : Oracle α} (d : o.Deterministic) (x : α) :
    o x = pure ((o x).argmax) := by
  rw [(o x).eq_bernoulli]
  rcases d x with h | h
  · simp only [h, bernoulli_zero, argmax_pure]
  · simp only [h, bernoulli_one, argmax_pure]
