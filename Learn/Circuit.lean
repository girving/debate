import Mathlib.Data.Real.Basic

/-!
# Circuits on top of a function class

The prover-estimator debate proofs can't be formulated in terms of oracle complexity, since we
construct Bob taking the problem distribution (including any oracles) into account.

Therefore, we need a notion of circuits of bounded complexity, referring to some fixed class of
functions at the leaves.
-/

open scoped Real
open Set
noncomputable section

variable {α β γ : Type}
variable {F : Set (α → β)}

/-- Circuits referring to some function class `F` -/
inductive Circuit (F : Set (α → β)) : Type → Type 1 where
  | leaf : (f : α → β) → f ∈ F → Circuit F β
  | const : {γ : Type} → γ → Circuit F γ
  | less : Circuit F ℝ → Circuit F ℝ → Circuit F Bool
  | add : Circuit F ℝ → Circuit F ℝ → Circuit F ℝ
  | mul : Circuit F ℝ → Circuit F ℝ → Circuit F ℝ
  | neg : Circuit F ℝ → Circuit F ℝ
  | abs : Circuit F ℝ → Circuit F ℝ

namespace Circuit

def eval : {γ : Type} → Circuit F γ → α → γ
| _, .leaf f _, x => f x
| _, .const c, _ => c
| _, .less f g, x => f.eval x < g.eval x
| _, .add f g, x => f.eval x + g.eval x
| _, .mul f g, x => f.eval x * g.eval x
| _, .neg f, x => -f.eval x
| _, .abs f, x => |f.eval x|

def size : {γ : Type} → Circuit F γ → ℕ
| _, .leaf _ _ => 1
| _, .const _ => 1
| _, .less x y => x.size + y.size + 1
| _, .add x y => x.size + y.size + 1
| _, .mul x y => x.size + y.size + 1
| _, .neg x => x.size + 1
| _, .abs x => x.size + 1

def depth : {γ : Type} → Circuit F γ → ℕ
| _, .leaf _ _ => 0
| _, .const _ => 0
| _, .less x y => 1 + max x.depth y.depth
| _, .add x y => 1 + max x.depth y.depth
| _, .mul x y => 1 + max x.depth y.depth
| _, .neg x => 1 + x.depth
| _, .abs x => 1 + x.depth
