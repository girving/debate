import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Comp.Defs
import Comp.Lipschitz
import Comp.Oracle
import Prob.Bernoulli
import Prob.Estimate

/-!
The stochastic oracle doubly-efficient debate protocol
-/

open Classical
open Comp
open Prob
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {n : ℕ}
variable {ι α I : Type}
variable {s : Set I}

/-- We distinguish debater and verify oracles so that we can measure cost separately
    for different agents.  We will plug in the same oracles in the end for all ids. -/
inductive OracleId where
  | AliceId : OracleId
  | BobId : OracleId
  | VeraId : OracleId

export OracleId (AliceId BobId VeraId)
abbrev AllIds := @univ OracleId

-- Next, we give type signatures for Alice and Bob, and the protocol that connects them.
-- See Figure 1 in the paper for the corresponding prose description.  We differ from Figure 1
-- in that we treat steps (2b,2c,2d) as fixed parts of the protocol, rather than agent moves.

/-- A state in a debate.  Either
    1. An uninterrupted data value, or
    2. A final result if we rejected. -/
def State (α : Type) := Except Bool α

/-- Alice takes the oracle input and estimates a probability that the oracle returns 1.
    Alice's goal is to produce output 1. An honest Alice will try to mimic the oracle. -/
def Alice' (ι : Type) (o : OracleId) := ι → Comp ι {o} ℝ

/-- Alice using the normal `AliceId`. This is the standard instantiation of Alice'
    that will be used in most debate protocols. -/
def Alice (ι : Type) := Alice' ι AliceId

/-- Bob sees the oracle input and Alice's claimed probability, and decides whether to continue.
    In the game, Bob's goal is to produce output 0. An honest Bob will yell iff Alice doesn't
    mimic the oracle. -/
def Bob' (ι : Type) (o : OracleId) := ι → ℝ → Comp ι {o} Bool

/-- Bob using the normal `BobId` -/
def Bob (ι : Type) := Bob' ι BobId

/-- Verifiers have an identical type signature to Bob, but use weaker parameters. -/
def Vera (ι : Type) := ι → ℝ → Comp ι {VeraId} Bool

/-- Enough samples to estimate a probability with error < e with failure probability ≤ q -/
def samples (e q : ℝ) : ℕ := Nat.ceil (-Real.log (q/2) / (2 * e^2))

/-- Honest Alice estimates the correct probability within error < e with failure probability ≤ q -/
def alice' (e q : ℝ) (o : OracleId) : Alice' ι o := fun y ↦
  estimate (query o y) (samples e q)

def alice (e q : ℝ) : Alice ι := alice' e q AliceId

/-- Honest Bob checks the probability against an honest copy of Alice.

    Bob has separate soundness and completeness conditions, but (for now) uses a single estimation
    with a single failure probability.  We need
    1. Completeness: If Alice is off by ≤ c, Bob should accept with probability ≥ 1-q
    2. Soundness: If Alice is off by ≥ s, Bob should reject with probability ≥ 1-q
    Assume Bob estimates p to within e, then rejects iff his estimate differs from Alice by > r.
    1. Completeness: To accept if Alice is off by ≤ c, we need c ≤ r - e
    2. Soundness: To reject if Alice is off by ≥ s, we need r + e ≤ s
    We want e as large as possible to reduce the number of samples.  This is achieved if
      r = (c + s) / 2
      e = (s - c) / 2 -/
def bob' (c s q : ℝ) (o : OracleId) : Bob' ι o := fun y p ↦
  return |p - (← alice' ((s-c)/2) q o y)| < (c+s)/2

def bob (c s q : ℝ) : Bob ι := bob' c s q BobId

/-- The verifier checks the probability estimate given by Alice.
    We reuse Honest Bob with a weaker error probability, which we will set later. -/
def vera (s v q : ℝ) : Vera ι := bob' s v q VeraId

/-- One step of the debate protocol, simulating a single oracle query -/
def step (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) (y : ι) : Comp ι AllIds (State Bool) := do
  let p ← (alice y).allow_all
  if ← (bob y p).allow_all then do  -- Bob accepts Alice's probability, so take the step
    let x ← bernoulli p  -- This is Figure 4, steps 2b,2c,2d, as a fixed part of the protocol
    return .ok x
  else  -- Bob rejects, so we call the verifier and end the computation
    return .error (←(vera y p).allow_all)

/-- Process a computation, replacing oracle queries with debate steps -/
def steps (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) : Comp ι s α → Comp ι AllIds (State α)
| .pure' x => pure' (.ok x)
| .sample' p f => .sample' p fun y ↦ steps alice bob vera (f y)
| .query' _ _ y f => do match ← step alice bob vera y with
  | .ok x => steps alice bob vera (f x)
  | .error r => return .error r

/-- The full debate protocol that stitches these together -/
def debate (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) (f : Comp ι s Bool) :
    Comp ι AllIds Bool := do
  match ← steps alice bob vera f with
  | .ok y => return y
  | .error r => return r

-- Next, we define what it means for the debate protocol to be correct.  The definition is
-- in this file to keep the details of the proof separated.  See Correct.lean for the final
-- Correct result, and Details.lean for the proof.

/-- The debate protocol is correct if, for all k-Lipschitz oracles o
    1. Whenever Pr(o.final) ≥ 2/3, Honest Alice beats any Bob (Eve) with probability w > 1/2
    2. Whenever Pr(o.final) ≤ 1/3, Honest Bob beats any Alice (Eve) with probability w > 1/2 -/
structure Correct (f : Comp ι s Bool) (w k : ℝ) (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) :
    Prop where
  /-- Success is more likely than failure -/
  half_lt_w : 1/2 < w
  /-- If we're in the language, Alice wins -/
  complete : ∀ (o : Oracle ι) (eve : Bob ι), f.lipschitz o k → 2/3 ≤ (f.prob' o).prob true →
    w ≤ ((debate alice eve vera f).prob' o).prob true
  /-- If we're out of the language, Bob wins -/
  sound : ∀ (o : Oracle ι) (eve : Alice ι), f.lipschitz o k → 2/3 ≤ (f.prob' o).prob false →
    w ≤ ((debate eve bob vera f).prob' o).prob false
