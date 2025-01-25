import Debate.Cost
import Debate.Details
import Debate.Protocol

/-!
Correctness of the stochastic oracle doubly-efficient debate algorithm
-/

open Classical
open Prob
open scoped Real
noncomputable section

variable {ι I : Type}
variable {o : BOracle ι}
variable {k : ℝ}
variable {u : Set I}
variable {f : BComp ι u Bool}

/-- Completeness for any valid parameters -/
theorem completeness (L : f.lipschitz o k) (eve : Bob ι) {w d : ℝ}
    (p : Params w d k f.worst) (m : w ≤ (f.prob' o).prob true) :
    d ≤ ((debate (alice p.c p.q) eve (vera p.c p.s p.v) f).prob' o).prob true :=
  completeness_p f L eve p m

/-- Soundness for any valid parameters -/
theorem soundness (L : f.lipschitz o k) (eve : Alice ι) {w d : ℝ}
    (p : Params w d k f.worst) (m : w ≤ (f.prob' o).prob false) :
    d ≤ ((debate eve (bob p.s p.b p.q) (vera p.c p.s p.v) f).prob' o).prob false :=
  soundness_p f L eve p m

/-- The debate protocol is correct with probability 3/5, using the default parameters -/
theorem correctness (k : ℝ) (k0 : 0 < k) :
    let p := defaults k f.worst k0
    Correct f (3/5) k (alice p.c p.q) (bob p.s p.b p.q) (vera p.c p.s p.v) where
  half_lt_w := by norm_num
  complete o eve L m := completeness L eve (defaults k f.worst k0) m
  sound o eve L m := soundness L eve (defaults k f.worst k0) m
