import Comp.Defs

/-!
# Lipschitz computations
-/

variable {I α : Type}
variable {ι : Type} {ω : ι → Type}
variable {s : Set I}

/-- An oracle computation is k-Lipschitz if the probabilities differ by `≤ k * oracle dist`.
    We define this asymmetrically, as we want the neighborhood of a particular oracle. -/
structure Comp.lipschitz (f : Comp (fun _ => ι) ω s α) (o : Oracle ι ω) (k : ℝ) : Prop where
  k0 : 0 ≤ k
  le : ∀ (o' : Oracle ι ω) (x : α),
    |(f.prob fun _ => o).prob x - (f.prob fun _ => o').prob x| ≤ k * dist o o'
