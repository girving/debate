import Comp.Defs

/-!
# Lipschitz computations
-/

variable {ι I α : Type}
variable {s : Set I}

/-- An oracle computation is k-Lipschitz if the probabilities differ by `≤ k * oracle dist`.
    We define this asymmetrically, as we want the neighborhood of a particular oracle. -/
structure Comp.lipschitz (f : Comp ι s α) (o : Oracle ι) (k : ℝ) : Prop where
  k0 : 0 ≤ k
  le : ∀ (o' : Oracle ι) (x : α), |(f.prob' o).prob x - (f.prob' o').prob x| ≤ k * dist o o'
