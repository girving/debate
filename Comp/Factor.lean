import DComp.Coe
import Prob.Dependent

/-!
## Factor a stochastic computation to make one initial random draw

`Comp` allows arbittrary interleaving of oracle queries and sampling from `Prob`. This is
nonessential: it is possible to move all the sampling up front, prior to any oracle queries, then
run a deterministic computation. Here we construct this factorisation.
-/

open Classical
open Option (some none)
open scoped Real
open Set
noncomputable section

variable {ι I : Type}
variable {ω : ι → Type}
variable {s t : Set I}
variable {α β γ : Type}

/-- A stochastic computation factored into a random draw and a deterministic followup. -/
structure Comp.Factor (ι : Type) (ω : ι → Type) (s : Set I) (α : Type) : Type 1 where
  /-- The type of the random draw. -/
  β : Type
  /-- The probability distribution of the random draw. -/
  p : Prob β
  /-- The deterministic followup computation. -/
  f : β → DComp ι ω s α

/-- Factor a stochastic computation into a single random draw followed by a deterministic
    computation. No effort is made to optimise the random draw. -/
def Comp.factor [∀ x, Fintype (ω x)] (f : Comp ι ω s α) : Comp.Factor ι ω s α := match f with
  | .pure' x => ⟨Unit, pure (), fun _ ↦ pure x⟩
  | .sample' p f =>
    let β := Σ x, (f x).factor.β
    let p : Prob β := p.dbind fun x ↦ (f x).factor.p
    let f : β → DComp ι ω s α := fun x ↦ (f x.1).factor.f x.2
    ⟨β, p, f⟩
  | .query' i m y f =>
    let β := Π x, (f x).factor.β
    let p : Prob β := Prob.pi fun x ↦ (f x).factor.p
    let f : β → DComp ι ω s α := fun x ↦ .query' i m y fun z ↦ (f z).factor.f (x z)
    ⟨β, p, f⟩

/-- If we put the `Comp.factor` pieces back together, we get the original computation. -/
def Comp.run_factor [∀ x, Fintype (ω x)] (f : Comp ι ω s α) (o : I → (x : ι) → ω x) :
    (do let x ← f.factor.p; return (f.factor.f x).run o) = f.run fun i x ↦ pure (o i x) := by
  induction' f with x β u v h j m y f h
  · simp only [factor, DComp.run_pure, bind_pure_comp, map_pure]
    rfl
  · simp only [factor, Comp.run, Prob.dbind_bind_assoc]
    strip x
    apply h
  · simp only [factor, run, pure_bind, ← h, bind_assoc, DComp.run_query']
    exact Prob.pi_bind (f := fun x ↦ (f x).factor.p) (x := o j y)
      (g := fun x ↦ pure ((((f (o j y)).factor.f x).run o).1,
        (((f (o j y)).factor.f x).run o).2 + fun k ↦ if k = j then 1 else 0))
