import DComp.Basic

/-!
## Lift a deterministic computation to a stochastic one
-/

open Classical
open Option (some none)
open scoped Real
open Set
noncomputable section
namespace DComp

variable {n : ℕ}
variable {ι I : Type}
variable {ω : ι → Type}
variable {s t : Set I}
variable {α β γ : Type}

/-!
### Coersion definitions
-/

/-- Convert a `DComp` to a `Comp` -/
@[coe] def toComp (f : DComp ι ω s α) : Comp ι ω s α := match f with
  | .pure' x => .pure' x
  | .query' i m y f => .query' i m y fun x ↦ (f x).toComp

/-- `DComp`s are `Comp`s -/
instance : Coe (DComp ι ω s α) (Comp ι ω s α) where
  coe f := f.toComp

/-!
### Coersion commutes with various things
-/

@[simp] lemma coe_pure' (x : α) : ((pure' x : DComp ι ω s α) : Comp ι ω s α) = pure x := rfl
@[simp] lemma coe_pure (x : α) : ((pure x : DComp ι ω s α) : Comp ι ω s α) = pure x := rfl
@[simp] lemma coe_query' (i : I) (m : i ∈ s) (y : ι) (f : ω y → DComp ι ω s α) :
    ((query' i m y f : DComp ι ω s α) : Comp ι ω s α) = Comp.query' i m y fun x ↦ f x := rfl
@[simp] lemma coe_query (i : I) (y : ι) :
    ((query i y : DComp ι ω {i} (ω y)) : Comp ι ω {i} (ω y)) = Comp.query i y := rfl
@[simp] lemma coe_allow (f : DComp ι ω s α) (st : s ⊆ t) :
    (f.allow st : Comp ι ω t α) = f.allow st := rfl
@[simp] lemma coe_allow_all (f : DComp ι ω s α) :
    (f.allow_all : Comp ι ω (@univ I) α) = f.allow_all := rfl
