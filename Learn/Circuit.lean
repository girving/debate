import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.Bound
import Misc.Finset
import Misc.Init

/-!
# Circuits on top of a function class

The prover-estimator debate proofs can't be formulated in terms of oracle complexity, since we
construct Bob taking the problem distribution (including any oracles) into account.

Therefore, we need a notion of circuits of bounded complexity, referring to some fixed class of
functions at the leaves.
-/

open Classical
open scoped Real
open Set
noncomputable section
namespace Circuit

variable {α β γ : Type}

/-!
### Definitions
-/

/-- A primitive function takes an input and some number of parameter circuits -/
structure Prim (α : Type) : Type where
  n : ℕ
  f : α → (Fin n → ℝ) → ℝ

variable {F : Set (Prim α)}

instance : CoeFun (Prim α) (fun f ↦ α → (Fin f.n → ℝ) → ℝ) where
  coe f := f.f

/-- Circuits referring to some primitive set `F` -/
inductive _root_.Circuit (F : Set (Prim α)) : Type where
  | node : (f : Prim α) → f ∈ F → (Fin f.n → Circuit F) → Circuit F

/-!
### Circuit sizes
-/

def eval : Circuit F → α → ℝ
| .node f _ g, x => f x fun k ↦ (g k).eval x

def size : Circuit F → ℕ
| .node _ _ a => 1 + ∑ k, (a k).size

def depth : Circuit F → ℕ
| .node _ _ a => 1 + Finset.univ.sup fun k ↦ (a k).depth

/-- All subcircuits of a circuit, useful for computing the size of a multihead circuit -/
def subs (f : Circuit F) : Finset (Circuit F) :=
  {f} ∪ match f with
  | .node _ _ a => Finset.univ.sup fun k ↦ (a k).subs

/-- The total size of a family of circuits, accounting for sharing -/
def total [Fintype β] (f : β → Circuit F) : ℕ :=
  (Finset.univ.sup fun x ↦ (f x).subs).card

/-!
### Arithmetic primitives
-/

namespace Prim
def const (x : ℝ) : Prim α := ⟨0, fun _ _ ↦ x⟩
def lt : Prim α := ⟨2, fun _ x ↦ if x 0 < x 1 then 1 else 0⟩
def le : Prim α := ⟨2, fun _ x ↦ if x 0 ≤ x 1 then 1 else 0⟩
def sum (n : ℕ) : Prim α := ⟨n, fun _ x ↦ ∑ k, x k⟩
def sub : Prim α := ⟨2, fun _ x ↦ x 0 - x 1⟩
def prod (n : ℕ) : Prim α := ⟨n, fun _ x ↦ ∏ k, x k⟩
def div : Prim α := ⟨2, fun _ x ↦ x 0 / x 1⟩
def neg : Prim α := ⟨1, fun _ x ↦ -x 0⟩
def abs : Prim α := ⟨1, fun _ x ↦ |x 0|⟩
def inv : Prim α := ⟨1, fun _ x ↦ (x 0)⁻¹⟩
def exp : Prim α := ⟨1, fun _ x ↦ Real.exp (x 0)⟩
def log : Prim α := ⟨1, fun _ x ↦ Real.log (x 0)⟩

/-- A standard set of arithmetic primitives-/
def arith : Set (Prim α) :=
  {lt, le, sub, div, neg, abs, exp, log, inv} ∪
  sum '' univ ∪
  prod '' univ ∪
  const '' univ

/-- A set of primitives that contains arithmetic -/
class Arith (F : Set (Prim α)) : Prop where
  subset : arith ⊆ F

-- Membership lemmas
attribute [prim_mem] Set.mem_union arith Set.mem_insert_iff or_true true_or
@[simp, prim_mem] lemma const_mem {x : ℝ} : const (α := α) x ∈ const '' univ := by simp
@[simp, prim_mem] lemma sum_mem {n : ℕ} : sum (α := α) n ∈ sum '' univ := by simp
@[simp, prim_mem] lemma prod_mem {n : ℕ} : prod (α := α) n ∈ prod '' univ := by simp

/-- Show a primitive is allowed in a circuit via `simp` -/
macro "prim_mem" : tactic =>
  `(tactic| simp only [prim_mem])

-- Membership lemmas based on `Arith`
@[prim_mem] lemma const_mem_arith [Arith F] (x : ℝ) : const x ∈ F := by apply Arith.subset; prim_mem
@[prim_mem] lemma sum_mem_arith [Arith F] {n : ℕ} : sum n ∈ F := by apply Arith.subset; prim_mem
@[prim_mem] lemma prod_mem_arith [Arith F] {n : ℕ} : prod n ∈ F := by apply Arith.subset; prim_mem
@[prim_mem] lemma neg_mem_arith [Arith F] : neg ∈ F := by apply Arith.subset; prim_mem
@[prim_mem] lemma exp_mem_arith [Arith F] : exp ∈ F := by apply Arith.subset; prim_mem
@[prim_mem] lemma div_mem_arith [Arith F] : div ∈ F := by apply Arith.subset; prim_mem

end Prim

-- Convenience notation for arithmetic primitives
def const (F : Set (Prim α)) [Prim.Arith F] (x : ℝ) : Circuit F :=
  .node (Prim.const x) (by prim_mem) Fin.elim0

def sum [Fintype β] (x : β → Circuit F) [Prim.Arith F] : Circuit F :=
  .node (Prim.sum _) (by prim_mem) (x ∘ (Fintype.equivFin β).symm)

def prod [Fintype β] (x : β → Circuit F) [Prim.Arith F] : Circuit F :=
  .node (Prim.prod _) (by prim_mem) (x ∘ (Fintype.equivFin β).symm)

instance [Prim.Arith F] : Add (Circuit F) where add x y := .node (Prim.sum 2) (by prim_mem) ![x, y]
instance [Prim.Arith F] : Mul (Circuit F) where mul x y := .node (Prim.prod 2) (by prim_mem) ![x, y]
instance [Prim.Arith F] : Div (Circuit F) where div x y := .node Prim.div (by prim_mem) ![x, y]
instance [Prim.Arith F] : Neg (Circuit F) where neg x := .node (Prim.neg) (by prim_mem) ![x]
def exp [Prim.Arith F] : Circuit F → Circuit F := fun x ↦ .node Prim.exp (by prim_mem) ![x]

/-!
### Circuit evaluation lemmas
-/

section Eval
variable [Prim.Arith F]
variable {a : α}
variable {x y : Circuit F}

@[simp, circuit_eval] lemma eval_const {x : ℝ} : (const F x).eval a = x := by
  simp [const, Prim.const, eval]

@[simp, circuit_eval] lemma eval_sum [Fintype β] (x : β → Circuit F) :
    (sum x).eval a = ∑ k, (x k).eval a := by
  simp only [sum, Prim.sum, eval, Function.comp_apply]
  apply Fintype.sum_equiv
  exact congrFun rfl

@[simp, circuit_eval] lemma eval_prod [Fintype β] (x : β → Circuit F) :
    (prod x).eval a = ∏ k, (x k).eval a := by
  simp only [prod, Prim.prod, eval, Function.comp_apply]
  apply Fintype.prod_equiv
  exact congrFun rfl

@[simp, circuit_eval] lemma eval_add : (x + y).eval a = x.eval a + y.eval a := by
  simp [Prim.sum, eval]

@[simp, circuit_eval] lemma eval_mul : (x * y).eval a = x.eval a * y.eval a := by
  simp [Prim.prod, eval]

@[simp, circuit_eval] lemma eval_div : (x / y).eval a = x.eval a / y.eval a := by
  simp [Prim.div, eval]

@[simp, circuit_eval] lemma eval_neg : (-x).eval a = -x.eval a := by
  simp [Neg.neg, Prim.neg, eval]

@[simp, circuit_eval] lemma eval_exp : (exp x).eval a = Real.exp (x.eval a) := by
  simp [exp, Prim.exp, eval]

end Eval

/-!
### Machinery to conveniently bound `total`
-/

@[simp] lemma self_mem_subs (f : Circuit F) : f ∈ f.subs := by
  unfold subs; simp

lemma mem_subs_trans {x y z : Circuit F} (xy : x ∈ y.subs) (yz : y ∈ z.subs) : x ∈ z.subs := by
  by_cases yze : y = z
  · simpa only [yze] using xy
  · unfold subs at yz ⊢
    match z with
    | .node _ _ a =>
      simp only [Finset.mem_union, Finset.mem_singleton, yze, Finset.mem_sup, Finset.mem_univ,
        true_and, false_or] at yz ⊢
      obtain ⟨i,yi⟩ := yz
      exact .inr ⟨i, mem_subs_trans xy yi⟩

section Subs

variable [Prim.Arith F]
variable {x y : Circuit F}
variable {s : γ → Circuit F}
variable {a : β → Circuit F} [Fintype β]

attribute [circuit_subs] total Finset.sup_union_distrib Finset.univ_sup_const_union
  Finset.univ_sup_union_const

@[circuit_subs] lemma subs_sum :
    (sum a).subs = {sum a} ∪ Finset.univ.sup fun x ↦ (a x).subs := by
  simp [subs, Prim.sum, Circuit.sum]
  exact congr_arg₂ _ rfl (Finset.univ_sup_comp_equivFin_symm fun k ↦ (a k).subs)

@[circuit_subs] lemma subs_prod :
    (prod a).subs = {prod a} ∪ Finset.univ.sup fun x ↦ (a x).subs := by
  simp [subs, Prim.prod, Circuit.prod]
  exact congr_arg₂ _ rfl (Finset.univ_sup_comp_equivFin_symm fun k ↦ (a k).subs)

@[circuit_subs] lemma subs_add : (x + y).subs = {x + y} ∪ x.subs ∪ y.subs := by
  simp [subs, Finset.univ_fin2, Prim.sum]

@[circuit_subs] lemma subs_mul : (x * y).subs = {x * y} ∪ x.subs ∪ y.subs := by
  simp [subs, Finset.univ_fin2, Prim.prod]

@[circuit_subs] lemma subs_div : (x / y).subs = {x / y} ∪ x.subs ∪ y.subs := by
  simp [subs, Finset.univ_fin2, Prim.div]

@[circuit_subs] lemma subs_neg : (-x).subs = {-x} ∪ x.subs := by simp [subs, Prim.neg]
@[circuit_subs] lemma subs_exp : x.exp.subs = {x.exp} ∪ x.subs := by simp [subs, exp, Prim.exp]

@[circuit_subs] lemma subs_const {x : ℝ} : (const F x).subs = {const F x} := by
  simp [subs, Circuit.const, Prim.const]

end Subs
