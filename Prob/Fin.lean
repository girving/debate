import Prob.Argmax
import Prob.Arith

/-!
# An equivalent `Prob` over `Fin n`

Standardsize any `Prob α` into one over some `Fin n`.
-/

open Classical
open Set
open scoped Real Topology
noncomputable section
namespace Prob

variable {n : ℕ}
variable {α β : Type}

def tofin (p : Prob α) (x : α) : Fin p.supp.card :=
  if m : x ∈ p.supp then p.supp.equivFin ⟨x,m⟩
  else p.supp.equivFin ⟨p.argmax, by
    simp only [p.mem_iff, ne_eq, prob_argmax_ne_zero, not_false_eq_true]⟩

def fromfin (p : Prob α) (n : Fin p.supp.card) : α :=
  p.supp.equivFin.symm n

def fin (p : Prob α) : Prob (Fin p.supp.card) :=
  p.tofin <$> p

@[simp] lemma fromfin_tofin (p : Prob α) {x : α} (px : p.prob x ≠ 0) :
    p.fromfin (p.tofin x) = x := by
  by_cases f : ∃ n, α = Fin n
  all_goals simp only [fromfin, tofin, mem_iff, ne_eq, px, not_false_eq_true, ↓reduceDIte,
    Equiv.symm_apply_apply]

@[simp] lemma fromfin_tofin_map (p : Prob α) : (fun x ↦ p.fromfin (p.tofin x)) <$> p = p := by
  ext x
  simp only [prob_map, ← pr_eq_prob p]
  refine pr_congr fun y py ↦ ?_
  simp only [ne_eq, py, not_false_eq_true, fromfin_tofin]

@[simp] lemma map_fin (p : Prob α) : p.fromfin <$> p.fin = p := by
  simp only [fin, Functor.map_map, fromfin_tofin_map]

@[simp] lemma bind_fin (p : Prob α) (f : α → Prob β) :
    (do let x ← p.fin; f (p.fromfin x)) = p >>= f := by
  ext x
  simp only [fin, bind_map_left, prob_bind]
  refine exp_congr fun y py ↦ ?_
  simp only [ne_eq, py, not_false_eq_true, fromfin_tofin]

@[simp] lemma fin_mem (p : Prob α) (x : Fin p.supp.card) : p.fromfin x ∈ p.supp := by
  simp only [fromfin, Finset.coe_mem]
