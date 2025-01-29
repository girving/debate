import Prob.Arith
import Prob.Uniform
import Misc.Bound

/-!
# Compression lemmas for use in complexity lower bounds

We follow

* Minki Hhan, A New Approach to Generic Lower Bounds, https://eprint.iacr.org/2024/268.

They derive lower bounds on query complexity over groups by deriving an encoder/decoder pair from
a group algorithm, then using the generation compression lemma below.
-/

open Classical
open Fintype (card)
open Set
noncomputable section

variable {α β γ ι I : Type}
variable {ω : ι → Type}
variable {s : Set I}
variable [Fintype β] [Nonempty β] [Fintype γ]

/-- The compression lemma: encoding then decoding is only accurate if we encode to a big space. -/
theorem Prob.compression (p : Prob α) (enc : α → β → γ) (dec : α → γ → β) :
    (do let r ← p; let x ← uniform_univ β; return (r, x)).pr (fun (r,x) ↦ dec r (enc r x) = x) ≤
      (card γ : ℝ) / card β := by
  simp only [pr_bind, pr_pure]
  refine exp_le_of_forall_le fun r _ ↦ ?_
  set s : Finset β := {x | dec r (enc r x) = x}
  have le : s.card ≤ card γ := by
    set t : Finset γ := {e | dec r e ∈ s}
    refine le_trans ?_ t.card_le_univ
    rw [(by aesop : s = Finset.image (dec r) t)]
    exact Finset.card_image_le
  have e : Finset.univ.filter (fun x ↦ dec r (enc r x) = x) = s := by aesop
  simp only [exp, Finsupp.sum, support_uniform_univ, prob_uniform_univ, smul_eq_mul, mul_one,
    mul_zero, ← Finset.mul_sum]
  rw [Finset.sum_ite, e]
  simp [div_eq_inv_mul]
  bound
