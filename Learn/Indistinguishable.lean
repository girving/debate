import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finsupp.Pointwise
import Learn.Circuit
import Misc.Bound
import Misc.Sgn
import Prob.Arith
import Prob.Argmax
import Prob.Force
import Prob.Jensen
import Prob.KL
import Prob.Scale
import Prob.Uniform

/-!
# Outcome indistinguishability via multiplicative weights

We formalise the multiclass outcome indistinguishability approach of

* Cynthia Dwork et al., Beyond Bernoulli: Generating random outcomes that cannot be
  distinguished from nature, https://proceedings.mlr.press/v167/dwork22a/dwork22a.pdf

The algorithm is essentially multiplicative weight updates. This is apparently a special case of
mirror descent, but I'm going to ignore that and formalise their proof directly.
-/

open Classical
open Circuit (Prim)
open Real (exp log)
open Set
noncomputable section
namespace Indistinguishable

variable {X Y : Type}

/-!
### Definitions and algorithm
-/

section Convergence

/-- A distinguisher turns a sample, an outcome, and a distribution over outcomes into a score. -/
def Distinguisher (X Y : Type) : Type :=
  X → Y → Prob Y → Icc (-1 : ℝ) 1

@[bound, simp] lemma abs_distinguisher_le (A : Distinguisher X Y) (x : X) (y : Y) (p : Prob Y) :
    |(A x y p : ℝ)| ≤ 1 := by
  simp only [abs_le, ← mem_Icc, Subtype.coe_prop]

@[bound, simp] lemma sq_distinguisher_le (A : Distinguisher X Y) (x : X) (y : Y) (p : Prob Y) :
    (A x y p : ℝ) ^ 2 ≤ 1 := by
  simp only [sq_le_one_iff_abs_le_one, abs_distinguisher_le]

-- Our algorithms and results are relative to
-- 1. A distribution over input pairs `μ : Prob X`
-- 2. A true outcome distribution `q : X → Prob Y`
-- 3. A set of distinguishers `As` (possibly infinite)
-- 4. An accuracy parameter `ε > 0`
variable (μ : Prob X)
variable (q p : X → Prob Y)
variable {As : Set (Distinguisher X Y)}
variable {ε : ℝ}

/-- The advantage of a distinguisher -/
def adv (p : X → Prob Y) (A : Distinguisher X Y) : ℝ :=
  μ.exp fun x ↦ (q x).exp (fun y ↦ ↑(A x y (p x))) - (p x).exp (fun y ↦ ↑(A x y (p x)))

/-- Indistinguishability means `adv` is always small -/
def AdvLe (As : Set (Distinguisher X Y)) (ε : ℝ) : Prop :=
  ∀ A ∈ As, |adv μ q p A| ≤ ε

/-- A reweighting step multiplies the probabilities by `η * A` for some distinguisher `A`, then
renormalises probabilities to sum to 1. This is one step of the "Generative OI Learning Algorithm"
once we've chosen a distinguisher. -/
def reweight (p : X → Prob Y) (A : Distinguisher X Y) (η : ℝ) (x : X) : Prob Y :=
  (p x).scale fun y ↦ η * sgn (adv μ q p A) * A x y (p x)

/-- One step including distinguisher choice -/
def step (As : Set (Distinguisher X Y)) (ε η : ℝ) (p : X → Prob Y) : X → Prob Y :=
  if h : ∃ A ∈ As, |adv μ q p A| > ε then
    let A := choose h
    reweight μ q p A η
  else
    p

/-- Our prior must cover the true support if we hope to converge -/
def Safe (p : X → Prob Y) : Prop :=
  ∀ x, μ.prob x ≠ 0 → ∀ y, (q x).prob y ≠ 0 → (p x).prob y ≠ 0

/-!
### Convergence

We will use real KL throughout, which requires us to assume that all of our KL-divergences are
finite. This is fundamental, as the algorithm does not converge otherwise.
-/

/-- A potential function that will decrease significantly with each step -/
def potential (p : X → Prob Y) : ℝ :=
  μ.exp fun x ↦ (q x).reKL (p x)

/-- Potential is non-negative -/
lemma Safe.potential_nonneg {μ : Prob X} {q p : X → Prob Y} (s : Safe μ q p) :
    0 ≤ potential μ q p :=
  Prob.exp_nonneg fun x μx ↦ Prob.reKL_nonneg _ _ (s x μx)

@[simp] lemma potential_self : potential μ q q = 0 := by
  simp only [potential, Prob.reKL_self, Prob.exp_const]

/-- Advantage is zero if potential is zero -/
lemma adv_eq_zero {μ : Prob X} {q p : X → Prob Y} (s : Safe μ q p) (z : potential μ q p = 0) :
    adv μ q p = 0 := by
  simp only [potential] at z
  rw [Prob.exp_eq_zero_iff] at z
  · funext A
    simp only [adv, Pi.zero_apply]
    refine μ.exp_eq_zero fun x μx ↦ ?_
    specialize z x μx
    rw [Prob.reKL_eq_zero_iff _ _ (s x μx)] at z
    simp only [z, sub_self]
  · intro x μx
    bound [Prob.reKL_nonneg _ _ (s x μx)]

/-- Partition function of a step -/
def partition (p : X → Prob Y) (A : Distinguisher X Y) (η : ℝ) (x : X) : ℝ :=
  (p x).partition fun y ↦ η * sgn (adv μ q p A) * A x y (p x)

/-- A bound on the log partition function -/
lemma log_partition_le {μ q p} {A : Distinguisher X Y} {η : ℝ} (η1 : |η| ≤ 1) {x : X} :
    log (partition μ q p A η x) ≤
      η * sgn (adv μ q p A) * (p x).exp (fun y ↦ (A x y (p x) : ℝ)) + η ^ 2 := by
  generalize hs : sgn (adv μ q p A) = s
  by_cases η0 : η = 0
  · simp [η0, partition, Prob.partition_zero]
  · have d1 : ∀ x y, |η * s * A x y (p x)| ≤ 1 := by
      simp only [← hs, abs_mul, abs_sgn, mul_one]
      bound
    have d1' : ∀ x y, |-η * s * A x y (p x)| ≤ 1 := by simp [d1]
    calc
      _ = log ((p x).exp fun y ↦ exp (η * s * ↑(A x y (p x)))) := by
            simp only [partition, Prob.partition, hs]
      _ ≤ log ((p x).exp fun y ↦ 1 + η * s * ↑(A x y (p x)) + η ^ 2) := by
            apply Real.log_le_log
            · apply Prob.partition_pos
            · refine Prob.exp_mono fun y y0 ↦ ?_
              refine le_trans (exp_le_quadratic (abs_le.mp (d1 x y)).2) ?_
              simp only [mul_pow, ← hs, sq_sgn, mul_one]
              bound
      _ = log (1 + (η * s * (p x).exp (fun y ↦ ↑(A x y (p x))) + η ^ 2)) := by
            simp only [Prob.exp_add_const, Prob.exp_const_add, add_assoc, Prob.exp_const_mul]
      _ ≤ (η * s * (p x).exp fun y ↦ ↑(A x y (p x))) + η ^ 2 := by
            apply log_one_add_le_self
            refine lt_of_le_of_lt (neg_le_of_abs_le ?_) (lt_add_of_pos_right _ ?_)
            · simp only [← Prob.exp_const_mul]
              refine le_trans (Prob.abs_exp_le_exp_abs _ _) ?_
              exact Prob.exp_le_of_forall_le fun y y0 ↦ d1 x y
            · rwa [sq_pos_iff]

/-- Reweight preserves safety -/
def Safe.reweight {μ q p} (s : Safe μ q p) (A : Distinguisher X Y) (η : ℝ) :
    Safe μ q (Indistinguishable.reweight μ q p A η) := by
  intro x μx y qy
  simp only [Indistinguishable.reweight, Prob.prob_scale]
  exact ne_of_gt (by bound [Prob.prob_pos (s x μx y qy)])

/-- The potential changes significantly each iteration -/
def le_potential_sub {μ q p} (s : Safe μ q p) (A : Distinguisher X Y) (η : ℝ) (η1 : |η| ≤ 1) :
    η * |adv μ q p A| - η ^ 2 ≤ potential μ q p - potential μ q (reweight μ q p A η) := by
  calc
    _ = μ.exp fun x ↦ (q x).exp fun y ↦ log ((reweight μ q p A η x).prob y) -
                                        log ((p x).prob y) := by
          simp only [potential, ← Prob.exp_sub (f := μ), Prob.reKL]
          refine Prob.exp_congr fun x μx ↦ ?_
          simp only [Prob.exp_log_div_eq_sub (s x μx),
            Prob.exp_log_div_eq_sub (s.reweight A η x μx), ← Prob.exp_sub]
          exact Prob.exp_congr fun y qy ↦ by abel
    _ = μ.exp fun x ↦ (q x).exp fun y ↦ η * sgn (adv μ q p A) * ↑(A x y (p x)) -
                                        log (partition μ q p A η x) := by
          simp only [reweight, Prob.prob_scale, partition]
          refine Prob.exp_congr fun x x0 ↦ Prob.exp_congr fun y y0 ↦ ?_
          have p0 := s _ x0 _ y0
          rw [Real.log_div (by positivity), Real.log_mul (by positivity) p0, Real.log_exp]
          · abel
          · exact (p x).partition_pos.ne'
    _ ≥ η * sgn (adv μ q p A) * μ.exp (fun x ↦
            (q x).exp (fun y ↦ ↑(A x y (p x))) - (p x).exp (fun y ↦ ↑(A x y (p x)))) - η ^ 2 := by
          simp only [← Prob.exp_const_mul, mul_sub, ← Prob.exp_sub_const]
          refine Prob.exp_mono fun x x0 ↦ ?_
          simp only [← sub_add_eq_sub_sub, Prob.exp_sub_const, sub_le_sub_iff_left,
            Prob.exp_const_mul, log_partition_le η1]
    _ = η * sgn (adv μ q p A) * (adv μ q p A) - η ^ 2 := by simp only [adv]
    _ = η * |adv μ q p A| - η ^ 2 := by simp only [mul_assoc, sgn_mul_eq_abs]

/-- `4 * potential / ε ^ 2` steps are sufficient to converge -/
lemma steps_converge {μ q p} (s : Safe μ q p) (As : Set (Distinguisher X Y)) (ε : ℝ) (ε0 : 0 < ε)
   (ε1 : ε ≤ 1) : AdvLe μ q ((step μ q As ε (ε / 2))^[⌈4 * potential μ q p / ε ^ 2⌉₊] p) As ε := by
  simp only [AdvLe]
  by_cases p0 : potential μ q p = 0
  · simp [adv_eq_zero s, p0, ε0.le]
  replace p0 : 0 < potential μ q p := (Ne.symm p0).lt_of_le (s.potential_nonneg)
  set n := ⌈4 * potential μ q p / ε ^ 2⌉₊
  set f := step μ q As ε (ε / 2)
  have η1 : |ε / 2| ≤ 1 := by simp only [abs_le]; exact ⟨by linarith, by linarith⟩
  by_cases c : ∃ k, k ≤ n ∧ ∀ A ∈ As, |adv μ q (f^[k] p) A| ≤ ε
  · obtain ⟨k, kn, c⟩ := c
    refine Nat.le_induction c ?_ n kn
    intro k _ le
    simp only [Function.iterate_succ_apply']
    generalize h : f^[k] p = r at le
    simp only [← not_lt, ← not_exists, exists_prop] at le
    simp only [f, step, le, dite_false, ← not_lt, ← not_exists, exists_prop, not_false_eq_true]
  · by_contra
    simp only [not_exists, not_and, not_forall, exists_prop, not_le] at c
    have i : ∀ k ≤ n, Safe μ q (f^[k] p) ∧
                      (0 < k → potential μ q (f^[k] p) < potential μ q p - ε ^ 2 / 4 * k) := by
      intro k kn
      induction' k with k h
      · simp [s]
      · simp only [Nat.add_one_pos, true_implies]
        obtain ⟨s, h⟩ := h (by omega)
        specialize c k (by omega)
        simp only [Function.iterate_succ_apply', Nat.cast_add_one, mul_add_one, sub_add_eq_sub_sub]
        generalize hr : f^[k] p = r at h c s
        simp only [f, step, c, dite_true]
        refine ⟨s.reweight _ _, ?_⟩
        refine lt_of_lt_of_le (b := potential μ q r - ε ^ 2 / 4) ?_ ?_
        · rw [lt_sub_iff_add_lt, add_comm, ← lt_sub_iff_add_lt]
          refine lt_of_lt_of_le ?_ (le_potential_sub (p := r) s _ (ε / 2) η1)
          rw [lt_sub_iff_add_lt, mul_comm (ε / 2), ← div_lt_iff₀ (by positivity)]
          ring_nf
          simp only [pow_two, mul_assoc, mul_inv_cancel₀ ε0.ne', mul_one, (choose_spec c).2]
        · by_cases k0 : k = 0
          · simp [k0, ← hr]
          · linarith [h (by omega)]
    obtain ⟨s,i⟩ := i n (le_refl _)
    contrapose i
    have n0 : 0 < n := by simp only [n]; bound
    have nn : 4 * potential μ q p / ε ^ 2 ≤ n := Nat.le_ceil _
    simp only [not_lt, n0, true_implies]
    refine le_trans ?_ s.potential_nonneg
    simp only [sub_nonpos]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left nn (by positivity))
    ring_nf
    simp only [mul_right_comm _ _ (ε ^ 2)⁻¹, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 ε0.ne'),
      one_mul, le_refl]

/-- As a simplification below, we use the fact that singletons are always indistinguishable -/
lemma advle_of_subsingleton [Inhabited Y] [Subsingleton Y] {μ q p} (ε0 : 0 ≤ ε) :
    AdvLe μ q p As ε := by
  intro A m
  refine le_trans (le_of_eq ?_) ε0
  simp only [adv, abs_eq_zero, Unique.eq_default, sub_self, Prob.exp_const]

/-- Uniform has nicely bounded potential -/
@[bound] lemma potential_uniform_le (μ : Prob X) (q : X → Prob Y) [Fintype Y] [Nonempty Y] :
    potential μ q (fun _ ↦ Prob.uniform_univ Y) ≤ log (Fintype.card Y) :=
  Prob.exp_le_of_forall_le fun _ _ ↦ Prob.reKL_uniform_univ_le _

end Convergence

/-!
### Circuit complexity
-/

variable [Fintype Y] [Inhabited Y]
variable {As : Set (Distinguisher X Y)}

/-- Turn a distinguisher into a circuit primitive -/
def Distinguisher.prim (A : Distinguisher X Y) (y : Y) : Prim X where
  n := Fintype.card Y
  f := fun x p ↦ A x y (Prob.force (p ∘ Fintype.equivFin Y) .univ)

/-- Our circuit primitives are the union of distinguishers and arithmetic -/
@[prim_mem] def prims (As : Set (Distinguisher X Y)) : Set (Prim X) :=
  Circuit.Prim.arith ∪ image2 Distinguisher.prim As univ

instance : Circuit.Prim.Arith (prims As) where subset := by simp [prims]
@[prim_mem] lemma Distinguisher.mem_prims (A : Distinguisher X Y) (m : A ∈ As) (y : Y) :
    A.prim y ∈ prims As := .inr (mem_image2_of_mem m (mem_univ _))

/-- Probability distributions as circuits -/
def Mimic (As : Set (Distinguisher X Y)) : Type :=
  Y → Circuit (prims As)

/-- Evaluate a mimic into a probability distribution -/
def Mimic.eval (p : Mimic As) (x : X) : Prob Y :=
  Prob.force (fun y ↦ (p y).eval x) .univ

/-- Mimics that have normalised probabilities (and are positive) -/
structure Mimic.Valid (p : Mimic As) : Prop where
  pos : ∀ x, (∀ y, 0 < (p y).eval x)
  total : ∀ x, ∑ y, (p y).eval x = 1

attribute [bound] Mimic.Valid.pos
@[bound] lemma Mimic.Valid.nonneg {p : Mimic As} (v : Mimic.Valid p) (x : X) (y : Y) :
    0 ≤ (p y).eval x := (v.pos x y).le

@[simp] lemma Mimic.Valid.prob_eval {p : Mimic As} (v : Mimic.Valid p) (x : X) (y : Y) :
    (p.eval x).prob y = (p y).eval x := by
  rw [Mimic.eval, Prob.prob_force]
  simp only [Finset.mem_univ, ↓reduceIte]
  exact ⟨by bound, v.total x⟩

/-- `Valid` implies `Safe` -/
lemma Mimic.Valid.safe {p : Mimic As} (v : p.Valid) {μ : Prob X} {q : X → Prob Y} :
    Safe μ q (p.eval) := by
  intro x μx y qy
  simp only [v, prob_eval]
  exact (v.pos x y).ne'

/-- The uniform distribution as a circuit -/
def Mimic.uniform (As : Set (Distinguisher X Y)) : Mimic As :=
  fun _ ↦ Circuit.const _ (1 / Fintype.card Y)

/-- A distinguisher as a circuit -/
def Distinguisher.circuit (A : Distinguisher X Y) (m : A ∈ As) (y : Y) (p : Mimic As) :
    Circuit (prims As) := Circuit.node (A.prim y) (A.mem_prims m y) (p ∘ (Fintype.equivFin Y).symm)

@[simp] lemma Distinguisher.eval_circuit {A : Distinguisher X Y} (m : A ∈ As) (y : Y) (p : Mimic As)
    (x : X) : (A.circuit m y p).eval x = A x y (p.eval x) := by
  simp [circuit, Circuit.eval, Distinguisher.prim, Function.comp_def, Mimic.eval]

@[circuit_subs] lemma Distinguisher.subs_circuit (A : Distinguisher X Y) (m : A ∈ As) (y : Y)
    (p : Mimic As) :
    (A.circuit m y p).subs = {A.circuit m y p} ∪ Finset.univ.sup fun x ↦ (p x).subs := by
  simp only [circuit, Circuit.subs]
  exact congr_arg₂ _ rfl (Finset.univ_sup_comp_equivFin_symm fun k ↦ (p k).subs)

/-- Reweight as a circuit -/
def Mimic.reweight (p : Mimic As) (μ : Prob X) (q : X → Prob Y) (A : Distinguisher X Y)
    (m : A ∈ As) (η : ℝ) : Mimic As :=
  let s := Circuit.const _ (η * sgn (adv μ q p.eval A))
  let r : Y → Circuit _ := fun y ↦ p y * (s * A.circuit m y p).exp
  let z := Circuit.sum r
  fun y ↦ r y / z

/-- Step as a circuit -/
def Mimic.step (μ : Prob X) (q : X → Prob Y) (ε η : ℝ) (p : Mimic As) : Mimic As :=
  if h : ∃ A ∈ As, |adv μ q p.eval A| > ε then
    p.reweight μ q (choose h) (choose_spec h).1 η
  else
    p

/-- Uniform is valid -/
lemma Mimic.Valid.uniform (As : Set (Distinguisher X Y)) : (Mimic.uniform As).Valid where
  pos := by simp [Mimic.uniform, Fintype.card_pos]
  total := by simp [Mimic.uniform]

/-- Reweight preserves validity -/
def Mimic.Valid.reweight {p : Mimic As} (v : p.Valid) (μ : Prob X) (q : X → Prob Y)
    (A : Distinguisher X Y) (m : A ∈ As) (η : ℝ) : (p.reweight μ q A m η).Valid := by
  constructor
  · intros
    simp only [Mimic.reweight, circuit_eval]
    refine div_pos ?_ (Finset.sum_pos ?_ (by simp))
    all_goals bound
  · intro x
    simp only [Mimic.reweight, circuit_eval]
    rw [← Finset.sum_div, div_eq_one_iff_eq]
    exact (Finset.sum_pos (by bound) (by simp)).ne'

/-- Step preserves validity -/
def Mimic.Valid.step {p : Mimic As} (v : p.Valid) {μ : Prob X} {q : X → Prob Y} {ε η : ℝ} :
    (p.step μ q ε η).Valid := by
  simp only [Mimic.step]
  split_ifs with h
  · apply v.reweight
  · assumption

@[simp] lemma eval_uniform (As : Set (Distinguisher X Y)) :
    (Mimic.uniform As).eval = fun _ ↦ Prob.uniform_univ Y := by
  ext x y
  simp only [Mimic.eval, Mimic.uniform, one_div, Circuit.eval_const, Prob.prob_uniform_univ]
  rw [Prob.prob_force _ _ (by bound)]
  simp only [Finset.mem_univ, ↓reduceIte]

/-- Reweight commutes with eval -/
@[simp] lemma eval_reweight (p : Mimic As) (v : p.Valid) (μ : Prob X) (q : X → Prob Y)
    (A : Distinguisher X Y) (m : A ∈ As) (η : ℝ) :
    (p.reweight μ q A m η).eval = reweight μ q p.eval A η := by
  ext x y
  simp only [(v.reweight μ q A m η).prob_eval]
  simp [Mimic.reweight, reweight, Prob.prob_scale, v.prob_eval, Prob.partition, Prob.exp_fintype,
    mul_comm]

/-- Step commutes with eval -/
@[simp] lemma eval_step {p : Mimic As} (v : p.Valid) {μ : Prob X} {q : X → Prob Y} {ε η : ℝ} :
    (p.step μ q ε η).eval = step μ q As ε η p.eval := by
  ext x y
  simp only [Mimic.step, step]
  split_ifs with h
  · simp [v]
  · rfl

/-- Uniform has total 1, since all the constants are the same -/
@[simp] lemma Mimic.total_uniform (As : Set (Distinguisher X Y)) :
    Circuit.total (Mimic.uniform As) = 1 := by
  simp only [uniform, circuit_subs, one_div, Finset.univ_sup_const, Finset.card_singleton]

/-- Reweight increases circuit size linearly.
TODO: Simplify this dramatically. Might need some tractic machinery for that. -/
def Mimic.total_reweight_le (p : Mimic As) {μ : Prob X} {q : X → Prob Y} (A : Distinguisher X Y)
    (m : A ∈ As) (η : ℝ) :
    Circuit.total (p.reweight μ q A m η) ≤ Circuit.total p + 5 * Fintype.card Y + 2 := by
  simp only [reweight, circuit_subs]
  ac_nf
  simp only [circuit_subs]
  ac_nf
  generalize Circuit.const (prims As) (η * sgn (adv μ q p.eval A)) = s
  generalize Circuit.sum (fun y ↦ p y * (s * A.circuit m y p).exp) = z
  simp only [← Finset.union_assoc, Finset.sup_union_distrib, Finset.univ_sup_union_const,
    Finset.univ_sup_union_const]
  ac_nf
  simp only [Finset.union_comm _ {s}, ← Finset.union_assoc]
  simp only [Finset.union_assoc, Finset.univ_sup_const_union]
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (add_le_add_left (Finset.card_union_le _ _) _) ?_
  simp only [Finset.card_singleton, ← add_assoc, Nat.reduceAdd]
  simp only [add_comm _ 2]
  simp only [add_assoc, add_le_add_iff_left]
  rw [← Finset.sup_union_distrib]
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [add_le_add_iff_left]
  refine le_trans (Finset.card_sup_le_sum_card _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 5 ?_) (by simp)
  intro y _
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [Finset.card_singleton, add_comm 1, Nat.reduceLeDiff]
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [Finset.card_singleton, add_comm 1, Nat.reduceLeDiff]
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [Finset.card_singleton, add_comm 1, Nat.reduceLeDiff]
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [Finset.card_singleton, add_comm 1, Nat.reduceLeDiff]

/-- Small indistinguishable circuits exist -/
lemma exists_small (μ : Prob X) (q : X → Prob Y) (As : Set (Distinguisher X Y))
    (ε : ℝ) (ε0 : 0 < ε) (ε1 : ε ≤ 1) :
    ∃ p : Mimic As, AdvLe μ q p.eval As ε ∧
      Circuit.total p ≤ 6 * Fintype.card Y * ⌈4 * log (Fintype.card Y) / ε ^ 2⌉₊ + 1 := by
  generalize hc : Fintype.card Y = c
  by_cases c2 : c < 2
  · have s : Subsingleton Y := by rw [← Fintype.card_le_one_iff_subsingleton]; omega
    exact ⟨Mimic.uniform As, advle_of_subsingleton ε0.le, by simp⟩
  simp only [not_lt] at c2
  set pp := potential μ q (Mimic.uniform As).eval
  use (Mimic.step μ q ε (ε / 2))^[⌈4 * pp / ε ^ 2⌉₊] (Mimic.uniform As)
  constructor
  · have uv : ∀ n, ((Mimic.step μ q ε (ε / 2))^[n] (Mimic.uniform As)).Valid := by
      intro n
      induction' n with n h
      · apply Mimic.Valid.uniform
      · simp only [Function.iterate_succ_apply', h, Mimic.Valid.step]
    have es : ∀ n, ((Mimic.step μ q ε (ε / 2))^[n] (Mimic.uniform As)).eval =
        (step μ q As ε (ε / 2))^[n] (Mimic.uniform As).eval := by
      intro n
      induction' n with n h
      · simp
      · simp only [Function.iterate_succ_apply', h, eval_step, uv]
    simp only [es]
    exact steps_converge (μ := μ) (q := q) (Mimic.Valid.uniform As).safe As ε ε0 ε1
  · have ts : ∀ n, Circuit.total ((Mimic.step μ q ε (ε / 2))^[n] (Mimic.uniform As)) ≤
        6 * Fintype.card Y * n + 1 := by
      intro n
      induction' n with n h
      · simp
      · simp only [Function.iterate_succ_apply']
        generalize hr : ((Mimic.step μ q ε (ε / 2))^[n] (Mimic.uniform As)) = r at h
        simp only [Mimic.step]
        split_ifs with i
        · refine le_trans (Mimic.total_reweight_le r _ _ _) ?_
          simp only [(by norm_num : 6 = 5 + 1), mul_add_one, add_one_mul]
          linarith
        · linarith
    refine le_trans (ts _) ?_
    simp only [eval_uniform, ← hc, pp]
    bound
