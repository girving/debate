import Comp.Basic
import Debate.Protocol
import Prob.Arith
import Prob.Chernoff
import Prob.Cond
import Prob.Jensen
import Mathlib.Tactic.Bound
import Misc.Finset
import Misc.If

/-!
# Correctness of the stochastic oracle doubly-efficient debate algorithm (details)

See `Correct.lean` for the summary.
-/

open Classical
open Prob
open Option (some none)
open Real (log)
open Set
open scoped Real
noncomputable section

variable {ι α β I : Type}
variable {i : OracleId}
variable {o : BOracle ι}
variable {k c s b e p q v : ℝ}
variable {u : Set I}
variable {t : List (ι × ℝ)}  -- Trace of oracle calls and Alice's claimed probabilities

/-!
## Correctness of Alice, Bob, and Vera

We first show that Honest Alice, Bob, and Vera do their jobs correctly to
within the necessary failure probabilities.
-/

/-- samples' is samples without the Nat.ceil -/
def samples' (e q : ℝ) : ℝ := -Real.log (q/2) / (2 * e^2)
@[bound] lemma le_samples (e q : ℝ) : samples' e q ≤ samples e q := Nat.le_ceil _

/-- Honest Alice has error ≥ e with probability ≤ q -/
lemma alice_pr_le (o : BOracle ι) (i : OracleId) (e0 : 0 < e) (q0 : 0 < q) (y : ι) :
    ((alice' e q i y).prob' o).pr (fun p ↦ e ≤ |p - (o y).prob true|) ≤ q := by
  simp only [alice', Comp.prob', Comp.prob_estimate, Comp.prob_query]
  refine le_trans (chernoff_estimate_abs_le (o y) (samples e q) (le_of_lt e0)) ?_
  have le : -2 * ↑(samples e q) * e^2 ≤ -2 * samples' e q * e^2 := by simp; bound
  refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr le) (by norm_num)) ?_
  simp only [samples', div_eq_inv_mul, ←mul_assoc, mul_inv]; norm_num
  simp only [mul_comm _ (e^2), ←mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt e0)), one_mul]
  rw [Real.exp_log]; ring_nf; rfl; positivity

/-- Honest Alice has error ≤ e with probability ≥ 1 - q
    < e is also true, but annoying to work with later. -/
lemma le_alice_pr (o : BOracle ι) (i : OracleId) (e0 : 0 < e) (q0 : 0 < q) (y : ι) :
    1 - q ≤ ((alice' e q i y).prob' o).pr (fun p ↦ |p - (o y).prob true| ≤ e) := by
  trans ((alice' e q i y).prob' o).pr (fun p ↦ |p - (o y).prob true| < e)
  · rw [pr_neg']; simp only [not_lt]; linarith [alice_pr_le o i e0 q0 y]
  · apply pr_mono; intro _ _ h; exact le_of_lt h

/-- Honest Bob usually accepts if Alice is off by ≤ c -/
lemma bob_complete (o : BOracle ι) (i : OracleId) (cs : c < s) (q0 : 0 < q) {y : ι}
    (good : |p - (o y).prob true| ≤ c) :
    ((bob' c s q i y p).prob' o).prob false ≤ q := by
  simp only [bob', prob_bind, prob_pure, false_eq_decide_iff, not_lt, Comp.prob',
    Comp.prob_bind, Comp.prob_pure]
  rw [← pr]
  refine le_trans (pr_mono ?_) (alice_pr_le o i (by linarith) q0 y)
  intro b _ h
  generalize (o y).prob true = x at good
  have e : b - x = -((p - b) - (p - x)) := by abel
  rw [e, abs_neg]
  refine le_trans ?_ (abs_sub_abs_le_abs_sub _ _)
  calc (s - c) / 2
    _ ≤ (c + s) / 2 - c := by linarith
    _ ≤ |p - b| - |p - x| := by bound

/-- Honest Bob usually accepts if Alice is off by ≤ c -/
lemma bob_complete' (o : BOracle ι) (i : OracleId) (cs : c < s) (q0 : 0 < q) {y : ι}
    (good : |p - (o y).prob true| ≤ c) :
    1 - q ≤ ((bob' c s q i y p).prob' o).prob true := by
  rw [bool_prob_true_of_false]
  linarith [bob_complete o i cs q0 good]

/-- Honest Bob usually rejects if Alice is off by ≥ s -/
lemma bob_sound (o : BOracle ι) (i : OracleId) (cs : c < s) (q0 : 0 < q) {y : ι}
    (bad : |p - (o y).prob true| ≥ s) :
    1 - q ≤ ((bob' c s q i y p).prob' o).prob false := by
  rw [bool_prob_false_of_true, sub_le_sub_iff_left]
  simp only [bob', prob_bind, prob_pure, true_eq_decide_iff, Comp.prob', Comp.prob_bind,
    Comp.prob_pure]
  rw [← pr]
  refine le_trans (pr_mono ?_) (alice_pr_le o i (by linarith) q0 y)
  intro b _ h
  generalize (o y).prob true = x at bad
  have e : b - x = (p - x) - (p - b) := by abel
  rw [e]
  refine le_trans ?_ (abs_sub_abs_le_abs_sub _ _)
  calc (s - c) / 2
    _ ≤ s - (c + s) / 2 := by linarith
    _ ≤ |p - x| - |p - b| := sub_le_sub bad (le_of_lt h)

/-!
## Transposed protocol with Alice moving first, then Bob

As written the debate protocol is awkward to analyze, since Alice's and Bob's moves are
interleaved and intermediate states are discarded.  Therefore, we rewrite it into a
form where Alice moves first, then Bob moves.
-/

/-- All of Alice's moves, and the resulting trace -/
def alices (o : BOracle ι) (alice : Alice ι) : BComp ι u α → Prob (List (ι × ℝ) × α)
  | .pure' x => pure (.nil, x)
  | .sample' p g => do
    let x ← p
    alices o alice (g x)
  | .query' _ _ y f => do
    let q ← (alice y).prob' o
    let x ← bernoulli q
    let (t,z) ← alices o alice (f x)
    return ((y,q) :: t, z)

/-- All of Bob's moves, after Alice's, producing an optional early exit -/
def bobs (o : BOracle ι) (bob : Bob ι) (vera : Vera ι) : List (ι × ℝ) → Prob (Option Bool)
  | [] => pure none
  | (y,q) :: t => do
    let b ← (bob y q).prob' o
    let v ← (vera y q).prob' o
    if b then bobs o bob vera t
    else return some v

/-- All of Alice's moves prior to Bob's, producing the full trace and an optional early exit -/
def trace (o : BOracle ι) (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) (f : BComp ι u α) :
    Prob ((List (ι × ℝ) × α) × Option Bool) := do
  let a ← alices o alice f
  Prod.mk a <$> bobs o bob vera a.1

/-- Extract the final result -/
def extract (x : (List (ι × ℝ) × Bool) × Option Bool) : Bool :=
  match x.2 with
  | none => x.1.2
  | some r => r

/-- debate, with all of Alice's moves prior to Bob's, and producing the full trace -/
def transposed (o : BOracle ι) (alice : Alice ι) (bob : Bob ι) (vera : Vera ι)
    (f : BComp ι u Bool) : Prob Bool :=
  extract <$> trace o alice bob vera f

/-- Shim to turn alices >>= bobs into steps -/
def shim (y : α) : Option Bool → State α
| some r => .error r
| none => .ok y

/-- The transposed formulation of debate is the same -/
lemma debate_eq_transposed (o : BOracle ι) (alice : Alice ι) (bob : Bob ι) (vera : Vera ι)
    (f : BComp ι u Bool) : (debate alice bob vera f).prob' o = transposed o alice bob vera f := by
  have h : ∀ (α : Type) (f : BComp ι u α), (steps alice bob vera f).prob (fun _ ↦ o) =
      alices o alice f >>= fun (t,y) ↦ shim y <$> bobs o bob vera t := by
    intro α f
    induction f with
    | pure' x =>
      simp only [steps, alices, pure_bind, bobs, shim, map_eq, Comp.prob_pure']
    | sample' p g h =>
      simp only [steps, Comp.prob_sample', h, alices, bind_assoc]
    | query' _ _ y f h =>
      simp only [steps, h, alices, bobs, bind_assoc, Comp.prob', Comp.prob_bind, step,
        Comp.prob_allow_all, bind_pure_comp, apply_ite (f := fun f ↦ Comp.prob f fun _ ↦ o),
        Comp.prob_map, Comp.prob_sample, Comp.prob_pure, bind_pure, if_bind, bind_map_left,
        map_bind]
      strip p
      lift (bernoulli _); strip b
      lift (alices _ _ _); strip (t,z)
      strip r
      match r with
      | true => simp only [↓reduceIte, bind_const]
      | false => simp only [Bool.false_eq_true, ↓reduceIte, map_pure, shim, bind_pure_comp]
  simp only [debate, transposed, trace, extract, h, bind_assoc, map_eq, Comp.prob', Comp.prob_bind]
  apply congr_arg₂ _ rfl; funext ⟨p,y⟩; apply congr_arg₂ _ rfl; funext r; match r with
  | some true => simp only [shim, pure_bind, Comp.prob_pure]
  | some false => simp only [shim, pure_bind, Comp.prob_pure]
  | none => simp only [shim, pure_bind, Comp.prob_pure]

/-- Traces are at most `f.worst` long -/
lemma trace_length_le (alice : Alice ι) (f : BComp ι u Bool) {t : List (ι × ℝ) × Bool}
    (p : (alices o alice f).prob t ≠ 0) : t.1.length ≤ f.worst := by
  induction' f with x n p g h i m y f h generalizing t
  · simp only [alices, prob_pure, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    Decidable.not_not] at p
    simp only [p, List.length_nil, Comp.worst_pure', le_refl]
  · simp only [alices, prob_bind_ne_zero] at p
    obtain ⟨x,_,z⟩ := p
    exact le_trans (h _ z) (by bound)
  · simp only [alices, Comp.prob', prob_bind_ne_zero, prob_pure] at p
    obtain ⟨p,p0,b,b0,r,r0,e⟩ := p
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at e
    simp only [e, List.length_cons, Comp.worst_query', add_comm 1, add_le_add_iff_right]
    exact le_trans (h _ r0) (by bound)

/-!
# Close probabilities

We define closeness of probability vectors to match Oracle dist, and a snapping operation
that turns any Alice into an always close Alice.  For close Alices, snap changes probabilities
only moderately.
-/

/-- Closeness of a trace to an oracle -/
def Oracle.close (o : BOracle ι) (e : ℝ) (yp : ι × ℝ) : Prop :=
  |yp.2 - o.prob yp.1| ≤ e

/-- Snap an Alice into a close oracle -/
def snap (o : BOracle ι) (alice : Alice ι) (e : ℝ) : BOracle ι := fun y ↦ do
  let p ← (alice y).prob' o
  let q := (o y).prob true
  let p := if |p - q| ≤ e then p else q
  bernoulli p

/-- Snap produces a close oracle -/
lemma snap_dist (alice : Alice ι) (e0 : 0 < e) : dist o (snap o alice e) ≤ e := by
  simp only [dist]
  refine Real.sSup_le (fun _ ↦ ?_) e0.le
  simp only [mem_range, forall_exists_index]
  intro y h; rw [← h]; clear h
  refine Real.sSup_le (fun _ ↦ ?_) e0.le
  simp only [mem_range, forall_exists_index]
  intro x h; rw [← h]; clear h
  simp only [snap, prob_bind, ← Prob.exp_const_sub]
  nth_rw 1[← Real.norm_eq_abs]
  refine le_trans (map_exp_le _ convexOn_univ_norm (by aesop)) ?_
  refine exp_le_of_forall_le fun q _ ↦ ?_
  simp only [Real.norm_eq_abs,bool_abs_prob_diff true, bernoulli_prob_true', max_comm (0 : ℝ),
    min_comm (1 : ℝ)]
  have m : (o y).prob true = (o y).prob true ⊓ 1 ⊔ 0 := by
    simp only [min_eq_left, max_eq_left, prob_nonneg, prob_le_one]
  nth_rw 1 [m]
  refine le_trans (abs_max_sub_max_le_abs _ _ _) (le_trans (abs_min_sub_min_le_max _ _ _ _) ?_)
  simp only [sub_self, abs_zero, abs_nonneg, sup_of_le_left]
  split_ifs with h
  · rwa [← abs_neg, neg_sub]
  · simp only [sub_self, abs_zero, e0.le]

/-- All of Alice's moves, but with probabilities snapped to close when sampling -/
def snaps (o : BOracle ι) (alice : Alice ι) (e : ℝ) : BComp ι u α → Prob (List (ι × ℝ) × α)
| .pure' x => pure (.nil, x)
| .sample' p g => do snaps o alice e (g (← p))
| .query' _ _ y f => do
  let q ← (alice y).prob' o
  let c := (o y).prob true
  let x ← bernoulli (if |q - c| ≤ e then q else c)
  let (t,z) ← snaps o alice e (f x)
  return ((y,q) :: t, z)

/-- Snapping doesn't changed prob for close p -/
lemma snaps_prob (alice : Alice ι) {z : α} (c : t.Forall (o.close e))
    (f : BComp ι u α) : (snaps o alice e f).prob (t,z) = (alices o alice f).prob (t,z) := by
  induction' f with x n p g h i m y f h generalizing t
  · simp only [snaps, alices]
  · simp only [snaps, prob_bind, h _ c, alices]
  · simp only [snaps, Comp.prob', bind_pure_comp, prob_bind, alices, prob_map]
    strip p
    match t with
    | [] => simp only [Prod.mk.injEq, reduceCtorEq, false_and, pr_false, exp_const]
    | (w,q) :: t =>
      by_cases e : y = w ∧ p = q
      · simp only [List.forall_cons, Oracle.close, Oracle.prob] at c
        rw [e.1]
        simp only [e, c.1, ↓reduceIte, Prod.mk.injEq, List.cons.injEq, true_and]
        simp [← Prod.mk.injEq, pr_eq_prob, h _ c.2]
      · simp only [e, Prod.mk.injEq, List.cons.injEq, false_and, pr_false, exp_const]

/-- Final result of snaps -/
def final (x : List (ι × ℝ) × α) : α := x.2

/-- As an oracle, snaps looks like snap (fold version) -/
lemma snaps_eq_snap_fold (alice : Alice ι) (f : BComp ι u α) :
    Prod.snd <$> snaps o alice e f = f.prob' (snap o alice e) := by
  induction' f with x n p g h i m y f h
  · simp only [snaps, map_pure, Comp.prob', Comp.prob_pure']
  · simp only [snaps, map_bind, h, Comp.prob', Comp.prob_sample']
  · simp only [snaps, Comp.prob', bind_pure_comp, map_bind, Functor.map_map, h, Comp.prob_query',
      snap, bind_assoc]

/-- As an oracle, snaps looks like snap (final version) -/
lemma snaps_eq_snap_final (alice : Alice ι) (f : BComp ι u α) :
    final <$> snaps o alice e f = f.prob' (snap o alice e) := by
  simp only [final, ← snaps_eq_snap_fold, map_eq]

/-!
# Completeness

We assume that
1. The oracle is k-Lipschitz
2. Alice is honest
3. Bob is secretly Eve, and might be evil

Then we have
1. Alice usually gives close probabilities at all steps.
2. When Alice is always close, she is effectively a close oracle,
   so with good probability she produces close probability with final = true.
3. If Alice is close and final = true, Bob has to reject, but Vera usually yells.

We prove all intermediate theorems with flexible constants, then pick at the end.
-/

/-- Alice produces a trace with close probs with good probability -/
lemma alices_close (e0 : 0 < e) (q0 : 0 < q) (q1 : q ≤ 1) (f : BComp ι u α) :
    (1 - q : ℝ) ^ f.worst ≤ (alices o (alice e q) f).pr fun (t,_) ↦ t.Forall (o.close e) := by
  induction' f with x n p g h i m y f h
  · simp only [Comp.worst_pure', pow_zero, alices, pr_pure, List.Forall, ↓reduceIte, le_refl]
  · simp only [Comp.worst_sample', alices, pr_bind]
    exact le_exp_of_forall_le fun x _ ↦ le_trans (by bound) (h _)
  · simp only [Comp.worst_query', alices, pr_bind, pr_pure, List.forall_cons, ite_and_one_zero,
      exp_const_mul, add_comm 1, pow_succ']
    apply le_exp_of_cut (fun x ↦ o.close e (y,x)) (1 - q) ((1 - q) ^ _)
    · apply le_alice_pr o _ e0 q0
    · intro p _ c
      simp only [c, if_true, one_mul]
      exact le_exp_of_forall_le fun x _ ↦ le_trans (by bound) (h _)
    · bound
    · bound

/-- Alice produces `(t,z)` with `t` close and `z = true` with good probability, since if we
    condition on Alice being close she does as least as well as a close oracle. -/
lemma alices_success (f : BComp ι u Bool) (L : f.lipschitz o k)
    (e0 : 0 < e) (q0 : 0 < q) (q1 : q ≤ 1) :
    (f.prob' o).prob true - k * e - ((1:ℝ) - (1 - q : ℝ) ^ f.worst) ≤
      (alices o (alice e q) f).pr (fun (t,z) => t.Forall (o.close e) ∧ z) := by
  trans (snaps o (alice e q) e f).pr (fun (_,z) ↦ z) - (1 - (1 - q) ^ f.worst)
  · apply sub_le_sub_right; trans (f.prob' (snap o (alice e q) e)).prob true
    · have lip := (abs_le.mp (L.le (snap o (alice e q) e) true)).2
      simp only [sub_le_iff_le_add, add_comm _ (k * e)] at lip ⊢
      exact le_trans lip (add_le_add_right (mul_le_mul_of_nonneg_left (snap_dist _ e0) L.k0) _)
    · simp only [← snaps_eq_snap_final, prob_map]
      apply pr_mono; aesop
  · simp only [sub_le_iff_le_add]
    rw [pr_eq_add_of_cut (fun (t,z) => t.Forall (o.close e))]
    apply add_le_add
    · apply exp_mono'
      intro (t,z)
      by_cases c : t.Forall (o.close e)
      · simp only [c, true_and, snaps_prob _ c, and_true, le_refl]
      · simp only [c, false_and, if_false, and_false, mul_zero, le_refl]
    · trans (snaps o (alice e q) e f).pr (fun (t,_) => ¬t.Forall (o.close e))
      · apply pr_mono; intro _ _
        simp only [and_imp, imp_self, implies_true]
      · have ae : (snaps o (alice e q) e f).pr (fun (t,_) => t.Forall (o.close e)) =
            (alices o (alice e q) f).pr (fun (t,_) => t.Forall (o.close e)) := by
          apply exp_congr'; intro (t,_)
          by_cases c : t.Forall (o.close e)
          · simp only [c, if_true, snaps_prob _ c]
          · simp only [c, if_false, smul_zero]
        simp only [pr_neg, ae]
        linarith [alices_close (o := o) e0 q0 q1 f]

/-- If Alice is correct and Bob rejects, the probability of false is low -/
lemma evil_bobs_lies' (eve : Bob ι) (cs : c < s) (v0 : 0 < v) (tc : t.Forall (o.close c)) :
    (bobs o eve (vera c s v) t).cond (fun r ↦ r = some false) (fun r ↦ r.isSome) ≤ v := by
  have v0' := le_of_lt v0
  induction' t with y t h
  · simp only [bobs, cond_pure, reduceCtorEq, Option.isSome_none, Bool.false_eq_true, and_self,
      ↓reduceIte, v0']
  · simp only [List.forall_cons] at tc
    refine le_trans (cond_bind_le_of_cut (fun b : Bool ↦ b)) (max_le ?_ ?_)
    · apply cond_bind_le_second (fun r ↦ r = some false) (fun r ↦ r.isSome) (fun b ↦ b = true) v0'
      intro b _ be
      simp only [Comp.prob', be, ↓reduceIte, bind_const, h tc.2]
    · apply cond_bind_le_second (fun r ↦ r = some false) (fun r ↦ r.isSome) (fun b ↦ ¬b = true) v0'
      intro b _ be
      simp only [Bool.not_eq_true] at be
      simp only [Comp.prob', be, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, cond_map,
        some.injEq, Option.isSome_some, Prob.cond_true, pr_eq_prob]
      exact bob_complete _ _ cs v0 tc.1

/-- If Alice is good, the probability of false is low -/
lemma evil_bobs_lies (eve : Bob ι) (cs : c < s) (v0 : 0 < v) (tc : t.Forall (o.close c)) :
    (bobs o eve (vera c s v) t).pr (fun r ↦ extract ((t,true),r) = false) ≤ v := by
  rw [pr_eq_cond_add_cond (fun r : Option Bool ↦ r.isSome)]
  have b1 : (bobs o eve (vera c s v) t).cond (fun r ↦ extract ((t,true),r) = false)
      (fun r ↦ ¬r.isSome) = 0 := by
    apply cond_eq_zero; intro r _ ri
    simp only [Option.not_isSome_iff_eq_none] at ri
    simp [ri, extract]
  simp only [b1, zero_mul, add_zero]
  refine le_trans (mul_le_of_le_one_right cond_nonneg pr_le_one) ?_
  refine le_trans (le_of_eq ?_) (evil_bobs_lies' eve cs v0 tc)
  apply cond_congr; intro r _ ri; match r with
  | some r => simp only [extract, Option.some_inj]
  | none => simp at ri

/-- Alice wins the debate with good probability -/
theorem completeness' (f : BComp ι u Bool) (L : f.lipschitz o k) (eve : Bob ι)
    (c0 : 0 < c) (cs : c < s) (q0 : 0 < q) (q1 : q ≤ 1) (v0 : 0 < v) (v1 : v ≤ 1) :
    (1 - v) * ((f.prob' o).prob true - k * c - (1 - (1 - q) ^ f.worst)) ≤
      ((debate (alice c q) eve (vera c s v) f).prob' o).prob true := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ← pr_eq_prob]
  refine le_trans ?_ (le_pr_bind_of_cut _ (1-v) (alices_success f L c0 q0 q1) ?_ ?_)
  · simp only [mul_comm _ (1-v), pr_eq_prob, le_refl]
  · intro ⟨t,z⟩ _ h
    simp only [pr_map] at h ⊢
    have b : (bobs o eve (vera c s v) t).pr (fun r ↦ ¬extract ((t,z),r) = true) ≤ v := by
      simp only [Bool.not_eq_true, h.2]
      exact evil_bobs_lies eve cs v0 h.1
    simp only [pr_neg] at b
    linarith
  · linarith

/-
# Soudness

We assume that
1. The oracle is k-Lipschitz
2. Bob is honest
3. Alice is secretly Eve, and might be evil

Then we have
1. Alice can't raise the probability of success too much with close p, by Lipschitz.
2. If Alice gives close p, Bob rarely rejects.
3. If Alice is ever not close, Bob usually rejects, and Vera agrees.

For soundness, the threshold for close is s > c, where c is the smaller threshold
for closeness during completeness.
-/

/-- Evil Alice produces a close true trace with low probability, since by remaining close
    she looks like a close oracle. -/
lemma evil_alices_lies (f : BComp ι u Bool) (L : f.lipschitz o k) (eve : Alice ι) (e0 : 0 < e) :
    (alices o eve f).pr (fun (t,z) ↦ t.Forall (o.close e) ∧ z) ≤
      (f.prob' o).prob true + k * e := by
  trans (snaps o eve e f).pr (fun (t,z) ↦ t.Forall (o.close e) ∧ z)
  · apply le_of_eq; apply exp_congr'; intro (t,_)
    by_cases c : t.Forall (o.close e)
    · simp only [c, true_and, snaps_prob _ c]
    · simp only [c, false_and, if_false, smul_zero]
  · trans (f.prob' (snap o eve e)).prob true
    · simp only [← snaps_eq_snap_final, prob_map]
      apply pr_mono; intro (p,y) _; simp only [final, and_imp, imp_self, implies_true]
    · have lip := (abs_le.mp (L.le (snap o eve e) true)).1
      rw [le_sub_iff_add_le, add_comm, ←sub_eq_add_neg, sub_le_iff_le_add] at lip
      exact le_trans lip (add_le_add_left (mul_le_mul_of_nonneg_left (snap_dist _ e0) L.k0) _)

/-- A score to take into account Vera's failure probability if Bob rejects -/
def vera_score (v : ℝ) : Option Bool → ℝ
| none => 1 - v
| some false => 1
| some true => 0

-- Macros for simple `vera_score` inequalities
macro "verarith" : tactic => `(tactic| focus { simp only [vera_score]; linarith })
macro "verariths" r:term : term => `(term|
  by match ($r) with | none => verarith | some false => verarith | some true => verarith)

-- `vera_score` is in `[0,1]` for sensible `v` -/
@[bound] lemma vera_score_nonneg (v1 : v ≤ 1) (r : Option Bool) : 0 ≤ vera_score v r := verariths r
@[bound] lemma vera_score_le_one (v0 : 0 ≤ v) (r : Option Bool) : vera_score v r ≤ 1 := verariths r

/-- `Option Bool`'s univ -/
lemma option_bool_univ : (.univ : Finset (Option Bool)) = {some true, some false, none} := by decide

/-- If Honest Bob rejects, Vera usually complains. We formulate this in terms of an auxiliary
    probability `rest` since this shows up in our two uses below. -/
lemma bob_safe (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1) (qv : q ≤ v)
    {y : ι} {p : ℝ} {n : ℕ} {rest : ℝ} (h : (1 - v) * (1 - q) ^ n ≤ rest) (rest0 : 0 ≤ rest) :
    (1 - v) * (1 - q) ^ n * (1 - q) ≤
      ((bob s b q y p).prob fun _ ↦ o).prob false * ((vera c s v y p).prob fun _ ↦ o).prob false +
      ((bob s b q y p).prob fun _ ↦ o).prob true * rest := by
  by_cases ys : o.close s (y,p)
  · rw [mul_comm _ rest]
    refine le_trans (mul_le_mul h ?_ (by linarith) (by bound)) (le_add_of_nonneg_left (by bound))
    exact bob_complete' o BobId sb q0 ys
  · generalize ha : ((bob s b q y p).prob fun _ ↦ o).prob false = a
    generalize hr : (1 - q) ^ n = r at h
    simp only [bool_prob_true_of_false, ha, mul_comm (1 - a)]
    trans a * (1 - v) * r + (1 - v) * r * (1 - a)
    · simp only [mul_assoc a, mul_comm a (_ * _), ← mul_add, add_sub_cancel, mul_one]
      bound
    · have vs : 1 - v ≤ ((vera c s v y p).prob fun x ↦ o).prob false :=
        bob_sound o VeraId cs v0 (not_le.mp ys).le
      refine add_le_add (le_trans (mul_le_of_le_one_right ?_ ?_) ?_) ?_
      all_goals bound

/-- If Honest Bob rejects, Vera usually complains.  The error probability is higher if Bob
    does complain, though, so we use an expectation over vera_score. -/
lemma bobs_safe (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1)
    (qv : q ≤ v) (t : List (ι × ℝ)) :
    (1 - v) * (1 - q) ^ t.length ≤ (bobs o (bob s b q) (vera c s v) t).exp (vera_score v) := by
  induction' t with y t h
  · simp only [List.length_nil, pow_zero, mul_one, bobs, exp_pure, vera_score, le_refl]
  · simp only [List.length_cons, pow_succ, ← mul_assoc, bobs, Comp.prob', exp_bind,
      apply_ite (f := fun p ↦ Prob.exp p (vera_score v)), exp_pure, vera_score, exp_bool,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Bool.false_eq_true, ↓reduceIte, add_zero, ← add_mul,
      bool_total', one_mul]
    exact bob_safe cs sb q0 v0 v1 qv h (by bound)

/-- If Alice lies about probabilities by more than b, Bob usually catches Alice in a lie -/
lemma bobs_catches (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1)
    (qv : q ≤ v) {t : List (ι × ℝ)} (tb : ¬t.Forall (o.close b)) :
    (1 - v) * (1 - q) ^ t.length ≤
      (bobs o (bob s b q) (vera c s v) t).pr (fun r ↦ r = some false) := by
  induction' t with y t h
  · simp only [List.Forall, not_true_eq_false] at tb
  · simp only [List.length_cons, pow_succ, ← mul_assoc, bobs, pr_bind]
    by_cases yb : ¬o.close b y
    · refine le_trans ?_ (le_exp_of_cut (fun x ↦ x = false) (1 - q) (1 - v) ?_ ?_ (by bound)
        (by linarith))
      · rw [mul_comm (1 - q)]
        bound
      · simp only [pr_eq_prob]
        exact bob_sound o BobId sb q0 (not_le.mp yb).le
      · intro b _ b0
        simp only [b0, Bool.false_eq_true, ↓reduceIte, pr_pure, some.injEq, exp_eq_prob]
        exact bob_sound o VeraId cs v0 (le_of_lt (lt_trans sb (not_le.mp yb)))
    · simp only [not_not] at yb
      simp only [List.forall_cons, yb, true_and] at tb
      simp only [exp_bool, smul_eq_mul, Bool.false_eq_true, ↓reduceIte, pr_pure, mul_one,
        some.injEq, Bool.true_eq_false, mul_zero, add_zero, ← add_mul, bool_total', one_mul]
      exact bob_safe cs sb q0 v0 v1 qv (h tb) (by bound)

/-- Bob wins the debate with good probability -/
theorem soundness' (f : BComp ι u Bool) (L : f.lipschitz o k) (eve : Alice ι)
    (c0 : 0 < c) (cs : c < s) (sb : s < b) (q0 : 0 < q) (v0 : 0 < v) (v1 : v ≤ 1) (qv : q ≤ v) :
    (1 - v) * (1 - q) ^ f.worst * ((f.prob' o).prob false - k * b) ≤
      ((debate eve (bob s b q) (vera c s v) f).prob' o).prob false := by
  simp only [debate_eq_transposed, transposed, trace, map_bind, ← pr_eq_prob (alices _ _ _ >>= _)]
  have lies := evil_alices_lies f L eve (lt_trans c0 (lt_trans cs sb))
  rw [pr_neg', sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add, bool_prob_true_of_false] at lies
  simp only [not_and_or, Bool.not_eq_true] at lies
  ring_nf at lies
  rw [mul_comm]
  refine le_pr_bind_of_cut _ _ lies ?_ (by bound)
  intro (t,z) t0 h
  simp only [pr_map]
  trans (1 - v) * (1 - q) ^ t.length
  · bound [trace_length_le eve f t0]
  · cases' h with h h
    · refine le_trans (bobs_catches cs sb q0 v0 v1 qv h) ?_
      exact pr_mono fun r _ e ↦ by simp only [e, extract]
    · simp only at h
      have safe := bobs_safe (o := o) cs sb q0 v0 v1 qv t
      simp only [@exp_fintype (Option Bool), option_bool_univ, smul_eq_mul, Finset.mem_insert,
        some.injEq, Bool.true_eq_false, Finset.mem_singleton, reduceCtorEq, or_self, extract, h,
        not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, ↓reduceIte, pr] at safe ⊢
      exact le_trans safe (by bound)

/-
# Parameters

We now fill in parameters.  We are given

  w = win margin of the computation: 1/2 < w ≤ (o.final t).prob true if we're in the language
  k = Lipschitz constant of the oracle
  t = steps, eliding the +1 in t+1 above
  d = desired win margin of the debate protocol

and we must set

  c = completeness threshold, which honest Alice tries to stay within
  s = soundness threshold, outside of which Vera usually complains
  b = bad threshold, outside of which Bob usually complains
  q = Alice's and Bob's per-step failure probability (we assume these are equal for simplicity)
  v = Vera's failure probability

The sample counts are (ignoring ceils)

  an = samples (alice c q) = log (2/q) / (2 c^2)
  bn = samples (bob s b q) = samples (alice (b-s)/2 q) = 2 log (2/q) / (b-s)^2
  vn = samples (vera c s v) = 2 log (2/v) / (s-c)^2

From completeness and soundness, we have

  d = (1-v) (w - k c - (1 - (1-q)^t)) ~ (1-v) (w - k c - q t)
  d = (1-v) (1-q)^t (w - k b)         ~ (1-v) (1 - q t) (w - k b)

Let v vary subject to d > (1-v) w.  Then we need

  d/(1-v) = w - k c - q t
  d/(1-v) = (1 - q t) (w - k b)

We want Alice and Bob to need the same number of samples, so

  log (2/q) / (2 c^2) = 2 log (2/q) / (b-s)^2
  (b-s)^2 = 4 c^2
  b - s = 2c
  b = 2c + s

Meh, let's get very lazy:
-/

/-- A valid set of parameters for the debate protocol -/
structure Params (w d k : ℝ) (t : ℕ) where
  /-- Vera's failure probability -/
  v : ℝ
  /-- Alice's probability goal: Honest Alice's claimed probabilities are usually off by `≤ c` -/
  c : ℝ
  /-- Vera's acceptance probability goal: Vera usually accepts if probabilities are off by `≤ s` -/
  s : ℝ
  /-- Vera's rejection probability goal: Vera usually rejects if probabilities are off by `≥ b` -/
  b : ℝ
  /-- Alice's and Bob's failure probability -/
  q : ℝ
  /-- Basic inequalities -/
  k0 : 0 < k
  c0 : 0 < c := by positivity
  cs : c < s
  sb : s < b
  q0 : 0 < q := by positivity
  q1 : q ≤ 1
  v0 : 0 < v := by positivity
  v1 : v ≤ 1
  qv : q ≤ v
  bw : k * b ≤ w
  /-- Inequality sufficient for completeness -/
  complete : d ≤ (1-v) * (w - k * c - q * t)
  /-- Inequality sufficient for soundness -/
  sound : d ≤ (1-v) * (1 - q * t) * (w - k * b)

-- Register `Params` fields for use with `bound`
attribute [bound_forward] Params.k0 Params.c0 Params.cs Params.sb Params.q0 Params.q1 Params.v0
  Params.v1 Params.qv Params.bw

/-- Completeness for any valid parameters -/
theorem completeness_p (f : BComp ι u Bool) (L : f.lipschitz o k) (eve : Bob ι)
    {w d : ℝ} (p : Params w d k f.worst) (m : w ≤ (f.prob' o).prob true) :
    d ≤ ((debate (alice p.c p.q) eve (vera p.c p.s p.v) f).prob' o).prob true := by
  refine le_trans (le_trans p.complete ?_) (completeness' f L eve p.c0 p.cs p.q0 p.q1 p.v0 p.v1)
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right m _) ?_) (by linarith [p.v1])
  rw [neg_le_neg_iff, sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add, mul_comm, sub_eq_add_neg,
    ← mul_neg]
  apply one_add_mul_le_pow
  linarith [p.q1]

/-- Soundness for any valid parameters -/
theorem soundness_p (f : BComp ι u Bool) (L : f.lipschitz o k) (eve : Alice ι)
    {w d : ℝ} (p : Params w d k f.worst) (m : w ≤ (f.prob' o).prob false) :
    d ≤ ((debate eve (bob p.s p.b p.q) (vera p.c p.s p.v) f).prob' o).prob false := by
  refine le_trans (le_trans p.sound ?_) (soundness' f L eve p.c0 p.cs p.sb p.q0 p.v0 p.v1 p.qv)
  simp only [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ ?_ ?_) (by linarith [p.v1])
  · rw [mul_comm, sub_eq_add_neg, ← mul_neg]
    apply one_add_mul_le_pow
    bound
  · apply add_le_add_right m
  · bound
  · bound

lemma t_div_le_one (t : ℕ) : (t : ℝ) / max 1 t ≤ 1 := by bound

/-- Default valid parameters (not tuned) -/
def defaults (k : ℝ) (t : ℕ) (k0 : 0 < k) : Params (2/3) (3/5) k t where
  v := 1 / 100
  c := 1 / (100 * k)
  s := 2 / (100 * k)
  b := 5 / (100 * k)
  q := 1 / (100 * max 1 t)
  k0 := k0
  cs := by bound
  sb := by bound
  v1 := by norm_num
  q1 := by bound
  qv := by bound
  bw := by
    simp only [div_eq_mul_inv, mul_inv, ←mul_assoc, mul_comm _ k⁻¹, inv_mul_cancel₀ (ne_of_gt k0)]
    norm_num
  complete := by
    simp only [←mul_div_assoc, mul_one, mul_comm _ k, ←div_div, div_self (ne_of_gt k0)]
    rw [mul_comm_div]
    bound [t_div_le_one t]
  sound := by
    simp only [← mul_div_assoc, mul_comm _ k, ← div_div]
    rw [mul_comm k 5, mul_div_assoc, div_self (ne_of_gt k0), mul_comm_div]
    bound [t_div_le_one t]
