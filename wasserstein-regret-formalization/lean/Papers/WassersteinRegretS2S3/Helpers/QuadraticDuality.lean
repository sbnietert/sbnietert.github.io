module
public import Papers.WassersteinRegretS2S3.Helpers.Cited
public import Papers.WassersteinRegretS2S3.Helpers.Resolvent
public import Mathlib.Data.EReal.Basic

/-!
# Population Wasserstein regret: Helpers/QuadraticDuality

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

/-- For [a linear transformation M](hyp:M), [a matrix center](hyp:center), and
[a real penalty multiplier eta](hyp:eta), the [quadratic envelope](goal) is the supremum
over all matrices W of the squared Frobenius norm of M times W minus eta times the
squared Frobenius distance from W to the center. -/
noncomputable def quadraticEnvelope {k d r : ℕ} (M : Mat k d) (center : Mat d r) (eta : ℝ) :
  EReal :=
  ⨆ W : Mat d r, ((frob (M * W) ^ 2 - eta * frob (W - center) ^ 2 : ℝ) : EReal)
/-- For [a linear transformation M](hyp:M), [a matrix center](hyp:center),
[a squared-radius threshold t](hyp:t), and [a real multiplier eta](hyp:eta), the
[quadratic dual term](goal) is eta times the sum of t and the trace of the inverse
of eta times the identity minus M times its transpose, multiplied by M, the center,
the transpose of the center, and the transpose of M, in that order. -/
noncomputable def quadraticDualTerm {k d r : ℕ} (M : Mat k d) (center : Mat d r) (t eta : ℝ) : ℝ :=
  eta * (t + Matrix.trace ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ *
    M * center * center.transpose * M.transpose))

-- @node: frob_sq_add_trace
/-- [The squared Frobenius norm of U plus V equals the sum of their squared
Frobenius norms plus twice the trace of the transpose of U times V](goal). -/
lemma frob_sq_add_trace {a b : ℕ} (U V : Mat a b) :
    frob (U + V) ^ 2 = frob U ^ 2 +
      2 * Matrix.trace (U.transpose * V) + frob V ^ 2 := by
  have hc : Matrix.trace (V.transpose * U) = Matrix.trace (U.transpose * V) := by
    rw [← Matrix.trace_transpose (V.transpose * U)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [frob_sq_trace, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, hc]
  ring

-- @node: quadraticBall_completion
/-- If [M transpose times M times star equals eta times the displacement of star
from the center](hyp:hstar), [the penalized quadratic objective at W equals its
value at star plus the squared Frobenius norm of M times the displacement from
star, minus eta times the squared Frobenius norm of that displacement](goal). -/
lemma quadraticBall_completion {k d r : ℕ} (M : Mat k d)
    (center star W : Mat d r) (eta : ℝ)
    (hstar : M.transpose * (M * star) = eta • (star - center)) :
    frob (M * W) ^ 2 - eta * frob (W - center) ^ 2 =
      (frob (M * star) ^ 2 - eta * frob (star - center) ^ 2) +
        frob (M * (W - star)) ^ 2 - eta * frob (W - star) ^ 2 := by
  have hgrad : (M * star).transpose * M = eta • (star - center).transpose := by
    have h := congrArg Matrix.transpose hstar
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul] using h
  have hcross : Matrix.trace ((M * star).transpose * (M * (W - star))) =
      eta * Matrix.trace ((star - center).transpose * (W - star)) := by
    rw [← Matrix.mul_assoc, hgrad, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hW : W = star + (W - star) := by abel
  have hC : W - center = (star - center) + (W - star) := by abel
  conv_lhs => arg 1; arg 1; rw [hW, Matrix.mul_add]
  rw [hC, frob_sq_add_trace, frob_sq_add_trace, hcross]
  ring

-- @node: quadraticBall_resolvent_maximizer
/-- If [eta exceeds the squared operator norm of M](hyp:heta), [there is a matrix
star satisfying the stationarity equation M transpose times M times star equals
eta times its displacement from the center, whose penalized objective equals eta
times the trace of the inverse of eta times the identity minus M times its
transpose, multiplied by M, the center, the center's transpose, and M's
transpose](goal). -/
lemma quadraticBall_resolvent_maximizer {k d r : ℕ} [NeZero k] [NeZero d]
    (M : Mat k d) (center : Mat d r) (eta : ℝ) (heta : opNorm M ^ 2 < eta) :
    ∃ star : Mat d r,
      M.transpose * (M * star) = eta • (star - center) ∧
      frob (M * star) ^ 2 - eta * frob (star - center) ^ 2 =
        eta * Matrix.trace ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ *
          M * center * center.transpose * M.transpose) := by
  let D : Mat d d := eta • 1 - M.transpose * M
  let R : Mat k k := eta • 1 - M * M.transpose
  have hnorm : opNorm (M.transpose * M) < eta := by
    exact (opNorm_mul_le M.transpose M).trans_lt
      (by rw [opNorm_transpose]; simpa [pow_two] using heta)
  have hD : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp (resolvent_isUnit _ eta hnorm)
  let star := eta • (D⁻¹ * center)
  have hn : D * star = eta • center := by
    simp only [star, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv D hD, Matrix.one_mul]
  have hstat : M.transpose * (M * star) = eta • (star - center) := by
    have h := hn
    change (eta • (1 : Mat d d) - M.transpose * M) * star = eta • center at h
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc] at h
    rw [smul_sub]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm
  have hid : star - center = M.transpose * R⁻¹ * M * center := by
    have h := (rectangularResolventIdentities M eta heta).2.2.2
    change eta • D⁻¹ = 1 + M.transpose * R⁻¹ * M at h
    have hm := congrArg (fun B => B * center) h
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul] at hm
    change star - center = _
    exact sub_eq_iff_eq_add.mpr (hm.trans (by abel))
  have hvalue : frob (M * star) ^ 2 =
      eta * Matrix.trace (star.transpose * (star - center)) := by
    rw [frob_sq_trace, Matrix.transpose_mul, Matrix.mul_assoc, hstat,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hc : Matrix.trace (star.transpose * (star - center)) -
      Matrix.trace ((star - center).transpose * (star - center)) =
      Matrix.trace (center.transpose * (star - center)) := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub]
    ring
  have ht : Matrix.trace (center.transpose * (star - center)) =
      Matrix.trace (R⁻¹ * M * center * center.transpose * M.transpose) := by
    rw [hid]
    calc
      _ = Matrix.trace ((center.transpose * M.transpose) * (R⁻¹ * M * center)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  refine ⟨star, hstat, ?_⟩
  rw [hvalue, frob_sq_trace, ← mul_sub, hc, ht]

-- @node: quadraticBall_envelope
/-- If [eta exceeds the squared operator norm of M](hyp:heta), [the quadratic
envelope equals eta times the trace of the inverse of eta times the identity
minus M times its transpose, multiplied by M, the center, the center's transpose,
and M's transpose](goal). -/
lemma quadraticBall_envelope {k d r : ℕ} [NeZero k] [NeZero d]
    (M : Mat k d) (center : Mat d r) (eta : ℝ) (heta : opNorm M ^ 2 < eta) :
    quadraticEnvelope M center eta =
      ((eta * Matrix.trace ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ *
        M * center * center.transpose * M.transpose) : ℝ) : EReal) := by
  obtain ⟨star, hstat, hvalue⟩ := quadraticBall_resolvent_maximizer M center eta heta
  apply le_antisymm
  · refine iSup_le fun W => EReal.coe_le_coe ?_
    rw [quadraticBall_completion M center star W eta hstat, hvalue]
    have hn := frob_mul_left_le M (W - star)
    have hs : frob (M * (W - star)) ^ 2 ≤ opNorm M ^ 2 * frob (W - star) ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (frob_nonneg _) hn 2
    nlinarith [mul_nonneg (sub_nonneg.mpr heta.le) (sq_nonneg (frob (W - star)))]
  · exact le_iSup_of_le star (by rw [hvalue])

-- @node: nonnegative_multiplier_iInf
/-- [The infimum of a plus eta times c over nonnegative multipliers eta is a when
c is nonnegative, and negative infinity when c is negative](goal). -/
lemma nonnegative_multiplier_iInf (a c : ℝ) :
    (⨅ (eta : ℝ) (_ : 0 ≤ eta), ((a + eta * c : ℝ) : EReal)) =
      if 0 ≤ c then (a : EReal) else ⊥ := by
  split_ifs with hc
  · apply le_antisymm
    · exact (iInf_le_of_le 0 (iInf_le_of_le (le_refl 0) (by simp)))
    · refine le_iInf fun eta => le_iInf fun heta => ?_
      exact EReal.coe_le_coe (by nlinarith [mul_nonneg heta hc])
  · apply (EReal.eq_bot_iff_forall_lt _).2
    intro y
    have hc' : 0 < -c := by linarith
    let eta := (|a - y| + 1) / (-c)
    have heta : 0 ≤ eta := le_of_lt (div_pos (by positivity) hc')
    have heq : eta * c = -(|a - y| + 1) := by
      dsimp [eta]
      field_simp [show c ≠ 0 by linarith]
    refine lt_of_le_of_lt (iInf_le_of_le eta (iInf_le_of_le heta le_rfl)) ?_
    apply EReal.coe_lt_coe_iff.2
    rw [heq]
    linarith [le_abs_self (a - y)]

-- @node: quadraticBall_primal_lagrangian
/-- [The supremum of the squared Frobenius norm of M times W over matrices whose
squared distance from the center is at most t equals the supremum over all W of
the infimum over nonnegative eta of that objective plus eta times the remaining
squared-distance budget](goal). -/
lemma quadraticBall_primal_lagrangian {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t : ℝ) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) =
    ⨆ W : Mat d r, ⨅ (eta : ℝ) (_ : 0 ≤ eta),
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal) := by
  congr 1
  funext W
  rw [nonnegative_multiplier_iInf]
  by_cases hW : frob (W - center) ^ 2 ≤ t
  · simp [hW, sub_nonneg.mpr hW]
  · simp [hW, show ¬0 ≤ t - frob (W - center) ^ 2 from fun h => hW (sub_nonneg.mp h)]

-- @node: quadraticBall_weak_duality
/-- [The supremum of the squared Frobenius norm of M times W subject to squared
distance from the center at most t is bounded above by the infimum over
nonnegative eta of the unrestricted supremum of that objective plus eta times
the remaining squared-distance budget](goal), including when the constraint is infeasible. -/
lemma quadraticBall_weak_duality {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t : ℝ) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) ≤
    ⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal) := by
  refine iSup_le fun W => iSup_le fun hW => le_iInf fun eta => le_iInf fun heta => ?_
  refine le_iSup_of_le W (EReal.coe_le_coe ?_)
  nlinarith [mul_nonneg heta (sub_nonneg.mpr hW)]

-- @node: quadraticBall_maximum
/-- If [the squared-radius threshold t is nonnegative](hyp:ht), [the squared
Frobenius norm of M times W has a finite, attained maximum over matrices whose
squared Frobenius distance from the center is at most t](goal). -/
lemma quadraticBall_maximum {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t : ℝ) (ht : 0 ≤ t) :
    ∃ gamma : ℝ, IsGreatest {v : ℝ | ∃ W : Mat d r,
      frob (W - center) ^ 2 ≤ t ∧ frob (M * W) ^ 2 = v} gamma := by
  have hfrob (W : Mat d r) : frob W = ‖W‖ := by
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have hset : {W : Mat d r | frob (W - center) ^ 2 ≤ t} =
      Metric.closedBall center (Real.sqrt t) := by
    ext W
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, ← hfrob]
    exact (Real.le_sqrt (frob_nonneg _) ht).symm
  have hcompact : IsCompact {W : Mat d r | frob (W - center) ^ 2 ≤ t} := by
    rw [hset]
    exact isCompact_closedBall _ _
  have hcont : Continuous (fun W : Mat d r => frob (M * W) ^ 2) := by
    unfold frob
    fun_prop
  obtain ⟨W, hW, hmax⟩ := hcompact.exists_isMaxOn
    (show Set.Nonempty {W : Mat d r | frob (W - center) ^ 2 ≤ t} from
      ⟨center, by simpa [frob] using ht⟩) hcont.continuousOn
  refine ⟨frob (M * W) ^ 2, ⟨W, hW, rfl⟩, ?_⟩
  rintro v ⟨V, hV, rfl⟩
  exact hmax hV

-- @node: quadraticBall_strong_duality_pos
/-- If [the squared-radius threshold t is positive](hyp:ht), [the supremum of the
squared Frobenius norm of M times W on the ball centered at the given center
equals the infimum over nonnegative eta of the unrestricted supremum of that
objective plus eta times the remaining squared-distance budget](goal). -/
lemma quadraticBall_strong_duality_pos {k d r : ℕ} [NeZero k] [NeZero d] [NeZero r]
    (M : Mat k d) (center : Mat d r) (t : ℝ) (ht : 0 < t) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) =
    ⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal) := by
  obtain ⟨gamma, hgamma⟩ := quadraticBall_maximum M center t ht.le
  obtain ⟨eta, heta, hcert⟩ := CitedQuadraticBallSLemma M center t gamma ht hgamma
  apply le_antisymm (quadraticBall_weak_duality M center t)
  obtain ⟨W, hW, hval⟩ := hgamma.1
  calc
    _ ≤ ⨆ V : Mat d r,
        ((frob (M * V) ^ 2 + eta * (t - frob (V - center) ^ 2) : ℝ) : EReal) :=
      iInf_le_of_le eta (iInf_le_of_le heta le_rfl)
    _ ≤ (gamma : EReal) := iSup_le fun V => EReal.coe_le_coe (by linarith [hcert V])
    _ ≤ _ := by
      rw [← hval]
      exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)

-- @node: quadraticBall_penalty_bound
/-- For [a positive error allowance delta](hyp:hdelta), [the squared Frobenius
norm of M times W, less its squared distance from the center times the penalty
coefficient given by the squared operator norm of M plus the square of the
product of that norm and the Frobenius norm of M times the center divided by
delta, is at most the squared Frobenius norm of M times the center plus delta](goal). -/
lemma quadraticBall_penalty_bound {k d r : ℕ}
    (M : Mat k d) (center W : Mat d r) (delta : ℝ) (hdelta : 0 < delta) :
    frob (M * W) ^ 2 -
        (opNorm M ^ 2 + (opNorm M * frob (M * center)) ^ 2 / delta) *
          frob (W - center) ^ 2 ≤ frob (M * center) ^ 2 + delta := by
  have hf (V : Mat k r) : frob V = ‖V‖ := by
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have htri : frob (M * W) ≤ frob (M * center) + opNorm M * frob (W - center) := by
    calc
      _ = frob (M * center + M * (W - center)) := by
        congr 1
        simp [Matrix.mul_sub]
      _ ≤ frob (M * center) + frob (M * (W - center)) := by
        simpa only [hf] using norm_add_le (M * center) (M * (W - center))
      _ ≤ _ := add_le_add_right (frob_mul_left_le M (W - center)) _
  have hs := pow_le_pow_left₀ (frob_nonneg _) htri 2
  have hy : 2 * (opNorm M * frob (M * center)) * frob (W - center) ≤
      delta + (opNorm M * frob (M * center)) ^ 2 / delta * frob (W - center) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hdelta).mp
    have hdiv : (opNorm M * frob (M * center)) ^ 2 / delta * delta =
        (opNorm M * frob (M * center)) ^ 2 := div_mul_cancel₀ _ hdelta.ne'
    nlinarith [sq_nonneg (delta - opNorm M * frob (M * center) * frob (W - center))]
  nlinarith

-- @node: quadraticBall_dual_upper
/-- If [delta is positive](hyp:hdelta) and [eta is at least the squared operator
norm of M plus the square of the product of that norm and the Frobenius norm of
M times the center divided by delta](hyp:heta), [the unrestricted supremum of the
squared Frobenius norm of M times W plus eta times the remaining squared-distance
budget is at most the squared Frobenius norm of M times the center plus delta
plus eta times t](goal). -/
lemma quadraticBall_dual_upper {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t delta eta : ℝ) (hdelta : 0 < delta)
    (heta : opNorm M ^ 2 + (opNorm M * frob (M * center)) ^ 2 / delta ≤ eta) :
    (⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) ≤
        ((frob (M * center) ^ 2 + delta + eta * t : ℝ) : EReal) := by
  refine iSup_le fun W => EReal.coe_le_coe ?_
  have hp := quadraticBall_penalty_bound M center W delta hdelta
  nlinarith [mul_nonneg (sub_nonneg.mpr heta) (sq_nonneg (frob (W - center)))]

-- @node: quadraticBall_primal_zero
/-- [The supremum of the squared Frobenius norm of M times W subject to squared
distance from the center at most zero equals the squared Frobenius norm of M
times the center](goal). -/
lemma quadraticBall_primal_zero {k d r : ℕ} (M : Mat k d) (center : Mat d r) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ 0),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) = (frob (M * center) ^ 2 : ℝ) := by
  apply le_antisymm
  · refine iSup_le fun W => iSup_le fun hW => ?_
    have hz : frob (W - center) = 0 := by nlinarith [sq_nonneg (frob (W - center))]
    have hf : frob (W - center) = ‖W - center‖ := by
      simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
    have he : W = center := sub_eq_zero.mp (norm_eq_zero.mp (hf.symm.trans hz))
    subst W
    exact le_rfl
  · exact le_iSup_of_le center (le_iSup_of_le (by simp [frob]) le_rfl)

-- @node: quadraticBall_strong_duality_zero
/-- [The supremum of the squared Frobenius norm of M times W on the ball with
zero squared radius equals the infimum over nonnegative eta of the unrestricted
supremum of that objective minus eta times the squared distance from the center](goal). -/
lemma quadraticBall_strong_duality_zero {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ 0),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) =
    ⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (0 - frob (W - center) ^ 2) : ℝ) : EReal) := by
  apply le_antisymm (quadraticBall_weak_duality M center 0)
  rw [quadraticBall_primal_zero]
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hd : 0 < z - frob (M * center) ^ 2 := by
    exact sub_pos.mpr (EReal.coe_lt_coe_iff.mp hz)
  let eta := opNorm M ^ 2 + (opNorm M * frob (M * center)) ^ 2 /
    (z - frob (M * center) ^ 2)
  have he : 0 ≤ eta := by dsimp [eta]; positivity
  refine (iInf_le_of_le eta (iInf_le_of_le he le_rfl)).trans ?_
  have hupper := quadraticBall_dual_upper M center 0
    (z - frob (M * center) ^ 2) eta hd le_rfl
  have heq : frob (M * center) ^ 2 + (z - frob (M * center) ^ 2) + eta * 0 = z := by ring
  simpa only [heq] using hupper

-- @node: quadraticBall_strong_duality_neg
/-- If [the squared-radius threshold t is negative](hyp:ht), [the constrained
supremum of the squared Frobenius norm of M times W equals the infimum over
nonnegative eta of the unrestricted supremum of that objective plus eta times
the remaining squared-distance budget](goal).

Both values are negative infinity because the constraint is infeasible. -/
lemma quadraticBall_strong_duality_neg {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t : ℝ) (ht : t < 0) :
    (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) =
    ⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal) := by
  have hp : (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t),
      ((frob (M * W) ^ 2 : ℝ) : EReal)) = ⊥ := by
    apply le_antisymm _ bot_le
    refine iSup_le fun W => iSup_le fun hW => ?_
    exact False.elim (not_le_of_gt ht ((sq_nonneg _).trans hW))
  rw [hp]
  symm
  apply (EReal.eq_bot_iff_forall_lt _).2
  intro y
  let base := opNorm M ^ 2 + (opNorm M * frob (M * center)) ^ 2
  let eta := base + (|frob (M * center) ^ 2 + 1 - y| + 1) / (-t)
  have hb : 0 ≤ base := by dsimp [base]; positivity
  have he : base ≤ eta := by
    dsimp [eta]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by linarith))
  have heta : 0 ≤ eta := hb.trans he
  have hprod : (eta - base) * (-t) = |frob (M * center) ^ 2 + 1 - y| + 1 := by
    dsimp [eta]
    rw [add_sub_cancel_left, div_mul_cancel₀ _ (neg_ne_zero.mpr ht.ne)]
  refine lt_of_le_of_lt (iInf_le_of_le eta (iInf_le_of_le heta le_rfl)) ?_
  refine (quadraticBall_dual_upper M center t 1 eta zero_lt_one
    (by simpa [base] using he)).trans_lt ?_
  apply EReal.coe_lt_coe_iff.mpr
  nlinarith [le_abs_self (frob (M * center) ^ 2 + 1 - y), mul_nonpos_of_nonneg_of_nonpos hb ht.le]

-- @node: quadraticBall_bounded_coefficient
/-- If [the squared Frobenius norm of M times W plus eta times the remaining
squared-distance budget is at most v for every W](hyp:hv), [the squared Frobenius
norm of M times V is at most eta times the squared Frobenius norm of V](goal). -/
lemma quadraticBall_bounded_coefficient {k d r : ℕ}
    (M : Mat k d) (center : Mat d r) (t eta v : ℝ)
    (hv : ∀ W : Mat d r,
      frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) ≤ v)
    (V : Mat d r) : frob (M * V) ^ 2 ≤ eta * frob V ^ 2 := by
  have hsm (s : ℝ) (U : Mat d r) : frob (s • U) ^ 2 = s ^ 2 * frob U ^ 2 := by
    simp only [frob_sq, Matrix.smul_apply, smul_eq_mul, mul_pow,
      ← Finset.mul_sum]
  have hsm' (s : ℝ) (U : Mat k r) : frob (s • U) ^ 2 = s ^ 2 * frob U ^ 2 := by
    simp only [frob_sq, Matrix.smul_apply, smul_eq_mul, mul_pow,
      ← Finset.mul_sum]
  have hb (s : ℝ) : s ^ 2 * (frob (M * V) ^ 2 - eta * frob V ^ 2) ≤
      v - frob (M * center) ^ 2 - eta * t := by
    have hp := hv (center + s • V)
    have hm := hv (center + (-s) • V)
    simp only [Matrix.mul_add, Matrix.mul_smul, frob_sq_add_trace,
      add_sub_cancel_left, hsm, hsm', Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul] at hp hm
    nlinarith
  by_contra hn
  have ha : 0 < frob (M * V) ^ 2 - eta * frob V ^ 2 := sub_pos.mpr (lt_of_not_ge hn)
  let a := frob (M * V) ^ 2 - eta * frob V ^ 2
  let c := v - frob (M * center) ^ 2 - eta * t
  have hs := hb (Real.sqrt ((|c| + 1) / a))
  have he : (Real.sqrt ((|c| + 1) / a)) ^ 2 = (|c| + 1) / a :=
    Real.sq_sqrt (div_nonneg (by positivity) ha.le)
  rw [he, div_mul_cancel₀ _ ha.ne'] at hs
  linarith [le_abs_self c]

-- @node: quadraticBall_bounded_spectral_threshold
/-- If [eta is nonnegative](hyp:heta) and [the squared Frobenius norm of M times W
plus eta times the remaining squared-distance budget is at most v for every
W](hyp:hv), [the squared operator norm of M is at most eta](goal). -/
lemma quadraticBall_bounded_spectral_threshold {k d r : ℕ} [NeZero r]
    (M : Mat k d) (center : Mat d r) (t eta v : ℝ) (heta : 0 ≤ eta)
    (hv : ∀ W : Mat d r,
      frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) ≤ v) :
    opNorm M ^ 2 ≤ eta := by
  classical
  have hn : opNorm M ≤ Real.sqrt eta := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    let V : Mat d r := fun i j => if j = 0 then x i else 0
    have hV : frob V ^ 2 = ‖x‖ ^ 2 := by
      rw [frob_sq, EuclideanSpace.real_norm_sq_eq]
      simp [V]
    have hMV : frob (M * V) ^ 2 = ‖matrixCLM M x‖ ^ 2 := by
      rw [frob_sq, EuclideanSpace.real_norm_sq_eq]
      change (∑ i, ∑ j, (∑ l, M i l * V l j) ^ 2) = _
      simp [V, mul_ite, matrixCLM, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    have h := quadraticBall_bounded_coefficient M center t eta v hv V
    rw [hV, hMV] at h
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt heta] using h
  have ho : 0 ≤ opNorm M := norm_nonneg _
  nlinarith [Real.sq_sqrt heta]
-- @node: quadraticBall_dual_formula
/-- If [eta exceeds the squared operator norm of M](hyp:heta), [the unrestricted
supremum of the squared Frobenius norm of M times W plus eta times the remaining
squared-distance budget equals the quadratic dual term for M, the center, t,
and eta](goal). -/
lemma quadraticBall_dual_formula {k d r : ℕ} [NeZero k] [NeZero d]
    (M : Mat k d) (center : Mat d r) (t eta : ℝ) (heta : opNorm M ^ 2 < eta) :
    (⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) =
      (quadraticDualTerm M center t eta : EReal) := by
  obtain ⟨star, _, hvalue⟩ := quadraticBall_resolvent_maximizer M center eta heta
  have hbound (W : Mat d r) :=
    (le_iSup (fun V : Mat d r =>
      ((frob (M * V) ^ 2 - eta * frob (V - center) ^ 2 : ℝ) : EReal)) W).trans_eq
        (quadraticBall_envelope M center eta heta)
  apply le_antisymm
  · refine iSup_le fun W => EReal.coe_le_coe ?_
    have hb := EReal.coe_le_coe_iff.mp (hbound W)
    unfold quadraticDualTerm
    linarith
  · refine le_iSup_of_le star (EReal.coe_le_coe ?_)
    unfold quadraticDualTerm
    linarith

-- @node: quadraticBall_multiplier_restriction
/-- [The infimum over nonnegative eta of the unrestricted supremum of the squared
Frobenius norm of M times W plus eta times the remaining squared-distance budget
equals the infimum of the quadratic dual term over eta strictly exceeding the
squared operator norm of M](goal). -/
lemma quadraticBall_multiplier_restriction {k d r : ℕ} [NeZero k] [NeZero d] [NeZero r]
    (M : Mat k d) (center : Mat d r) (t : ℝ) :
    (⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
      ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) =
    ⨅ (eta : ℝ) (_ : opNorm M ^ 2 < eta), (quadraticDualTerm M center t eta : EReal) := by
  apply le_antisymm
  · refine le_iInf fun eta => le_iInf fun heta => ?_
    rw [← quadraticBall_dual_formula M center t eta heta]
    exact iInf_le_of_le eta (iInf_le_of_le ((sq_nonneg _).trans heta.le) le_rfl)
  · refine le_iInf fun eta => le_iInf fun heta => ?_
    apply EReal.le_of_forall_lt_iff_le.mp
    intro y hy
    obtain ⟨v, hv, hvy⟩ := EReal.exists_between_coe_real hy
    have hbound (W : Mat d r) :
        frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) ≤ v := by
      exact EReal.coe_le_coe_iff.mp ((le_iSup _ W).trans hv.le)
    have hb := quadraticBall_bounded_spectral_threshold M center t eta v heta hbound
    have hgap : 0 < y - v := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hvy)
    let delta := (y - v) / (|t| + 1)
    have hd : 0 < delta := div_pos hgap (by positivity)
    have hnew : opNorm M ^ 2 < eta + delta := by linarith
    refine (iInf_le_of_le (eta + delta) (iInf_le_of_le hnew le_rfl)).trans ?_
    rw [← quadraticBall_dual_formula M center t (eta + delta) hnew]
    refine iSup_le fun W => EReal.coe_le_coe ?_
    have he : delta * (|t| + 1) = y - v := div_mul_cancel₀ _ (by positivity)
    have ht : delta * t ≤ delta * (|t| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self t]) hd.le
    have hw := hbound W
    nlinarith [mul_nonneg hd.le (sq_nonneg (frob (W - center)))]

-- @node: lem:quadratic-ball-duality
/-- [Above the squared operator norm of M, the quadratic envelope has the
resolvent trace formula; for every real squared-radius threshold, the constrained
quadratic supremum equals the supremum of the pointwise infimum of its
Lagrangian, this supremum and infimum can be interchanged, and the resulting
dual equals the infimum of the quadratic dual term over multipliers strictly
above the squared operator norm of M](goal).

The resolvent formula is eta times the trace of the inverse of eta times the
identity minus M times its transpose, multiplied by M, the center, the center's
transpose, and M's transpose. The Lagrangian adds eta times the remaining
squared-distance budget to the squared Frobenius norm of M times W. -/
lemma quadraticBallDuality {k d r : ℕ} [NeZero k] [NeZero d] [NeZero r]
    (M : Mat k d) (center : Mat d r) :
    (∀ eta : ℝ, opNorm M ^ 2 < eta → quadraticEnvelope M center eta =
      ((eta * Matrix.trace ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ *
        M * center * center.transpose * M.transpose) : ℝ) : EReal)) ∧
    (∀ t : ℝ,
      (⨆ (W : Mat d r) (_ : frob (W - center) ^ 2 ≤ t), ((frob (M * W) ^ 2 : ℝ) : EReal)) =
        ⨆ W : Mat d r, ⨅ (eta : ℝ) (_ : 0 ≤ eta),
          ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) ∧
    (∀ t : ℝ,
      (⨆ W : Mat d r, ⨅ (eta : ℝ) (_ : 0 ≤ eta),
        ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) =
      ⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
        ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) ∧
    (∀ t : ℝ,
      (⨅ (eta : ℝ) (_ : 0 ≤ eta), ⨆ W : Mat d r,
        ((frob (M * W) ^ 2 + eta * (t - frob (W - center) ^ 2) : ℝ) : EReal)) =
      ⨅ (eta : ℝ) (_ : opNorm M ^ 2 < eta), (quadraticDualTerm M center t eta : EReal)) := by
  refine ⟨?_, quadraticBall_primal_lagrangian M center, ?_, ?_⟩
  · exact quadraticBall_envelope M center
  · intro t
    by_cases ht : 0 < t
    · rw [← quadraticBall_primal_lagrangian M center t]
      exact quadraticBall_strong_duality_pos M center t ht
    · rw [← quadraticBall_primal_lagrangian M center t]
      rcases lt_or_eq_of_le (le_of_not_gt ht) with hneg | rfl
      · exact quadraticBall_strong_duality_neg M center t hneg
      · exact quadraticBall_strong_duality_zero M center
  · exact quadraticBall_multiplier_restriction M center
-- @realizes b(squared Euclidean operator norm threshold)
-- @realizes \bW(unrestricted real matrix optimization variable)
-- @realizes \tilde{\bW}(arbitrary real matrix center)
-- @realizes k(positive row dimension) @realizes r(positive factor column dimension)

end Papers.WassersteinRegretS2S3
