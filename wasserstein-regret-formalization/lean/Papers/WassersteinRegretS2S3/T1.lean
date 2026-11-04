module
public import Papers.WassersteinRegretS2S3.Helpers.ConditionComparison
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentGeometry
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Population Wasserstein regret: T1

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: localMinimax_matrix
/-- For [a joint law with finite second moments](hyp:P) and [a nonnegative
Wasserstein radius](hyp:eps), [local minimax regret equals matrix minimax regret
over the Bures ball around the law's second-moment matrix](goal). -/
lemma localMinimax_matrix {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) :
    localMinimax P eps = matrixMinimaxValue (momentPSD P) eps := by
  rw [localMinimax_coefficient_formula]
  unfold matrixMinimaxValue matrixWorstRegret
  apply iInf_congr
  intro A
  simp_rw [fun Q => (law_matrix_risk_regret Q A).2]
  exact law_matrix_sup P eps (fun S => ENNReal.ofReal (matrixRegret A S))

-- @node: conditionNumber_matrix
/-- For [a joint law with positive definite feature second moment](hyp:P),
[the law's condition number equals the matrix condition number of its joint
second-moment matrix](goal). -/
lemma conditionNumber_matrix {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) :
    conditionNumber P.carrier.val = matrixCondition (momentPSD P.carrier.val) := by
  rw [conditionNumber, if_pos P.carrier.property]
  simp_rw [localMinimax_matrix]
  rfl

-- @node: conditionNumber_ne_top
/-- For [a joint law with positive definite feature second moment](hyp:P),
[the condition number is finite](goal). -/
lemma conditionNumber_ne_top {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) : conditionNumber P.carrier.val ≠ ⊤ := by
  rw [conditionNumber_matrix]
  exact matrixCondition_ne_top (assPin1_valid m) assSingularValueConvention_valid
    ⟨⟨momentPSD P.carrier.val, P.carrier.property⟩⟩

-- @node: localMinimax_normalized_tendsto
/-- For [a joint law with positive definite feature second moment](hyp:P),
[local minimax regret divided by the squared radius converges to the condition
number as the radius decreases to zero, in the extended nonnegative reals](goal). -/
lemma localMinimax_normalized_tendsto {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) :
    Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * localMinimax P.carrier.val eps)
      positiveRadii (nhds (conditionNumber P.carrier.val)) := by
  simp_rw [localMinimax_matrix, conditionNumber_matrix]
  exact matrixMinimax_normalized_tendsto (assPin1_valid m) assSingularValueConvention_valid
    ⟨⟨momentPSD P.carrier.val, P.carrier.property⟩⟩

-- @node: localMinimax_normalized_toReal_tendsto
/-- For [a joint law with positive definite feature second moment](hyp:P),
[the real value of local minimax regret divided by the squared radius converges
to the real value of the condition number as the radius decreases to zero](goal). -/
lemma localMinimax_normalized_toReal_tendsto {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) :
    Filter.Tendsto (fun eps : ℝ≥0 => (localMinimax P.carrier.val eps).toReal / (eps : ℝ) ^ 2)
      positiveRadii (nhds (conditionNumber P.carrier.val).toReal) := by
  have h := (ENNReal.tendsto_toReal (conditionNumber_ne_top P)).comp
    (localMinimax_normalized_tendsto P)
  simpa only [Function.comp_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.coe_toReal, div_eq_mul_inv, inv_pow, mul_comm] using h

-- @node: localMinimax_quadratic_expansion
/-- For [a joint law with positive definite feature second moment](hyp:P),
[there is a remainder negligible relative to the squared radius such that,
at all sufficiently small positive radii, local minimax regret is finite and
its real value equals the condition number times the squared radius plus
that remainder](goal). -/
lemma localMinimax_quadratic_expansion {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) :
    ∃ rem : ℝ≥0 → ℝ,
      Asymptotics.IsLittleO positiveRadii rem (fun eps => (eps : ℝ) ^ 2) ∧
      (∀ᶠ eps : ℝ≥0 in positiveRadii,
        localMinimax P.carrier.val eps ≠ ⊤ ∧
        (localMinimax P.carrier.val eps).toReal = (conditionNumber P.carrier.val).toReal *
          (eps : ℝ) ^ 2 + rem eps) := by
  let rem : ℝ≥0 → ℝ := fun eps => (localMinimax P.carrier.val eps).toReal -
    (conditionNumber P.carrier.val).toReal * (eps : ℝ) ^ 2
  have hpos : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  refine ⟨rem, ?_, ?_⟩
  · apply Asymptotics.isLittleO_of_tendsto'
      (hpos.mono fun eps heps hz => False.elim (ne_of_gt (sq_pos_of_pos
        (show 0 < (eps : ℝ) from heps)) hz))
    have h := (localMinimax_normalized_toReal_tendsto P).sub_const
      (conditionNumber P.carrier.val).toReal
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [hpos] with eps heps
    dsimp only [rem]
    have he : (eps : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (show 0 < (eps : ℝ) from heps))
    field_simp
  · have hfinite := (localMinimax_normalized_tendsto P).eventually
      (eventually_lt_nhds (lt_top_iff_ne_top.mpr (conditionNumber_ne_top P)))
    filter_upwards [hpos, hfinite] with eps heps hf
    refine ⟨?_, by dsimp only [rem]; ring⟩
    apply (ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt hf) ?_).ne
    exact pow_ne_zero 2 (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)

-- @node: thm:condition-number-formula
/-- Assume [the squared Euclidean norm is the sum of squared response coordinates](hyp:hpin)
and [singular values are nonnegative and decreasing, with the minimum at the
smaller matrix dimension](hyp:hsv). For [a joint law with positive definite
feature second moment](hyp:P), [the condition number is finite, normalized local
minimax regret converges to it, and local minimax regret has a quadratic expansion
with a remainder negligible relative to the squared radius; the condition number
equals one plus the largest eigenvalue of the sum of the optimal coefficient
matrix times its transpose and the residual second moment divided by the smallest
feature eigenvalue, and lies between one plus the maximum and one plus the sum
of the squared coefficient operator norm and the ratio of the largest residual
eigenvalue to the smallest feature eigenvalue](goal). -/
theorem conditionNumberFormula {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m) :
    conditionNumber P.carrier.val ≠ ⊤ ∧
    Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * localMinimax P.carrier.val eps)
      positiveRadii (nhds (conditionNumber P.carrier.val)) ∧
    (∃ rem : ℝ≥0 → ℝ,
      Asymptotics.IsLittleO positiveRadii rem (fun eps => (eps : ℝ) ^ 2) ∧
      (∀ᶠ eps : ℝ≥0 in positiveRadii,
        localMinimax P.carrier.val eps ≠ ⊤ ∧
        (localMinimax P.carrier.val eps).toReal = (conditionNumber P.carrier.val).toReal * (eps
          : ℝ) ^ 2 + rem eps)) ∧
    conditionNumber P.carrier.val = ENNReal.ofReal
      (1 + lambdaMax (optimalPredictor P * (optimalPredictor P).transpose +
        (lambdaMin (secondMomentX P.carrier.val))⁻¹ • residualSecondMoment P)) ∧
    ENNReal.ofReal (1 + max (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val))) ≤
        conditionNumber P.carrier.val ∧
    conditionNumber P.carrier.val ≤ ENNReal.ofReal (1 + opNorm (optimalPredictor P) ^ 2 +
      lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val)) := by
  let Sigma : NondegenerateSecondMoments p m :=
    ⟨⟨momentPSD P.carrier.val, P.carrier.property⟩⟩
  have hc : conditionNumber P.carrier.val = alternativeConditionNumber Sigma := by
    rw [conditionNumber_matrix]
    exact matrixCondition_eq_alternativeConditionNumber hpin hsv Sigma
  have hb := altConditionNumberClosedForm hpin hsv Sigma
  have hres := (residual_law_matrix P).1
  have hpred := optimalPredictor_eq_canonical P
  refine ⟨conditionNumber_ne_top P, localMinimax_normalized_tendsto P,
    localMinimax_quadratic_expansion P, ?_, ?_, ?_⟩
  · rw [hc, hb.1]
    simp only [conditionSpectral, Sigma, momentPSD]
    rw [← hpred, ← hres]
  · rw [hc]
    simpa only [conditionLower, Sigma, momentPSD, ← hpred, ← hres] using hb.2.1
  · rw [hc]
    simpa only [conditionUpper, Sigma, momentPSD, ← hpred, ← hres] using hb.2.2

end Papers.WassersteinRegretS2S3
