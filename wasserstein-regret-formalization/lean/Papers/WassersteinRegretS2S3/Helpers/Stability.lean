module
public import Papers.WassersteinRegretS2S3.T1
public import Papers.WassersteinRegretS2S3.Helpers.RefinedStability

/-!
# Population Wasserstein regret: Helpers/Stability

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:regret-stability
/-- Assume [the squared Euclidean norm equals the sum of squared response
coordinates](hyp:hpin) and [singular values are ordered nonincreasingly,
nonnegative, and use the smaller-dimension convention for the minimum](hyp:hsv).
For [a coefficient matrix A](hyp:A), [a reference law P with finite second
moments and a positive definite feature second-moment matrix](hyp:P), and
[another joint law Q with finite second moments](hyp:Q), [the absolute change in
the square root of A's regret is at most the Wasserstein distance from P to Q
times the sum of twice the square root of P's condition number and A's operator
norm; moreover, the regret under Q of P's optimal predictor is at most four
times P's condition number times the squared Wasserstein distance](goal). -/
lemma regretStability {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (A : Mat m p)
    (P : NondegenerateLaws p m) (Q : JointLaws p m) :
    |Real.sqrt (regret A P.carrier.val) - Real.sqrt (regret A Q)| ≤
      (2 * Real.sqrt (conditionNumber P.carrier.val).toReal + opNorm A) * wassersteinDistance
        P.carrier.val Q ∧
    ENNReal.ofReal (regret (optimalPredictor P) Q) ≤
      4 * conditionNumber P.carrier.val * ENNReal.ofReal (wassersteinDistance P.carrier.val Q)
         ^ 2 := by
  have hf := conditionNumberFormula hpin hsv P
  have hl : 1 + max (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val)) ≤
      (conditionNumber P.carrier.val).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hf.1).mp hf.2.2.2.2.1
  have hA : Real.sqrt (1 + opNorm (optimalPredictor P) ^ 2) ≤
      Real.sqrt (conditionNumber P.carrier.val).toReal := by
    apply Real.sqrt_le_sqrt
    exact (add_le_add_right (le_max_left _ _) 1).trans hl
  have hE : Real.sqrt (lambdaMax (residualSecondMoment P) /
      lambdaMin (secondMomentX P.carrier.val)) ≤
      Real.sqrt (conditionNumber P.carrier.val).toReal := by
    apply Real.sqrt_le_sqrt
    have hm := le_max_right (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val))
    linarith
  let eps : ℝ≥0 := ⟨wassersteinDistance P.carrier.val Q, wasserstein_nonneg _ _⟩
  have hQ : Q ∈ lawBall P.carrier.val eps := by
    change wassersteinDistance P.carrier.val Q ≤ (eps : ℝ)
    exact le_rfl
  refine ⟨regret_stability_of_spectral_bounds hpin hsv eps A P Q hQ _ hA hE, ?_⟩
  have hb := optimal_regret_of_spectral_bounds hpin hsv eps P Q hQ _
    ENNReal.toReal_nonneg hA hE
  have he := ENNReal.ofReal_le_ofReal hb
  change ENNReal.ofReal (regret (optimalPredictor P) Q) ≤
    ENNReal.ofReal (4 * (conditionNumber P.carrier.val).toReal *
      wassersteinDistance P.carrier.val Q ^ 2) at he
  simpa only [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      ENNReal.toReal_nonneg), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf.1,
    ENNReal.ofReal_pow (wasserstein_nonneg _ _), eps, NNReal.coe_mk, ENNReal.ofReal_ofNat] using he

end Papers.WassersteinRegretS2S3
