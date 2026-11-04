module
public import Papers.WassersteinRegretS2S3.Helpers.AlternativeCondition
public import Papers.WassersteinRegretS2S3.Helpers.Kronecker
public import Papers.WassersteinRegretS2S3.Helpers.ConditionSensitivity
public import Papers.WassersteinRegretS2S3.Helpers.SpectralBounds
public import Papers.WassersteinRegretS2S3.Helpers.ConditionKroneckerSpectral

/-!
# Population Wasserstein regret: Helpers/ConditionClosedForm

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:alt-condition-number-closed-form
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [the alternative condition number of
a nondegenerate joint second moment equals one plus the largest eigenvalue of the
sum of the coefficient matrix times its transpose and the residual moment divided
by the smallest feature eigenvalue; it lies between one plus the maximum and one
plus the sum of the squared coefficient operator norm and the ratio of the largest
residual eigenvalue to the smallest feature eigenvalue](goal). -/
lemma altConditionNumberClosedForm {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m) :
    alternativeConditionNumber Sigma = ENNReal.ofReal (conditionSpectral Sigma.carrier.val.val) ∧
    ENNReal.ofReal (conditionLower Sigma.carrier.val.val) ≤ alternativeConditionNumber Sigma ∧
    alternativeConditionNumber Sigma ≤ ENNReal.ofReal (conditionUpper Sigma.carrier.val.val) :=
      by
  have hformula : alternativeConditionNumber Sigma =
      ENNReal.ofReal (conditionSpectral Sigma.carrier.val.val) := by
    rw [alternativeConditionNumber_kronecker_sphere Sigma]
    let S := Sigma.carrier.val.val
    let A := canonicalCoefficient S
    have hE : (matrixResidual S).PosSemidef :=
      Sigma.carrier.val.property.mul_mul_conjTranspose_same (quadraticRegressionMatrix A)
    have hG : (A * A.transpose).IsHermitian := by
      simpa using (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian
    rw [condition_kronecker_spectral_sup _ _ _ Sigma.carrier.property.inv.isHermitian hE hG,
      lambdaMax_inv_eq_inv_lambdaMin _ Sigma.carrier.property]
    rfl
  have hb := conditionSpectral_bounds Sigma
  exact ⟨hformula, hformula ▸ ENNReal.ofReal_le_ofReal hb.1,
    hformula ▸ ENNReal.ofReal_le_ofReal hb.2⟩

end Papers.WassersteinRegretS2S3
