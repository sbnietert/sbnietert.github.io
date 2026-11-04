module
public import Papers.WassersteinRegretS2S3.Helpers.AlternativeCondition
public import Papers.WassersteinRegretS2S3.Helpers.ConditionDuality

/-!
# Whitened derivative sensitivity

Connect the derivative formula to the feature and response dual calculation.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: condition_inverse_sqrt_identities
/-- If [M is positive definite](hyp:hM), then [the inverse of its positive semidefinite
square root is symmetric, whitens M when multiplied on both sides, has square equal to
the inverse of M, and equals the inverse of M times its positive semidefinite square
root](goal). -/
lemma condition_inverse_sqrt_identities {p : ℕ} (M : Mat p p) (hM : M.PosDef) :
    let H := (CFC.sqrt M)⁻¹
    H.transpose = H ∧ H * M * H = 1 ∧ H * H = M⁻¹ ∧ M⁻¹ * CFC.sqrt M = H := by
  let R := CFC.sqrt M
  have hR : R.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hsq : R * R = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hi := (Matrix.isUnit_iff_isUnit_det R).mp
    ((CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit)
  have hl := Matrix.nonsing_inv_mul R hi
  have hr := Matrix.mul_nonsing_inv R hi
  change (R⁻¹).transpose = R⁻¹ ∧ R⁻¹ * M * R⁻¹ = 1 ∧
    R⁻¹ * R⁻¹ = M⁻¹ ∧ M⁻¹ * R = R⁻¹
  refine ⟨hR.inv.isHermitian.eq, ?_, ?_, ?_⟩
  · rw [← hsq, ← Matrix.mul_assoc, hl, Matrix.one_mul, hr]
  · rw [← hsq, Matrix.mul_inv_rev]
  · rw [← hsq, Matrix.mul_inv_rev, Matrix.mul_assoc, hl, Matrix.mul_one]

-- @node: condition_factor_tangent_blocks
/-- If [S is symmetric](hyp:hS), then [the feature block of S times the transpose of D
plus D times S is the upper row block of S times the transpose of the upper row block
of D plus the upper row block of D times the transpose of the upper row block of S,
and its response-feature block is the lower row block
of S times the transpose of the upper row block of D plus the lower row block of D
times the transpose of the upper row block of S](goal). -/
lemma condition_factor_tangent_blocks {p m : ℕ} (S D : Mat (p + m) (p + m))
    (hS : S.transpose = S) :
    blockX p m (S * D.transpose + D * S) =
      (factorBlocks p m S).1 * (factorBlocks p m D).1.transpose +
        (factorBlocks p m D).1 * (factorBlocks p m S).1.transpose ∧
    blockYX p m (S * D.transpose + D * S) =
      (factorBlocks p m S).2 * (factorBlocks p m D).1.transpose +
        (factorBlocks p m D).2 * (factorBlocks p m S).1.transpose := by
  have he : S * D.transpose + D * S = S * D.transpose + D * S.transpose := by rw [hS]
  rw [he]
  constructor <;> ext i j <;> rfl

-- @node: condition_derivative_whitened
/-- [For the nondegenerate second moments Sigma and perturbation D, derivative
sensitivity equals the squared Frobenius norm of the residual times the transpose of
the upper perturbation block times the inverse feature square root, minus the
regression coefficient times the upper perturbation block times the whitened feature
matrix, plus the lower perturbation block times that whitened feature matrix](goal).
The feature and response factors are the upper and lower row blocks of the positive
semidefinite square root of Sigma; the residual is the response factor minus the
regression coefficient times the feature factor, and the whitened feature matrix is
the transpose of the feature factor times the inverse square root of the feature moment. -/
lemma condition_derivative_whitened {p m : ℕ} (Sigma : NondegenerateSecondMoments p m)
    (D : Mat (p + m) (p + m)) :
    let S := CFC.sqrt Sigma.carrier.val.val
    let X := (factorBlocks p m S).1
    let Y := (factorBlocks p m S).2
    let A := canonicalCoefficient Sigma.carrier.val.val
    let H := (CFC.sqrt (blockX p m Sigma.carrier.val.val))⁻¹
    derivativeSensitivity Sigma.carrier.val D =
      frob ((Y - A * X) * (factorBlocks p m D).1.transpose * H -
        A * (factorBlocks p m D).1 * (X.transpose * H) +
        (factorBlocks p m D).2 * (X.transpose * H)) ^ 2 := by
  dsimp only
  rw [derivativeSensitivity, parameterMap_fderiv_apply _ Sigma.carrier.property]
  rw [← canonicalCoefficient_eq_parameterMap _ Sigma.carrier.property]
  have ht := condition_factor_tangent_blocks (CFC.sqrt Sigma.carrier.val.val) D
    (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  dsimp only [factorTangent, symOfPSD]
  rw [ht.1, ht.2, Matrix.mul_assoc,
    (condition_inverse_sqrt_identities _ Sigma.carrier.property).2.2.2]
  congr 2
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

-- @node: condition_sqrt_factor_geometry
/-- [For nondegenerate second moments Sigma in positive feature and response dimensions,
the transpose of the feature factor times the inverse square root of the feature moment
has orthonormal columns, the residual factor times this whitened feature matrix is
zero, and the residual factor times its transpose equals the residual moment matrix](goal).
The feature and response factors are the upper and lower row blocks of the positive
semidefinite square root of Sigma, and the residual factor is the response factor minus
the canonical regression coefficient times the feature factor. -/
lemma condition_sqrt_factor_geometry {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : NondegenerateSecondMoments p m) :
    let S := CFC.sqrt Sigma.carrier.val.val
    let X := (factorBlocks p m S).1
    let Y := (factorBlocks p m S).2
    let A := canonicalCoefficient Sigma.carrier.val.val
    let H := (CFC.sqrt (blockX p m Sigma.carrier.val.val))⁻¹
    let Q := X.transpose * H
    let E := Y - A * X
    Q.transpose * Q = 1 ∧ E * Q = 0 ∧
      E * E.transpose = matrixResidual Sigma.carrier.val.val := by
  dsimp only
  have hf := psd_sqrt_factor Sigma.carrier.val
  have hX := (factor_gram_blocks (CFC.sqrt Sigma.carrier.val.val)).1
  rw [← hf] at hX
  have hi := condition_inverse_sqrt_identities _ Sigma.carrier.property
  obtain ⟨_, _, _, horth, _, hres, _⟩ := regretProjectionFormula
    (assPin1_valid m) assSingularValueConvention_valid Sigma.carrier.val
    (CFC.sqrt Sigma.carrier.val.val) hf
  refine ⟨condition_whitened_gram _ _ hi.1 ?_, ?_, hres⟩
  · rw [← hX]
    exact hi.2.1
  · rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]

-- @node: alternativeConditionNumber_kronecker_ball
/-- [For nondegenerate second moments Sigma in positive feature and response dimensions,
the alternative condition number equals the supremum over matrices B of Frobenius norm
at most one of the quadratic form at the vectorized B of the Kronecker sum of the inverse
feature moment with the residual moment and the identity with the canonical regression
coefficient times its transpose, plus the squared Frobenius norm of B, interpreted in
the extended nonnegative reals](goal). -/
lemma alternativeConditionNumber_kronecker_ball {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : NondegenerateSecondMoments p m) :
    alternativeConditionNumber Sigma =
      ⨆ (B : Mat m p) (_ : frob B ≤ 1),
        ENNReal.ofReal (Matrix.vec B ⬝ᵥ
          ((Matrix.kronecker (blockX p m Sigma.carrier.val.val)⁻¹
              (matrixResidual Sigma.carrier.val.val) +
            Matrix.kronecker (1 : Mat p p)
              (canonicalCoefficient Sigma.carrier.val.val *
                (canonicalCoefficient Sigma.carrier.val.val).transpose)) *ᵥ Matrix.vec B) +
          frob B ^ 2) := by
  rw [(altConditionNumberFormula (assPin1_valid m)).1 Sigma]
  simp_rw [condition_derivative_whitened Sigma]
  have hi := condition_inverse_sqrt_identities _ Sigma.carrier.property
  have hg := condition_sqrt_factor_geometry Sigma
  rw [condition_primal_kronecker_ball_sup _ _ _ _ hi.1 hg.1 hg.2.1]
  dsimp only at hi hg ⊢
  rw [hi.2.2.1, hg.2.2]

-- @node: condition_homogeneous_ball_sphere_sup
/-- If [F is nonnegative at every matrix](hyp:hF) and [scaling a matrix by any real
number scales F by the square of that number](hyp:hhom), then [the supremum of F over
the Frobenius unit ball equals its supremum over the Frobenius unit sphere, in the
extended nonnegative reals](goal). -/
lemma condition_homogeneous_ball_sphere_sup {m p : ℕ} (F : Mat m p → ℝ)
    (hF : ∀ B, 0 ≤ F B) (hhom : ∀ (r : ℝ) B, F (r • B) = r ^ 2 * F B) :
    (⨆ (B : Mat m p) (_ : frob B ≤ 1), ENNReal.ofReal (F B)) =
      ⨆ (B : Mat m p) (_ : frob B = 1), ENNReal.ofReal (F B) := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    by_cases hz : frob B = 0
    · have hzero : B = 0 := by
        apply norm_eq_zero.mp
        rwa [← frob_eq_matrix_norm]
      have hfzero : F 0 = 0 := by simpa using hhom 0 (0 : Mat m p)
      simp [hzero, hfzero]
    · have hp : 0 < frob B := lt_of_le_of_ne (frob_nonneg B) (Ne.symm hz)
      let C := (frob B)⁻¹ • B
      have hC : frob C = 1 := by
        rw [frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hp), ← frob_eq_matrix_norm]
        exact inv_mul_cancel₀ hz
      have hBC : frob B • C = B := by simp [C, smul_smul, hz]
      have heq : F B = frob B ^ 2 * F C := by
        conv_lhs => rw [← hBC]
        exact hhom _ _
      refine le_iSup_of_le C (le_iSup_of_le hC (ENNReal.ofReal_le_ofReal ?_))
      rw [heq]
      exact mul_le_of_le_one_left (hF C) (by nlinarith [frob_nonneg B])
  · exact iSup_le fun B => iSup_le fun hB =>
      le_iSup_of_le B (le_iSup_of_le hB.le le_rfl)

-- @node: condition_primal_kronecker_sphere_sup
/-- If [H is symmetric](hyp:hH), [Q has orthonormal columns](hyp:hQ), and [E times Q is
zero](hyp:hEQ), then [the supremum of the squared Frobenius norm of E times the transpose
of the upper perturbation block times H minus A times that block times Q plus the lower
block times Q, over stacked perturbations of Frobenius norm at most one, equals the
supremum over B of Frobenius norm one of one plus the quadratic form at the vectorized B
of the Kronecker sum of H squared with E times its transpose and the identity with A
times its transpose](goal). Both suprema are taken in the extended nonnegative reals. -/
lemma condition_primal_kronecker_sphere_sup {m p d : ℕ}
    (A : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    (⨆ (D : Mat (p + m) d) (_ : frob D ≤ 1),
      ENNReal.ofReal (frob (E * (factorBlocks p m D).1.transpose * H -
        A * (factorBlocks p m D).1 * Q + (factorBlocks p m D).2 * Q) ^ 2)) =
    ⨆ (B : Mat m p) (_ : frob B = 1),
      ENNReal.ofReal (1 + Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker (H * H) (E * E.transpose) +
          Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ Matrix.vec B)) := by
  rw [condition_primal_dual_ball_sup A H E Q hH]
  rw [condition_homogeneous_ball_sphere_sup
    (fun B : Mat m p => frob (H * B.transpose * E - A.transpose * B * Q.transpose) ^ 2 +
      frob (B * Q.transpose) ^ 2) (by intro B; positivity) (by
        intro r B
        have he : H * (r • B).transpose * E - A.transpose * (r • B) * Q.transpose =
            r • (H * B.transpose * E - A.transpose * B * Q.transpose) := by
          simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [he, Matrix.smul_mul]
        simp only [frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring)]
  apply iSup_congr; intro B
  apply iSup_congr; intro hB
  rw [condition_dual_kronecker_decomposition A B H E Q hH hQ hEQ, hB]
  congr 1
  ring

-- @node: alternativeConditionNumber_kronecker_sphere
/-- [For nondegenerate second moments Sigma in positive feature and response dimensions,
the alternative condition number equals the supremum over matrices B of Frobenius norm
one of one plus the quadratic form at the vectorized B of the Kronecker sum of the inverse
feature moment with the residual moment and the identity with the canonical regression
coefficient times its transpose, interpreted in the extended nonnegative reals](goal). -/
lemma alternativeConditionNumber_kronecker_sphere {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : NondegenerateSecondMoments p m) :
    alternativeConditionNumber Sigma =
      ⨆ (B : Mat m p) (_ : frob B = 1),
        ENNReal.ofReal (1 + Matrix.vec B ⬝ᵥ
          ((Matrix.kronecker (blockX p m Sigma.carrier.val.val)⁻¹
              (matrixResidual Sigma.carrier.val.val) +
            Matrix.kronecker (1 : Mat p p)
              (canonicalCoefficient Sigma.carrier.val.val *
                (canonicalCoefficient Sigma.carrier.val.val).transpose)) *ᵥ Matrix.vec B)) := by
  rw [(altConditionNumberFormula (assPin1_valid m)).1 Sigma]
  simp_rw [condition_derivative_whitened Sigma]
  have hi := condition_inverse_sqrt_identities _ Sigma.carrier.property
  have hg := condition_sqrt_factor_geometry Sigma
  rw [condition_primal_kronecker_sphere_sup _ _ _ _ hi.1 hg.1 hg.2.1]
  dsimp only at hi hg ⊢
  rw [hi.2.2.1, hg.2.2]

end Papers.WassersteinRegretS2S3
