module
public import Papers.WassersteinRegretS2S3.Helpers.QuadraticDuality
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentGeometry
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection

/-!
# Population Wasserstein regret: Helpers/InnerDRO

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: innerDro_factor_sup
/-- For [a joint law P with finite second moments](hyp:P), [a nonnegative Wasserstein
radius eps](hyp:eps), and [a linear loss matrix M](hyp:M), [the worst-case expected squared
norm of M times the observation over the Wasserstein ball around P equals the supremum
of the squared Frobenius norm of M times W over matrices W within Frobenius distance eps
of the positive semidefinite square root of P's second moment](goal). -/
lemma innerDro_factor_sup {p m k : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) (M : Mat k (p + m)) :
    (⨆ Q ∈ lawBall P eps,
      ENNReal.ofReal (∫ z, ‖matrixCLM M z‖ ^ 2 ∂lawMeasure Q)) =
    ⨆ (W : Mat (p + m) (p + m))
      (_ : frob (W - CFC.sqrt (secondMoment P)) ≤ eps),
      ENNReal.ofReal (frob (M * W) ^ 2) := by
  have himage := (w2BuresEquivalence assSingularValueConvention_valid P eps)
  have hfactor := himage.1.trans himage.2
  have hvalue (Q : JointLaws p m) :
      (∫ z, ‖matrixCLM M z‖ ^ 2 ∂lawMeasure Q) =
        Matrix.trace (M * secondMoment Q * M.transpose) := by
    exact integral_norm_sq_linear (lawMeasure Q) id Q.carrier.property M
  have htrace (W : Mat (p + m) (p + m)) :
      Matrix.trace (M * (W * W.transpose) * M.transpose) = frob (M * W) ^ 2 := by
    rw [frob_sq_trace_rows, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  apply le_antisymm
  · refine iSup_le fun Q => iSup_le fun hQ => ?_
    have hm := Set.mem_image_of_mem secondMoment hQ
    rw [hfactor] at hm
    obtain ⟨Delta, hd, he⟩ := hm
    rw [hvalue, he, htrace]
    exact le_iSup_of_le (CFC.sqrt (secondMoment P) + Delta)
      (le_iSup_of_le (by simpa using hd) le_rfl)
  · refine iSup_le fun W => iSup_le fun hW => ?_
    have hm : W * W.transpose ∈ secondMoment '' lawBall P eps := by
      rw [hfactor]
      exact ⟨W - CFC.sqrt (secondMoment P), hW, by simp⟩
    obtain ⟨Q, hQ, he⟩ := hm
    have hv := hvalue Q
    rw [he, htrace] at hv
    rw [← hv]
    exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)

-- @node: residualMatrix_opNorm
/-- For [a regression coefficient matrix A with at least one response coordinate](hyp:A),
[the squared operator norm of the residual matrix formed by concatenating A and minus
the identity equals one plus the squared operator norm of A](goal). -/
lemma residualMatrix_opNorm {p m : ℕ} [NeZero m] (A : Mat m p) :
    opNorm (quadraticRegressionMatrix A) ^ 2 = 1 + opNorm A ^ 2 := by
  classical
  let B := (quadraticRegressionMatrix A).transpose
  have hb : opNorm B = opNorm (quadraticRegressionMatrix A) := opNorm_transpose _
  have ha : opNorm A.transpose = opNorm A := opNorm_transpose _
  have hid (x : Euc m) :
      ‖matrixCLM B x‖ ^ 2 = ‖matrixCLM A.transpose x‖ ^ 2 + ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (∑ j, B i j * x j) ^ 2) =
      (∑ i, (∑ j, A.transpose i j * x j) ^ 2) + ∑ i, x i ^ 2
    rw [Fin.sum_univ_add]
    simp [B, quadraticRegressionMatrix, Matrix.transpose_apply,
      Matrix.one_apply, Fin.addCases_left, Fin.addCases_right]
  have hupper : opNorm B ≤ Real.sqrt (1 + opNorm A ^ 2) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [hid, mul_pow, Real.sq_sqrt (by positivity)]
    have h := pow_le_pow_left₀ (norm_nonneg _) ((matrixCLM A.transpose).le_opNorm x) 2
    change ‖matrixCLM A.transpose x‖ ^ 2 ≤ (opNorm A.transpose * ‖x‖) ^ 2 at h
    rw [mul_pow, ha] at h
    nlinarith
  have hpoint (x : Euc m) :
      ‖matrixCLM A.transpose x‖ ^ 2 + ‖x‖ ^ 2 ≤ opNorm B ^ 2 * ‖x‖ ^ 2 := by
    rw [← hid]
    exact (pow_le_pow_left₀ (norm_nonneg _) ((matrixCLM B).le_opNorm x) 2).trans_eq (mul_pow ..)
  let x : Euc m := WithLp.toLp 2 (Pi.single 0 1)
  have hx : ‖x‖ ^ 2 = 1 := by simp [x, EuclideanSpace.real_norm_sq_eq]
  have hone : 1 ≤ opNorm B ^ 2 := by
    have h := hpoint x
    rw [hx, mul_one] at h
    nlinarith [sq_nonneg ‖matrixCLM A.transpose x‖]
  have hlower : opNorm A.transpose ≤ Real.sqrt (opNorm B ^ 2 - 1) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro y
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith [hpoint y]
  have hl := pow_le_pow_left₀ (norm_nonneg _) hlower 2
  have hu := pow_le_pow_left₀ (norm_nonneg _) hupper 2
  change opNorm A.transpose ^ 2 ≤ (Real.sqrt (opNorm B ^ 2 - 1)) ^ 2 at hl
  change opNorm B ^ 2 ≤ (Real.sqrt (1 + opNorm A ^ 2)) ^ 2 at hu
  rw [Real.sq_sqrt (by linarith), ha] at hl
  rw [Real.sq_sqrt (by positivity)] at hu
  rw [hb] at hl hu
  linarith

-- @node: innerDro_toENNReal_iSup
/-- For [an indexed family f of extended real numbers](hyp:f), [converting its supremum
to a nonnegative extended real number equals the supremum of the converted values](goal).

The conversion replaces negative values by zero and preserves positive infinity. -/
lemma innerDro_toENNReal_iSup {ι : Sort*} (f : ι → EReal) :
    (⨆ i, f i).toENNReal = ⨆ i, (f i).toENNReal := by
  exact Monotone.map_iSup_of_continuousAt EReal.continuous_toENNReal.continuousAt
    (fun _ _ h => EReal.toENNReal_le_toENNReal h) EReal.toENNReal_bot

-- @node: innerDro_toENNReal_iInf
/-- For [an indexed family f of extended real numbers](hyp:f), [converting its infimum
to a nonnegative extended real number equals the infimum of the converted values](goal).

The conversion replaces negative values by zero and preserves positive infinity. -/
lemma innerDro_toENNReal_iInf {ι : Sort*} (f : ι → EReal) :
    (⨅ i, f i).toENNReal = ⨅ i, (f i).toENNReal := by
  exact Monotone.map_iInf_of_continuousAt EReal.continuous_toENNReal.continuousAt
    (fun _ _ h => EReal.toENNReal_le_toENNReal h) EReal.toENNReal_top

-- @node: residualMatrix_gram
/-- For [a regression coefficient matrix A](hyp:A), [the residual matrix formed by
concatenating A and minus the identity, multiplied by its transpose, equals A times its
transpose plus the identity](goal). -/
lemma residualMatrix_gram {p m : ℕ} (A : Mat m p) :
    quadraticRegressionMatrix A * (quadraticRegressionMatrix A).transpose =
      A * A.transpose + 1 := by
  ext i j
  simp [Matrix.mul_apply, quadraticRegressionMatrix, Fin.sum_univ_add,
    Matrix.transpose_apply, Matrix.one_apply]

-- @node: lem:inner-dro-strong-duality
/-- Assume [the squared Euclidean norm of every response vector is the sum of its squared
coordinates](hyp:hpin) and [singular values are nonnegative and ordered from largest to
smallest, with the smallest indexed accordingly](hyp:hsv). For [a joint law P with finite
second moments](hyp:P) and [a nonnegative Wasserstein radius eps](hyp:eps) that [is strictly
positive](hyp:heps), [every linear loss with a positive output dimension no larger than the
joint dimension has worst-case expected squared norm equal to the infimum, over eta above
the squared operator norm, of eta times the sum of eps squared and the trace of the inverse
of the difference between eta times the identity and the loss matrix's Gram matrix, multiplied by the transformed
second moment; the same formula holds for every regression squared-error risk, with
threshold one plus the squared operator norm of the coefficient matrix and inverse matrix
given by eta minus one, multiplied by the identity, minus the coefficient matrix times its transpose](goal).

In both formulas eta multiplies the entire sum of the radius squared and the trace term.
The transformed second moment is the loss matrix times P's second moment times the loss
matrix's transpose; for regression the loss matrix concatenates the coefficient matrix
and minus the identity. Suprema and infima are taken in the nonnegative extended reals. -/
lemma innerDroStrongDuality {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : JointLaws p m)
    (eps : ℝ≥0) (heps : 0 < eps) :
    (∀ (k : ℕ) [NeZero k], k ≤ p + m → ∀ M : Mat k (p + m),
      (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (∫ z, ‖matrixCLM M z‖ ^ 2 ∂lawMeasure Q)) =
      ⨅ (eta : ℝ) (_ : opNorm M ^ 2 < eta),
        ENNReal.ofReal (eta * ((eps : ℝ) ^ 2 + Matrix.trace
          ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ * M * secondMoment P * M.transpose)))) ∧
    (∀ A : Mat m p,
      (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (risk A Q)) =
      ⨅ (eta : ℝ) (_ : 1 + opNorm A ^ 2 < eta),
        ENNReal.ofReal (eta * ((eps : ℝ) ^ 2 + Matrix.trace
          (((eta - 1) • (1 : Mat m m) - A * A.transpose)⁻¹ *
            quadraticRegressionMatrix A * secondMoment P * (quadraticRegressionMatrix
              A).transpose)))) := by
  have hgeneral (k : ℕ) [NeZero k] (M : Mat k (p + m)) :
      (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (∫ z, ‖matrixCLM M z‖ ^ 2 ∂lawMeasure Q)) =
      ⨅ (eta : ℝ) (_ : opNorm M ^ 2 < eta),
        ENNReal.ofReal (eta * ((eps : ℝ) ^ 2 + Matrix.trace
          ((eta • (1 : Mat k k) - M * M.transpose)⁻¹ * M * secondMoment P * M.transpose))) := by
    let S := CFC.sqrt (secondMoment P)
    have hdual := quadraticBallDuality M S
    have heq := (hdual.2.1 ((eps : ℝ) ^ 2)).trans
      ((hdual.2.2.1 ((eps : ℝ) ^ 2)).trans (hdual.2.2.2 ((eps : ℝ) ^ 2)))
    have hconvert := congrArg EReal.toENNReal heq
    simp only [innerDro_toENNReal_iSup, innerDro_toENNReal_iInf,
      EReal.real_coe_toENNReal] at hconvert
    rw [innerDro_factor_sup]
    have hs : S * S.transpose = secondMoment P := (psd_sqrt_factor (momentPSD P)).symm
    have hsq (W : Mat (p + m) (p + m)) :
        frob (W - S) ^ 2 ≤ (eps : ℝ) ^ 2 ↔ frob (W - S) ≤ eps :=
      sq_le_sq₀ (frob_nonneg _) eps.coe_nonneg
    simp_rw [hsq, quadraticDualTerm, Matrix.mul_assoc, ← Matrix.mul_assoc S S.transpose M.transpose,
      hs] at hconvert
    simpa only [Matrix.mul_assoc] using hconvert
  refine ⟨fun k _ _ M => hgeneral k M, ?_⟩
  intro A
  have h := hgeneral m (quadraticRegressionMatrix A)
  have hmatrix (eta : ℝ) :
      eta • (1 : Mat m m) - quadraticRegressionMatrix A * (quadraticRegressionMatrix A).transpose =
        (eta - 1) • (1 : Mat m m) - A * A.transpose := by
    rw [residualMatrix_gram, sub_smul, one_smul]
    abel
  simp_rw [residualMatrix_opNorm, hmatrix, quadraticRegressionMatrix_apply] at h
  exact h

end Papers.WassersteinRegretS2S3
