module
public import Papers.WassersteinRegretS2S3.Helpers.InnerDRO

/-!
# Population Wasserstein regret: T2

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @realizes r_i^2(nonnegative coordinate residual second moment, integral of a square)
/-- For [a joint law with finite second moments](hyp:P), [a linear coefficient
matrix](hyp:A), and [a response coordinate](hyp:i), the [coordinate residual
second moment](goal) is the expected squared prediction error in that coordinate. -/
noncomputable def coordinateResidual {p m : ℕ} (P : JointLaws p m) (A : Mat m p) (i : Fin m) : ℝ :=
  ∫ z, (matrixCLM A (feature z) - response z) i ^ 2 ∂lawMeasure P
/-- In [a Euclidean space of the specified dimension](hyp:m), the [coordinate
vector](goal) for [a chosen coordinate](hyp:i) has entry one there and zero elsewhere. -/
def coordinateVector (m : ℕ) (i : Fin m) : Euc m :=
  WithLp.toLp 2 (Pi.single i 1)
-- @realizes e_i(standard Euclidean coordinate vector)

-- @node: coordinateResidual_eq_secondMoment
/-- For [a joint law with finite second moments](hyp:P), [a linear coefficient
matrix](hyp:A), and [a response coordinate](hyp:i), [the coordinate residual second
moment equals the corresponding diagonal entry of the joint second moment
transformed by the prediction-error matrix and its transpose](goal). -/
lemma coordinateResidual_eq_secondMoment {p m : ℕ} (P : JointLaws p m)
    (A : Mat m p) (i : Fin m) :
    coordinateResidual P A i =
      (quadraticRegressionMatrix A * secondMoment P *
        (quadraticRegressionMatrix A).transpose) i i := by
  have h := integral_linear_secondMoment (lawMeasure P) id P.carrier.property
    (quadraticRegressionMatrix A) i i
  change (∫ z, matrixCLM (quadraticRegressionMatrix A) z i *
    matrixCLM (quadraticRegressionMatrix A) z i ∂lawMeasure P) =
    (quadraticRegressionMatrix A * secondMoment P *
      (quadraticRegressionMatrix A).transpose) i i at h
  simpa only [id_eq, quadraticRegressionMatrix_apply, ← pow_two,
    coordinateResidual] using h

-- @node: diagonal_resolvent_trace
/-- For [real diagonal parameters](hyp:a), [a real resolvent parameter](hyp:eta),
and [a square matrix](hyp:B), if [the resolvent parameter minus one minus each
squared diagonal parameter is nonzero](hyp:hne), then [the trace of the inverse
diagonal resolvent multiplied by the matrix equals the sum of the matrix's
diagonal entries divided by those respective denominators](goal). -/
lemma diagonal_resolvent_trace {m : ℕ} (a : Fin m → ℝ) (eta : ℝ)
    (B : Mat m m) (hne : ∀ i, eta - 1 - (a i) ^ 2 ≠ 0) :
    Matrix.trace (((eta - 1) • (1 : Mat m m) -
      Matrix.diagonal (fun i => (a i) ^ 2))⁻¹ * B) =
      ∑ i, B i i / (eta - 1 - (a i) ^ 2) := by
  have hd : (eta - 1) • (1 : Mat m m) - Matrix.diagonal (fun i => (a i) ^ 2) =
      Matrix.diagonal (fun i => eta - 1 - (a i) ^ 2) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]
  rw [hd, Matrix.inv_diagonal]
  have hu : IsUnit (fun i => eta - 1 - (a i) ^ 2) :=
    isUnit_iff_exists_inv.mpr ⟨fun i => (eta - 1 - (a i) ^ 2)⁻¹,
      by ext i; exact mul_inv_cancel₀ (hne i)⟩
  have hi := Ring.inverse_mul_cancel _ hu
  have heq : Ring.inverse (fun i => eta - 1 - (a i) ^ 2) =
      (fun i => (eta - 1 - (a i) ^ 2)⁻¹) := by
    funext i
    have h := congrFun hi i
    have hh := congrArg (fun x : ℝ => x * (eta - 1 - (a i) ^ 2)⁻¹) h
    simpa only [Pi.mul_apply, Pi.one_apply, mul_assoc, mul_inv_cancel₀ (hne i),
      mul_one, one_mul] using hh
  rw [heq]
  simp [Matrix.trace, Matrix.diagonal_mul, div_eq_mul_inv, mul_comm]

open scoped Matrix.Norms.L2Operator in
-- @node: diagonal_gram_opNorm_sq
/-- For [a coefficient matrix](hyp:A) and [real diagonal parameters](hyp:a), if
[the coefficient matrix times its transpose is diagonal with entries equal to
the squared parameters](hyp:hdiag), then [the squared operator norm of the
coefficient matrix equals the largest squared parameter](goal). -/
lemma diagonal_gram_opNorm_sq {p m : ℕ} [NeZero m]
    (A : Mat m p) (a : Fin m → ℝ)
    (hdiag : A * A.transpose = Matrix.diagonal (fun i => (a i) ^ 2)) :
    opNorm A ^ 2 = Finset.univ.sup' Finset.univ_nonempty (fun i => (a i) ^ 2) := by
  classical
  have hgram := Matrix.l2_opNorm_conjTranspose_mul_self A.transpose
  have htrans : A.transpose.conjTranspose = A := by ext; simp
  rw [htrans, hdiag, Matrix.l2_opNorm_diagonal] at hgram
  change ‖(fun i => (a i) ^ 2)‖ = opNorm A.transpose * opNorm A.transpose at hgram
  rw [opNorm_transpose, ← pow_two] at hgram
  rw [← hgram]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ?_).mpr
    · intro i
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a i))] using
        (Finset.le_sup' (fun i => (a i) ^ 2) (Finset.mem_univ i))
    · exact (sq_nonneg (a 0)).trans
        (Finset.le_sup' (fun i => (a i) ^ 2) (Finset.mem_univ 0))
  · apply Finset.sup'_le
    intro i _
    exact (le_abs_self ((a i) ^ 2)).trans
      (norm_le_pi_norm (fun i => (a i) ^ 2) i)

-- @node: thm:dro-strong-duality-diagonal
/-- Assume [the squared Euclidean norm is the sum of squared response coordinates](hyp:hpin)
and [singular values are nonnegative and decreasing, with the minimum at the
smaller matrix dimension](hyp:hsv). For [a joint law with finite second moments](hyp:P),
[a nonnegative Wasserstein radius](hyp:eps), [a coefficient matrix](hyp:A), and
[real diagonal parameters](hyp:a), if [the radius is positive and the coefficient
matrix times its transpose is diagonal with entries equal to the squared
parameters](hyp:hdiag), then [each coordinate residual second moment is the
corresponding diagonal entry of the transformed joint second moment, and the
worst-case risk over the Wasserstein ball equals the infimum, over real parameters
greater than one plus the largest squared diagonal parameter, of the parameter
times the sum of the squared radius and the coordinate residual second moments
divided by the parameter minus one minus their respective squared diagonal parameters](goal). -/
theorem droStrongDualityDiagonal {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : JointLaws p m)
    (eps : ℝ≥0) (A : Mat m p) (a : Fin m → ℝ)
    (hdiag : assDroStrongDualityDiagonal P eps A a) :
    (∀ i : Fin m, coordinateResidual P A i =
      (quadraticRegressionMatrix A * secondMoment P * (quadraticRegressionMatrix A).transpose)
        i i) ∧
    (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (risk A Q)) =
      ⨅ (eta : ℝ) (_ : 1 + (Finset.univ.sup' Finset.univ_nonempty (fun i => (a i) ^ 2)) < eta),
        ENNReal.ofReal (eta * ((eps : ℝ) ^ 2 + ∑ i, coordinateResidual P A i / (eta - 1 - (a i)
           ^ 2))) := by
  refine ⟨coordinateResidual_eq_secondMoment P A, ?_⟩
  classical
  have hnorm := diagonal_gram_opNorm_sq A a hdiag.2
  rw [(innerDroStrongDuality hpin hsv P eps hdiag.1).2 A, hnorm]
  refine iInf_congr fun eta => iInf_congr fun heta => ?_
  have hne (i : Fin m) : eta - 1 - (a i) ^ 2 ≠ 0 := by
    have hi := Finset.le_sup' (fun i => (a i) ^ 2) (Finset.mem_univ i)
    linarith
  have ht := diagonal_resolvent_trace a eta
    (quadraticRegressionMatrix A * secondMoment P * (quadraticRegressionMatrix A).transpose) hne
  rw [hdiag.2]
  simpa only [Matrix.mul_assoc, coordinateResidual_eq_secondMoment] using
    congrArg (fun t : ℝ => ENNReal.ofReal (eta * ((eps : ℝ) ^ 2 + t))) ht

end Papers.WassersteinRegretS2S3
