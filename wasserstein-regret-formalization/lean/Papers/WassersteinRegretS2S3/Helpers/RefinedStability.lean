module
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentGeometry
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection
public import Papers.WassersteinRegretS2S3.Helpers.RowSpacePerturbation

/-!
# Population Wasserstein regret: Helpers/RefinedStability

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: refined_projected_residual_identity
/-- Suppose [right multiplication by P leaves X unchanged](hyp:hXP),
[right multiplication by Q leaves X + DX unchanged](hyp:hXQ), and
[the residual Y − CX vanishes after right multiplication by P](hyp:hEP).
Then [the difference between (Y − AX)P and the perturbed residual
(Y + DY − A(X + DX))Q equals (A − C)DX(I − Q) + (ADX − DY)Q − (Y − CX)Q](goal). -/
lemma refined_projected_residual_identity {p m d : ℕ}
    (A C : Mat m p) (X DX : Mat p d) (Y DY : Mat m d) (P Q : Mat d d)
    (hXP : X * P = X) (hXQ : (X + DX) * Q = X + DX)
    (hEP : (Y - C * X) * P = 0) :
    (Y - A * X) * P - (Y + DY - A * (X + DX)) * Q =
      (A - C) * DX * (1 - Q) + (A * DX - DY) * Q - (Y - C * X) * Q := by
  have hYP : Y * P = C * X := by
    simpa only [Matrix.sub_mul, Matrix.mul_assoc, hXP, sub_eq_zero] using hEP
  have hDXQ : DX * Q = X + DX - X * Q := by
    rw [Matrix.add_mul] at hXQ
    exact eq_sub_of_add_eq' hXQ
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.mul_one, Matrix.mul_assoc, hXP, hYP, hDXQ]
  abel

-- @node: refined_complementary_projection_norm_sq
/-- If [Q is an orthogonal projection](hyp:hQ), then [the squared Frobenius norm
of U(I − Q) + VQ equals the sum of the squared Frobenius norms of U(I − Q) and VQ](goal). -/
lemma refined_complementary_projection_norm_sq {m d : ℕ}
    (U V : Mat m d) (Q : Mat d d) (hQ : assBasicMatrixNormsProjection Q) :
    frob (U * (1 - Q) + V * Q) ^ 2 =
      frob (U * (1 - Q)) ^ 2 + frob (V * Q) ^ 2 := by
  have hc : (1 - Q) * Q = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hQ.2, sub_self]
  have hd : Q * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQ.2, sub_self]
  have he : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.mul_sub, Matrix.mul_one, hc, sub_zero]
  have h := frob_projection_pythagoras (U * (1 - Q) + V * Q) Q hQ
  simpa only [Matrix.add_mul, Matrix.mul_assoc, hc, hd, he, hQ.2,
    Matrix.mul_zero, zero_add, add_zero, add_comm] using h

-- @node: refined_residual_projection_bound
/-- Assume [singular values are ordered nonincreasingly, are nonnegative, and the
minimum singular value is the entry indexed by the smaller matrix dimension](hyp:hsv),
[X has full row rank](hyp:hrank), and [E vanishes when projected onto the row space
of X](hyp:hE). Then [the Frobenius norm of E projected onto the row space of X + DX
is at most the operator norm of E times the Frobenius norm of DX divided by the
minimum singular value of X](goal). -/
lemma refined_residual_projection_bound {p m d : ℕ} [NeZero p] [NeZero d]
    (hsv : assSingularValueConvention) (X DX : Mat p d) (E : Mat m d)
    (hrank : assSinThmVariantRowRank X) (hE : E * rowProjector X = 0) :
    frob (E * rowProjector (X + DX)) ≤
      opNorm E * (frob DX / minSV X) := by
  have heq : E * rowProjector (X + DX) =
      E * ((1 - rowProjector X) * rowProjector (X + DX)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hE, sub_zero]
  rw [heq]
  exact (frob_mul_left_le _ _).trans
    (mul_le_mul_of_nonneg_left
      ((sinThmVariant hsv X DX hrank).1.trans (sinThmVariant hsv X DX hrank).2)
      (norm_nonneg _))

-- @node: refined_response_perturbation_sq
/-- [The squared Frobenius norm of AX − Y is at most one plus the squared
operator norm of A, multiplied by the sum of the squared Frobenius norms of X and Y](goal). -/
lemma refined_response_perturbation_sq {p m d : ℕ}
    (A : Mat m p) (X : Mat p d) (Y : Mat m d) :
    frob (A * X - Y) ^ 2 ≤ (1 + opNorm A ^ 2) * (frob X ^ 2 + frob Y ^ 2) := by
  have hn (M : Mat m d) : frob M = ‖M‖ := by
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have ht : frob (A * X - Y) ≤ opNorm A * frob X + frob Y := by
    calc
      _ ≤ frob (A * X) + frob Y := by simpa only [hn] using norm_sub_le (A * X) Y
      _ ≤ _ := add_le_add (frob_mul_left_le A X) (le_refl _)
  have hs := pow_le_pow_left₀ (frob_nonneg _) ht 2
  nlinarith [sq_nonneg (frob X - opNorm A * frob Y)]

-- @node: refined_main_perturbation_sq
/-- If [Q is an orthogonal projection](hyp:hQ), then [the squared Frobenius norm
of (A − C)X(I − Q) + (AX − Y)Q is at most the square of the larger of the operator
norm of A − C and the square root of one plus the squared operator norm of A,
multiplied by the sum of the squared Frobenius norms of X and Y](goal). -/
lemma refined_main_perturbation_sq {p m d : ℕ}
    (A C : Mat m p) (X : Mat p d) (Y : Mat m d)
    (Q : Mat d d) (hQ : assBasicMatrixNormsProjection Q) :
    frob ((A - C) * X * (1 - Q) + (A * X - Y) * Q) ^ 2 ≤
      (max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2))) ^ 2 *
        (frob X ^ 2 + frob Y ^ 2) := by
  let c := max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2))
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (le_max_left _ _)
  have hca : opNorm (A - C) ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
  have hcb : 1 + opNorm A ^ 2 ≤ c ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (1 + opNorm A ^ 2))
      (le_max_right (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2))) 2
    rw [Real.sq_sqrt (by positivity)] at h
    exact h
  have hfirst := pow_le_pow_left₀ (frob_nonneg _)
    (frob_mul_left_le (A - C) (X * (1 - Q))) 2
  rw [mul_pow] at hfirst
  have hsecond := refined_response_perturbation_sq A (X * Q) (Y * Q)
  have hx := frob_projection_pythagoras X Q hQ
  have hy := frob_projection_pythagoras Y Q hQ
  rw [refined_complementary_projection_norm_sq _ _ Q hQ]
  simp only [Matrix.mul_assoc, Matrix.sub_mul] at *
  calc
    _ ≤ opNorm (A - C) ^ 2 * frob (X * (1 - Q)) ^ 2 +
        (1 + opNorm A ^ 2) * (frob (X * Q) ^ 2 + frob (Y * Q) ^ 2) :=
      add_le_add hfirst hsecond
    _ ≤ c ^ 2 * frob (X * (1 - Q)) ^ 2 +
        c ^ 2 * (frob (X * Q) ^ 2 + frob (Y * Q) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hca (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hcb (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (frob (Y * (1 - Q))))]

-- @node: refined_gram_opNorm_le_sqrt_lambdaMax
/-- [The operator norm of a real matrix E with at least one row is at most the
square root of the largest eigenvalue of its Gram matrix E times its transpose](goal). -/
lemma refined_gram_opNorm_le_sqrt_lambdaMax {m d : ℕ} [NeZero m]
    (E : Mat m d) : opNorm E ≤ Real.sqrt (lambdaMax (E * E.transpose)) := by
  have hadj : (Matrix.toEuclideanLin E.transpose).adjoint = Matrix.toEuclideanLin E := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp
  have hform (x : Euc m) :
      inner ℝ x (matrixCLM (E * E.transpose) x) = ‖matrixCLM E.transpose x‖ ^ 2 := by
    change inner ℝ x (Matrix.toEuclideanLin (E * E.transpose) x) = _
    rw [euclideanLin_mul, LinearMap.comp_apply, ← hadj]
    exact (Matrix.toEuclideanLin E.transpose).adjoint_inner_right x
      (Matrix.toEuclideanLin E.transpose x) |>.trans (real_inner_self_eq_norm_sq _)
  have hb : BddAbove {t : ℝ | ∃ x : Euc m, ‖x‖ = 1 ∧
      inner ℝ x (matrixCLM (E * E.transpose) x) = t} := by
    refine ⟨opNorm E.transpose ^ 2, ?_⟩
    rintro t ⟨x, hx, rfl⟩
    rw [hform]
    have h := (matrixCLM E.transpose).le_opNorm x
    rw [hx, mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← opNorm_transpose E]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
  intro x hx
  have hle : ‖matrixCLM E.transpose x‖ ^ 2 ≤ lambdaMax (E * E.transpose) := by
    rw [← hform]
    exact le_csSup hb ⟨x, hx, rfl⟩
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hle)).mpr hle

-- @node: refined_factor_row_rank
/-- If [X times its transpose is positive definite](hyp:hX), then
[X has full row rank, so multiplication by X maps onto the Euclidean space whose
dimension is the number of rows of X](goal). -/
lemma refined_factor_row_rank {p d : ℕ} (X : Mat p d)
    (hX : (X * X.transpose).PosDef) : assSinThmVariantRowRank X := by
  have hunit := hX.isUnit
  have hid : X * (X.transpose * (X * X.transpose)⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]
  intro y
  refine ⟨Matrix.toEuclideanLin (X.transpose * (X * X.transpose)⁻¹) y, ?_⟩
  have h := congrArg (fun M => Matrix.toEuclideanLin M y) hid
  simpa only [euclideanLin_mul, LinearMap.comp_apply, Matrix.toLpLin_one,
    LinearMap.id_apply] using h

-- @node: refined_inverse_minSV_le
/-- If [the first p rows of S have full row rank](hyp:hrank), then [the reciprocal
of their minimum singular value is at most the reciprocal of the square root of
the smallest eigenvalue of the leading p-by-p block of S times its transpose](goal). -/
lemma refined_inverse_minSV_le {p m : ℕ} [NeZero p]
    (S : Mat (p + m) (p + m))
    (hrank : assSinThmVariantRowRank (factorBlocks p m S).1) :
    (minSV (factorBlocks p m S).1)⁻¹ ≤
      (Real.sqrt (lambdaMin (blockX p m (S * S.transpose))))⁻¹ := by
  let X := (factorBlocks p m S).1
  have hr : Module.finrank ℝ (Matrix.toEuclideanLin X).range = p := by
    rw [LinearMap.range_eq_top.mpr hrank]
    simp
  have hrankX : X.rank = p := by
    rw [X.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (p + m)) ℝ).toBasis]
    exact hr
  have hrankT : X.transpose.rank = p := (Matrix.rank_transpose X).trans hrankX
  have hrT : Module.finrank ℝ (Matrix.toEuclideanLin X.transpose).range = p := by
    have h := X.transpose.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin (p + m)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
    exact h.symm.trans hrankT
  have hs : 0 < minSV X.transpose := by
    change 0 < (Matrix.toEuclideanLin X.transpose).singularValues (min (p + m) p - 1)
    rw [min_eq_right (Nat.le_add_right p m),
      LinearMap.singularValues_pos_iff_lt_finrank_range, hrT]
    exact Nat.sub_one_lt (NeZero.ne p)
  have hbound := norm_moorePenroseInverse_le_inv X.transpose hrankT hs
    (show minSV X.transpose ≤ singularValue X.transpose (p - 1) by
      simp only [minSV, min_eq_right (Nat.le_add_right p m), le_refl])
  change opNorm (moorePenroseInverse X.transpose) ≤ (minSV X.transpose)⁻¹ at hbound
  rw [penrose_transpose, opNorm_transpose, penrose_full_row_norm X hrank] at hbound
  rw [sqrt_lambdaMin_factorX]
  exact hbound

-- @node: refined_factor_stability
/-- Assume [singular values are nonincreasing and nonnegative, with the minimum
at the smaller matrix dimension](hyp:hsv), [X has full row rank](hyp:hrank), and
[the residual Y − CX is orthogonal to the row space of X](hyp:hE).
Then [the absolute change in the Frobenius norm of the residual Y − AX projected
onto the row space of X, after perturbing X and Y by DX and DY and updating the
row space, is at most the larger of the operator norm of A − C and the square root
of one plus the squared operator norm of A, times the square root of the sum of
the squared Frobenius norms of DX and DY, plus the operator norm of Y − CX times
the Frobenius norm of DX divided by the minimum singular value of X](goal). -/
lemma refined_factor_stability {p m d : ℕ} [NeZero p] [NeZero d]
    (hsv : assSingularValueConvention) (A C : Mat m p)
    (X DX : Mat p d) (Y DY : Mat m d)
    (hrank : assSinThmVariantRowRank X)
    (hE : (Y - C * X) * rowProjector X = 0) :
    |frob ((Y - A * X) * rowProjector X) -
      frob ((Y + DY - A * (X + DX)) * rowProjector (X + DX))| ≤
      max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2)) *
        Real.sqrt (frob DX ^ 2 + frob DY ^ 2) +
      opNorm (Y - C * X) * (frob DX / minSV X) := by
  let Q := rowProjector (X + DX)
  let T := (A - C) * DX * (1 - Q) + (A * DX - DY) * Q
  let c := max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2))
  have hn {a b : ℕ} (M : Mat a b) : frob M = ‖M‖ := by
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have hXP : X * rowProjector X = X := by
    simpa only [rowProjector, Matrix.mul_assoc] using (moorePenroseInverse_spec X).1
  have hXQ : (X + DX) * Q = X + DX := by
    simpa only [Q, rowProjector, Matrix.mul_assoc] using (moorePenroseInverse_spec (X + DX)).1
  have hid := refined_projected_residual_identity A C X DX Y DY
    (rowProjector X) Q hXP hXQ hE
  have hT : frob T ≤ c * Real.sqrt (frob DX ^ 2 + frob DY ^ 2) := by
    have hs := refined_main_perturbation_sq A C DX DY Q (penrose_projectors (X + DX)).1
    have hc : 0 ≤ c := le_trans (norm_nonneg _) (le_max_left _ _)
    have hroot := Real.sq_sqrt (add_nonneg (sq_nonneg (frob DX)) (sq_nonneg (frob DY)))
    apply (sq_le_sq₀ (frob_nonneg T) (mul_nonneg hc (Real.sqrt_nonneg _))).mp
    rw [mul_pow, hroot]
    exact hs
  calc
    _ ≤ frob (((Y - A * X) * rowProjector X) -
        ((Y + DY - A * (X + DX)) * Q)) := by
      simpa only [hn] using abs_norm_sub_norm_le
        ((Y - A * X) * rowProjector X) ((Y + DY - A * (X + DX)) * Q)
    _ = frob (T - (Y - C * X) * Q) := congrArg frob hid
    _ ≤ frob T + frob ((Y - C * X) * Q) := by
      simpa only [hn] using norm_sub_le T ((Y - C * X) * Q)
    _ ≤ _ := add_le_add hT (refined_residual_projection_bound hsv X DX (Y - C * X) hrank hE)

-- @node: lem:regret-stability-refined
/-- For [a nonnegative Wasserstein radius eps](hyp:eps), assume [squared Euclidean norms of response vectors equal the sums of their
squared coordinates](hyp:hpin) and [singular values are nonincreasing and
nonnegative, with the minimum at the smaller matrix dimension](hyp:hsv).
If [Q lies within Wasserstein distance eps of the nondegenerate reference law P](hyp:hQ),
then [the absolute difference between the square roots of the regrets of A under
P and Q is at most eps times the sum of two terms: the larger of the operator norm
of A minus P's optimal predictor and the square root of one plus the squared
operator norm of A; and the square root of the ratio of the largest eigenvalue of
P's residual second moment to the smallest eigenvalue of P's feature second moment](goal). -/
lemma regretStabilityRefined {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (eps : ℝ≥0) (A : Mat m p)
    (P : NondegenerateLaws p m) (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val eps) :
    |Real.sqrt (regret A P.carrier.val) - Real.sqrt (regret A Q)| ≤
      (max (opNorm (A - optimalPredictor P)) (Real.sqrt (1 + opNorm A ^ 2)) +
        Real.sqrt (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX
          P.carrier.val))) * eps := by
  obtain ⟨S, T, hS, hT, hc⟩ :=
    (buresProcrustes (momentPSD P.carrier.val) (momentPSD Q)).2.1.1
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  let DX := (factorBlocks p m (T - S)).1
  let DY := (factorBlocks p m (T - S)).2
  let C := canonicalCoefficient (secondMoment P.carrier.val)
  let E := Y - C * X
  have hblocks : (factorBlocks p m T).1 = X + DX ∧
      (factorBlocks p m T).2 = Y + DY := by
    constructor <;> ext i j <;>
      simp [X, Y, DX, DY, factorBlocks, Matrix.submatrix_apply]
  have hg := regretProjectionFormula hpin hsv (momentPSD P.carrier.val) S hS
  have hgt := regretProjectionFormula hpin hsv (momentPSD Q) T hT
  dsimp only [momentPSD] at hg hgt hS hT hc
  have hX : (X * X.transpose).PosDef := by
    have hb : secondMomentX P.carrier.val = X * X.transpose := by
      rw [show secondMomentX P.carrier.val = blockX p m (S * S.transpose) from
        congrArg (blockX p m) hS]
      exact blockX_factor_gram S
    rw [← hb]
    exact P.carrier.property
  have hrank := refined_factor_row_rank X hX
  have hEP : E * rowProjector X = 0 := hg.2.2.2.2.1
  have hEE : E * E.transpose = residualSecondMoment P :=
    hg.2.2.2.2.2.1.trans (residual_law_matrix P).1.symm
  have hregP : Real.sqrt (regret A P.carrier.val) =
      frob ((Y - A * X) * rowProjector X) := by
    rw [(law_matrix_risk_regret P.carrier.val A).2, (hg.2.2.2.2.2.2 A).2.1,
      Real.sqrt_sq (frob_nonneg _)]
  have hregQ : Real.sqrt (regret A Q) =
      frob ((Y + DY - A * (X + DX)) * rowProjector (X + DX)) := by
    rw [(law_matrix_risk_regret Q A).2, (hgt.2.2.2.2.2.2 A).2.1,
      Real.sqrt_sq (frob_nonneg _), hblocks.1, hblocks.2]
  have hD : frob (T - S) ≤ (eps : ℝ) := by
    have hn : frob (T - S) = frob (S - T) := by
      unfold frob
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact sub_sq_comm _ _
    rw [hn, hc]
    exact (bures_le_wasserstein P.carrier.val Q).trans hQ
  have hsize : Real.sqrt (frob DX ^ 2 + frob DY ^ 2) = frob (T - S) := by
    rw [← frob_factorBlocks_sq, Real.sqrt_sq (frob_nonneg _)]
  have hDX : frob DX ≤ frob (T - S) := by
    apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
    rw [frob_factorBlocks_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hmin : 0 ≤ lambdaMin (secondMomentX P.carrier.val) := by
    have hb : secondMomentX P.carrier.val = X * X.transpose := by
      rw [show secondMomentX P.carrier.val = blockX p m (S * S.transpose) from
        congrArg (blockX p m) hS]
      exact blockX_factor_gram S
    rw [hb, lambdaMin_gram_transpose]
    exact sq_nonneg _
  have hi := refined_inverse_minSV_le S hrank
  have hi' : (minSV X)⁻¹ ≤ (Real.sqrt (lambdaMin (secondMomentX P.carrier.val)))⁻¹ := by
    simpa only [← hS, X] using hi
  have he : opNorm E ≤ Real.sqrt (lambdaMax (residualSecondMoment P)) := by
    rw [← hEE]
    exact refined_gram_opNorm_le_sqrt_lambdaMax E
  have hres : opNorm E * (frob DX / minSV X) ≤
      Real.sqrt (lambdaMax (residualSecondMoment P) /
        lambdaMin (secondMomentX P.carrier.val)) * frob (T - S) := by
    rw [Real.sqrt_div' _ hmin]
    calc
      _ = opNorm E * (minSV X)⁻¹ * frob DX := by ring
      _ ≤ Real.sqrt (lambdaMax (residualSecondMoment P)) *
          (Real.sqrt (lambdaMin (secondMomentX P.carrier.val)))⁻¹ * frob DX := by
        apply mul_le_mul_of_nonneg_right _ (frob_nonneg _)
        exact mul_le_mul he hi' (inv_nonneg.mpr ((hsv p (p + m) X).2.1 _))
          (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hDX (mul_nonneg (Real.sqrt_nonneg _)
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  rw [hregP, hregQ, optimalPredictor_eq_canonical]
  have hb := refined_factor_stability hsv A C X DX Y DY hrank hEP
  rw [hsize] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2)) +
        Real.sqrt (lambdaMax (residualSecondMoment P) /
          lambdaMin (secondMomentX P.carrier.val))) * frob (T - S) := by
      rw [add_mul]
      exact add_le_add (le_refl _) hres
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (add_nonneg
      (le_trans (norm_nonneg _) (le_max_left _ _)) (Real.sqrt_nonneg _))

-- @node: stability_coefficient_le
/-- If [the square root of one plus the squared operator norm of C is at most
the square root of k](hyp:hC), then [the larger of the operator norm of A − C and
the square root of one plus the squared operator norm of A is at most the operator
norm of A plus the square root of k](goal). -/
lemma stability_coefficient_le {p m : ℕ} (A C : Mat m p) (k : ℝ)
    (hC : Real.sqrt (1 + opNorm C ^ 2) ≤ Real.sqrt k) :
    max (opNorm (A - C)) (Real.sqrt (1 + opNorm A ^ 2)) ≤
      opNorm A + Real.sqrt k := by
  have hCn : 0 ≤ opNorm C := norm_nonneg _
  have hAn : 0 ≤ opNorm A := norm_nonneg _
  have hsC : opNorm C ≤ Real.sqrt (1 + opNorm C ^ 2) := by
    apply (Real.le_sqrt hCn (by positivity)).mpr
    linarith
  have hone : 1 ≤ Real.sqrt (1 + opNorm C ^ 2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg (opNorm C)]
  have hsA : Real.sqrt (1 + opNorm A ^ 2) ≤ opNorm A + 1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  apply max_le
  · have ht : opNorm (A - C) ≤ opNorm A + opNorm C := by
      simpa [opNorm, matrixCLM] using
        norm_sub_le (matrixCLM A) (matrixCLM C)
    exact ht.trans (add_le_add_right (hsC.trans hC) _)
  · exact hsA.trans (add_le_add_right (hone.trans hC) _)

-- @node: regret_stability_of_spectral_bounds
/-- For [a nonnegative Wasserstein radius eps](hyp:eps), assume [squared Euclidean norms of response vectors equal the sums of their
squared coordinates](hyp:hpin), [singular values are nonincreasing and nonnegative,
with the minimum at the smaller matrix dimension](hyp:hsv), and [Q is within
Wasserstein distance eps of the nondegenerate reference law P](hyp:hQ).
If [the square root of one plus the squared operator norm of P's optimal predictor
is at most the square root of k](hyp:hA) and [the square root of the ratio of the
largest eigenvalue of P's residual second moment to the smallest eigenvalue of
P's feature second moment is at most the square root of k](hyp:hE), then
[the absolute difference between the square roots of the regrets of A under P and
Q is at most eps multiplied by the sum of twice the square root of k and the
operator norm of A](goal). -/
lemma regret_stability_of_spectral_bounds {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (eps : ℝ≥0) (A : Mat m p) (P : NondegenerateLaws p m)
    (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val eps) (k : ℝ)
    (hA : Real.sqrt (1 + opNorm (optimalPredictor P) ^ 2) ≤ Real.sqrt k)
    (hE : Real.sqrt (lambdaMax (residualSecondMoment P) /
      lambdaMin (secondMomentX P.carrier.val)) ≤ Real.sqrt k) :
    |Real.sqrt (regret A P.carrier.val) - Real.sqrt (regret A Q)| ≤
      (2 * Real.sqrt k + opNorm A) * eps := by
  apply (regretStabilityRefined hpin hsv eps A P Q hQ).trans
  apply mul_le_mul_of_nonneg_right _ eps.property
  have hc := stability_coefficient_le A (optimalPredictor P) k hA
  linarith

-- @node: optimal_regret_of_spectral_bounds
/-- For [a nonnegative Wasserstein radius eps](hyp:eps), assume [squared Euclidean norms of response vectors equal the sums of their
squared coordinates](hyp:hpin), [singular values are nonincreasing and nonnegative,
with the minimum at the smaller matrix dimension](hyp:hsv), [Q is within
Wasserstein distance eps of the nondegenerate reference law P](hyp:hQ), and
[k is nonnegative](hyp:hk). If [the square root of one plus the squared operator
norm of P's optimal predictor is at most the square root of k](hyp:hA) and
[the square root of the ratio of the largest eigenvalue of P's residual second
moment to the smallest eigenvalue of P's feature second moment is at most the
square root of k](hyp:hE), then [the regret under Q of P's optimal predictor is at
most four times k times eps squared](goal). -/
lemma optimal_regret_of_spectral_bounds {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (eps : ℝ≥0) (P : NondegenerateLaws p m)
    (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val eps) (k : ℝ)
    (hk : 0 ≤ k)
    (hA : Real.sqrt (1 + opNorm (optimalPredictor P) ^ 2) ≤ Real.sqrt k)
    (hE : Real.sqrt (lambdaMax (residualSecondMoment P) /
      lambdaMin (secondMomentX P.carrier.val)) ≤ Real.sqrt k) :
    regret (optimalPredictor P) Q ≤ 4 * k * (eps : ℝ) ^ 2 := by
  have hz : regret (optimalPredictor P) P.carrier.val = 0 := by
    rw [optimalPredictor_eq_canonical]
    exact canonical_regret_zero _
  have hb := regretStabilityRefined hpin hsv eps (optimalPredictor P) P Q hQ
  simp only [hz, Real.sqrt_zero, zero_sub, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg _), sub_self] at hb
  have hop : opNorm (0 : Mat m p) = 0 := by simp [opNorm, matrixCLM]
  rw [hop, max_eq_right (Real.sqrt_nonneg _)] at hb
  have hr : Real.sqrt (regret (optimalPredictor P) Q) ≤ 2 * Real.sqrt k * eps :=
    hb.trans (mul_le_mul_of_nonneg_right (by linarith) eps.property)
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
  rw [Real.sq_sqrt (regret_nonneg _ _)] at hs
  calc
    _ ≤ (2 * Real.sqrt k * (eps : ℝ)) ^ 2 := hs
    _ = 4 * k * (eps : ℝ) ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hk]; ring

end Papers.WassersteinRegretS2S3
