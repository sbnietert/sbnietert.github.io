module
public import Papers.WassersteinRegretS2S3.Helpers.Stability

/-!
# Population Wasserstein regret: Helpers/PerturbedCondition

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: posDef_of_lambdaMin_pos
/-- For [a real square matrix A](hyp:A), if [A is symmetric](hyp:hA) and
[its smallest eigenvalue is strictly positive](hyp:hp), then [A is positive definite](goal). -/
lemma posDef_of_lambdaMin_pos {n : ℕ} (A : Mat n n)
    (hA : A.IsHermitian) (hp : 0 < lambdaMin A) : A.PosDef := by
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hb := lambdaMin_le_rayleigh A (hA.eigenvectorBasis i)
    (hA.eigenvectorBasis.orthonormal.1 i)
  have he : inner ℝ (hA.eigenvectorBasis i)
      (matrixCLM A (hA.eigenvectorBasis i)) = hA.eigenvalues i := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM, Matrix.toLpLin_apply,
      dotProduct_comm] using (hA.eigenvalues_eq i).symm
  rw [he] at hb
  exact hp.trans_le hb

-- @node: perturbed_feature_sqrt_lower
/-- Under [the convention that singular values are nonnegative and decreasing and
the minimum singular value is the last one](hyp:hsv), take [a reference joint
second-moment matrix with positive definite feature block](hyp:Sigma) and
[a positive semidefinite perturbed matrix](hyp:barSigma). If [their Bures distance
is at most half the square root of the smallest reference feature eigenvalue](hyp:hradius),
then [the square root of the smallest perturbed feature eigenvalue is at least
half its reference counterpart](goal). -/
lemma perturbed_feature_sqrt_lower {p m : ℕ} [NeZero p] [NeZero m]
    (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) (hradius : assPerturbedConditionNumberRadius Sigma barSigma) :
    Real.sqrt (lambdaMin (blockX p m Sigma.carrier.val.val)) / 2 ≤
      Real.sqrt (lambdaMin (blockX p m barSigma.val)) := by
  have hc := (buresLambdaMinContinuity hsv).1 Sigma.carrier.val barSigma
  have hl := (abs_le.mp hc).1
  change buresDistance barSigma.val Sigma.carrier.val.val ≤ _ at hradius
  linarith

-- @node: perturbed_feature_eigenvalue_lower
/-- Under [the convention that singular values are nonnegative and decreasing and
the minimum singular value is the last one](hyp:hsv), take [a reference joint
second-moment matrix with positive definite feature block](hyp:Sigma) and
[a positive semidefinite perturbed matrix](hyp:barSigma). If [their Bures distance
is at most half the square root of the smallest reference feature eigenvalue](hyp:hradius),
then [the smallest perturbed feature eigenvalue is at least one quarter of the
smallest reference feature eigenvalue](goal). -/
lemma perturbed_feature_eigenvalue_lower {p m : ℕ} [NeZero p] [NeZero m]
    (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) (hradius : assPerturbedConditionNumberRadius Sigma barSigma) :
    lambdaMin (blockX p m Sigma.carrier.val.val) / 4 ≤
      lambdaMin (blockX p m barSigma.val) := by
  have hl := perturbed_feature_sqrt_lower hsv Sigma barSigma hradius
  have hp := lambdaMin_pos_of_posDef _ Sigma.carrier.property
  have hb := lambdaMin_nonneg_of_psd (blockX p m barSigma.val)
    (barSigma.property.submatrix (Fin.castAdd m))
  have hs := Real.sq_sqrt hp.le
  have ht := Real.sq_sqrt hb
  have hn := Real.sqrt_nonneg (lambdaMin (blockX p m Sigma.carrier.val.val))
  nlinarith [sq_nonneg (Real.sqrt (lambdaMin (blockX p m barSigma.val)) -
    Real.sqrt (lambdaMin (blockX p m Sigma.carrier.val.val)) / 2)]

-- @node: perturbed_feature_posDef
/-- Under [the convention that singular values are nonnegative and decreasing and
the minimum singular value is the last one](hyp:hsv), take [a reference joint
second-moment matrix with positive definite feature block](hyp:Sigma) and
[a positive semidefinite perturbed matrix](hyp:barSigma). If [their Bures distance
is at most half the square root of the smallest reference feature eigenvalue](hyp:hradius),
then [the perturbed feature block is positive definite](goal). -/
lemma perturbed_feature_posDef {p m : ℕ} [NeZero p] [NeZero m]
    (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) (hradius : assPerturbedConditionNumberRadius Sigma barSigma) :
    (blockX p m barSigma.val).PosDef := by
  apply posDef_of_lambdaMin_pos _
    (barSigma.property.submatrix (Fin.castAdd m)).isHermitian
  exact (div_pos (lambdaMin_pos_of_posDef _ Sigma.carrier.property)
    (by norm_num : (0 : ℝ) < 4)).trans_le
      (perturbed_feature_eigenvalue_lower hsv Sigma barSigma hradius)

-- @node: perturbed_feature_radius_ratios
/-- Under [the convention that singular values are nonnegative and decreasing and
the minimum singular value is the last one](hyp:hsv), take [a reference joint
second-moment matrix with positive definite feature block](hyp:Sigma) and
[a positive semidefinite perturbed matrix](hyp:barSigma), with [Bures distance at
most half the square root of the smallest reference feature eigenvalue](hyp:hradius).
Then [the Bures distance divided by the square root of the smallest perturbed
feature eigenvalue is at most one, and the sum of the square root of the smallest
reference feature eigenvalue and the Bures distance, divided by that same perturbed
square root, is at most three](goal). -/
lemma perturbed_feature_radius_ratios {p m : ℕ} [NeZero p] [NeZero m]
    (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) (hradius : assPerturbedConditionNumberRadius Sigma barSigma) :
    buresDistance barSigma.val Sigma.carrier.val.val /
        Real.sqrt (lambdaMin (blockX p m barSigma.val)) ≤ 1 ∧
    (Real.sqrt (lambdaMin (blockX p m Sigma.carrier.val.val)) +
        buresDistance barSigma.val Sigma.carrier.val.val) /
        Real.sqrt (lambdaMin (blockX p m barSigma.val)) ≤ 3 := by
  have hl := perturbed_feature_sqrt_lower hsv Sigma barSigma hradius
  have hp := Real.sqrt_pos.mpr (lambdaMin_pos_of_posDef _
    (perturbed_feature_posDef hsv Sigma barSigma hradius))
  change buresDistance barSigma.val Sigma.carrier.val.val ≤ _ at hradius
  constructor
  · apply (div_le_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

-- @node: coefficient_difference_factor_bound
/-- For [coefficient matrices A and B](hyp:A,B) and [a feature factor X](hyp:X)
with [full row rank](hyp:hX), [the operator norm of B minus A is at most the
Frobenius norm of their difference times X, divided by the minimum singular value
of X](goal). -/
lemma coefficient_difference_factor_bound {p m d : ℕ} [NeZero p]
    (A B : Mat m p) (X : Mat p d) (hX : assSinThmVariantRowRank X) :
    opNorm (B - A) ≤ frob ((B - A) * X) / minSV X := by
  have hid : (B - A) * X * moorePenroseInverse X = B - A := by
    rw [Matrix.mul_assoc, penrose_full_row_projection X hX, Matrix.mul_one]
  calc
    _ = opNorm ((B - A) * X * moorePenroseInverse X) := congrArg opNorm hid.symm
    _ ≤ frob ((B - A) * X * moorePenroseInverse X) := opNorm_le_frob _
    _ ≤ frob ((B - A) * X) * opNorm (moorePenroseInverse X) := frob_mul_right_le _ _
    _ = _ := by rw [penrose_full_row_norm X hX, div_eq_mul_inv]

-- @node: projected_optimal_residual_perturbation
/-- Under [the convention that singular values are nonnegative and decreasing and
the minimum singular value is the last one](hyp:hsv), take [a coefficient matrix
C](hyp:C), [a feature factor X and its perturbation DX](hyp:X,DX), and [a response
factor Y and its perturbation DY](hyp:Y,DY). If [X has full row rank](hyp:hX) and
[the residual Y minus C times X has zero projection onto the row space of X](hyp:hE),
then [the Frobenius norm of the perturbed residual projected onto the perturbed
feature row space is at most the combined Frobenius size of DX and DY times the
sum of the square root of one plus the squared operator norm of C and the operator
norm of the original residual divided by the minimum singular value of X](goal). -/
lemma projected_optimal_residual_perturbation {p m d : ℕ} [NeZero p] [NeZero d]
    (hsv : assSingularValueConvention) (C : Mat m p)
    (X DX : Mat p d) (Y DY : Mat m d)
    (hX : assSinThmVariantRowRank X)
    (hE : (Y - C * X) * rowProjector X = 0) :
    frob ((Y + DY - C * (X + DX)) * rowProjector (X + DX)) ≤
      (Real.sqrt (1 + opNorm C ^ 2) + opNorm (Y - C * X) / minSV X) *
        Real.sqrt (frob DX ^ 2 + frob DY ^ 2) := by
  have h := refined_factor_stability hsv C C X DX Y DY hX hE
  have hz : opNorm (0 : Mat m p) = 0 := by simp [opNorm, matrixCLM]
  simp only [hE, show frob (0 : Mat m d) = 0 by simp [frob], zero_sub, abs_neg,
    abs_of_nonneg (frob_nonneg _), sub_self, hz, max_eq_right (Real.sqrt_nonneg _)] at h
  have hd : frob DX ≤ Real.sqrt (frob DX ^ 2 + frob DY ^ 2) := by
    apply (Real.le_sqrt (frob_nonneg _) (by positivity)).mpr
    nlinarith [sq_nonneg (frob DY)]
  calc
    _ ≤ _ := h
    _ ≤ Real.sqrt (1 + opNorm C ^ 2) * Real.sqrt (frob DX ^ 2 + frob DY ^ 2) +
        opNorm (Y - C * X) * (Real.sqrt (frob DX ^ 2 + frob DY ^ 2) / minSV X) := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hd ((hsv p d X).2.1 _))
        (show 0 ≤ opNorm (Y - C * X) from norm_nonneg _))
    _ = _ := by ring

set_option maxHeartbeats 800000 in
-- @node: residual_factor_perturbation_bound
/-- For [a coefficient matrix C](hyp:C), [a feature factor X and its perturbation
DX](hyp:X,DX), [a response factor Y and its perturbation DY](hyp:Y,DY), and
[a square matrix Q acting on factor columns](hyp:Q), suppose [the operator norm of
the identity minus Q is at most one](hyp:hQ) and [the perturbed feature factor
times the identity minus Q is zero](hyp:hXQ). Then [the operator norm of the
perturbed response factor times the identity minus Q is at most the operator norm
of the original residual plus the square root of one plus the squared operator
norm of C times the combined Frobenius size of DX and DY](goal). -/
lemma residual_factor_perturbation_bound {p m d : ℕ}
    (C : Mat m p) (X DX : Mat p d) (Y DY : Mat m d)
    (Q : Mat d d) (hQ : opNorm (1 - Q) ≤ 1)
    (hXQ : (X + DX) * (1 - Q) = 0) :
    opNorm ((Y + DY) * (1 - Q)) ≤ opNorm (Y - C * X) +
      Real.sqrt (1 + opNorm C ^ 2) * Real.sqrt (frob DX ^ 2 + frob DY ^ 2) := by
  have hid : (Y + DY) * (1 - Q) =
      ((Y - C * X) + (DY - C * DX)) * (1 - Q) := by
    have hz := congrArg (fun M => C * M) hXQ
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, Matrix.add_mul] at hz
    simp only [Matrix.add_mul, Matrix.sub_mul]
    rw [show C * X * (1 - Q) = -(C * DX * (1 - Q)) from eq_neg_of_add_eq_zero_left hz]
    abel
  have hproj : opNorm (1 - Q) ≤ 1 := hQ
  have hn : opNorm ((Y - C * X) + (DY - C * DX)) ≤
      opNorm (Y - C * X) + opNorm (DY - C * DX) := by
    simpa [opNorm, matrixCLM] using norm_add_le
      (matrixCLM (Y - C * X)) (matrixCLM (DY - C * DX))
  have hd : opNorm (DY - C * DX) ≤
      Real.sqrt (1 + opNorm C ^ 2) * Real.sqrt (frob DX ^ 2 + frob DY ^ 2) := by
    apply (opNorm_le_frob _).trans
    have hb := refined_response_perturbation_sq C DX DY
    have he : frob (DY - C * DX) = frob (C * DX - DY) := by
      simp [frob, sub_sq_comm]
    rw [he]
    apply (sq_le_sq₀ (frob_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    exact hb
  rw [hid]
  exact (opNorm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hproj (norm_nonneg _)).trans
    (by simpa only [mul_one, opNorm] using hn.trans (add_le_add (le_refl _) hd)))

set_option maxHeartbeats 1600000 in
-- @node: lem:perturbed-condition-number
/-- Assuming [the squared Euclidean norm of each response vector equals the sum
of its squared coordinates](hyp:hpin) and [singular values are nonnegative and
decreasing with the minimum singular value last](hyp:hsv), take [a reference joint
second-moment matrix with positive definite feature block](hyp:Sigma) and
[a positive semidefinite perturbed matrix](hyp:barSigma). If [their Bures distance
is at most half the square root of the smallest reference feature eigenvalue](hyp:hradius),
then [the perturbed feature block is positive definite and the perturbed matrix
condition number is at most nineteen times the reference matrix condition number](goal). -/
lemma perturbedConditionNumber {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) (hradius : assPerturbedConditionNumberRadius Sigma barSigma) :
    (blockX p m barSigma.val).PosDef ∧ matrixCondition barSigma ≤ 19 * matrixCondition
      Sigma.carrier.val := by
  have hbar := perturbed_feature_posDef hsv Sigma barSigma hradius
  refine ⟨hbar, ?_⟩
  let k := (matrixCondition Sigma.carrier.val).toReal
  let C := canonicalCoefficient Sigma.carrier.val.val
  let B := canonicalCoefficient barSigma.val
  let l := lambdaMin (blockX p m Sigma.carrier.val.val)
  let lb := lambdaMin (blockX p m barSigma.val)
  let e := buresDistance barSigma.val Sigma.carrier.val.val
  have hl : 0 < l := lambdaMin_pos_of_posDef _ Sigma.carrier.property
  have hlb : 0 < lb := lambdaMin_pos_of_posDef _ hbar
  have hfinite := matrixCondition_ne_top hpin hsv Sigma
  have hlow := (altConditionNumberClosedForm hpin hsv Sigma).2.1
  rw [← matrixCondition_eq_alternativeConditionNumber hpin hsv Sigma] at hlow
  have hkbound : 1 + max (opNorm C ^ 2)
      (lambdaMax (matrixResidual Sigma.carrier.val.val) / l) ≤ k :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hlow
  have hC : 1 + opNorm C ^ 2 ≤ k := by
    have hm := le_max_left (opNorm C ^ 2)
      (lambdaMax (matrixResidual Sigma.carrier.val.val) / l)
    linarith
  have hk : 1 ≤ k := by nlinarith [sq_nonneg (opNorm C)]
  have hk0 : 0 ≤ k := hk.trans' (by norm_num)
  have hres : lambdaMax (matrixResidual Sigma.carrier.val.val) / l ≤ k := by
    have hm := le_max_right (opNorm C ^ 2)
      (lambdaMax (matrixResidual Sigma.carrier.val.val) / l)
    linarith
  have hCsqrt : Real.sqrt (1 + opNorm C ^ 2) ≤ Real.sqrt k := Real.sqrt_le_sqrt hC
  obtain ⟨S, T, hS, hT, hd⟩ :=
    (buresProcrustes Sigma.carrier.val barSigma).2.1.1
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  let DX := (factorBlocks p m (T - S)).1
  let DY := (factorBlocks p m (T - S)).2
  let E := Y - C * X
  let Q := rowProjector (X + DX)
  have hblocks : (factorBlocks p m T).1 = X + DX ∧
      (factorBlocks p m T).2 = Y + DY := by
    constructor <;> ext i j <;>
      simp [X, Y, DX, DY, factorBlocks, Matrix.submatrix_apply]
  have hgramX : blockX p m Sigma.carrier.val.val = X * X.transpose := by
    rw [hS]
    exact (factor_gram_blocks S).1
  have hgramT : blockX p m barSigma.val = (X + DX) * (X + DX).transpose := by
    rw [hT, (factor_gram_blocks T).1, hblocks.1]
  have hX := refined_factor_row_rank X (hgramX ▸ Sigma.carrier.property)
  have hXT := refined_factor_row_rank (X + DX) (hgramT ▸ hbar)
  have hg := regretProjectionFormula hpin hsv Sigma.carrier.val S hS
  have ht := regretProjectionFormula hpin hsv barSigma T hT
  have hEP : E * rowProjector X = 0 := hg.2.2.2.2.1
  have hEE : E * E.transpose = matrixResidual Sigma.carrier.val.val := hg.2.2.2.2.2.1
  have hsize : Real.sqrt (frob DX ^ 2 + frob DY ^ 2) = e := by
    rw [← frob_factorBlocks_sq, Real.sqrt_sq (frob_nonneg _)]
    have heq : frob (T - S) = frob (S - T) := by simp [frob, sub_sq_comm]
    rw [heq, hd, bures_distance_symm Sigma.carrier.val barSigma]
  have hi : (minSV X)⁻¹ ≤ (Real.sqrt l)⁻¹ := by
    simpa only [← hS, X, l] using refined_inverse_minSV_le S hX
  have hEi : opNorm E / minSV X ≤ Real.sqrt k := by
    have he := refined_gram_opNorm_le_sqrt_lambdaMax E
    rw [hEE] at he
    calc
      _ = opNorm E * (minSV X)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.sqrt (lambdaMax (matrixResidual Sigma.carrier.val.val)) *
          (Real.sqrt l)⁻¹ := mul_le_mul he hi
            (inv_nonneg.mpr ((hsv p (p + m) X).2.1 _)) (Real.sqrt_nonneg _)
      _ = Real.sqrt (lambdaMax (matrixResidual Sigma.carrier.val.val) / l) := by
        rw [Real.sqrt_div' _ hl.le, div_eq_mul_inv]
      _ ≤ Real.sqrt k := Real.sqrt_le_sqrt hres
  have hEnorm : opNorm E ≤ Real.sqrt k * Real.sqrt l := by
    have he := refined_gram_opNorm_le_sqrt_lambdaMax E
    rw [hEE] at he
    apply he.trans
    rw [← Real.sqrt_mul hk0]
    exact Real.sqrt_le_sqrt ((div_le_iff₀ hl).mp hres)
  have hproj := projected_optimal_residual_perturbation hsv C X DX Y DY hX hEP
  rw [hsize] at hproj
  have he0 : 0 ≤ e := by rw [← hsize]; positivity
  have hproj2 : frob ((Y + DY - C * (X + DX)) * Q) ≤ 2 * Real.sqrt k * e :=
    hproj.trans (mul_le_mul_of_nonneg_right (by linarith) he0)
  have hcoef : (Y + DY - C * (X + DX)) * Q = (B - C) * (X + DX) := by
    have hx : (X + DX) * Q = X + DX := by
      simpa only [Q, rowProjector, Matrix.mul_assoc] using
        (moorePenroseInverse_spec (X + DX)).1
    have hb : B * (X + DX) = (Y + DY) * Q := by
      have hc := ht.2.1
      rw [hblocks.1, hblocks.2] at hc
      change B = (Y + DY) * moorePenroseInverse (X + DX) at hc
      rw [hc, Matrix.mul_assoc]
      rfl
    rw [Matrix.sub_mul, Matrix.mul_assoc C, hx, Matrix.sub_mul, hb]
  rw [hcoef] at hproj2
  have hit : (minSV (X + DX))⁻¹ ≤ (Real.sqrt lb)⁻¹ := by
    have hh := refined_inverse_minSV_le T (hblocks.1.symm ▸ hXT)
    simpa only [← hT, hblocks.1, lb] using hh
  have hdiff : opNorm (B - C) ≤ 2 * Real.sqrt k * e / Real.sqrt lb := by
    apply (coefficient_difference_factor_bound C B (X + DX) hXT).trans
    simp only [div_eq_mul_inv]
    exact mul_le_mul hproj2 hit (inv_nonneg.mpr ((hsv p (p + m) (X + DX)).2.1 _))
      (by positivity)
  have hratios := perturbed_feature_radius_ratios hsv Sigma barSigma hradius
  have hdiff2 : opNorm (B - C) ≤ 2 * Real.sqrt k := by
    apply hdiff.trans
    calc
      _ = (2 * Real.sqrt k) * (e / Real.sqrt lb) := by ring
      _ ≤ (2 * Real.sqrt k) * 1 := mul_le_mul_of_nonneg_left hratios.1 (by positivity)
      _ = _ := mul_one _
  have hCnorm : opNorm C ≤ Real.sqrt k := by
    apply (Real.le_sqrt (show 0 ≤ opNorm C from norm_nonneg _) hk0).mpr
    linarith
  have hBnorm : opNorm B ≤ 3 * Real.sqrt k := by
    have hn : opNorm B ≤ opNorm (B - C) + opNorm C := by
      have hh := norm_add_le (matrixCLM (B - C)) (matrixCLM C)
      simpa [opNorm, matrixCLM] using hh
    linarith
  have hBsquare : opNorm B ^ 2 ≤ 9 * k := by
    have hh := pow_le_pow_left₀ (show 0 ≤ opNorm B from norm_nonneg _) hBnorm 2
    simpa only [mul_pow, Real.sq_sqrt hk0, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hkill : (X + DX) * (1 - Q) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Q, rowProjector, ← Matrix.mul_assoc,
      (moorePenroseInverse_spec (X + DX)).1, sub_self]
  have hresfactor := residual_factor_perturbation_bound C X DX Y DY Q
    (rowProjection_norms_le_one (X + DX)).2 hkill
  rw [hsize] at hresfactor
  have hresfactor2 : opNorm ((Y + DY) * (1 - Q)) ≤ Real.sqrt k * (Real.sqrt l + e) := by
    calc
      _ ≤ opNorm E + Real.sqrt (1 + opNorm C ^ 2) * e := hresfactor
      _ ≤ Real.sqrt k * Real.sqrt l + Real.sqrt k * e :=
        add_le_add hEnorm (mul_le_mul_of_nonneg_right hCsqrt he0)
      _ = _ := by ring
  have hresgram : matrixResidual barSigma.val =
      ((Y + DY) * (1 - Q)) * ((Y + DY) * (1 - Q)).transpose := by
    have he := ht.2.2.1
    have hh := ht.2.2.2.2.2.1
    rw [he, hblocks.1, hblocks.2] at hh
    exact hh.symm
  have hresbar : lambdaMax (matrixResidual barSigma.val) / lb ≤ 9 * k := by
    rw [hresgram, lambdaMax_gram]
    apply (div_le_iff₀ hlb).mpr
    have hr : Real.sqrt l + e ≤ 3 * Real.sqrt lb :=
      (div_le_iff₀ (Real.sqrt_pos.mpr hlb)).mp hratios.2
    have hn := hresfactor2.trans (mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg k))
    have hs := pow_le_pow_left₀
      (show 0 ≤ opNorm ((Y + DY) * (1 - Q)) from norm_nonneg _) hn 2
    simpa only [mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt hlb.le,
      show (3 : ℝ) ^ 2 = 9 by norm_num, mul_left_comm, mul_assoc] using hs
  let barS : NondegenerateSecondMoments p m := ⟨⟨barSigma, hbar⟩⟩
  have hub := (altConditionNumberClosedForm hpin hsv barS).2.2
  rw [← matrixCondition_eq_alternativeConditionNumber hpin hsv barS] at hub
  have hreal : conditionUpper barSigma.val ≤ 19 * k := by
    change 1 + opNorm B ^ 2 + lambdaMax (matrixResidual barSigma.val) / lb ≤ 19 * k
    linarith
  calc
    matrixCondition barSigma ≤ ENNReal.ofReal (conditionUpper barSigma.val) := hub
    _ ≤ ENNReal.ofReal (19 * k) := ENNReal.ofReal_le_ofReal hreal
    _ = 19 * matrixCondition Sigma.carrier.val := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 19),
        ENNReal.ofReal_toReal hfinite]
      norm_num

end Papers.WassersteinRegretS2S3
