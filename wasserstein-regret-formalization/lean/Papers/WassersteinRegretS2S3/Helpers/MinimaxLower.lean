module
public import Papers.WassersteinRegretS2S3.Helpers.Scaling

/-!
# Population Wasserstein regret: Helpers/MinimaxLower

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: noiseless_identity_law
/-- [Every real coefficient matrix A can be realized by a joint law with identity
feature second-moment matrix, canonical regression coefficient A, and zero residual
second-moment matrix](goal). -/
lemma noiseless_identity_law {p m : ℕ} (A : Mat m p) :
    ∃ P : JointLaws p m, secondMomentX P = 1 ∧
      canonicalCoefficient (secondMoment P) = A ∧ matrixResidual (secondMoment P) = 0 := by
  let F : Mat (p + m) p := fun i j => Fin.addCases (fun k => (1 : Mat p p) k j)
    (fun k => A k j) i
  have hF : factorBlocks p m F = (1, A) := by
    apply Prod.ext <;> ext i j <;> simp [factorBlocks, F, Matrix.submatrix]
  obtain ⟨P, hP⟩ := psd_law_realization
    ⟨F * F.transpose, by simpa using Matrix.posSemidef_self_mul_conjTranspose F⟩
  have hx : blockX p m (secondMoment P) = 1 := by
    rw [hP, (factor_gram_blocks F).1, hF]
    simp
  have hyx : blockYX p m (secondMoment P) = A := by
    rw [hP, (factor_gram_blocks F).2.1, hF]
    simp
  have hA : canonicalCoefficient (secondMoment P) = A := by
    rw [canonicalCoefficient, hx, hyx,
      penrose_eq_inverse_of_isUnit _ (isUnit_one)]
    simp
  refine ⟨P, hx, hA, ?_⟩
  have hzero : quadraticRegressionMatrix A * F = 0 := by
    rw [quadraticRegressionMatrix_factor, hF]
    simp
  rw [matrixResidual, hA, hP, ← Matrix.mul_assoc, hzero, Matrix.zero_mul, Matrix.zero_mul]

-- @node: opNorm_single_entry
/-- If [b is nonnegative](hyp:hb), then [the operator norm of the matrix with b in
its first entry and zeros everywhere else equals b](goal). -/
lemma opNorm_single_entry {p m : ℕ} [NeZero p] [NeZero m] (b : ℝ) (hb : 0 ≤ b) :
    opNorm (fun (i : Fin m) (j : Fin p) => if i = 0 ∧ j = 0 then b else 0) = b := by
  let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then b else 0
  have hf : frob A = b := by
    simp only [frob, A, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    simp_rw [ite_and]
    simp [Real.sqrt_sq hb]
  apply le_antisymm ((opNorm_le_frob A).trans_eq hf)
  let x : Euc p := EuclideanSpace.single 0 1
  have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.single, PiLp.norm_single]
  have hAx : matrixCLM A x = EuclideanSpace.single 0 b := by
    ext i
    change (∑ j, A i j * x j) = (EuclideanSpace.single 0 b) i
    by_cases hi : i = 0
    · subst i
      simp [A, x, EuclideanSpace.single, PiLp.single_apply]
    · simp [A, hi, EuclideanSpace.single]
  have h := (matrixCLM A).le_opNorm x
  rw [hAx, hx, mul_one] at h
  simpa [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
    abs_of_nonneg hb, opNorm] using h

-- @node: prescribed_condition_law
/-- If [kappa is at least one](hyp:hkappa), then [there exists a joint law with positive
definite feature second-moment matrix whose condition number is exactly kappa](goal). -/
lemma prescribed_condition_law {p m : ℕ} [NeZero p] [NeZero m]
    (kappa : ℝ) (hkappa : 1 ≤ kappa) :
    ∃ P : NondegenerateLaws p m, conditionNumber P.carrier.val = ENNReal.ofReal kappa := by
  let b := Real.sqrt (kappa - 1)
  let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then b else 0
  obtain ⟨P, hx, hA, hE⟩ := noiseless_identity_law A
  let P' : NondegenerateLaws p m := ⟨⟨P, by rw [hx]; exact Matrix.PosDef.one⟩⟩
  refine ⟨P', ?_⟩
  have hpred : optimalPredictor P' = A := (optimalPredictor_eq_canonical P').trans hA
  have hres : residualSecondMoment P' = 0 := (residual_law_matrix P').1.trans hE
  rw [(conditionNumberFormula (assPin1_valid m) assSingularValueConvention_valid P').2.2.2.1,
    hpred, hres, smul_zero, add_zero, lambdaMax_gram,
    opNorm_single_entry b (Real.sqrt_nonneg _)]
  rw [show b ^ 2 = kappa - 1 from Real.sq_sqrt (by linarith)]
  congr 1
  ring

-- @node: localMinimax_le_classMinimax
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [the reference law P belongs to the class G](hyp:hP), then [the local minimax
regret at P is at most the class minimax regret over G at the same radius](goal). -/
lemma localMinimax_le_classMinimax {p m : ℕ} (G : Set (JointLaws p m))
    (P : JointLaws p m) (hP : P ∈ G) (eps : ℝ≥0) :
    localMinimax P eps ≤ classMinimax G eps := by
  apply iInf_mono
  intro rule
  exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

-- @node: scaled_localMinimax_le_classMinimax
/-- For [a nonnegative target radius eps](hyp:eps), [a nonnegative reference radius delta](hyp:delta),
and a law with positive definite feature second-moment matrix, suppose [its
condition number is at most the nonnegative part of kappa](hyp:hP),
[the target radius eps is positive](hyp:heps), and [the reference radius delta is
positive](hyp:hdelta). Then [the local minimax regret at radius delta, multiplied
by eps squared and divided by delta squared, is at most the class minimax regret
at radius eps over laws with positive definite feature second moment and condition
number at most the nonnegative part of kappa](goal). -/
lemma scaled_localMinimax_le_classMinimax {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) (kappa : ℝ)
    (hP : conditionNumber P.carrier.val ≤ ENNReal.ofReal kappa)
    (eps delta : ℝ≥0) (heps : 0 < eps) (hdelta : 0 < delta) :
    (eps : ℝ≥0∞) ^ 2 * ((delta : ℝ≥0∞)⁻¹ ^ 2 * localMinimax P.carrier.val delta) ≤
      classMinimax (wellConditionedSet p m kappa) eps := by
  let a : ℝ := (eps : ℝ) / delta
  have ha : 0 < a := div_pos heps hdelta
  have har : a.toNNReal * delta = eps := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ ha.le]
    dsimp [a]
    exact div_mul_cancel₀ _ (ne_of_gt (show 0 < (delta : ℝ) from hdelta))
  have hPa : dilateLaw a P.carrier.val ∈ wellConditionedSet p m kappa := by
    refine ⟨(secondMomentX_dilate_posDef_iff a ha _).mpr P.carrier.property, ?_⟩
    rw [conditionNumber_dilateLaw (assPin1_valid m) assSingularValueConvention_valid a ha]
    exact hP
  have hbound := localMinimax_le_classMinimax _ _ hPa eps
  rw [← har, localMinimax_dilateLaw a ha] at hbound
  rw [har] at hbound
  have hcoef : ENNReal.ofReal (a ^ 2) =
      (eps : ℝ≥0∞) ^ 2 * (delta : ℝ≥0∞)⁻¹ ^ 2 := by
    rw [ENNReal.ofReal_pow ha.le]
    have he : ENNReal.ofReal a = (eps : ℝ≥0∞) / (delta : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (show 0 < (delta : ℝ) from hdelta)]
      simp
    rw [he, div_eq_mul_inv, mul_pow]
  rw [hcoef, mul_assoc] at hbound
  exact hbound

-- @node: lem:minimax-lb
/-- For [a nonnegative Wasserstein radius eps](hyp:eps), assume [squared Euclidean response norms equal the sums of squared
coordinates](hyp:hpin) and [singular values are nonnegative and ordered from largest
to smallest, with the minimum singular value given by the last indexed value](hyp:hsv).
If [the Wasserstein radius eps is positive](hyp:heps) and [kappa is at least one](hyp:hkappa),
then [the class minimax regret over laws with positive definite feature second
moment and condition number at most kappa is at least kappa times eps squared](goal). -/
lemma minimaxLb {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (eps : ℝ≥0) (heps : 0 < eps)
    (kappa : ℝ) (hkappa : 1 ≤ kappa) :
    ENNReal.ofReal (kappa * (eps : ℝ) ^ 2) ≤ classMinimax (wellConditionedSet p m kappa) eps := by
  obtain ⟨P, hP⟩ := prescribed_condition_law (p := p) (m := m) kappa hkappa
  have hlim := ENNReal.Tendsto.const_mul (localMinimax_normalized_tendsto P)
    (a := (eps : ℝ≥0∞) ^ 2) (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
  have hbound : (eps : ℝ≥0∞) ^ 2 * conditionNumber P.carrier.val ≤
      classMinimax (wellConditionedSet p m kappa) eps := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact scaled_localMinimax_le_classMinimax P kappa (le_of_eq hP) eps delta heps hdelta
  rw [hP] at hbound
  have he : ENNReal.ofReal (kappa * (eps : ℝ) ^ 2) =
      (eps : ℝ≥0∞) ^ 2 * ENNReal.ofReal kappa := by
    rw [ENNReal.ofReal_mul (by linarith : 0 ≤ kappa),
      ENNReal.ofReal_pow eps.coe_nonneg]
    simp [mul_comm]
  rwa [he]

end Papers.WassersteinRegretS2S3
