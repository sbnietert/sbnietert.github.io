module
public import Papers.WassersteinRegretS2S3.Helpers.Stability
public import Papers.WassersteinRegretS2S3.Helpers.InnerDRO

/-!
# Population Wasserstein regret: Helpers/Regularizer

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: regularizer_factor_variation
/-- For [a linear transformation M](hyp:M), [a factor matrix S](hyp:S), and
[a factor perturbation D](hyp:D), [the change in the squared Frobenius norm
of the transformed factor is bounded below by minus twice the Frobenius norm
of the transpose of M times M times S times the perturbation norm, and above
by the corresponding positive term plus the squared operator norm of M times
the squared perturbation norm](goal). -/
lemma regularizer_factor_variation {k d r : ℕ}
    (M : Mat k d) (S D : Mat d r) :
    -2 * frob (M.transpose * (M * S)) * frob D ≤
        frob (M * (S + D)) ^ 2 - frob (M * S) ^ 2 ∧
    frob (M * (S + D)) ^ 2 - frob (M * S) ^ 2 ≤
      2 * frob (M.transpose * (M * S)) * frob D + opNorm M ^ 2 * frob D ^ 2 := by
  have hc := condition_trace_pairing_le (M.transpose * (M * S)) D
  have ht : Matrix.trace ((M * S).transpose * (M * D)) =
      Matrix.trace ((M.transpose * (M * S)).transpose * D) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have he := frob_sq_add_trace (M * S) (M * D)
  rw [ht, ← Matrix.mul_add] at he
  have hm := pow_le_pow_left₀ (frob_nonneg _) (frob_mul_left_le M D) 2
  rw [mul_pow] at hm
  constructor
  · nlinarith [(abs_le.mp hc).1, sq_nonneg (frob (M * D))]
  · nlinarith [(abs_le.mp hc).2]

-- @node: regularizer_gradient_norm
/-- For [a joint law P with positive definite feature second moments](hyp:P)
and [a square joint factor S](hyp:S), if [the second-moment matrix of P equals
S times its transpose](hyp:hS), then [the Frobenius norm of the transpose of
the optimal regression residual matrix times that residual matrix times S
equals the distributionally robust regularizer scale of P](goal). -/
lemma regularizer_gradient_norm {p m : ℕ} (P : NondegenerateLaws p m)
    (S : Mat (p + m) (p + m)) (hS : secondMoment P.carrier.val = S * S.transpose) :
    frob ((quadraticRegressionMatrix (optimalPredictor P)).transpose *
      (quadraticRegressionMatrix (optimalPredictor P) * S)) = droRegularizerScale P := by
  let M := quadraticRegressionMatrix (optimalPredictor P)
  have hr : residualSecondMoment P = (M * S) * (M * S).transpose := by
    rw [(residual_law_matrix P).1]
    change quadraticRegressionMatrix (canonicalCoefficient (secondMoment P.carrier.val)) *
      secondMoment P.carrier.val *
      (quadraticRegressionMatrix (canonicalCoefficient (secondMoment P.carrier.val))).transpose = _
    rw [← optimalPredictor_eq_canonical, hS]
    simp only [M, Matrix.transpose_mul, Matrix.mul_assoc]
  have he : frob (M.transpose * (M * S)) ^ 2 =
      Matrix.trace (((1 : Mat m m) + optimalPredictor P * (optimalPredictor P).transpose) *
        residualSecondMoment P) := by
    calc
      _ = Matrix.trace ((M.transpose * ((M * S) * (M * S).transpose)) * M) := by
        rw [frob_sq_trace_rows, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((M * M.transpose) * ((M * S) * (M * S).transpose)) := by
        rw [Matrix.trace_mul_cycle]
      _ = _ := by rw [residualMatrix_gram, add_comm, ← hr]
  rw [droRegularizerScale, ← he, Real.sqrt_sq (frob_nonneg _)]

-- @node: fixed_predictor_loss_variation_two_sided
/-- Assuming [the Euclidean squared-norm identity](hyp:hpin) and
[nonincreasing, nonnegative singular values with the specified minimum-value
convention](hyp:hsv), consider [a joint law P with positive definite feature
second moments](hyp:P), [a nonnegative radius delta](hyp:delta), and
[a joint law Q](hyp:Q) such that [Q is within Wasserstein distance delta of
P](hyp:hQ), with positive feature and response dimensions. [The change from
P to Q in the risk of the optimal predictor for P lies between minus twice
the regularizer scale times delta and twice that scale times delta plus the
condition number of P times delta squared](goal). -/
lemma fixed_predictor_loss_variation_two_sided {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m)
    (delta : ℝ≥0) (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val delta) :
    -2 * droRegularizerScale P * delta ≤
        risk (optimalPredictor P) Q - risk (optimalPredictor P) P.carrier.val ∧
    risk (optimalPredictor P) Q - risk (optimalPredictor P) P.carrier.val ≤
      2 * droRegularizerScale P * delta +
        (conditionNumber P.carrier.val).toReal * (delta : ℝ) ^ 2 := by
  let S := CFC.sqrt (secondMoment P.carrier.val)
  let M := quadraticRegressionMatrix (optimalPredictor P)
  have hS : secondMoment P.carrier.val = S * S.transpose :=
    psd_sqrt_factor (momentPSD P.carrier.val)
  have hi := w2BuresEquivalence hsv P.carrier.val delta
  have hmem := Set.mem_image_of_mem secondMoment hQ
  rw [hi.1, hi.2] at hmem
  obtain ⟨D, hD, hfactor⟩ := hmem
  have hr (T : JointLaws p m) (W : Mat (p + m) (p + m))
      (hW : secondMoment T = W * W.transpose) :
      risk (optimalPredictor P) T = frob (M * W) ^ 2 := by
    rw [risk_eq_matrixRisk, hW, matrixRisk_gram_factor, quadraticRegressionMatrix_factor]
  have hg := regularizer_gradient_norm P S hS
  have hb := regularizer_factor_variation M S D
  rw [hg] at hb
  have hf := conditionNumberFormula hpin hsv P
  have hl : 1 + max (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val)) ≤
      (conditionNumber P.carrier.val).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hf.1).mp hf.2.2.2.2.1
  have hk : opNorm M ^ 2 ≤ (conditionNumber P.carrier.val).toReal := by
    rw [residualMatrix_opNorm]
    exact (add_le_add_right (le_max_left _ _) 1).trans hl
  have hquad : opNorm M ^ 2 * frob D ^ 2 ≤
      (conditionNumber P.carrier.val).toReal * (delta : ℝ) ^ 2 :=
    mul_le_mul hk (pow_le_pow_left₀ (frob_nonneg _) hD 2) (sq_nonneg _)
      ENNReal.toReal_nonneg
  have hlin : 2 * droRegularizerScale P * frob D ≤ 2 * droRegularizerScale P * delta :=
    mul_le_mul_of_nonneg_left hD
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _))
  rw [hr Q (S + D) hfactor, hr P.carrier.val S hS]
  constructor <;> linarith [hb.1, hb.2]

-- @node: fixed_predictor_loss_variation
/-- Assuming [the Euclidean squared-norm identity](hyp:hpin) and
[nonincreasing, nonnegative singular values with the specified minimum-value
convention](hyp:hsv), consider [a joint law P with positive definite feature
second moments](hyp:P), [a nonnegative radius delta](hyp:delta), and
[a joint law Q](hyp:Q) such that [Q is within Wasserstein distance delta of
P](hyp:hQ), with positive feature and response dimensions. [The absolute
change from P to Q in the risk of the optimal predictor for P is at most
twice the regularizer scale times delta plus the condition number of P times
delta squared](goal). -/
lemma fixed_predictor_loss_variation {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m)
    (delta : ℝ≥0) (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val delta) :
    |risk (optimalPredictor P) Q - risk (optimalPredictor P) P.carrier.val| ≤
      2 * droRegularizerScale P * delta + (conditionNumber P.carrier.val).toReal * (delta : ℝ)
         ^ 2 := by
  have hb := fixed_predictor_loss_variation_two_sided hpin hsv P delta Q hQ
  apply abs_le.mpr
  constructor
  · have hnon : 0 ≤ (conditionNumber P.carrier.val).toReal * (delta : ℝ) ^ 2 := by positivity
    linarith [hb.1]
  · exact hb.2

-- @node: dro_selection_risk_le
/-- For [a nonnegative radius](hyp:eps) and [an estimator rule](hyp:rule) that
[minimizes worst-case population risk at that radius for every law](hyp:hsel),
consider [a center law and a target law](hyp:center,target) such that
[the target lies in the Wasserstein ball about the center](hyp:htarget).
If [a comparison predictor A](hyp:A) and [a real bound C](hyp:C) satisfy
[C is nonnegative](hyp:hC) and [the risk of A is at most C at every law in
that ball](hyp:hbound), then [the rule fitted to the center has risk at most
C under the target law](goal). -/
lemma dro_selection_risk_le {p m : ℕ} (eps : ℝ≥0)
    (rule : Estimator p m) (hsel : IsPopulationSelection 1 eps rule)
    (center target : JointLaws p m) (htarget : target ∈ lawBall center eps)
    (A : Mat m p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ Q ∈ lawBall center eps, risk A Q ≤ C) :
    risk (rule center) target ≤ C := by
  have ho := hsel center (Set.mem_univ A)
  change populationObjective 1 center eps (rule center) ≤ populationObjective 1 center eps A at ho
  simp only [populationObjective, show (1 : Fin 4) ≠ 0 by decide, if_false, ite_true] at ho
  have hs : (⨆ Q ∈ lawBall center eps, ENNReal.ofReal (risk A Q)) ≤ ENNReal.ofReal C :=
    iSup_le fun Q => iSup_le fun hQ => ENNReal.ofReal_le_ofReal (hbound Q hQ)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  calc
    _ ≤ ⨆ Q ∈ lawBall center eps, ENNReal.ofReal (risk (rule center) Q) :=
      le_iSup₂_of_le target htarget le_rfl
    _ ≤ ENNReal.ofReal C := ho.trans hs

-- @node: lem:dro-regularizer
/-- Assuming [the Euclidean squared-norm identity](hyp:hpin) and
[nonincreasing, nonnegative singular values with the specified minimum-value
convention](hyp:hsv), consider [a joint law P with positive definite feature
second moments](hyp:P), [a nonnegative radius](hyp:eps), and [an estimator
rule](hyp:rule) that [minimizes worst-case population risk at that radius for
every law](hyp:hsel), with positive feature and response dimensions.
[Its robust regret about P is at most four times the regularizer scale of P
times the radius plus five times the condition number of P times the squared
radius](goal). -/
lemma droRegularizer {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m)
    (eps : ℝ≥0) (rule : Estimator p m) (hsel : IsPopulationSelection 1 eps rule) :
    robustRegret rule P.carrier.val eps ≤
      ENNReal.ofReal (4 * droRegularizerScale P * eps) + 5 * conditionNumber P.carrier.val *
        (eps : ℝ≥0∞) ^ 2 := by
  let A := optimalPredictor P
  let k := (conditionNumber P.carrier.val).toReal
  let g := droRegularizerScale P
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have he : 0 ≤ (eps : ℝ) := eps.property
  have hrisk : 0 ≤ risk A P.carrier.val := risk_nonneg _ _
  have hcomparison (delta : ℝ≥0) (Q : JointLaws p m)
      (hQ : Q ∈ lawBall P.carrier.val delta) :=
    fixed_predictor_loss_variation_two_sided hpin hsv P delta Q hQ
  have hsource (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val eps) :
      regret (rule P.carrier.val) Q ≤ 4 * g * eps + 5 * k * (eps : ℝ) ^ 2 := by
    have hb : risk (rule P.carrier.val) Q ≤
        risk A P.carrier.val + 2 * g * eps + k * (eps : ℝ) ^ 2 := by
      apply dro_selection_risk_le eps rule hsel P.carrier.val Q hQ A
      · positivity
      · intro T hT
        have ht := (hcomparison eps T hT).2
        dsimp only [A, k, g] at *
        linarith
    have hl := (hcomparison eps Q hQ).1
    have hs := (regretStability hpin hsv A P Q).2
    have hsreal : regret A Q ≤ 4 * k * wassersteinDistance P.carrier.val Q ^ 2 := by
      have hf := conditionNumber_ne_top P
      have heq : 4 * conditionNumber P.carrier.val *
          ENNReal.ofReal (wassersteinDistance P.carrier.val Q) ^ 2 =
          ENNReal.ofReal (4 * k * wassersteinDistance P.carrier.val Q ^ 2) := by
        simp only [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hk),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_toReal hf,
          ENNReal.ofReal_pow (wasserstein_nonneg _ _), ENNReal.ofReal_ofNat, k]
      rw [heq] at hs
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hs
    have hsrad : regret A Q ≤ 4 * k * (eps : ℝ) ^ 2 :=
      hsreal.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (wasserstein_nonneg _ _) hQ 2) (by positivity))
    have hid : regret (rule P.carrier.val) Q =
        risk (rule P.carrier.val) Q - risk A Q + regret A Q := by
      unfold regret
      ring
    dsimp only [A, k, g] at *
    linarith
  have htarget (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val eps) :
      regret (rule Q) P.carrier.val ≤ 4 * g * eps + 5 * k * (eps : ℝ) ^ 2 := by
    have hrev : P.carrier.val ∈ lawBall Q eps := by
      change wassersteinDistance Q P.carrier.val ≤ eps
      rw [wasserstein_symm]
      exact hQ
    have hb : risk (rule Q) P.carrier.val ≤
        risk A P.carrier.val + 4 * g * eps + 4 * k * (eps : ℝ) ^ 2 := by
      apply dro_selection_risk_le eps rule hsel Q P.carrier.val hrev A
      · positivity
      · intro T hT
        have hT' : T ∈ lawBall P.carrier.val (2 * eps) := by
          change wassersteinDistance P.carrier.val T ≤ ((2 * eps : ℝ≥0) : ℝ)
          have ht := wasserstein_triangle P.carrier.val Q T
          change wassersteinDistance Q T ≤ (eps : ℝ) at hT
          change wassersteinDistance P.carrier.val Q ≤ (eps : ℝ) at hQ
          push_cast
          linarith
        have ht := (hcomparison (2 * eps) T hT').2
        push_cast at ht
        dsimp only [A, k, g] at *
        nlinarith
    have hz : regret A P.carrier.val = 0 := by
      change regret (optimalPredictor P) P.carrier.val = 0
      rw [optimalPredictor_eq_canonical]
      exact canonical_regret_zero _
    have hid : regret (rule Q) P.carrier.val =
        risk (rule Q) P.carrier.val - risk A P.carrier.val := by
      unfold regret at hz ⊢
      linarith
    rw [hid]
    nlinarith [mul_nonneg hk (sq_nonneg (eps : ℝ))]
  have hbound : robustRegret rule P.carrier.val eps ≤
      ENNReal.ofReal (4 * g * eps + 5 * k * (eps : ℝ) ^ 2) := by
    refine iSup_le fun Q => iSup_le fun hQ => max_le ?_ ?_
    · exact ENNReal.ofReal_le_ofReal (hsource Q hQ)
    · exact ENNReal.ofReal_le_ofReal (htarget Q hQ)
  apply hbound.trans_eq
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hk),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
    ENNReal.ofReal_toReal (conditionNumber_ne_top P),
    ENNReal.ofReal_pow he, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat, k]

end Papers.WassersteinRegretS2S3
