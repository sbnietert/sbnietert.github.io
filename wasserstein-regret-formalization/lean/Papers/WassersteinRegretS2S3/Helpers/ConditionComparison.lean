module
public import Papers.WassersteinRegretS2S3.Helpers.ConditionClosedForm
public import Papers.WassersteinRegretS2S3.Helpers.AlternativeContinuity
public import Papers.WassersteinRegretS2S3.Helpers.Scalar
public import Papers.WassersteinRegretS2S3.Helpers.TwoPointComparison

/-!
# Population Wasserstein regret: Helpers/ConditionComparison

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: matrixMinimax_le_source_predictor
/-- For [a nonnegative moment uncertainty radius](hyp:eps), [the minimax regret over a moment uncertainty ball is at most the worst-case
regret of the regression coefficient fitted to the ball's center](goal). -/
lemma matrixMinimax_le_source_predictor {p m : ℕ}
    (Sigma : PSD (p + m)) (eps : ℝ≥0) :
    matrixMinimaxValue Sigma eps ≤
      matrixWorstRegret Sigma eps (canonicalCoefficient Sigma.val) := by
  exact iInf_le _ _

-- @node: source_predictor_regret_le_alternativeValue
/-- For [a nonnegative Bures radius](hyp:eps), if [a target second moment is within the given Bures radius of the source second
moment](hyp:hT), then [the regret at the target of the source-fitted regression
coefficient is at most the alternative value centered at the target with that
radius](goal). -/
lemma source_predictor_regret_le_alternativeValue {p m : ℕ}
    (Sigma T : PSD (p + m)) (eps : ℝ≥0) (hT : T ∈ matrixBall Sigma eps) :
    ENNReal.ofReal (matrixRegret (canonicalCoefficient Sigma.val) T.val) ≤
      alternativeValue T eps := by
  have hS : Sigma ∈ matrixBall T eps := by
    change buresDistance Sigma.val T.val ≤ eps
    rw [bures_distance_symm Sigma T]
    exact hT
  exact le_iSup_of_le Sigma (le_iSup_of_le hS le_rfl)

-- @node: matrixMinimax_le_nearby_alternativeValue
/-- For [a nonnegative moment uncertainty radius](hyp:eps), [the minimax regret over a moment uncertainty ball is bounded above by the
supremum of the alternative values centered at moments in that ball, each evaluated
at the same radius](goal). -/
lemma matrixMinimax_le_nearby_alternativeValue {p m : ℕ}
    (Sigma : PSD (p + m)) (eps : ℝ≥0) :
    matrixMinimaxValue Sigma eps ≤
      ⨆ T ∈ matrixBall Sigma eps, alternativeValue T eps := by
  apply (matrixMinimax_le_source_predictor Sigma eps).trans
  refine iSup_le fun T => iSup_le fun hT => ?_
  exact (source_predictor_regret_le_alternativeValue Sigma T eps hT).trans
    (le_iSup_of_le T (le_iSup_of_le hT le_rfl))

-- @node: matrixCondition_le_nearby_alternative_limsup
/-- [The matrix condition number at a joint second moment is at most the upper limit,
as positive radii shrink to zero, of the supremum of alternative values over the
corresponding moment ball divided by the squared radius](goal). -/
lemma matrixCondition_le_nearby_alternative_limsup {p m : ℕ}
    (Sigma : PSD (p + m)) :
    matrixCondition Sigma ≤ Filter.limsup
      (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 *
        ⨆ T ∈ matrixBall Sigma eps, alternativeValue T eps) positiveRadii := by
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall fun eps =>
    mul_le_mul' le_rfl (matrixMinimax_le_nearby_alternativeValue Sigma eps))

-- @node: lem:condition-number-comparison-ub
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [the matrix condition number at a
nondegenerate joint second moment is at most its alternative condition number](goal). -/
lemma conditionNumberComparisonUb {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m) :
    matrixCondition Sigma.carrier.val ≤ alternativeConditionNumber Sigma := by
  apply (matrixCondition_le_nearby_alternative_limsup Sigma.carrier.val).trans
  exact nearby_alternative_limsup_le Sigma

-- @node: lem:condition-number-comparison-lb
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [the lower asymptotic coefficient of
normalized minimax regret at a nondegenerate joint second moment is at most its
matrix condition number and at least its alternative condition number](goal). -/
lemma conditionNumberComparisonLb {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (Sigma : NondegenerateSecondMoments p m) :
    lowerAsymptoticCoefficient Sigma ≤ matrixCondition Sigma.carrier.val ∧
    alternativeConditionNumber Sigma ≤ lowerAsymptoticCoefficient Sigma := by
  refine ⟨lowerAsymptotic_le_matrixCondition Sigma, ?_⟩
  rw [(altConditionNumberFormula hpin).1 Sigma]
  exact iSup_le fun D => iSup_le fun hD =>
    derivativeSensitivity_le_lowerAsymptotic Sigma D hD

-- @node: matrixCondition_eq_alternativeConditionNumber
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [the matrix condition number and the
alternative condition number agree at every nondegenerate joint second moment](goal). -/
lemma matrixCondition_eq_alternativeConditionNumber {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (Sigma : NondegenerateSecondMoments p m) :
    matrixCondition Sigma.carrier.val = alternativeConditionNumber Sigma := by
  apply le_antisymm (conditionNumberComparisonUb hpin hsv Sigma)
  exact (conditionNumberComparisonLb hpin hsv Sigma).2.trans
    (conditionNumberComparisonLb hpin hsv Sigma).1

-- @node: matrixCondition_ne_top
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [the matrix condition number of a
nondegenerate joint second moment is finite](goal). -/
lemma matrixCondition_ne_top {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (Sigma : NondegenerateSecondMoments p m) :
    matrixCondition Sigma.carrier.val ≠ ⊤ := by
  rw [matrixCondition_eq_alternativeConditionNumber hpin hsv Sigma]
  exact alternativeConditionNumber_ne_top Sigma

-- @node: matrixMinimax_normalized_tendsto
/-- Assuming [squared Euclidean norms equal sums of squared response coordinates](hyp:hpin)
and [singular values are nonnegative, ordered from largest to smallest, with the
specified smallest-value convention](hyp:hsv), [minimax regret at a nondegenerate
joint second moment divided by the squared uncertainty radius converges to the
matrix condition number as the radius tends to zero through positive values](goal). -/
lemma matrixMinimax_normalized_tendsto {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (Sigma : NondegenerateSecondMoments p m) :
    Filter.Tendsto
      (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * matrixMinimaxValue Sigma.carrier.val eps)
      positiveRadii (nhds (matrixCondition Sigma.carrier.val)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · change matrixCondition Sigma.carrier.val ≤ lowerAsymptoticCoefficient Sigma
    rw [matrixCondition_eq_alternativeConditionNumber hpin hsv Sigma]
    exact (conditionNumberComparisonLb hpin hsv Sigma).2
  · exact le_rfl
  · exact Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
  · exact Filter.isBoundedUnder_of ⟨⊥, fun _ => bot_le⟩

end Papers.WassersteinRegretS2S3
