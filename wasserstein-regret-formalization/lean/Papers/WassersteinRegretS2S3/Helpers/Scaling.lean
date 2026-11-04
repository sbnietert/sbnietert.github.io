module
public import Papers.WassersteinRegretS2S3.Helpers.Stability
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Population Wasserstein regret: Helpers/Scaling

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: dilateLaw_comp
/-- [Scaling all observations in a joint law first by b and then by a gives the
same law as scaling once by their product](goal). -/
lemma dilateLaw_comp {p m : ℕ} (a b : ℝ) (P : JointLaws p m) :
    dilateLaw a (dilateLaw b P) = dilateLaw (a * b) P := by
  apply congrArg JointLaws.mk
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun z => a • z) (Measure.map (fun z => b • z) (lawMeasure P)) =
    Measure.map (fun z => (a * b) • z) (lawMeasure P)
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, smul_smul]

-- @node: dilateLaw_one
/-- [Scaling all observations in a joint law by one leaves the law unchanged](goal). -/
lemma dilateLaw_one {p m : ℕ} (P : JointLaws p m) : dilateLaw 1 P = P := by
  apply congrArg JointLaws.mk
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun z => (1 : ℝ) • z) (lawMeasure P) = lawMeasure P
  simp only [one_smul, Measure.map_id']

-- @node: coupling_dilate
/-- If [the scale factor a is nonnegative](hyp:ha), [every coupling of two joint
laws yields a coupling of their scaled laws whose root mean squared transport
cost equals a times the original coupling's cost](goal). -/
lemma coupling_dilate {p m : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (P Q : JointLaws p m) (pi : Couplings P Q) :
    ∃ gamma : Couplings (dilateLaw a P) (dilateLaw a Q),
      couplingCost gamma.val = a * couplingCost pi.val := by
  let gamma := pi.val.map
    (f := fun z : Observation p m × Observation p m => (a • z.1, a • z.2)) (by fun_prop)
  have hg : Measure.map Prod.fst (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure (dilateLaw a P) ∧
      Measure.map Prod.snd (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure (dilateLaw a Q) := by
    constructor
    · change Measure.map Prod.fst (Measure.map _ _) = Measure.map _ (lawMeasure P)
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have h := congrArg (Measure.map (fun z => a • z)) pi.property.1
      rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
      exact h
    · change Measure.map Prod.snd (Measure.map _ _) = Measure.map _ (lawMeasure Q)
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have h := congrArg (Measure.map (fun z => a • z)) pi.property.2
      rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
      exact h
  refine ⟨⟨gamma, hg⟩, ?_⟩
  unfold couplingCost
  rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
  simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

-- @node: wasserstein_dilate_le
/-- If [the scale factor a is positive](hyp:ha), [the Wasserstein distance between
two laws after scaling all observations by a is at most a times their original
Wasserstein distance](goal). -/
lemma wasserstein_dilate_le {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P Q : JointLaws p m) :
    wassersteinDistance (dilateLaw a P) (dilateLaw a Q) ≤ a * wassersteinDistance P Q := by
  apply le_of_forall_pos_lt_add
  intro delta hd
  obtain ⟨pi, hpi⟩ := wasserstein_approx_coupling P Q (delta / a) (div_pos hd ha)
  obtain ⟨gamma, hgamma⟩ := coupling_dilate a ha.le P Q pi
  calc
    wassersteinDistance (dilateLaw a P) (dilateLaw a Q) ≤ couplingCost gamma.val :=
      wasserstein_le_couplingCost _ _ gamma
    _ = a * couplingCost pi.val := hgamma
    _ < a * (wassersteinDistance P Q + delta / a) := mul_lt_mul_of_pos_left hpi ha
    _ = a * wassersteinDistance P Q + delta := by field_simp

-- @node: wasserstein_dilateLaw
/-- If [the scale factor a is positive](hyp:ha), [scaling all observations in two
joint laws by a multiplies their Wasserstein distance by a](goal). -/
lemma wasserstein_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P Q : JointLaws p m) :
    wassersteinDistance (dilateLaw a P) (dilateLaw a Q) = a * wassersteinDistance P Q := by
  apply le_antisymm (wasserstein_dilate_le a ha P Q)
  have h := wasserstein_dilate_le a⁻¹ (inv_pos.mpr ha) (dilateLaw a P) (dilateLaw a Q)
  rw [dilateLaw_comp, dilateLaw_comp, inv_mul_cancel₀ ha.ne',
    dilateLaw_one, dilateLaw_one] at h
  calc
    a * wassersteinDistance P Q ≤
        a * (a⁻¹ * wassersteinDistance (dilateLaw a P) (dilateLaw a Q)) :=
      mul_le_mul_of_nonneg_left h ha.le
    _ = wassersteinDistance (dilateLaw a P) (dilateLaw a Q) := by
      rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

-- @node: lawBall_dilateLaw_iff
/-- For [a nonnegative Wasserstein radius epsilon](hyp:eps), if [the scale factor a is positive](hyp:ha), [the scaled law Q lies in the
Wasserstein ball about the scaled law P with radius a times epsilon exactly when
Q lies in the ball about P with radius epsilon](goal). -/
lemma lawBall_dilateLaw_iff {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P Q : JointLaws p m) (eps : ℝ≥0) :
    dilateLaw a Q ∈ lawBall (dilateLaw a P) (a.toNNReal * eps) ↔ Q ∈ lawBall P eps := by
  change wassersteinDistance (dilateLaw a P) (dilateLaw a Q) ≤ _ ↔
    wassersteinDistance P Q ≤ _
  rw [wasserstein_dilateLaw a ha, NNReal.coe_mul, Real.coe_toNNReal _ ha.le]
  exact mul_le_mul_iff_right₀ ha

-- @node: lawBall_dilateLaw_surjective
/-- For [a nonnegative Wasserstein radius epsilon](hyp:eps), if [a is positive](hyp:ha) and [Q lies within Wasserstein distance a times
epsilon of the law P scaled by a](hyp:hQ), [there is a law within distance epsilon
of P whose scaling by a equals Q](goal). -/
lemma lawBall_dilateLaw_surjective {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) (Q : JointLaws p m)
    (hQ : Q ∈ lawBall (dilateLaw a P) (a.toNNReal * eps)) :
    ∃ T ∈ lawBall P eps, dilateLaw a T = Q := by
  let T := dilateLaw a⁻¹ Q
  have ht : dilateLaw a T = Q := by
    dsimp [T]
    rw [dilateLaw_comp, mul_inv_cancel₀ ha.ne', dilateLaw_one]
  refine ⟨T, ?_, ht⟩
  apply (lawBall_dilateLaw_iff a ha P T eps).mp
  rwa [ht]

-- @node: iSup_lawBall_dilateLaw
/-- For [a nonnegative Wasserstein radius epsilon](hyp:eps) and
[a function assigning an extended nonnegative real value to each joint law](hyp:f),
if [a is positive](hyp:ha), [the supremum of that function
over the ball of radius a times epsilon about scaled P equals
the supremum of that function evaluated at scaled laws from the ball of radius
epsilon about P](goal). -/
lemma iSup_lawBall_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) (f : JointLaws p m → ℝ≥0∞) :
    (⨆ Q ∈ lawBall (dilateLaw a P) (a.toNNReal * eps), f Q) =
      ⨆ Q ∈ lawBall P eps, f (dilateLaw a Q) := by
  apply le_antisymm
  · refine iSup_le fun Q => iSup_le fun hQ => ?_
    obtain ⟨T, hT, rfl⟩ := lawBall_dilateLaw_surjective a ha P eps Q hQ
    exact le_iSup_of_le T (le_iSup_of_le hT le_rfl)
  · refine iSup_le fun Q => iSup_le fun hQ => ?_
    exact le_iSup_of_le (dilateLaw a Q)
      (le_iSup_of_le ((lawBall_dilateLaw_iff a ha P Q eps).mpr hQ) le_rfl)

-- @node: secondMoment_dilateLaw
/-- [Scaling every observation in a joint law by a multiplies its uncentered
second-moment matrix by a squared](goal). -/
lemma secondMoment_dilateLaw {p m : ℕ} (a : ℝ) (P : JointLaws p m) :
    secondMoment (dilateLaw a P) = a ^ 2 • secondMoment P := by
  ext i j
  change (∫ z, z i * z j ∂Measure.map (fun z => a • z) (lawMeasure P)) =
    a ^ 2 * ∫ z, z i * z j ∂lawMeasure P
  rw [integral_map (dilation_measurable a).aemeasurable (by fun_prop)]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have he (z : Observation p m) : a * z i * (a * z j) = a ^ 2 * (z i * z j) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

-- @node: lambdaMin_smul_pos
/-- If [c is positive](hyp:hc), [multiplying a real square matrix by c multiplies
its minimum quadratic form over unit vectors by c](goal). -/
lemma lambdaMin_smul_pos {n : ℕ} [NeZero n] (A : Mat n n) (c : ℝ) (hc : 0 < c) :
    lambdaMin (c • A) = c * lambdaMin A := by
  obtain ⟨x, hx, hex⟩ := lambdaMin_attained A
  obtain ⟨y, hy, hey⟩ := lambdaMin_attained (c • A)
  apply le_antisymm
  · have h := lambdaMin_le_rayleigh (c • A) x hx
    have he : inner ℝ x (matrixCLM (c • A) x) = c * inner ℝ x (matrixCLM A x) := by
      simp [matrixCLM, map_smul, real_inner_smul_right]
    rwa [he, hex] at h
  · have h := mul_le_mul_of_nonneg_left (lambdaMin_le_rayleigh A y hy) hc.le
    have he : inner ℝ y (matrixCLM (c • A) y) = c * inner ℝ y (matrixCLM A y) := by
      simp [matrixCLM, map_smul, real_inner_smul_right]
    rw [← he, hey] at h
    exact h

-- @node: canonicalCoefficient_smul_pos
/-- If [the feature block of the joint matrix S is positive definite](hyp:hS)
and [c is positive](hyp:hc), [multiplying S by c leaves its canonical regression
coefficient matrix unchanged](goal). -/
lemma canonicalCoefficient_smul_pos {p m : ℕ} (S : Mat (p + m) (p + m))
    (hS : (blockX p m S).PosDef) (c : ℝ) (hc : 0 < c) :
    canonicalCoefficient (c • S) = canonicalCoefficient S := by
  have hx : blockX p m (c • S) = c • blockX p m S := rfl
  have hyx : blockYX p m (c • S) = c • blockYX p m S := rfl
  let := invertibleOfNonzero hc.ne'
  simp only [canonicalCoefficient, hx, hyx,
    penrose_eq_inverse_of_isUnit _ (hS.smul hc).isUnit,
    penrose_eq_inverse_of_isUnit _ hS.isUnit]
  rw [Matrix.inv_smul (blockX p m S) c ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc.ne']

-- @node: conditionSpectral_smul_pos
/-- If [the feature block of the joint matrix S is positive definite](hyp:hS)
and [c is positive](hyp:hc), [multiplying S by c leaves its spectral condition
expression unchanged](goal). -/
lemma conditionSpectral_smul_pos {p m : ℕ} [NeZero p]
    (S : Mat (p + m) (p + m)) (hS : (blockX p m S).PosDef) (c : ℝ) (hc : 0 < c) :
    conditionSpectral (c • S) = conditionSpectral S := by
  have hA := canonicalCoefficient_smul_pos S hS c hc
  have hE : matrixResidual (c • S) = c • matrixResidual S := by
    simp only [matrixResidual, hA, Matrix.mul_smul, Matrix.smul_mul]
  have hx : blockX p m (c • S) = c • blockX p m S := rfl
  unfold conditionSpectral
  rw [hA, hx, lambdaMin_smul_pos _ c hc, hE, smul_smul]
  congr 3
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

-- @node: secondMomentX_dilate_posDef_iff
/-- If [a is positive](hyp:ha), [the feature second-moment matrix of a joint law
scaled by a is positive definite exactly when the original feature second-moment
matrix is positive definite](goal). -/
lemma secondMomentX_dilate_posDef_iff {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) :
    (secondMomentX (dilateLaw a P)).PosDef ↔ (secondMomentX P).PosDef := by
  have hf (b : ℝ) (hb : 0 < b) (Q : JointLaws p m) (hQ : (secondMomentX Q).PosDef) :
      (secondMomentX (dilateLaw b Q)).PosDef := by
    change (blockX p m (secondMoment (dilateLaw b Q))).PosDef
    rw [secondMoment_dilateLaw]
    exact hQ.smul (sq_pos_of_pos hb)
  constructor
  · intro h
    have h' := hf a⁻¹ (inv_pos.mpr ha) (dilateLaw a P) h
    rwa [dilateLaw_comp, inv_mul_cancel₀ ha.ne', dilateLaw_one] at h'
  · exact hf a ha P

-- @node: conditionNumber_dilateLaw
/-- Assuming [the squared response norm equals the sum of squared coordinates](hyp:hpin)
and [singular values are nonnegative and ordered decreasingly, with the minimum
at the smaller matrix dimension](hyp:hsv), if [a is positive](hyp:ha),
[scaling every observation in a joint law by a leaves its condition number
unchanged](goal). -/
lemma conditionNumber_dilateLaw {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (a : ℝ) (ha : 0 < a) (P : JointLaws p m) :
    conditionNumber (dilateLaw a P) = conditionNumber P := by
  by_cases hP : (secondMomentX P).PosDef
  · let P' : NondegenerateLaws p m := ⟨⟨P, hP⟩⟩
    let Pa : NondegenerateLaws p m :=
      ⟨⟨dilateLaw a P, (secondMomentX_dilate_posDef_iff a ha P).mpr hP⟩⟩
    have hf (Q : NondegenerateLaws p m) :
        conditionNumber Q.carrier.val =
          ENNReal.ofReal (conditionSpectral (secondMoment Q.carrier.val)) := by
      rw [(conditionNumberFormula hpin hsv Q).2.2.2.1,
        optimalPredictor_eq_canonical, (residual_law_matrix Q).1]
      rfl
    rw [hf Pa, hf P']
    change ENNReal.ofReal (conditionSpectral (secondMoment (dilateLaw a P))) = _
    rw [secondMoment_dilateLaw, conditionSpectral_smul_pos _ hP _ (sq_pos_of_pos ha)]
  · have hPa := mt (secondMomentX_dilate_posDef_iff a ha P).mp hP
    simp only [conditionNumber, hP, hPa, if_false]

-- @node: matrixRisk_smul
/-- [For any coefficient matrix, multiplying the joint second-moment matrix by
a real scalar c multiplies the matrix expression for squared prediction risk
by c](goal). -/
lemma matrixRisk_smul {p m : ℕ} (c : ℝ) (A : Mat m p)
    (S : Mat (p + m) (p + m)) : matrixRisk A (c • S) = c * matrixRisk A S := by
  have hx : blockX p m (c • S) = c • blockX p m S := rfl
  have hxy : blockXY p m (c • S) = c • blockXY p m S := rfl
  have hy : blockY p m (c • S) = c • blockY p m S := rfl
  simp only [matrixRisk, hx, hxy, hy, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

-- @node: risk_dilateLaw
/-- [For any fixed coefficient matrix, scaling every observation in a joint law
by a multiplies squared prediction risk by a squared](goal). -/
lemma risk_dilateLaw {p m : ℕ} (a : ℝ) (P : JointLaws p m) (A : Mat m p) :
    risk A (dilateLaw a P) = a ^ 2 * risk A P := by
  rw [risk_eq_matrixRisk, secondMoment_dilateLaw, matrixRisk_smul, risk_eq_matrixRisk]

-- @node: optimal_risk_dilateLaw
/-- [The infimum of squared prediction risk over all coefficient matrices under
the law scaled by a equals a squared times the risk of the canonical regression
coefficient under the original law](goal). -/
lemma optimal_risk_dilateLaw {p m : ℕ} (a : ℝ) (P : JointLaws p m) :
    (⨅ A : Mat m p, risk A (dilateLaw a P)) =
      a ^ 2 * risk (canonicalCoefficient (secondMoment P)) P := by
  have hmin (A : Mat m p) : a ^ 2 * risk (canonicalCoefficient (secondMoment P)) P ≤
      risk A (dilateLaw a P) := by
    rw [risk_dilateLaw]
    exact mul_le_mul_of_nonneg_left (canonical_risk_minimal P A) (sq_nonneg a)
  apply le_antisymm
  · exact (ciInf_le ⟨_, by rintro _ ⟨A, rfl⟩; exact hmin A⟩
      (canonicalCoefficient (secondMoment P))).trans (by rw [risk_dilateLaw])
  · exact le_ciInf hmin

-- @node: regret_dilateLaw
/-- [For any fixed coefficient matrix, scaling every observation in a joint law
by a multiplies excess squared prediction risk above the optimal linear risk
by a squared](goal). -/
lemma regret_dilateLaw {p m : ℕ} (a : ℝ) (P : JointLaws p m) (A : Mat m p) :
    regret A (dilateLaw a P) = a ^ 2 * regret A P := by
  have hz := canonical_regret_zero P
  unfold regret at hz ⊢
  rw [risk_dilateLaw, optimal_risk_dilateLaw]
  rw [show (⨅ B : Mat m p, risk B P) =
    risk (canonicalCoefficient (secondMoment P)) P by linarith]
  ring

-- @node: population_erm_dilateLaw
/-- For [a nonnegative radius argument epsilon for the original law](hyp:eps) and
[a nonnegative radius argument delta for the scaled law](hyp:delta), if [a is nonzero](hyp:ha), [the set of population risk minimizers for the
law scaled by a is the same as for the original law, regardless of the two
nonnegative radius arguments](goal). -/
lemma population_erm_dilateLaw {p m : ℕ} (a : ℝ) (ha : a ≠ 0)
    (P : JointLaws p m) (eps delta : ℝ≥0) :
    populationMinimizers 0 (dilateLaw a P) delta = populationMinimizers 0 P eps := by
  have hp : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  ext A
  constructor
  · intro hA
    apply (population_erm_iff_risk_eq_canonical P eps A).mpr
    have hb := hA (Set.mem_univ (canonicalCoefficient (secondMoment P)))
    change ENNReal.ofReal (risk A (dilateLaw a P)) ≤
      ENNReal.ofReal (risk (canonicalCoefficient (secondMoment P)) (dilateLaw a P)) at hb
    have hr := (ENNReal.ofReal_le_ofReal_iff (risk_nonneg _ _)).mp hb
    rw [risk_dilateLaw, risk_dilateLaw] at hr
    exact le_antisymm ((mul_le_mul_iff_right₀ hp).mp hr) (canonical_risk_minimal P A)
  · intro hA B hB
    change ENNReal.ofReal (risk A (dilateLaw a P)) ≤
      ENNReal.ofReal (risk B (dilateLaw a P))
    apply ENNReal.ofReal_le_ofReal
    rw [risk_dilateLaw, risk_dilateLaw,
      (population_erm_iff_risk_eq_canonical P eps A).mp hA]
    exact mul_le_mul_of_nonneg_left (canonical_risk_minimal P B) hp.le

-- @node: robustRegret_dilateLaw
/-- For [a nonnegative Wasserstein radius epsilon](hyp:eps), if [a is positive](hyp:ha), [an estimator's robust regret about scaled P at
radius a times epsilon equals a squared times the robust regret about P at
radius epsilon of the rule that first scales its input law by a and then applies
that estimator](goal). -/
lemma robustRegret_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) (rule : Estimator p m) :
    robustRegret rule (dilateLaw a P) (a.toNNReal * eps) =
      ENNReal.ofReal (a ^ 2) * robustRegret (fun Q => rule (dilateLaw a Q)) P eps := by
  unfold robustRegret
  rw [iSup_lawBall_dilateLaw a ha]
  simp_rw [regret_dilateLaw, ENNReal.ofReal_mul (sq_nonneg a),
    ENNReal.mul_iSup, mul_max]

-- @node: estimator_dilate_surjective
/-- If [a is positive](hyp:ha), [every law-to-coefficient estimator can be
represented by first scaling its input law by a and then applying another
law-to-coefficient estimator](goal). -/
lemma estimator_dilate_surjective {p m : ℕ} (a : ℝ) (ha : 0 < a) :
    Function.Surjective (fun rule : Estimator p m => fun Q => rule (dilateLaw a Q)) := by
  intro rule
  refine ⟨fun Q => rule (dilateLaw a⁻¹ Q), ?_⟩
  funext Q
  change rule (dilateLaw a⁻¹ (dilateLaw a Q)) = rule Q
  rw [dilateLaw_comp, inv_mul_cancel₀ ha.ne', dilateLaw_one]

-- @node: localMinimax_dilateLaw
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [a is positive](hyp:ha), [scaling the reference law by a and the
Wasserstein radius by a multiplies local minimax regret by a squared](goal). -/
lemma localMinimax_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) :
    localMinimax (dilateLaw a P) (a.toNNReal * eps) =
      ENNReal.ofReal (a ^ 2) * localMinimax P eps := by
  unfold localMinimax
  simp_rw [robustRegret_dilateLaw a ha]
  rw [← ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ha)).ne' ENNReal.ofReal_ne_top]
  congr 1
  exact (estimator_dilate_surjective (p := p) (m := m) a ha).iInf_comp
    (fun rule => robustRegret rule P eps)

-- @node: population_dro_objective_dilateLaw
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [a is positive](hyp:ha), [scaling the reference law and Wasserstein
radius by a multiplies the worst squared prediction risk of a fixed coefficient
matrix over that ball by a squared](goal). -/
lemma population_dro_objective_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) (A : Mat m p) :
    populationObjective 1 (dilateLaw a P) (a.toNNReal * eps) A =
      ENNReal.ofReal (a ^ 2) * populationObjective 1 P eps A := by
  simp only [populationObjective, show (1 : Fin 4) ≠ 0 by decide, if_false, if_true]
  rw [iSup_lawBall_dilateLaw a ha]
  simp_rw [risk_dilateLaw, ENNReal.ofReal_mul (sq_nonneg a), ENNReal.mul_iSup]

-- @node: population_dro_dilateLaw
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [a is positive](hyp:ha), [scaling the reference law and Wasserstein
radius by a leaves the set of coefficient matrices minimizing worst squared
prediction risk over the ball unchanged](goal). -/
lemma population_dro_dilateLaw {p m : ℕ} (a : ℝ) (ha : 0 < a)
    (P : JointLaws p m) (eps : ℝ≥0) :
    populationMinimizers 1 (dilateLaw a P) (a.toNNReal * eps) =
      populationMinimizers 1 P eps := by
  have hz : ENNReal.ofReal (a ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ha)).ne'
  ext A
  change (∀ B ∈ Set.univ, populationObjective 1 (dilateLaw a P) (a.toNNReal * eps) A ≤
    populationObjective 1 (dilateLaw a P) (a.toNNReal * eps) B) ↔
    (∀ B ∈ Set.univ, populationObjective 1 P eps A ≤ populationObjective 1 P eps B)
  simp_rw [population_dro_objective_dilateLaw a ha]
  exact forall_congr' fun B => imp_congr_right fun _ =>
    ENNReal.mul_le_mul_iff_right hz ENNReal.ofReal_ne_top

-- @node: lem:rescaling-invariance
/-- Assuming [the squared response norm equals the sum of squared coordinates](hyp:hpin)
and [singular values are nonnegative and ordered decreasingly, with the minimum
at the smaller matrix dimension](hyp:hsv), let [a be positive](hyp:ha).
[Scaling both joint laws by a multiplies their Wasserstein distance by a and,
for the fixed coefficient matrix, risk and regret by a squared; it preserves
the reference law's condition number and, for every nonnegative radius, scaling
that radius by a multiplies local minimax regret by a squared and preserves
the population minimizers of worst risk over the Wasserstein ball](goal). -/
lemma rescalingInvariance {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P Q : JointLaws p m)
    (A : Mat m p) (a : ℝ) (ha : 0 < a) :
    wassersteinDistance (dilateLaw a P) (dilateLaw a Q) = a * wassersteinDistance P Q ∧
    risk A (dilateLaw a P) = a ^ 2 * risk A P ∧
    regret A (dilateLaw a P) = a ^ 2 * regret A P ∧
    conditionNumber (dilateLaw a P) = conditionNumber P ∧
    (∀ eps : ℝ≥0,
      localMinimax (dilateLaw a P) (a.toNNReal * eps) = ENNReal.ofReal (a ^ 2) * localMinimax P
        eps ∧
      populationMinimizers 1 (dilateLaw a P) (a.toNNReal * eps) = populationMinimizers 1 P eps)
        := by
  exact ⟨wasserstein_dilateLaw a ha P Q, risk_dilateLaw a P A, regret_dilateLaw a P A,
    conditionNumber_dilateLaw hpin hsv a ha P, fun eps =>
      ⟨localMinimax_dilateLaw a ha P eps, population_dro_dilateLaw a ha P eps⟩⟩
-- @realizes \lambda(positive dilation factor)

end Papers.WassersteinRegretS2S3
