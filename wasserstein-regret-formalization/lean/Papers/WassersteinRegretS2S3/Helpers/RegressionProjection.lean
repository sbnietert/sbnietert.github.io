module
public import Papers.WassersteinRegretS2S3.Basic
public import Papers.WassersteinRegretS2S3.Helpers.Pseudoinverse
public import Papers.WassersteinRegretS2S3.Helpers.MatrixNorms
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentGeometry

/-!
# Population Wasserstein regret: Helpers/RegressionProjection

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: pin1_proved
/-- In [dimension m](hyp:m), [the squared Euclidean norm of every vector equals
the sum of the squares of its coordinates](goal). -/
lemma pin1_proved (m : ℕ) : assPin1 m := by
  intro v
  simpa only [pow_two] using EuclideanSpace.real_norm_sq_eq v

-- @node: factor_gram_blocks
/-- For [a joint factor matrix S](hyp:S), [the feature, response–feature,
feature–response, and response blocks of its Gram matrix are respectively the
products of the feature rows with their transpose, the response rows with the
feature-row transpose, the feature rows with the response-row transpose, and
the response rows with their transpose](goal). -/
lemma factor_gram_blocks {p m r : ℕ} (S : Mat (p + m) r) :
    blockX p m (S * S.transpose) = (factorBlocks p m S).1 * (factorBlocks p m S).1.transpose ∧
    blockYX p m (S * S.transpose) = (factorBlocks p m S).2 * (factorBlocks p m S).1.transpose ∧
    blockXY p m (S * S.transpose) = (factorBlocks p m S).1 * (factorBlocks p m S).2.transpose ∧
    blockY p m (S * S.transpose) = (factorBlocks p m S).2 * (factorBlocks p m S).2.transpose := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> rfl

-- @node: frob_sq_trace_rows
/-- For [a rectangular matrix M](hyp:M), [its squared Frobenius norm equals
the trace of M multiplied by its transpose](goal). -/
lemma frob_sq_trace_rows {a b : ℕ} (M : Mat a b) :
    frob M ^ 2 = Matrix.trace (M * M.transpose) := by
  rw [frob_sq_trace, Matrix.trace_mul_comm]

-- @node: matrixRisk_gram_factor
/-- For [a joint factor matrix S](hyp:S) and [a predictor matrix A](hyp:A),
[risk evaluated at the Gram matrix of S equals the squared Frobenius norm of
A times the feature rows of S minus its response rows](goal). -/
lemma matrixRisk_gram_factor {p m r : ℕ} (S : Mat (p + m) r) (A : Mat m p) :
    matrixRisk A (S * S.transpose) =
      frob (A * (factorBlocks p m S).1 - (factorBlocks p m S).2) ^ 2 := by
  obtain ⟨hX, hYX, hXY, hY⟩ := factor_gram_blocks S
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  have hquad : Matrix.trace (A.transpose * A * (X * X.transpose)) =
      Matrix.trace ((A * X) * (A * X).transpose) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm A.transpose]
    simp only [Matrix.mul_assoc]
  have hcross : Matrix.trace (Y * (A * X).transpose) =
      Matrix.trace (A * (X * Y.transpose)) := by
    rw [← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [matrixRisk, hX, hXY, hY]
  change Matrix.trace (A.transpose * A * (X * X.transpose)) -
    2 * Matrix.trace (A * (X * Y.transpose)) + Matrix.trace (Y * Y.transpose) =
      frob (A * X - Y) ^ 2
  rw [hquad, frob_sq_trace_rows]
  simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  rw [hcross]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  ring

-- @node: quadraticRegressionMatrix_factor
/-- For [a predictor matrix A](hyp:A) and [a joint factor matrix S](hyp:S),
[multiplying S by the regression residual matrix gives A times the feature
rows of S minus its response rows](goal). -/
lemma quadraticRegressionMatrix_factor {p m r : ℕ} (A : Mat m p) (S : Mat (p + m) r) :
    quadraticRegressionMatrix A * S = A * (factorBlocks p m S).1 - (factorBlocks p m S).2 := by
  ext i j
  simp [Matrix.mul_apply, quadraticRegressionMatrix, Fin.sum_univ_add,
    factorBlocks, Matrix.sub_apply, Matrix.one_apply, sub_eq_add_neg]

-- @node: lem:regret-projection-formula
/-- Assuming [the Euclidean squared-norm identity](hyp:hpin) and
[nonincreasing, nonnegative singular values with the specified minimum-value
convention](hyp:hsv), let [Sigma be a positive semidefinite joint second-moment
matrix](hyp:Sigma) and [S be a rectangular factor](hyp:S) such that
[Sigma is S times its transpose](hyp:hfactor). [The canonical coefficient is
both the response–feature moment times the feature-moment pseudoinverse and
the response factor times the feature-factor pseudoinverse; its residual
factor is the response factor projected off the feature row space, is
orthogonal to the feature rows and their row projector, and has Gram matrix
equal to the residual second moment; for every predictor, risk is the squared
Frobenius norm of its factor residual, while regret is both the squared norm
of the row-projected residual and the squared norm of the coefficient error
times the feature factor](goal). -/
lemma regretProjectionFormula {p m r : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (Sigma : PSD (p + m))
    (S : Mat (p + m) r) -- @realizes \bS(arbitrary width real Gram factor)
    (hfactor : assRegretProjectionFormulaFactor Sigma S) :
    let SX := (factorBlocks p m S).1 -- @realizes \bS_X(feature rows with width r)
    let SY := (factorBlocks p m S).2 -- @realizes \bS_Y(response rows with width r)
    let PiX := rowProjector SX -- @realizes \bPi_X(factor row projector)
    let E := SY - canonicalCoefficient Sigma.val * SX -- @realizes \bE(optimal residual factor)
    canonicalCoefficient Sigma.val = blockYX p m Sigma.val * moorePenroseInverse (blockX p m
      Sigma.val) ∧
    canonicalCoefficient Sigma.val = SY * moorePenroseInverse SX ∧
    E = SY * (1 - PiX) ∧ E * SX.transpose = 0 ∧ E * PiX = 0 ∧
    E * E.transpose = matrixResidual Sigma.val ∧
    (∀ A : Mat m p, matrixRisk A Sigma.val = frob (A * SX - SY) ^ 2 ∧
      matrixRegret A Sigma.val = frob ((SY - A * SX) * PiX) ^ 2 ∧
      matrixRegret A Sigma.val = frob ((A - canonicalCoefficient Sigma.val) * SX) ^ 2) := by
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  let P := rowProjector X
  let C := canonicalCoefficient Sigma.val
  have hf : Sigma.val = S * S.transpose := hfactor
  obtain ⟨hX, hYX, hXY, hY⟩ := factor_gram_blocks S
  have hC : C = Y * moorePenroseInverse X := by
    dsimp [C, canonicalCoefficient]
    rw [hf, hYX, hX, Matrix.mul_assoc, ← penrose_transpose_gram_formula]
  have hCP : C * X = Y * P := by rw [hC, Matrix.mul_assoc]; rfl
  have hXP : X * P = X := by
    simpa only [P, rowProjector, Matrix.mul_assoc] using (moorePenroseInverse_spec X).1
  have hPt : P.transpose = P := (penrose_projectors X).1.1
  have hPP : P * P = P := (penrose_projectors X).1.2
  have hPXt : P * X.transpose = X.transpose := by
    simpa only [Matrix.transpose_mul, hPt] using congrArg Matrix.transpose hXP
  have hE : Y - C * X = Y * (1 - P) := by
    rw [hCP, Matrix.mul_sub, Matrix.mul_one]
  have hEP : (Y - C * X) * P = 0 := by
    rw [hE, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self,
      Matrix.mul_zero]
  have hEX : (Y - C * X) * X.transpose = 0 := by
    rw [hE, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPXt, sub_self,
      Matrix.mul_zero]
  have hres : (Y - C * X) * (Y - C * X).transpose = matrixResidual Sigma.val := by
    unfold matrixResidual
    rw [hf]
    rw [← Matrix.mul_assoc, quadraticRegressionMatrix_factor]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, quadraticRegressionMatrix_factor, ← hf]
    change (Y - C * X) * (Y - C * X).transpose =
      (C * X - Y) * (C * X - Y).transpose
    rw [show C * X - Y = -(Y - C * X) by abel]
    simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine ⟨rfl, hC, hE, hEX, hEP, hres, ?_⟩
  intro A
  have hrisk (B : Mat m p) : matrixRisk B Sigma.val = frob (B * X - Y) ^ 2 := by
    rw [hf]
    exact matrixRisk_gram_factor S B
  have hproj : (A * X - Y) * P = (A - C) * X := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hXP, Matrix.sub_mul, hCP]
  have hcomp (B : Mat m p) : (B * X - Y) * (1 - P) = -(Y - C * X) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hXP,
      sub_self, Matrix.mul_zero, zero_sub, ← hE]
  have hcanon : (C * X - Y) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hXP, hCP, sub_self]
  have hp := frob_projection_pythagoras (A * X - Y) P ⟨hPt, hPP⟩
  have hc := frob_projection_pythagoras (C * X - Y) P ⟨hPt, hPP⟩
  rw [hcomp] at hp
  rw [hcomp, hcanon] at hc
  have hz : frob (0 : Mat m r) = 0 := by simp [frob]
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_add] at hc
  have hreg : matrixRegret A Sigma.val = frob ((A * X - Y) * P) ^ 2 := by
    rw [matrixRegret, hrisk A, hrisk C, hp, hc]
    ring
  refine ⟨hrisk A, ?_, hreg.trans (congrArg (fun M => frob M ^ 2) hproj)⟩
  rw [hreg, show (Y - A * X) * P = -((A * X - Y) * P) by
    rw [← Matrix.neg_mul]; congr 1; abel]
  rw [frob_sq, frob_sq]
  simp only [Matrix.neg_apply, neg_sq]

-- @node: quadraticRegressionMatrix_apply
/-- For [a predictor matrix A](hyp:A) and [an observation z](hyp:z),
[applying the regression residual matrix to z gives the predicted response
minus the observed response](goal). -/
lemma quadraticRegressionMatrix_apply {p m : ℕ} (A : Mat m p) (z : Observation p m) :
    matrixCLM (quadraticRegressionMatrix A) z =
      matrixCLM A (feature z) - response z := by
  ext i
  simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
    quadraticRegressionMatrix, Fin.sum_univ_add, feature, response,
    Matrix.one_apply, sub_eq_add_neg]

-- @node: psd_sqrt_factor
/-- For [a positive semidefinite matrix S](hyp:S), [S equals its positive
semidefinite square root multiplied by the transpose of that square root](goal). -/
lemma psd_sqrt_factor {n : ℕ} (S : PSD n) :
    S.val = CFC.sqrt S.val * (CFC.sqrt S.val).transpose := by
  have ht : (CFC.sqrt S.val).transpose = CFC.sqrt S.val :=
    (CFC.sqrt_nonneg S.val).posSemidef.isHermitian.eq
  rw [ht, CFC.sqrt_mul_sqrt_self S.val S.property.nonneg]

-- @node: risk_eq_matrixRisk
/-- For [a joint law P with finite second moments](hyp:P) and [a predictor
matrix A](hyp:A), [population squared-error risk equals matrix risk evaluated
at the joint second-moment matrix of P](goal). -/
lemma risk_eq_matrixRisk {p m : ℕ} (P : JointLaws p m) (A : Mat m p) :
    risk A P = matrixRisk A (secondMoment P) := by
  let S := CFC.sqrt (secondMoment P)
  have hf : secondMoment P = S * S.transpose := psd_sqrt_factor (momentPSD P)
  have hi := integral_norm_sq_linear (lawMeasure P) id P.carrier.property
    (quadraticRegressionMatrix A)
  simp only [id_eq, quadraticRegressionMatrix_apply] at hi
  change risk A P = Matrix.trace (quadraticRegressionMatrix A * secondMoment P *
    (quadraticRegressionMatrix A).transpose) at hi
  rw [hi, hf, matrixRisk_gram_factor]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ S.transpose,
    ← Matrix.transpose_mul, ← frob_sq_trace_rows, quadraticRegressionMatrix_factor]

-- @node: law_matrix_risk_regret
/-- For [a joint law P with finite second moments](hyp:P) and [a predictor
matrix A](hyp:A), [population risk and regret equal their matrix counterparts
evaluated at the joint second-moment matrix of P](goal). -/
lemma law_matrix_risk_regret {p m : ℕ} (P : JointLaws p m) (A : Mat m p) :
    risk A P = matrixRisk A (secondMoment P) ∧ regret A P = matrixRegret A (secondMoment P) := by
  refine ⟨risk_eq_matrixRisk P A, ?_⟩
  by_cases hp : p = 0
  · subst p
    have he : ∀ B : Mat m 0, B = A := fun _ => Subsingleton.elim _ _
    simp [regret, matrixRegret, he, risk_eq_matrixRisk]
  by_cases hm : m = 0
  · subst m
    have he : ∀ B : Mat 0 p, B = A := fun _ => Subsingleton.elim _ _
    simp [regret, matrixRegret, he, risk_eq_matrixRisk]
  letI : NeZero p := ⟨hp⟩
  letI : NeZero m := ⟨hm⟩
  have hf := psd_sqrt_factor (momentPSD P)
  have hg := (regretProjectionFormula (assPin1_valid m) assSingularValueConvention_valid
    (momentPSD P) (CFC.sqrt (secondMoment P)) hf).2.2.2.2.2.2
  dsimp only [momentPSD] at hg
  have hmin (B : Mat m p) :
      risk (canonicalCoefficient (secondMoment P)) P ≤ risk B P := by
    have hn := sq_nonneg (frob ((B - canonicalCoefficient (secondMoment P)) *
      (factorBlocks p m (CFC.sqrt (secondMoment P))).1))
    rw [← (hg B).2.2] at hn
    simpa only [matrixRegret, ← risk_eq_matrixRisk] using sub_nonneg.mp hn
  have hinf : (⨅ B : Mat m p, risk B P) = risk (canonicalCoefficient (secondMoment P)) P := by
    apply le_antisymm
    · exact ciInf_le ⟨_, by rintro _ ⟨B, rfl⟩; exact hmin B⟩ _
    · exact le_ciInf hmin
  rw [regret, hinf, risk_eq_matrixRisk, risk_eq_matrixRisk]
  rfl

-- @node: regret_nonneg
/-- For [a joint law P](hyp:P) and [a predictor matrix A](hyp:A),
[regret is nonnegative](goal). -/
lemma regret_nonneg {p m : ℕ} (P : JointLaws p m) (A : Mat m p) : 0 ≤ regret A P := by
  have hb : BddBelow (Set.range (fun B : Mat m p => risk B P)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact integral_nonneg (fun _ => sq_nonneg _)
  exact sub_nonneg.mpr (ciInf_le hb A)
-- @node: canonical_regret_zero
/-- For [a joint law P](hyp:P), [the canonical coefficient formed from its
second-moment matrix has zero regret under P](goal). -/
lemma canonical_regret_zero {p m : ℕ} (P : JointLaws p m) :
    regret (canonicalCoefficient (secondMoment P)) P = 0 := by
  rw [(law_matrix_risk_regret P _).2, matrixRegret, sub_self]

-- @node: canonical_risk_minimal
/-- For [a joint law P](hyp:P) and [any predictor matrix A](hyp:A),
[the canonical coefficient formed from the second moments of P has risk no
greater than that of A](goal). -/
lemma canonical_risk_minimal {p m : ℕ} (P : JointLaws p m) (A : Mat m p) :
    risk (canonicalCoefficient (secondMoment P)) P ≤ risk A P := by
  have hz := canonical_regret_zero P
  have hn := regret_nonneg P A
  unfold regret at hz hn
  linarith

-- @node: canonical_mem_population_erm
/-- For [a joint law P](hyp:P) and [any nonnegative radius](hyp:eps),
[the canonical coefficient formed from its second moments is a population
minimizer of ordinary risk](goal). -/
lemma canonical_mem_population_erm {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) :
    canonicalCoefficient (secondMoment P) ∈ populationMinimizers 0 P eps := by
  intro A hA
  change populationObjective 0 P eps (canonicalCoefficient (secondMoment P)) ≤
    populationObjective 0 P eps A
  simpa only [populationObjective, ite_true] using
    ENNReal.ofReal_le_ofReal (canonical_risk_minimal P A)

-- @node: population_erm_iff_risk_eq_canonical
/-- For [a joint law P](hyp:P), [a nonnegative radius](hyp:eps), and
[a predictor matrix A](hyp:A), [A minimizes ordinary population risk if and
only if its risk equals that of the canonical coefficient](goal). -/
lemma population_erm_iff_risk_eq_canonical {p m : ℕ} (P : JointLaws p m)
    (eps : ℝ≥0) (A : Mat m p) :
    A ∈ populationMinimizers 0 P eps ↔
      risk A P = risk (canonicalCoefficient (secondMoment P)) P := by
  constructor
  · intro hA
    have h := hA (Set.mem_univ (canonicalCoefficient (secondMoment P)))
    change populationObjective 0 P eps A ≤
      populationObjective 0 P eps (canonicalCoefficient (secondMoment P)) at h
    simp only [populationObjective, ite_true] at h
    have hn : 0 ≤ risk (canonicalCoefficient (secondMoment P)) P :=
      integral_nonneg (fun _ => sq_nonneg _)
    exact le_antisymm ((ENNReal.ofReal_le_ofReal_iff hn).mp h)
      (canonical_risk_minimal P A)
  · intro he B hB
    change populationObjective 0 P eps A ≤ populationObjective 0 P eps B
    simp only [populationObjective, ite_true]
    rw [he]
    exact ENNReal.ofReal_le_ofReal (canonical_risk_minimal P B)

-- @node: population_erm_regret_zero
/-- For [a joint law P](hyp:P), [a nonnegative radius](hyp:eps), and
[a predictor matrix A](hyp:A), if [A minimizes ordinary population risk](hyp:hA),
then [A has zero regret under P](goal). -/
lemma population_erm_regret_zero {p m : ℕ} (P : JointLaws p m)
    (eps : ℝ≥0) (A : Mat m p) (hA : A ∈ populationMinimizers 0 P eps) :
    regret A P = 0 := by
  have he := (population_erm_iff_risk_eq_canonical P eps A).mp hA
  unfold regret
  rw [he]
  exact canonical_regret_zero P

-- @node: secondMoment_eq_of_mem_lawBall_zero
/-- For [joint laws P and Q](hyp:P,Q) with positive feature and response
dimensions, if [Q belongs to the radius-zero Wasserstein ball about P](hyp:hQ),
then [their joint second-moment matrices agree](goal). -/
lemma secondMoment_eq_of_mem_lawBall_zero {p m : ℕ} [NeZero p] [NeZero m]
    (P Q : JointLaws p m) (hQ : Q ∈ lawBall P 0) : secondMoment Q = secondMoment P := by
  have hi := w2BuresEquivalence assSingularValueConvention_valid P 0
  have hm := Set.mem_image_of_mem secondMoment hQ
  rw [hi.1, hi.2] at hm
  obtain ⟨D, hD, he⟩ := hm
  have hn : frob D = ‖D‖ := by
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have hz : D = 0 := norm_le_zero_iff.mp (by simpa only [hn, NNReal.coe_zero] using hD)
  simp only [hz, add_zero] at he
  exact he.trans (psd_sqrt_factor (momentPSD P)).symm

-- @node: lawBall_zero_moment_sup
/-- For [a joint law P](hyp:P) with positive feature and response dimensions
and [a nonnegative, possibly infinite function of a joint second-moment
matrix](hyp:f), [the supremum of that function over the radius-zero Wasserstein
ball about P equals its value at the second moments of P](goal). -/
lemma lawBall_zero_moment_sup {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (f : Mat (p + m) (p + m) → ℝ≥0∞) :
    (⨆ Q ∈ lawBall P 0, f (secondMoment Q)) = f (secondMoment P) := by
  apply le_antisymm
  · refine iSup_le fun Q => iSup_le fun hQ => ?_
    rw [secondMoment_eq_of_mem_lawBall_zero P Q hQ]
  · exact le_iSup_of_le P (le_iSup_of_le (by simp [lawBall, wasserstein_self]) le_rfl)

-- @node: populationObjective_zero
/-- For [an objective index from zero to three](hyp:o), [a joint law P](hyp:P)
with positive feature and response dimensions, and [a predictor matrix A](hyp:A),
[the radius-zero population objective equals regret when the index is two
and risk otherwise, viewed as a nonnegative extended real number](goal). -/
lemma populationObjective_zero {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) (A : Mat m p) :
    populationObjective o P 0 A =
      if o = 2 then ENNReal.ofReal (regret A P) else ENNReal.ofReal (risk A P) := by
  unfold populationObjective
  split_ifs with h0 h2 h1 h2 h2
  · subst o
    norm_num [Fin.ext_iff] at h2
  · rfl
  · subst o
    norm_num [Fin.ext_iff] at h2
  · simp_rw [risk_eq_matrixRisk]
    exact lawBall_zero_moment_sup P (fun S => ENNReal.ofReal (matrixRisk A S))
  · simp_rw [fun Q => (law_matrix_risk_regret Q A).2]
    exact lawBall_zero_moment_sup P (fun S => ENNReal.ofReal (matrixRegret A S))
  · simp

-- @node: canonical_mem_population_zero
/-- For [any of the four population objectives](hyp:o) and [a joint law P](hyp:P)
with positive feature and response dimensions, [the canonical coefficient
formed from its second moments minimizes that objective at radius zero](goal). -/
lemma canonical_mem_population_zero {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) :
    canonicalCoefficient (secondMoment P) ∈ populationMinimizers o P 0 := by
  intro A hA
  change populationObjective o P 0 _ ≤ populationObjective o P 0 A
  rw [populationObjective_zero, populationObjective_zero]
  split_ifs
  · rw [canonical_regret_zero, ENNReal.ofReal_zero]
    exact bot_le
  · exact ENNReal.ofReal_le_ofReal (canonical_risk_minimal P A)

-- @node: population_zero_regret_zero
/-- For [a population objective index](hyp:o), [a joint law P](hyp:P) with
positive feature and response dimensions, and [a predictor matrix A](hyp:A),
if [A minimizes that objective at radius zero](hyp:hA), then
[A has zero regret under P](goal). -/
lemma population_zero_regret_zero {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) (A : Mat m p)
    (hA : A ∈ populationMinimizers o P 0) : regret A P = 0 := by
  have h := hA (Set.mem_univ (canonicalCoefficient (secondMoment P)))
  change populationObjective o P 0 A ≤ populationObjective o P 0 _ at h
  rw [populationObjective_zero, populationObjective_zero] at h
  split_ifs at h
  · rw [canonical_regret_zero, ENNReal.ofReal_zero] at h
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le))
      (regret_nonneg P A)
  · have hn : 0 ≤ risk (canonicalCoefficient (secondMoment P)) P :=
      integral_nonneg (fun _ => sq_nonneg _)
    have he := le_antisymm ((ENNReal.ofReal_le_ofReal_iff hn).mp h)
      (canonical_risk_minimal P A)
    exact population_erm_regret_zero P 0 A
      ((population_erm_iff_risk_eq_canonical P 0 A).mpr he)

-- @node: population_minimizers_zero_eq_erm
/-- For [any of the four population objectives](hyp:o) and [a joint law P](hyp:P)
with positive feature and response dimensions, [the radius-zero minimizer set
equals the set of ordinary population risk minimizers at radius zero](goal). -/
lemma population_minimizers_zero_eq_erm {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) :
    populationMinimizers o P 0 = populationMinimizers 0 P 0 := by
  ext A
  constructor
  · intro hA
    apply (population_erm_iff_risk_eq_canonical P 0 A).mpr
    have h := population_zero_regret_zero o P A hA
    have hc := canonical_regret_zero P
    unfold regret at h hc
    linarith
  · intro hA B hB
    change populationObjective o P 0 A ≤ populationObjective o P 0 B
    rw [populationObjective_zero, populationObjective_zero]
    split_ifs
    · rw [population_erm_regret_zero P 0 A hA, ENNReal.ofReal_zero]
      exact bot_le
    · rw [(population_erm_iff_risk_eq_canonical P 0 A).mp hA]
      exact ENNReal.ofReal_le_ofReal (canonical_risk_minimal P B)

-- @node: localMinimax_coefficient_formula
/-- For [a joint law P](hyp:P) with positive feature and response dimensions
and [a nonnegative radius](hyp:eps), [local minimax regret equals the infimum
over fixed coefficient matrices of their worst regret over the Wasserstein
ball about P](goal). -/
lemma localMinimax_coefficient_formula {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) :
    localMinimax P eps = ⨅ A : Mat m p, ⨆ Q ∈ lawBall P eps, ENNReal.ofReal (regret A Q) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro A
    let rule : Estimator p m := fun Q =>
      if Q = P then A else canonicalCoefficient (secondMoment P)
    have hself : rule P = A := if_pos rfl
    apply iInf_le_of_le rule
    apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    apply max_le
    · rw [hself]
      exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
    · by_cases he : Q = P
      · subst Q
        rw [hself]
        exact le_iSup_of_le P (le_iSup_of_le hQ le_rfl)
      · simp only [rule, if_neg he, canonical_regret_zero, ENNReal.ofReal_zero]
        exact bot_le
  · apply le_iInf
    intro rule
    apply iInf_le_of_le (rule P)
    apply iSup_mono
    intro Q
    apply iSup_mono
    intro hQ
    exact le_max_left _ _

-- @node: law_matrix_sup
/-- For [a joint law P](hyp:P) with positive feature and response dimensions,
[a nonnegative radius](hyp:eps), and [a nonnegative, possibly infinite function
of a joint second-moment matrix](hyp:f), [the supremum over second moments of
laws in the Wasserstein ball equals the supremum over the corresponding Bures
ball of positive semidefinite matrices](goal). -/
lemma law_matrix_sup {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) (f : Mat (p + m) (p + m) → ℝ≥0∞) :
    (⨆ Q ∈ lawBall P eps, f (secondMoment Q)) =
      ⨆ T ∈ matrixBall (momentPSD P) eps, f T.val := by
  have himage := (w2BuresEquivalence assSingularValueConvention_valid P eps).1
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    have hmem := himage ▸ (Set.mem_image_of_mem secondMoment hQ)
    exact le_iSup_of_le (momentPSD Q) (le_iSup_of_le hmem.2 le_rfl)
  · apply iSup_le
    intro T
    apply iSup_le
    intro hT
    have hmem : T.val ∈ secondMoment '' lawBall P eps := by
      rw [himage]
      exact ⟨T.property, hT⟩
    obtain ⟨Q, hQ, he⟩ := hmem
    rw [← he]
    exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)

-- @node: law_matrix_estimators
/-- Assuming [nonincreasing, nonnegative singular values with the specified
minimum-value convention](hyp:hsv), for [a joint law P](hyp:P) with positive
feature and response dimensions, [a nonnegative radius](hyp:eps), and
[one of the four objective indices](hyp:o), [the population minimizer set
equals the matrix minimizer set centered at the second moments of P](goal). -/
lemma law_matrix_estimators {p m : ℕ} [NeZero p] [NeZero m]
    (hsv : assSingularValueConvention) (P : JointLaws p m) (eps : ℝ≥0) (o : Fin 4) :
    populationMinimizers o P eps = matrixMinimizers o (momentPSD P) eps := by
  have he : populationObjective o P eps = matrixObjective o (momentPSD P) eps := by
    funext A
    unfold populationObjective matrixObjective matrixWorstRegret
    simp only [(law_matrix_risk_regret P A).1, momentPSD]
    split_ifs
    · rfl
    · simp_rw [risk_eq_matrixRisk]
      exact law_matrix_sup P eps (fun S => ENNReal.ofReal (matrixRisk A S))
    · simp_rw [fun Q => (law_matrix_risk_regret Q A).2]
      exact law_matrix_sup P eps (fun S => ENNReal.ofReal (matrixRegret A S))
    · rfl
  simp only [populationMinimizers, matrixMinimizers, he]

-- @node: risk_nonneg
/-- For [a joint law P](hyp:P) and [a predictor matrix A](hyp:A),
[population squared-error risk is nonnegative](goal). -/
lemma risk_nonneg {p m : ℕ} (P : JointLaws p m) (A : Mat m p) : 0 ≤ risk A P := by
  exact integral_nonneg (fun _ => sq_nonneg _)
-- @node: penrose_eq_inverse_of_isUnit
/-- For [a square matrix M](hyp:M), if [M is invertible](hyp:hM), then
[its Moore–Penrose pseudoinverse equals its ordinary inverse](goal). -/
lemma penrose_eq_inverse_of_isUnit {n : ℕ} (M : Mat n n) (hM : IsUnit M) :
    moorePenroseInverse M = M⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det M).mp hM
  apply isMoorePenroseInverse_unique (moorePenroseInverse_spec M)
  constructor
  · rw [Matrix.mul_nonsing_inv M hd, Matrix.one_mul]
  constructor
  · rw [Matrix.nonsing_inv_mul M hd, Matrix.one_mul]
  constructor
  · rw [Matrix.mul_nonsing_inv M hd, Matrix.transpose_one]
  · rw [Matrix.nonsing_inv_mul M hd, Matrix.transpose_one]

-- @node: optimalPredictor_eq_canonical
/-- For [a joint law P with positive definite feature second moments](hyp:P),
[the optimal predictor equals the canonical coefficient formed from the joint
second-moment matrix of P](goal). -/
lemma optimalPredictor_eq_canonical {p m : ℕ} (P : NondegenerateLaws p m) :
    optimalPredictor P = canonicalCoefficient (secondMoment P.carrier.val) := by
  unfold optimalPredictor canonicalCoefficient
  rw [penrose_eq_inverse_of_isUnit _ P.carrier.property.isUnit]

-- @node: frob_eq_zero_iff
/-- For [a rectangular matrix M](hyp:M), [its Frobenius norm is zero if and
only if M is the zero matrix](goal). -/
lemma frob_eq_zero_iff {a b : ℕ} (M : Mat a b) : frob M = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ∑ j, M i j ^ 2) = 0 := by rw [← frob_sq, h]; norm_num
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))).mp hs
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (M i j))).mp
      (hi i (Finset.mem_univ _)) j (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hj
  · rintro rfl
    simp [frob]

-- @node: optimalPredictor_unique_minimizer
/-- For [a joint law P with positive definite feature second moments](hyp:P),
[the optimal predictor globally minimizes population squared-error risk, and
every coefficient matrix that globally minimizes that risk equals this predictor](goal). -/
lemma optimalPredictor_unique_minimizer {p m : ℕ} (P : NondegenerateLaws p m) :
    IsMinOn (fun A : Mat m p => risk A P.carrier.val) Set.univ (optimalPredictor P) ∧
    (∀ A : Mat m p, IsMinOn (fun B => risk B P.carrier.val) Set.univ A → A = optimalPredictor
      P) := by
  have hmin : IsMinOn (fun A : Mat m p => risk A P.carrier.val) Set.univ
      (optimalPredictor P) := by
    intro B _
    have h := regret_nonneg P.carrier.val B
    have hz := canonical_regret_zero P.carrier.val
    rw [← optimalPredictor_eq_canonical P] at hz
    unfold regret at h hz
    change risk (optimalPredictor P) P.carrier.val ≤ risk B P.carrier.val
    linarith
  refine ⟨hmin, ?_⟩
  intro A hA
  by_cases hp : p = 0
  · subst p
    exact Subsingleton.elim _ _
  by_cases hm : m = 0
  · subst m
    exact Subsingleton.elim _ _
  letI : NeZero p := ⟨hp⟩
  letI : NeZero m := ⟨hm⟩
  let S := CFC.sqrt (secondMoment P.carrier.val)
  let X := (factorBlocks p m S).1
  have hf : secondMoment P.carrier.val = S * S.transpose :=
    psd_sqrt_factor (momentPSD P.carrier.val)
  have hg := (regretProjectionFormula (assPin1_valid m) assSingularValueConvention_valid
    (momentPSD P.carrier.val) S hf).2.2.2.2.2.2 A
  have heq : risk A P.carrier.val = risk (optimalPredictor P) P.carrier.val :=
    le_antisymm (hA (Set.mem_univ _)) (hmin (Set.mem_univ _))
  have hz : matrixRegret A (secondMoment P.carrier.val) = 0 := by
    rw [matrixRegret, ← optimalPredictor_eq_canonical P,
      ← risk_eq_matrixRisk, ← risk_eq_matrixRisk, heq, sub_self]
  have hprod : (A - canonicalCoefficient (secondMoment P.carrier.val)) * X = 0 := by
    apply (frob_eq_zero_iff _).mp
    apply sq_eq_zero_iff.mp
    exact hg.2.2.symm.trans hz
  have hX : blockX p m (secondMoment P.carrier.val) = X * X.transpose := by
    rw [hf]
    exact (factor_gram_blocks S).1
  have hmul : (A - canonicalCoefficient (secondMoment P.carrier.val)) *
      blockX p m (secondMoment P.carrier.val) = 0 := by
    rw [hX, ← Matrix.mul_assoc, hprod, Matrix.zero_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp P.carrier.property.isUnit
  have hcancel := congrArg
    (fun B => B * (blockX p m (secondMoment P.carrier.val))⁻¹) hmul
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one,
    Matrix.zero_mul] at hcancel
  rw [optimalPredictor_eq_canonical]
  exact sub_eq_zero.mp hcancel

-- @node: residual_law_matrix
/-- For [a joint law P with positive definite feature second moments](hyp:P),
[the second-moment matrix of the optimal prediction residual equals the
matrix residual computed from the joint second moments and is positive
semidefinite](goal). -/
lemma residual_law_matrix {p m : ℕ} (P : NondegenerateLaws p m) :
    residualSecondMoment P = matrixResidual (secondMoment P.carrier.val) ∧
    (residualSecondMoment P).PosSemidef := by
  have he : residualSecondMoment P = matrixResidual (secondMoment P.carrier.val) := by
    ext i j
    have hi := integral_linear_secondMoment (lawMeasure P.carrier.val) id
      P.carrier.val.carrier.property (quadraticRegressionMatrix (optimalPredictor P)) i j
    simp only [id_eq, quadraticRegressionMatrix_apply] at hi
    change (∫ z, (matrixCLM (optimalPredictor P) (feature z) - response z) i *
      (matrixCLM (optimalPredictor P) (feature z) - response z) j ∂lawMeasure P.carrier.val) =
      (quadraticRegressionMatrix (optimalPredictor P) * secondMoment P.carrier.val *
        (quadraticRegressionMatrix (optimalPredictor P)).transpose) i j at hi
    rw [optimalPredictor_eq_canonical] at hi
    unfold matrixResidual
    rw [← hi]
    unfold residualSecondMoment
    apply integral_congr_ae
    filter_upwards [] with z
    change (response z i - matrixCLM (optimalPredictor P) (feature z) i) *
      (response z j - matrixCLM (optimalPredictor P) (feature z) j) = _
    rw [← optimalPredictor_eq_canonical]
    change _ = (matrixCLM (optimalPredictor P) (feature z) i - response z i) *
      (matrixCLM (optimalPredictor P) (feature z) j - response z j)
    ring
  refine ⟨he, ?_⟩
  rw [he]
  exact (secondMoment_posSemidef P.carrier.val).mul_mul_conjTranspose_same
    (quadraticRegressionMatrix (canonicalCoefficient (secondMoment P.carrier.val)))
-- @node: effectiveRank_bounds
/-- For [a positive semidefinite matrix M](hyp:M), [its effective rank lies
between zero and its dimension, and its trace equals its effective rank times
its Euclidean operator norm](goal). -/
lemma effectiveRank_bounds {n : ℕ} (M : PSD n) :
    0 ≤ effectiveRank M.val ∧ effectiveRank M.val ≤ n ∧
    Matrix.trace M.val = effectiveRank M.val * opNorm M.val := by
  classical
  have htrace : 0 ≤ Matrix.trace M.val := M.property.trace_nonneg
  have hnorm : 0 ≤ opNorm M.val := norm_nonneg _
  have he (i : Fin n) : M.property.isHermitian.eigenvalues i ≤ opNorm M.val := by
    have hb := (matrixCLM M.val).le_opNorm (M.property.isHermitian.eigenvectorBasis i)
    have hv : matrixCLM M.val (M.property.isHermitian.eigenvectorBasis i) =
        M.property.isHermitian.eigenvalues i • M.property.isHermitian.eigenvectorBasis i := by
      apply PiLp.ext
      intro j
      exact congrFun (M.property.isHermitian.mulVec_eigenvectorBasis i) j
    rw [hv, norm_smul, M.property.isHermitian.eigenvectorBasis.norm_eq_one,
      mul_one, mul_one] at hb
    exact (le_abs_self _).trans hb
  have hbound : Matrix.trace M.val ≤ (n : ℝ) * opNorm M.val := by
    rw [M.property.isHermitian.trace_eq_sum_eigenvalues]
    calc
      _ ≤ ∑ _i : Fin n, opNorm M.val := Finset.sum_le_sum fun i _ => he i
      _ = _ := by simp
  by_cases hz : opNorm M.val = 0
  · have ht : Matrix.trace M.val = 0 := le_antisymm (by simpa [hz] using hbound) htrace
    simp [effectiveRank, hz, ht]
  · have hp : 0 < opNorm M.val := lt_of_le_of_ne hnorm (Ne.symm hz)
    exact ⟨div_nonneg htrace hnorm, (div_le_iff₀ hp).mpr hbound,
      (div_mul_cancel₀ _ hz).symm⟩

end Papers.WassersteinRegretS2S3
