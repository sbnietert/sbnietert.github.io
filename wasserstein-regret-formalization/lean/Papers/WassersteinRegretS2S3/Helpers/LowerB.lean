module
public import Papers.WassersteinRegretS2S3.Helpers.LowerA
public import Papers.WassersteinRegretS2S3.Helpers.DROScalarB
public import Papers.WassersteinRegretS2S3.Helpers.FactorRegression
public import Papers.WassersteinRegretS2S3.Helpers.LowerBGaussian

/-!
# Population Wasserstein regret: Helpers/LowerB

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: droLowerB_coefficient_gram
/-- [A coefficient matrix with alpha in its first row and first column and zero
elsewhere has a diagonal row Gram matrix with alpha squared in the first
position and zero elsewhere](goal). -/
lemma droLowerB_coefficient_gram {p m : ℕ} [NeZero p] [NeZero m] (alpha : ℝ) :
    let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then alpha else 0
    A * A.transpose = Matrix.diagonal (fun i => (if i = 0 then alpha else 0) ^ 2) := by
  dsimp only
  ext i j
  change (∑ k : Fin p, (if i = 0 ∧ k = 0 then alpha else 0) *
    (if j = 0 ∧ k = 0 then alpha else 0)) = _
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [hi, hj, Matrix.diagonal_apply, eq_comm, pow_two]

-- @node: droLowerB_diagonal_threshold
/-- [The largest squared entry of a nonempty diagonal vector with alpha in the
first position and zero elsewhere is alpha squared](goal). -/
lemma droLowerB_diagonal_threshold {m : ℕ} [NeZero m] (alpha : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin m => (if i = 0 then alpha else 0) ^ 2) = alpha ^ 2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    split_ifs <;> nlinarith [sq_nonneg alpha]
  · calc
      alpha ^ 2 = (if (0 : Fin m) = 0 then alpha else 0) ^ 2 := by rw [if_pos rfl]
      _ ≤ _ := Finset.le_sup'
        (fun i : Fin m => (if i = 0 then alpha else 0) ^ 2) (Finset.mem_univ (0 : Fin m))

-- @node: droLowerB_residual_sum
/-- [The sum of the coordinate residual fractions equals (alpha c minus a)
squared divided by eta minus one minus alpha squared, plus m minus one times
s divided by eta minus one, when the first coordinate has residual numerator
(alpha c minus a) squared and coefficient alpha, and every other coordinate
has residual numerator s and coefficient zero](goal). -/
lemma droLowerB_residual_sum {m : ℕ} [NeZero m] (s a c alpha eta : ℝ) :
    (∑ i : Fin m, (if i = 0 then (alpha * c - a) ^ 2 else s) /
      (eta - 1 - (if i = 0 then alpha else 0) ^ 2)) =
      (alpha * c - a) ^ 2 / (eta - 1 - alpha ^ 2) +
        (((m : ℝ) - 1) * s) / (eta - 1) := by
  have he (i : Fin m) :
      (if i = 0 then (alpha * c - a) ^ 2 else s) /
        (eta - 1 - (if i = 0 then alpha else 0) ^ 2) =
      s / (eta - 1) + if i = 0 then
        (alpha * c - a) ^ 2 / (eta - 1 - alpha ^ 2) - s / (eta - 1) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

-- @node: droLowerB_matrix_objective
/-- If [the predictor with only its first coefficient equal to alpha has
coordinate residual second moments (alpha c minus a) squared in the first
coordinate and s in every other coordinate](hyp:hres), [its population DRO
objective with both scale and radius equal to one equals the scalar
lower-bound B objective with aggregate residual level (m minus one) times
s](goal). -/
lemma droLowerB_matrix_objective {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (s a c alpha : ℝ)
    (hres : ∀ i : Fin m,
      coordinateResidual P (fun i j => if i = 0 ∧ j = 0 then alpha else 0) i =
        if i = 0 then (alpha * c - a) ^ 2 else s) :
    populationObjective 1 P 1 (fun i j => if i = 0 ∧ j = 0 then alpha else 0) =
      droLowerBObjective (((m : ℝ) - 1) * s) a c alpha := by
  have hd := (droStrongDualityDiagonal (assPin1_valid m) assSingularValueConvention_valid
    P 1 (fun i j => if i = 0 ∧ j = 0 then alpha else 0)
    (fun i => if i = 0 then alpha else 0)
    ⟨by norm_num, droLowerB_coefficient_gram alpha⟩).2
  simp only [droLowerB_diagonal_threshold] at hd
  change (⨆ Q ∈ lawBall P 1, ENNReal.ofReal
    (risk (fun i j => if i = 0 ∧ j = 0 then alpha else 0) Q)) = _
  rw [hd]
  unfold droLowerBObjective
  apply iInf_congr
  intro eta
  apply iInf_congr
  intro heta
  simp_rw [hres, droLowerB_residual_sum]
  norm_num only [NNReal.coe_one, one_pow]
  unfold droLowerBDual
  rw [add_assoc]

-- @node: droLowerB_coordinate_expansion
/-- [For a predictor with alpha in its first row and first column and zero
elsewhere, the first coordinate's residual second moment is alpha squared
times the first feature's second moment, minus alpha times each of the two
cross moments with the first response, plus that response's second moment;
every other coordinate's residual second moment is its response second
moment](goal). -/
lemma droLowerB_coordinate_expansion {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (alpha : ℝ) (i : Fin m) :
    coordinateResidual P (fun i j => if i = 0 ∧ j = 0 then alpha else 0) i =
      if i = 0 then
        alpha ^ 2 * secondMomentX P 0 0 -
          alpha * secondMoment P (Fin.castAdd m 0) (Fin.natAdd p i) -
          alpha * secondMomentYX P i 0 + secondMomentY P i i
      else secondMomentY P i i := by
  rw [coordinateResidual_eq_secondMoment P (fun i j => if i = 0 ∧ j = 0 then alpha else 0) i]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadraticRegressionMatrix,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  by_cases hi : i = 0
  · subst i
    simp [Matrix.one_apply, pow_two,
      secondMomentX, secondMomentYX, secondMomentY, blockX, blockYX, blockY,
      rawBlocks, Matrix.submatrix_apply]
    ring
  · simp [hi, Matrix.one_apply, secondMomentY, blockY, rawBlocks, Matrix.submatrix_apply]

-- @node: droLowerB_contracted_residual
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient has a in its first row and first column
and zero elsewhere](hyp:hPA), and [the residual second-moment matrix is
diagonal with zero in the first coordinate and s in every other
coordinate](hyp:hPE), [scaling the first feature by c gives the predictor
with sole coefficient alpha a residual second moment of (alpha c minus a)
squared in the first coordinate and s in every other coordinate](goal). -/
lemma droLowerB_contracted_residual {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (s a c alpha : ℝ)
    (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0)
    (hPE : matrixResidual (secondMoment P) =
      Matrix.diagonal (fun i => if i = 0 then 0 else s)) (i : Fin m) :
    coordinateResidual (contractFeatureLaw 0 c P)
      (fun i j => if i = 0 ∧ j = 0 then alpha else 0) i =
        if i = 0 then (alpha * c - a) ^ 2 else s := by
  have hcan : canonicalCoefficient (secondMoment P) = secondMomentYX P := by
    unfold canonicalCoefficient
    rw [show blockX p m (secondMoment P) = 1 from hPX,
      penrose_eq_inverse_of_isUnit _ isUnit_one]
    simp [secondMomentYX]
  have hyx := hcan.symm.trans hPA
  have hcross (Q : JointLaws p m) (j : Fin m) :
      secondMoment Q (Fin.castAdd m 0) (Fin.natAdd p j) = secondMomentYX Q j 0 := by
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p j) (Fin.castAdd m 0))
      (momentPSD Q).property.isHermitian.eq
  have hY (j : Fin m) : secondMomentY P j j = if j = 0 then a ^ 2 else s := by
    have hr : coordinateResidual P (fun i k => if i = 0 ∧ k = 0 then a else 0) j =
        if j = 0 then 0 else s := by
      rw [coordinateResidual_eq_secondMoment P
        (fun i k => if i = 0 ∧ k = 0 then a else 0) j, ← hPA]
      change matrixResidual (secondMoment P) j j = _
      rw [hPE, Matrix.diagonal_apply_eq]
    rw [droLowerB_coordinate_expansion P a j, hcross, hyx, hPX] at hr
    by_cases hj : j = 0
    · subst j
      simp only [and_self, Matrix.one_apply_eq, ite_true] at hr ⊢
      nlinarith
    · simpa only [hj, if_false] using hr
  rw [droLowerB_coordinate_expansion, hcross,
    contractFeatureLaw_cross_moment, contractFeatureLaw_response_moment, hY,
    contractFeatureLaw_feature_moment, hPX, hyx]
  by_cases hi : i = 0
  · subst i
    simp only [and_self, Matrix.one_apply_eq, ite_true]
    ring
  · simp [hi]

-- @node: droLowerB_target_regret
/-- If [the feature second-moment matrix is the identity](hyp:hPX) and
[the canonical regression coefficient has a in its first row and first column
and zero elsewhere](hyp:hPA), [the predictor with alpha in that same position
and zero elsewhere has regret (alpha minus a) squared](goal). -/
lemma droLowerB_target_regret {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (a alpha : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0) :
    regret (fun i j => if i = 0 ∧ j = 0 then alpha else 0) P = (alpha - a) ^ 2 := by
  let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then alpha else 0
  change regret A P = _
  rw [(law_matrix_risk_regret P A).2]
  change matrixRegret A (momentPSD P).val = _
  rw [matrixRegret_feature_sqrt (momentPSD P) A]
  change frob ((A - canonicalCoefficient (secondMoment P)) *
    CFC.sqrt (secondMomentX P)) ^ 2 = _
  rw [hPA, hPX, CFC.sqrt_one, Matrix.mul_one]
  unfold frob
  rw [Real.sq_sqrt (by positivity)]
  have he (i : Fin m) (j : Fin p) :
      ((if i = 0 ∧ j = 0 then alpha else 0) -
        (if i = 0 ∧ j = 0 then a else 0)) ^ 2 =
      if i = 0 ∧ j = 0 then (alpha - a) ^ 2 else 0 := by
    split_ifs <;> simp
  change (∑ i : Fin m, ∑ j : Fin p,
    ((if i = 0 ∧ j = 0 then alpha else 0) -
      (if i = 0 ∧ j = 0 then a else 0)) ^ 2) = _
  simp_rw [he]
  simp [ite_and]

-- @node: droLowerB_target_source
/-- If [there are at least two responses](hyp:hm2), [kappa exceeds one](hyp:hkappa),
[a squared is at most kappa minus one](hyp:ha2), and [c is positive](hyp:hc)
and [at most one](hyp:hc1), [there exist a centered Gaussian target law and a
source law obtained by scaling its first feature by c: the target has identity
feature second moments, sole canonical coefficient a in the first position,
diagonal residual second moments zero in the first coordinate and kappa minus
one elsewhere, and condition number kappa; the source lies in the target's
unit Wasserstein ball and has the same response second-moment matrix](goal). -/
lemma droLowerB_target_source {p m : ℕ} [NeZero p] [NeZero m] (hm2 : 2 ≤ m)
    (kappa a c : ℝ) (hkappa : 1 < kappa) (ha2 : a ^ 2 ≤ kappa - 1)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then a else 0
    let E : Mat m m := Matrix.diagonal (fun i => if i = 0 then 0 else kappa - 1)
    ∃ P tildeP : JointLaws p m,
      secondMomentX P = 1 ∧ canonicalCoefficient (secondMoment P) = A ∧
      matrixResidual (secondMoment P) = E ∧
      lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P) ∧
      conditionNumber P = ENNReal.ofReal kappa ∧
      tildeP = contractFeatureLaw 0 c P ∧ tildeP ∈ lawBall P 1 ∧
      secondMomentY tildeP = secondMomentY P := by
  dsimp only
  let s := kappa - 1
  have hs : 0 < s := sub_pos.mpr hkappa
  let A : Mat m p := fun i j => if i = 0 ∧ j = 0 then a else 0
  let E : Mat m m := Matrix.diagonal (fun i => if i = 0 then 0 else s)
  have hE : E.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> positivity
  obtain ⟨P, hPX, hPA, hPE, hGaussian⟩ := regression_identity_law A ⟨E, hE⟩
  let tildeP := contractFeatureLaw (0 : Fin p) c P
  have hsource : tildeP ∈ lawBall P 1 :=
    contractFeatureLaw_mem_lawBall 0 c hc.le hc1 P hPX
  have hresponse : secondMomentY tildeP = secondMomentY P :=
    contractFeatureLaw_response_moment 0 c P
  have hgram : A * A.transpose + E =
      Matrix.diagonal (fun i : Fin m => if i = 0 then a ^ 2 else s) := by
    ext i j
    change (∑ k, A i k * A j k) + E i j = _
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [A, E, Matrix.diagonal_apply, hi, hj, eq_comm, pow_two]
  let j1 : Fin m := ⟨1, by omega⟩
  have hj1 : j1 ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    norm_num [j1] at hv
  have hmax : lambdaMax (A * A.transpose + E) = s := by
    rw [hgram]
    have hd := lambdaMax_diagonal_of_largest
      (fun i : Fin m => if i = 0 then a ^ 2 else s) j1 (by
        intro i
        simp only [hj1, if_false]
        split_ifs
        · exact ha2
        · exact le_rfl)
    simpa only [hj1, if_false] using hd
  let P' : NondegenerateLaws p m := ⟨⟨P, by rw [hPX]; exact Matrix.PosDef.one⟩⟩
  have hpred : optimalPredictor P' = A := (optimalPredictor_eq_canonical P').trans hPA
  have hres : residualSecondMoment P' = E := (residual_law_matrix P').1.trans hPE
  have hcondition : conditionNumber P = ENNReal.ofReal kappa := by
    have hf :=
      (conditionNumberFormula (assPin1_valid m) assSingularValueConvention_valid P').2.2.2.1
    change conditionNumber P = _ at hf
    change conditionNumber P = ENNReal.ofReal kappa
    rw [hf, hpred, hres]
    change ENNReal.ofReal (1 + lambdaMax (A * A.transpose +
      (lambdaMin (secondMomentX P))⁻¹ • E)) = _
    rw [hPX, lambdaMin_identity, inv_one, one_smul, hmax]
    congr 1
    dsimp [s]
    ring
  exact ⟨P, tildeP, hPX, hPA, hPE, hGaussian, hcondition, rfl, hsource, hresponse⟩

-- @node: lem:dro-lb-b
/-- [There is a universal positive constant c such that, for all positive
feature and response dimensions satisfying the paper's normalization and
singular-value conventions, every rule selecting population DRO minimizers
with scale and radius one has worst-case robust regret over the class with
condition number at most kappa bounded below by c times the square root of
m times (kappa minus one), for every kappa at least one](goal). -/
lemma droLbB :
    ∃ c : ℝ, 0 < c ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ rule : Estimator p m, IsPopulationSelection 1 1 rule →
      ENNReal.ofReal (c * Real.sqrt ((m : ℝ) * (kappa - 1))) ≤
        classRisk (wellConditionedSet p m kappa) 1 rule := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro p m _ _ hpin hsv kappa hkappa rule hsel
  by_cases hk : kappa = 1
  · subst kappa
    simp
  by_cases hm : m = 1
  · subst m
    have hminimax := minimaxLb (p := p) (m := 1) hpin hsv 1 (by norm_num) kappa hkappa
    have hbound : ENNReal.ofReal kappa ≤ classRisk (wellConditionedSet p 1 kappa) 1 rule := by
      calc
        ENNReal.ofReal kappa ≤ classMinimax (wellConditionedSet p 1 kappa) 1 := by
          simpa using hminimax
        _ ≤ classRisk (wellConditionedSet p 1 kappa) 1 rule := iInf_le _ rule
    apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
    simp only [Nat.cast_one, one_mul]
    have hroot := Real.sq_sqrt (show 0 ≤ kappa - 1 by linarith)
    nlinarith [Real.sqrt_nonneg (kappa - 1)]
  have hm2 : 2 ≤ m := by
    have hm0 := NeZero.ne m
    omega
  have hs : 0 < kappa - 1 := by
    exact sub_pos.mpr (lt_of_le_of_ne hkappa (Ne.symm hk))
  let s := kappa - 1
  let N := ((m : ℝ) - 1) * s
  let alphaStar := Real.sqrt (Real.sqrt N)
  let a := (1 / 2 : ℝ) * min (Real.sqrt s) alphaStar
  let c := a / alphaStar
  obtain ⟨ha, ha2, hc, hc2, hreg⟩ := droLowerB_scalar_regret m hm2 s hs
  change 0 < a at ha
  change a ^ 2 ≤ s at ha2
  change 0 < c at hc
  change c ≤ 1 / 2 at hc2
  change (1 / 8 : ℝ) * Real.sqrt ((m : ℝ) * s) ≤ (alphaStar - a) ^ 2 at hreg
  obtain ⟨P, tildeP, hPX, hPA, hPE, hGaussian, hcondition, hcontract, hsource, hresponse⟩ :=
    droLowerB_target_source (p := p) hm2 kappa a c (by linarith) ha2 hc (by linarith)
  have htarget : P ∈ wellConditionedSet p m kappa :=
    ⟨by rw [hPX]; exact Matrix.PosDef.one, hcondition.le⟩
  have hN : 0 < N := by
    have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    dsimp [N]
    exact mul_pos (by linarith) hs
  have hobjective (alpha : ℝ) :
      populationObjective 1 tildeP 1 (fun i j => if i = 0 ∧ j = 0 then alpha else 0) =
        droLowerBObjective N a c alpha := by
    apply droLowerB_matrix_objective tildeP s a c alpha
    intro i
    rw [hcontract]
    exact droLowerB_contracted_residual P s a c alpha hPX hPA hPE i
  have hrestricted (alpha : ℝ)
      (hmin : (fun i j => if i = 0 ∧ j = 0 then alpha else 0) ∈
        populationMinimizers 1 tildeP 1) : alpha = alphaStar := by
    apply droLowerBObjective_unique_minimizer N a hN ha alpha
    intro beta
    rw [← hobjective alpha, ← hobjective beta]
    exact hmin (Set.mem_univ _)
  have hcandidate :
      populationObjective 1 tildeP 1
        (fun i j => if i = 0 ∧ j = 0 then alphaStar else 0) =
        ENNReal.ofReal ((1 + Real.sqrt N) ^ 2) := by
    rw [hobjective]
    exact droLowerBObjective_candidate N a hN
  have hcandidateRegret :
      (1 / 8 : ℝ) * Real.sqrt ((m : ℝ) * (kappa - 1)) ≤
        regret (fun i j => if i = 0 ∧ j = 0 then alphaStar else 0) P := by
    rw [droLowerB_target_regret P a alphaStar hPX hPA]
    exact hreg
  suffices hinv : assDroSymmetryInvariantLaws (droLowerBSymmetryGroup p m) P tildeP by
    have hsym := droSymmetry hpin (droLowerBSymmetryGroup p m)
      (droLowerBSymmetryGroup_compact p m) P tildeP hinv 1 1 (rule tildeP)
      ⟨by norm_num, by norm_num, hsel tildeP⟩
    obtain ⟨alpha, hbar⟩ := (droLowerBSymmetryGroup_invariant_iff _).mp hsym.2.1
    have halpha : alpha = alphaStar := hrestricted alpha (by rw [← hbar]; exact hsym.1)
    have hregret : (1 / 8 : ℝ) * Real.sqrt ((m : ℝ) * (kappa - 1)) ≤
        regret (rule tildeP) P := by
      apply le_trans _ hsym.2.2.1
      rw [hbar, halpha]
      exact hcandidateRegret
    calc
      ENNReal.ofReal ((1 / 16 : ℝ) * Real.sqrt ((m : ℝ) * (kappa - 1))) ≤
          ENNReal.ofReal (regret (rule tildeP) P) := by
        apply ENNReal.ofReal_le_ofReal
        exact (mul_le_mul_of_nonneg_right (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8)
          (Real.sqrt_nonneg _)).trans hregret
      _ ≤ max (ENNReal.ofReal (regret (rule P) tildeP))
          (ENNReal.ofReal (regret (rule tildeP) P)) := le_max_right _ _
      _ ≤ robustRegret rule P 1 := le_iSup₂_of_le tildeP hsource le_rfl
      _ ≤ classRisk (wellConditionedSet p m kappa) 1 rule :=
        le_iSup₂_of_le P htarget le_rfl
  rw [hcontract]
  exact droLowerB_gaussian_invariant P s a c hPX hPA hPE hGaussian

end Papers.WassersteinRegretS2S3
