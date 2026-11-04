module
public import Papers.WassersteinRegretS2S3.Helpers.Symmetry
public import Papers.WassersteinRegretS2S3.Helpers.SpectralExtrema

/-!
# Laws used in the DRO lower bounds

Identity feature second moments with arbitrary regression and residual matrices,
and deterministic contraction of one feature coordinate. These constructions
retain finite uncentered second moments and leave response coordinates fixed.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: diagonal_rayleigh_eq
/-- [The quadratic form of a diagonal matrix equals the sum of its diagonal entries
times the squared corresponding coordinates](goal). -/
lemma diagonal_rayleigh_eq {n : ℕ} (v : Fin n → ℝ) (x : Euc n) :
    inner ℝ x (matrixCLM (Matrix.diagonal v) x) = ∑ i, v i * (x i) ^ 2 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change (Matrix.diagonal v *ᵥ x.ofLp) i * x i = _
  rw [Matrix.mulVec_diagonal]
  ring

-- @node: lambdaMax_diagonal_of_largest
/-- If [every diagonal entry is at most the entry at the chosen coordinate](hyp:hmax),
[the largest Rayleigh value of the diagonal matrix equals that entry](goal). -/
lemma lambdaMax_diagonal_of_largest {n : ℕ} [NeZero n] (v : Fin n → ℝ)
    (j : Fin n) (hmax : ∀ i, v i ≤ v j) :
    lambdaMax (Matrix.diagonal v) = v j := by
  apply le_antisymm
  · apply csSup_le (rayleigh_values_nonempty (Matrix.diagonal v))
    rintro t ⟨x, hx, rfl⟩
    rw [diagonal_rayleigh_eq]
    calc
      (∑ i, v i * (x i) ^ 2) ≤ ∑ i, v j * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg _)
      _ = v j * ‖x‖ ^ 2 := by
        simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
      _ = v j := by rw [hx]; ring
  · let x : Euc n := EuclideanSpace.single j 1
    have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.single, PiLp.norm_single]
    have h := rayleigh_le_lambdaMax (Matrix.diagonal v) x hx
    rw [diagonal_rayleigh_eq] at h
    simpa [x, EuclideanSpace.single, PiLp.single_apply] using h

-- @node: lambdaMin_identity
/-- [The smallest Rayleigh value of the identity matrix in positive dimension is one](goal). -/
lemma lambdaMin_identity (n : ℕ) [NeZero n] : lambdaMin (1 : Mat n n) = 1 := by
  obtain ⟨x, hx, he⟩ := lambdaMin_attained (1 : Mat n n)
  have hI : matrixCLM (1 : Mat n n) x = x := by
    ext i
    change ((1 : Mat n n) *ᵥ x.ofLp) i = x i
    simp
  rw [hI, real_inner_self_eq_norm_sq, hx] at he
  simpa using he.symm

-- @node: gaussianJointLaw
/-- Given [a positive semidefinite joint covariance matrix](hyp:Sigma), the
[Gaussian joint law](goal) is the centered multivariate Gaussian with that covariance,
viewed as a probability law with finite second moments. -/
noncomputable def gaussianJointLaw {p m : ℕ} (Sigma : PSD (p + m)) : JointLaws p m :=
  ⟨⟨⟨ProbabilityTheory.multivariateGaussian (0 : Observation p m) Sigma.val, inferInstance⟩,
    by
      change MemLp id 2 (ProbabilityTheory.multivariateGaussian (0 : Observation p m) Sigma.val)
      exact ProbabilityTheory.IsGaussian.memLp_two_id⟩⟩

-- @node: gaussianJointLaw_secondMoment
/-- [The uncentered second-moment matrix of the centered Gaussian joint law is its
specified covariance matrix](goal). -/
lemma gaussianJointLaw_secondMoment {p m : ℕ} (Sigma : PSD (p + m)) :
    secondMoment (gaussianJointLaw Sigma) = Sigma.val := by
  ext i j
  exact gaussian_coordinate_secondMoment Sigma.val Sigma.property i j

-- @node: regression_identity_law
/-- [There exists a centered Gaussian joint law whose feature second-moment matrix
is the identity, whose canonical regression coefficient is the prescribed matrix,
and whose residual second-moment matrix is the prescribed positive semidefinite matrix](goal). -/
lemma regression_identity_law {p m : ℕ} (A : Mat m p) (E : PSD m) :
    ∃ P : JointLaws p m, secondMomentX P = 1 ∧
      canonicalCoefficient (secondMoment P) = A ∧ matrixResidual (secondMoment P) = E.val ∧
      lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P) := by
  let F : Mat (p + m) p := fun i j => Fin.addCases (fun k => (1 : Mat p p) k j)
    (fun k => A k j) i
  let G : Mat (p + m) m := fun i j => Fin.addCases (fun _ => 0)
    (fun k => CFC.sqrt E.val k j) i
  have hF : factorBlocks p m F = (1, A) := by
    apply Prod.ext <;> ext i j <;> simp [factorBlocks, F, Matrix.submatrix]
  have hG : factorBlocks p m G = (0, CFC.sqrt E.val) := by
    apply Prod.ext <;> ext i j <;> simp [factorBlocks, G, Matrix.submatrix]
  have hpsdF : (F * F.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose F
  have hpsdG : (G * G.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose G
  have hpsd := hpsdF.add hpsdG
  let P : JointLaws p m := gaussianJointLaw ⟨_, hpsd⟩
  have hP := gaussianJointLaw_secondMoment (p := p) (m := m) ⟨_, hpsd⟩
  have hx : blockX p m (secondMoment P) = 1 := by
    rw [hP]
    change blockX p m (F * F.transpose) + blockX p m (G * G.transpose) = 1
    rw [(factor_gram_blocks F).1, (factor_gram_blocks G).1, hF, hG]
    simp
  have hyx : blockYX p m (secondMoment P) = A := by
    rw [hP]
    change blockYX p m (F * F.transpose) + blockYX p m (G * G.transpose) = A
    rw [(factor_gram_blocks F).2.1, (factor_gram_blocks G).2.1, hF, hG]
    simp
  have hA : canonicalCoefficient (secondMoment P) = A := by
    rw [canonicalCoefficient, hx, hyx, penrose_eq_inverse_of_isUnit _ isUnit_one]
    simp
  have hzero : quadraticRegressionMatrix A * F = 0 := by
    rw [quadraticRegressionMatrix_factor, hF]
    simp
  have hnoise : quadraticRegressionMatrix A * G = -CFC.sqrt E.val := by
    rw [quadraticRegressionMatrix_factor, hG]
    simp
  have hsqrt : (CFC.sqrt E.val).transpose = CFC.sqrt E.val :=
    (CFC.sqrt_nonneg E.val).posSemidef.isHermitian.eq
  refine ⟨P, hx, hA, ?_, ?_⟩
  · rw [matrixResidual, hA, hP, Matrix.mul_add, Matrix.add_mul]
    simp only [← Matrix.mul_assoc, hzero, Matrix.zero_mul, zero_add]
    rw [hnoise, Matrix.mul_assoc, ← Matrix.transpose_mul, hnoise,
      Matrix.transpose_neg, neg_mul_neg, hsqrt,
      CFC.sqrt_mul_sqrt_self E.val E.property.nonneg]
  · rw [hP]
    rfl

-- @node: coordinateScalingMatrix
/-- For [a dimension](hyp:n), [a coordinate to scale](hyp:j), and [a real scaling
factor](hyp:c), the [coordinate scaling matrix](goal) is diagonal, with that factor
at the chosen coordinate and ones elsewhere. -/
noncomputable def coordinateScalingMatrix (n : ℕ) (j : Fin n) (c : ℝ) : Mat n n :=
  Matrix.diagonal (fun i => if i = j then c else 1)

-- @node: coordinateScalingMatrix_apply
/-- [Applying the coordinate scaling matrix multiplies the chosen coordinate by
the scaling factor and leaves every other coordinate unchanged](goal). -/
lemma coordinateScalingMatrix_apply {n : ℕ} (j : Fin n) (c : ℝ) (z : Euc n) (i : Fin n) :
    matrixCLM (coordinateScalingMatrix n j c) z i = (if i = j then c else 1) * z i := by
  change (coordinateScalingMatrix n j c *ᵥ z.ofLp) i = _
  simp [coordinateScalingMatrix, Matrix.mulVec_diagonal]

-- @node: coordinateScalingMatrix_displacement
/-- [The squared Euclidean displacement caused by scaling one coordinate equals
the square of one minus the scaling factor times the square of that coordinate](goal). -/
lemma coordinateScalingMatrix_displacement {n : ℕ} (j : Fin n) (c : ℝ) (z : Euc n) :
    ‖z - matrixCLM (coordinateScalingMatrix n j c) z‖ ^ 2 = (1 - c) ^ 2 * (z j) ^ 2 := by
  have hvec : z - matrixCLM (coordinateScalingMatrix n j c) z =
      EuclideanSpace.single j ((1 - c) * z j) := by
    ext i
    simp only [PiLp.sub_apply, coordinateScalingMatrix_apply]
    by_cases hi : i = j
    · subst i
      simp [EuclideanSpace.single]
      ring
    · simp [hi, EuclideanSpace.single]
  rw [hvec]
  simp [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, mul_pow]

-- @node: wasserstein_lawMapCLM_self_le
/-- [The Wasserstein distance from a joint law to its image under a continuous
linear map is at most the square root of the expected squared displacement under
that map](goal). -/
lemma wasserstein_lawMapCLM_self_le {p m : ℕ}
    (F : Observation p m →L[ℝ] Observation p m) (P : JointLaws p m) :
    wassersteinDistance P (lawMapCLM F P) ≤
      Real.sqrt (∫ z, ‖z - F z‖ ^ 2 ∂lawMeasure P) := by
  let gamma := P.carrier.val.map (f := fun z => (z, F z)) (by fun_prop)
  have hg : Measure.map Prod.fst (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure P ∧
      Measure.map Prod.snd (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure (lawMapCLM F P) := by
    constructor
    · simp only [gamma, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      exact Measure.map_id
    · simp only [gamma, ProbabilityMeasure.toMeasure_map, lawMapCLM_measure]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
  have hc : couplingCost gamma = Real.sqrt (∫ z, ‖z - F z‖ ^ 2 ∂lawMeasure P) := by
    unfold couplingCost
    rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
  exact (wasserstein_le_couplingCost P (lawMapCLM F P) ⟨gamma, hg⟩).trans_eq hc

-- @node: contractFeatureLaw
/-- For [a selected feature coordinate](hyp:j), [a real scaling factor](hyp:c), and
[a joint feature-response law](hyp:P), the [feature-scaled law](goal) is obtained by
multiplying that feature coordinate by the factor and leaving all other feature
and response coordinates unchanged. -/
noncomputable def contractFeatureLaw {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) : JointLaws p m :=
  lawMapCLM (matrixCLM (coordinateScalingMatrix (p + m) (Fin.castAdd m j) c)) P

-- @node: secondMoment_lawMapCLM_matrix
/-- [The joint second-moment matrix after a linear transformation equals the
transformation matrix times the original second-moment matrix times the transpose
of the transformation matrix](goal). -/
lemma secondMoment_lawMapCLM_matrix {p m : ℕ}
    (M : Mat (p + m) (p + m)) (P : JointLaws p m) :
    secondMoment (lawMapCLM (matrixCLM M) P) = M * secondMoment P * M.transpose := by
  ext i j
  unfold secondMoment
  rw [lawMapCLM_measure, integral_map (by fun_prop) (by fun_prop)]
  exact integral_linear_secondMoment (lawMeasure P) id P.carrier.property M i j

-- @node: contractFeatureLaw_secondMoment
/-- [Scaling one feature coordinate multiplies each joint second-moment entry by
one scaling factor for each of its two indices that equals the selected feature
coordinate, and by one for each other index](goal). -/
lemma contractFeatureLaw_secondMoment {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) (i k : Fin (p + m)) :
    secondMoment (contractFeatureLaw j c P) i k =
      (if i = Fin.castAdd m j then c else 1) *
      (if k = Fin.castAdd m j then c else 1) * secondMoment P i k := by
  unfold secondMoment contractFeatureLaw
  rw [lawMapCLM_measure, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [coordinateScalingMatrix_apply]
  have hprod (z : Observation p m) :
      (if i = Fin.castAdd m j then c else 1) * z i *
        ((if k = Fin.castAdd m j then c else 1) * z k) =
      ((if i = Fin.castAdd m j then c else 1) *
        (if k = Fin.castAdd m j then c else 1)) * (z i * z k) := by ring
  simp_rw [hprod]
  exact integral_const_mul _ _

-- @node: contractFeatureLaw_feature_moment
/-- [After scaling one feature coordinate, each feature second-moment entry is
multiplied by the scaling factor for each index equal to that coordinate and by
one for each other index](goal). -/
lemma contractFeatureLaw_feature_moment {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) (i k : Fin p) :
    secondMomentX (contractFeatureLaw j c P) i k =
      (if i = j then c else 1) * (if k = j then c else 1) * secondMomentX P i k := by
  change secondMoment (contractFeatureLaw j c P) (Fin.castAdd m i) (Fin.castAdd m k) = _
  rw [contractFeatureLaw_secondMoment]
  simp only [Fin.castAdd_inj]
  rfl

-- @node: contractFeatureLaw_cross_moment
/-- [Scaling one feature coordinate multiplies the response-feature cross-moment
entries in that feature's column by the scaling factor and leaves the other
columns unchanged](goal). -/
lemma contractFeatureLaw_cross_moment {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) (i : Fin m) (k : Fin p) :
    secondMomentYX (contractFeatureLaw j c P) i k =
      (if k = j then c else 1) * secondMomentYX P i k := by
  change secondMoment (contractFeatureLaw j c P) (Fin.natAdd p i) (Fin.castAdd m k) = _
  rw [contractFeatureLaw_secondMoment]
  have hne : Fin.natAdd p i ≠ Fin.castAdd m j := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at he
    omega
  simp only [hne, if_false, one_mul, Fin.castAdd_inj]
  rfl

-- @node: contractFeatureLaw_response_moment
/-- [Scaling a feature coordinate leaves the response second-moment matrix unchanged](goal). -/
lemma contractFeatureLaw_response_moment {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) : secondMomentY (contractFeatureLaw j c P) = secondMomentY P := by
  ext i k
  change secondMoment (contractFeatureLaw j c P) (Fin.natAdd p i) (Fin.natAdd p k) = _
  rw [contractFeatureLaw_secondMoment]
  have hne (a : Fin m) : Fin.natAdd p a ≠ Fin.castAdd m j := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at he
    omega
  simp only [hne, if_false, one_mul]
  rfl

-- @node: contractFeatureLaw_wasserstein_le
/-- [The Wasserstein distance from a joint law to its one-feature-scaled version
is at most the square root of the square of one minus the scaling factor times
that feature's original second moment](goal). -/
lemma contractFeatureLaw_wasserstein_le {p m : ℕ} (j : Fin p) (c : ℝ)
    (P : JointLaws p m) :
    wassersteinDistance P (contractFeatureLaw j c P) ≤
      Real.sqrt ((1 - c) ^ 2 * secondMomentX P j j) := by
  apply (wasserstein_lawMapCLM_self_le _ P).trans_eq
  congr 1
  simp_rw [coordinateScalingMatrix_displacement]
  rw [integral_const_mul]
  simp only [secondMomentX, blockX, rawBlocks, Matrix.submatrix_apply, secondMoment, pow_two]

-- @node: contractFeatureLaw_mem_lawBall
/-- If [the scaling factor is nonnegative](hyp:hc) and [at most one](hyp:hc1), and
[the original feature second-moment matrix is the identity](hyp:hP), then
[the feature-scaled law lies in the Wasserstein ball of radius one around the
original law](goal). -/
lemma contractFeatureLaw_mem_lawBall {p m : ℕ} (j : Fin p) (c : ℝ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (P : JointLaws p m) (hP : secondMomentX P = 1) :
    contractFeatureLaw j c P ∈ lawBall P 1 := by
  change wassersteinDistance P (contractFeatureLaw j c P) ≤ 1
  have hbound := contractFeatureLaw_wasserstein_le j c P
  rw [hP, Matrix.one_apply_eq, mul_one, Real.sqrt_sq (by linarith : 0 ≤ 1 - c)] at hbound
  exact hbound.trans (by linarith)

end Papers.WassersteinRegretS2S3
