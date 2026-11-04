module
public import Papers.WassersteinRegretS2S3.Helpers.Transport.SingularCompletion
public import Papers.WassersteinRegretS2S3.Helpers.BuresGeometry
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Population Wasserstein regret: Helpers/Transport/MomentGeometry

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: integral_gram_posSemidef
/-- For [a measure](hyp:μ) and [a finite family of real functions](hyp:f), if
[every pairwise product is integrable](hyp:hi), [the matrix of integrals of
these products is positive semidefinite](goal). -/
lemma integral_gram_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : Ω → ι → ℝ)
    (hi : ∀ i j, Integrable (fun z => f z i * f z j) μ) :
    (Matrix.of (fun i j => ∫ z, f z i * f z j ∂μ)).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp [Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have hquad : star x ⬝ᵥ ((Matrix.of fun i j => ∫ z, f z i * f z j ∂μ) *ᵥ x) =
        ∫ z : Ω, (∑ i, x i * f z i) ^ 2 ∂μ := by
      calc
        _ = ∑ i, ∑ j, ∫ z : Ω,
            (x i * (f z i * f z j)) * x j ∂μ := by
          simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum,
            Pi.star_apply, star_trivial, integral_mul_const, integral_const_mul]
          simp only [mul_assoc]
        _ = ∫ z : Ω, ∑ i, ∑ j,
            (x i * (f z i * f z j)) * x j ∂μ := by
          rw [integral_finsetSum _ (fun i _ =>
            integrable_finsetSum _ (fun j _ =>
              ((hi i j).const_mul (x i)).mul_const (x j)))]
          apply Finset.sum_congr rfl
          intro i _
          exact (integral_finsetSum _ (fun j _ =>
            ((hi i j).const_mul (x i)).mul_const (x j))).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with z
          simp only [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    rw [hquad]
    exact integral_nonneg (fun _ => sq_nonneg _)

/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [the cross-moment matrix](goal) has each
entry equal to the expected product of the corresponding coordinate of the
first observation and coordinate of the second observation under the coupling. -/
noncomputable def couplingCrossMoment {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    Mat (p + m) (p + m) := fun i j =>
  ∫ z : Observation p m × Observation p m, z.1 i * z.2 j
    ∂(pi.val : Measure (Observation p m × Observation p m))
-- @realizes \bC(raw coupling cross moment; no symmetry constraint)
-- @node: coupling_block_posSemidef
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [the block matrix with their second-moment
matrices on the diagonal and the coupling's cross-moment matrix and its
transpose off the diagonal is positive semidefinite](goal). -/
lemma coupling_block_posSemidef {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    (Matrix.fromBlocks (secondMoment P) (couplingCrossMoment P Q pi)
      (couplingCrossMoment P Q pi).transpose (secondMoment Q)).PosSemidef := by
  let μ := (pi.val : Measure (Observation p m × Observation p m))
  have hf : MemLp (fun z : Observation p m × Observation p m => z.1) 2 μ := by
    have h := P.carrier.property
    change MemLp id 2 (lawMeasure P) at h
    rw [← pi.property.1] at h
    exact h.comp_of_map (by fun_prop)
  have hs : MemLp (fun z : Observation p m × Observation p m => z.2) 2 μ := by
    have h := Q.carrier.property
    change MemLp id 2 (lawMeasure Q) at h
    rw [← pi.property.2] at h
    exact h.comp_of_map (by fun_prop)
  let f := fun (z : Observation p m × Observation p m)
    (i : Fin (p + m) ⊕ Fin (p + m)) => Sum.elim (fun i => z.1 i) (fun i => z.2 i) i
  have hi (i : Fin (p + m) ⊕ Fin (p + m)) : MemLp (fun z => f z i) 2 μ := by
    cases i with
    | inl i => exact hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i : Observation p m →L[ℝ] ℝ)
    | inr i => exact hs.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i : Observation p m →L[ℝ] ℝ)
  have heq : Matrix.fromBlocks (secondMoment P) (couplingCrossMoment P Q pi)
      (couplingCrossMoment P Q pi).transpose (secondMoment Q) =
      (fun i j => ∫ z, f z i * f z j ∂μ) := by
    ext i j
    cases i <;> cases j
    · simp only [Matrix.fromBlocks_apply₁₁, secondMoment]
      rw [← pi.property.1, integral_map (by fun_prop) (by fun_prop)]
      rfl
    · rfl
    · simp [f, couplingCrossMoment, Matrix.transpose_apply, mul_comm, μ]
    · simp only [Matrix.fromBlocks_apply₂₂, secondMoment]
      rw [← pi.property.2, integral_map (by fun_prop) (by fun_prop)]
      rfl
  rw [heq]
  exact integral_gram_posSemidef μ f (fun i j => (hi i).integrable_mul (hi j))
-- @node: trace_contraction_mul_psd_le
/-- For [two square real matrices, H and K](hyp:H,K), if [H is positive
semidefinite](hyp:hH) and [K has operator norm at most one](hyp:hK),
[the trace of K times H is at most the trace of H](goal). -/
lemma trace_contraction_mul_psd_le {n : ℕ} (H K : Mat n n)
    (hH : H.PosSemidef) (hK : opNorm K ≤ 1) :
    Matrix.trace (K * H) ≤ Matrix.trace H := by
  let S := CFC.sqrt H
  have hS : S.transpose = S := (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hquad (v : Euc n) : inner ℝ v (matrixCLM K v) ≤ inner ℝ v v := by
    calc
      _ ≤ ‖v‖ * ‖matrixCLM K v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * (1 * ‖v‖) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hK (norm_nonneg v))) (norm_nonneg v)
      _ = _ := by rw [one_mul, real_inner_self_eq_norm_sq, sq]
  calc
    Matrix.trace (K * H) = Matrix.trace (S * (K * S)) := by
      rw [← hSS, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      rw [Matrix.mul_assoc]
    _ ≤ Matrix.trace (S * S) := by
      apply Finset.sum_le_sum
      intro i _
      have hv := hquad (WithLp.toLp 2 (fun j => S j i))
      rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq] at hv
      have hs (j) : S i j = S j i := congrFun (congrFun hS j) i
      simpa [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM,
        Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, hs, mul_comm,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, sq] using hv
    _ = Matrix.trace H := congrArg Matrix.trace hSS

open scoped Matrix.Norms.L2Operator in
-- @node: trace_block_cross_le
/-- For [positive semidefinite matrices A and B](hyp:A,B) and [a square real
matrix C](hyp:C), if [the block matrix with A and B on the diagonal and C and
its transpose off the diagonal is positive semidefinite](hyp:hBlock), [the trace
of C is at most the trace of the positive semidefinite square root of the
product of the square root of A, B, and the square root of A](goal). -/
lemma trace_block_cross_le {n : ℕ} (A B : PSD n) (C : Mat n n)
    (hBlock : (Matrix.fromBlocks A.val C C.transpose B.val).PosSemidef) :
    Matrix.trace C ≤ Matrix.trace (CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val)) := by
  obtain ⟨K, hK, hC⟩ := CitedBlockContraction A B C hBlock
  obtain ⟨U, hU⟩ := real_orthogonal_polar (CFC.sqrt B.val * CFC.sqrt A.val)
  have hSA : (CFC.sqrt A.val).transpose = CFC.sqrt A.val :=
    (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq
  have hSB : (CFC.sqrt B.val).transpose = CFC.sqrt B.val :=
    (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq
  have hG : (CFC.sqrt B.val * CFC.sqrt A.val).transpose *
      (CFC.sqrt B.val * CFC.sqrt A.val) = CFC.sqrt A.val * B.val * CFC.sqrt A.val := by
    rw [Matrix.transpose_mul, hSA, hSB, Matrix.mul_assoc,
      ← Matrix.mul_assoc (CFC.sqrt B.val), CFC.sqrt_mul_sqrt_self B.val B.property.nonneg,
      ← Matrix.mul_assoc]
  rw [hG] at hU
  have hKU : opNorm (K * U.val) ≤ 1 := by
    change ‖K * U.val‖ ≤ 1
    rw [CStarRing.norm_mul_mem_unitary K U.property]
    exact hK
  calc
    Matrix.trace C = Matrix.trace (K * (CFC.sqrt B.val * CFC.sqrt A.val)) := by
      rw [hC, Matrix.trace_mul_cycle']
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((K * U.val) *
        CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val)) := by
      rw [hU]
      simp only [Matrix.mul_assoc]
    _ ≤ _ := trace_contraction_mul_psd_le _ _ (CFC.sqrt_nonneg _).posSemidef hKU

-- @node: coupling_squared_cost_trace
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [the expected squared distance between
the paired observations equals the sum of the traces of their second-moment
matrices minus twice the trace of the coupling's cross-moment matrix](goal). -/
lemma coupling_squared_cost_trace {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    (∫ z : Observation p m × Observation p m, ‖z.1 - z.2‖ ^ 2 ∂(pi.val : Measure _)) =
      Matrix.trace (secondMoment P) + Matrix.trace (secondMoment Q) -
        2 * Matrix.trace (couplingCrossMoment P Q pi) := by
  let μ := (pi.val : Measure (Observation p m × Observation p m))
  have hf (i : Fin (p + m)) : MemLp (fun z : Observation p m × Observation p m => z.1 i) 2 μ := by
    have h := law_coordinate_memLp P i
    rw [← pi.property.1] at h
    exact h.comp_of_map (by fun_prop)
  have hg (i : Fin (p + m)) : MemLp (fun z : Observation p m × Observation p m => z.2 i) 2 μ := by
    have h := law_coordinate_memLp Q i
    rw [← pi.property.2] at h
    exact h.comp_of_map (by fun_prop)
  have hP (i : Fin (p + m)) :
      (∫ z : Observation p m × Observation p m, z.1 i ^ 2 ∂μ) = secondMoment P i i := by
    rw [secondMoment, ← pi.property.1, integral_map (by fun_prop) (by fun_prop)]
    simp only [sq, μ]
  have hQ (i : Fin (p + m)) :
      (∫ z : Observation p m × Observation p m, z.2 i ^ 2 ∂μ) = secondMoment Q i i := by
    rw [secondMoment, ← pi.property.2, integral_map (by fun_prop) (by fun_prop)]
    simp only [sq, μ]
  calc
    _ = ∫ z : Observation p m × Observation p m,
        ∑ i, (z.1 i ^ 2 + z.2 i ^ 2 - 2 * (z.1 i * z.2 i)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
      ring
    _ = ∑ i, ∫ z : Observation p m × Observation p m,
        (z.1 i ^ 2 + z.2 i ^ 2 - 2 * (z.1 i * z.2 i)) ∂μ := by
      exact integral_finsetSum _ (fun i _ =>
        ((hf i).integrable_sq.add (hg i).integrable_sq).sub
          (((hf i).integrable_mul (hg i)).const_mul 2))
    _ = _ := by
      have hentry (i : Fin (p + m)) :
          (∫ z : Observation p m × Observation p m,
            (z.1 i ^ 2 + z.2 i ^ 2 - 2 * (z.1 i * z.2 i)) ∂μ) =
          secondMoment P i i + secondMoment Q i i -
            2 * couplingCrossMoment P Q pi i i := by
        have hsub := integral_sub ((hf i).integrable_sq.add (hg i).integrable_sq)
          (((hf i).integrable_mul (hg i)).const_mul 2)
        have hadd := integral_add (hf i).integrable_sq (hg i).integrable_sq
        simp only [Pi.add_apply, Pi.mul_apply] at hsub hadd
        rw [hsub, hadd, integral_const_mul, hP, hQ]
        rfl
      simp only [hentry, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Matrix.trace, Matrix.diag]


-- @node: bures_le_couplingCost
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [the Bures distance between their
second-moment matrices is at most the coupling's root mean squared transport cost](goal). -/
lemma bures_le_couplingCost {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    buresDistance (secondMoment P) (secondMoment Q) ≤ couplingCost pi.val := by
  unfold buresDistance couplingCost
  apply Real.sqrt_le_sqrt
  rw [coupling_squared_cost_trace P Q pi]
  have hcross := trace_block_cross_le (momentPSD P) (momentPSD Q)
    (couplingCrossMoment P Q pi) (coupling_block_posSemidef P Q pi)
  change Matrix.trace (couplingCrossMoment P Q pi) ≤
    Matrix.trace (CFC.sqrt (CFC.sqrt (secondMoment P) * secondMoment Q *
      CFC.sqrt (secondMoment P))) at hcross
  linarith

-- @node: psd_law_realization
/-- For [a positive semidefinite matrix of the observation dimension](hyp:Sigma),
[there exists an observation law with finite second moments whose second-moment
matrix is exactly that matrix](goal). -/
lemma psd_law_realization {p m : ℕ} (Sigma : PSD (p + m)) :
    ∃ P : JointLaws p m, secondMoment P = Sigma.val := by
  let μ := ProbabilityTheory.multivariateGaussian (0 : Observation p m) Sigma.val
  have hμ : MemLp id 2 μ := ProbabilityTheory.IsGaussian.memLp_two_id
  let P : JointLaws p m := ⟨⟨⟨μ, inferInstance⟩, hμ⟩⟩
  refine ⟨P, ?_⟩
  have hmean (i : Fin (p + m)) : (∫ z : Observation p m, z i ∂μ) = 0 := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i : Observation p m →L[ℝ] ℝ).integral_comp_id_comm
      (μ := μ) ProbabilityTheory.IsGaussian.integrable_id
    simpa [μ] using h
  ext i j
  have hcov := ProbabilityTheory.covariance_eval_multivariateGaussian
    (μ := (0 : Observation p m)) Sigma.property i j
  change ProbabilityTheory.covariance (fun z : Observation p m => z i)
    (fun z => z j) (lawMeasure P) = Sigma.val i j at hcov
  rw [ProbabilityTheory.covariance_eq_sub
    (law_coordinate_memLp P i) (law_coordinate_memLp P j)] at hcov
  change (∫ z : Observation p m, z i * z j ∂μ) -
    (∫ z : Observation p m, z i ∂μ) * (∫ z : Observation p m, z j ∂μ) = Sigma.val i j at hcov
  change (∫ z : Observation p m, z i * z j ∂μ) = Sigma.val i j
  simpa only [hmean, zero_mul, sub_zero] using hcov

-- @node: bures_distance_symm
/-- For [two positive semidefinite matrices](hyp:A,B), [the Bures distance
is unchanged when the matrices are exchanged](goal). -/
lemma bures_distance_symm {n : ℕ} (A B : PSD n) :
    buresDistance A.val B.val = buresDistance B.val A.val := by
  have hAB := (buresProcrustes A B).2.1
  have hBA := (buresProcrustes B A).2.1
  have hswap (S T : Mat n n) : frob (S - T) = frob (T - S) := by
    simp only [frob]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact sub_sq_comm _ _
  apply le_antisymm
  · obtain ⟨S, T, hB, hA, hc⟩ := hBA.1
    exact hAB.2 ⟨T, S, hA, hB, (hswap T S).trans hc⟩
  · obtain ⟨S, T, hA, hB, hc⟩ := hAB.1
    exact hBA.2 ⟨T, S, hB, hA, (hswap T S).trans hc⟩

-- @node: bures_le_wasserstein
/-- For [two observation laws with finite second moments](hyp:P,Q),
[the Bures distance between their second-moment matrices is at most their
quadratic Wasserstein distance](goal). -/
lemma bures_le_wasserstein {p m : ℕ} (P Q : JointLaws p m) :
    buresDistance (secondMoment P) (secondMoment Q) ≤ wassersteinDistance P Q := by
  obtain ⟨pi⟩ := couplings_nonempty P Q
  unfold wassersteinDistance
  refine le_csInf ?_ ?_
  · exact ⟨couplingCost pi.val, pi, rfl⟩
  · rintro c ⟨gamma, rfl⟩
    exact bures_le_couplingCost P Q gamma

-- @node: lem:w2-bures-equivalence
/-- Assuming [the singular-value convention](hyp:hsv), for [an observation law
with finite second moments](hyp:P) and [a nonnegative radius](hyp:eps), with
both predictor and response dimensions positive, [the second-moment matrices
attainable within that quadratic Wasserstein radius are exactly the positive
semidefinite matrices within the same Bures radius of the reference second
moment; this set is also exactly the matrices obtained by adding a perturbation
of Frobenius norm at most the radius to the positive semidefinite square root
of the reference second moment and multiplying the resulting factor by its
transpose](goal). -/
lemma w2BuresEquivalence (hsv : assSingularValueConvention) {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) :
    secondMoment '' lawBall P eps =
      {Sigma : Mat (p + m) (p + m) | Sigma.PosSemidef ∧ buresDistance Sigma (secondMoment P) ≤
        eps} ∧
    {Sigma : Mat (p + m) (p + m) | Sigma.PosSemidef ∧ buresDistance Sigma (secondMoment P) ≤ eps} =
      {Sigma | ∃ Delta : Mat (p + m) (p + m), frob Delta ≤ eps ∧
        Sigma = (CFC.sqrt (secondMoment P) + Delta) * (CFC.sqrt (secondMoment P) +
          Delta).transpose} := by
  constructor
  · ext Sigma
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      refine ⟨secondMoment_posSemidef Q, ?_⟩
      change buresDistance (momentPSD Q).val (momentPSD P).val ≤ eps
      rw [bures_distance_symm (momentPSD Q) (momentPSD P)]
      exact (bures_le_wasserstein P Q).trans hQ
    · rintro ⟨hSigma, hdist⟩
      obtain ⟨Delta, hDelta, hfactor⟩ :=
        ((buresProcrustes ⟨Sigma, hSigma⟩ (momentPSD P)).2.2.1 eps).mp hdist
      obtain ⟨Q, hQ, hcost⟩ := factor_law_realization P (CFC.sqrt (secondMoment P) + Delta)
      refine ⟨Q, ?_, hQ.trans hfactor.symm⟩
      change wassersteinDistance P Q ≤ eps
      apply hcost.trans
      simpa [frob] using hDelta
  · ext Sigma
    constructor
    · rintro ⟨hSigma, hdist⟩
      exact ((buresProcrustes ⟨Sigma, hSigma⟩ (momentPSD P)).2.2.1 eps).mp hdist
    · rintro ⟨Delta, hDelta, hfactor⟩
      have hSigma : Sigma.PosSemidef := by
        rw [hfactor]
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.posSemidef_self_mul_conjTranspose (CFC.sqrt (secondMoment P) + Delta)
      exact ⟨hSigma,
        ((buresProcrustes ⟨Sigma, hSigma⟩ (momentPSD P)).2.2.1 eps).mpr
          ⟨Delta, hDelta, hfactor⟩⟩

-- @node: nondegenerate_secondMoment_image
/-- When both predictor and response dimensions are positive, [the second-moment
matrices of observation laws with positive definite predictor second moments
are exactly the positive semidefinite matrices whose predictor block is
positive definite](goal). -/
lemma nondegenerate_secondMoment_image {p m : ℕ} [NeZero p] [NeZero m] :
    {Sigma : Mat (p + m) (p + m) | ∃ P : NondegenerateLaws p m, secondMoment P.carrier.val =
      Sigma} =
    {Sigma | Sigma.PosSemidef ∧ (blockX p m Sigma).PosDef} := by
  ext Sigma
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨secondMoment_posSemidef P.carrier.val, P.carrier.property⟩
  · rintro ⟨hSigma, hX⟩
    obtain ⟨P, hP⟩ := psd_law_realization (p := p) (m := m) ⟨Sigma, hSigma⟩
    exact ⟨⟨⟨P, by simpa only [secondMomentX, hP] using hX⟩⟩, hP⟩

end Papers.WassersteinRegretS2S3
