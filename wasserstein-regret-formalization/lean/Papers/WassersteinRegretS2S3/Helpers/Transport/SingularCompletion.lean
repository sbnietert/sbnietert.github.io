module
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentTransforms
public import Papers.WassersteinRegretS2S3.Helpers.Pseudoinverse
public import Papers.WassersteinRegretS2S3.Helpers.MatrixNorms
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Population Wasserstein regret: Helpers/Transport/SingularCompletion

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

/-- For [a joint law with finite second moments](hyp:P), the [completion projection](goal)
is the orthogonal projection onto the range of the square root of its second-moment matrix. -/
noncomputable def completionProjection {p m : ℕ} (P : JointLaws p m) : Mat (p + m) (p + m) :=
  rangeProjector (CFC.sqrt (secondMoment P))
/-- For [a joint law with finite second moments](hyp:P), the [completion measure](goal)
is its product with an independent, mean-zero Gaussian whose covariance is the
identity minus the completion projection. -/
noncomputable def completionMeasure {p m : ℕ} (P : JointLaws p m) :
    Measure (Observation p m × Euc (p + m)) :=
  (lawMeasure P).prod (ProbabilityTheory.multivariateGaussian 0 (1 - completionProjection P))
/-- For [a joint law with finite second moments](hyp:P) and [a pair consisting of an
observation and an auxiliary vector](hyp:z), the [completed vector](goal) is the
pseudoinverse of the square root of the law's second-moment matrix applied to the
observation, plus the auxiliary vector. -/
noncomputable def completedVector {p m : ℕ} (P : JointLaws p m)
    (z : Observation p m × Euc (p + m)) : Euc (p + m) :=
  matrixCLM (moorePenroseInverse (CFC.sqrt (secondMoment P))) z.1 + z.2
-- @realizes U(singular completion Bp dagger Z plus independent Gaussian W)

-- @node: completedVector_measurable
/-- For [a joint law with finite second moments](hyp:P), [the completed vector is
a measurable function of the observation and auxiliary vector](goal). -/
@[fun_prop] lemma completedVector_measurable {p m : ℕ} (P : JointLaws p m) :
    Measurable (completedVector P) := by
  unfold completedVector
  fun_prop

-- @node: completionMeasure_probability
/-- For [a joint law with finite second moments](hyp:P), the [completion measure
is a probability measure](goal). -/
instance completionMeasure_probability {p m : ℕ} (P : JointLaws p m) :
    IsProbabilityMeasure (completionMeasure P) := by
  unfold completionMeasure
  infer_instance

-- @node: completionProjection_facts
/-- For [a joint law with finite second moments](hyp:P), [the complement of the
completion projection is positive semidefinite; transforming the second moment
by the pseudoinverse square root gives that projection; the projection preserves
the second moment; and the square root annihilates the complementary projection](goal). -/
lemma completionProjection_facts {p m : ℕ} (P : JointLaws p m) :
    (1 - completionProjection P).PosSemidef ∧
    moorePenroseInverse (CFC.sqrt (secondMoment P)) * secondMoment P *
      (moorePenroseInverse (CFC.sqrt (secondMoment P))).transpose = completionProjection P ∧
    completionProjection P * secondMoment P = secondMoment P ∧
    CFC.sqrt (secondMoment P) * (1 - completionProjection P) = 0 := by
  let B := CFC.sqrt (secondMoment P)
  let G := moorePenroseInverse B
  have hB : B.transpose = B := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hG : G.transpose = G := by
    dsimp [G]
    rw [← penrose_transpose, hB]
  have hc : G * B = B * G := by
    have h : (B * G).transpose = B * G := (moorePenroseInverse_spec B).2.2.1
    simpa only [Matrix.transpose_mul, hB, hG] using h
  have hp : completionProjection P = B * G := rfl
  have hs : (completionProjection P).transpose = completionProjection P :=
    (rangeProjection_penrose B).2
  have hi : completionProjection P * completionProjection P = completionProjection P :=
    (rangeProjection_penrose B).1
  have hBB : B * B = secondMoment P :=
    CFC.sqrt_mul_sqrt_self _ (secondMoment_posSemidef P).nonneg
  have hpB : completionProjection P * B = B := (moorePenroseInverse_spec B).1
  have hBp : B * completionProjection P = B := by
    simpa only [Matrix.transpose_mul, hB, hs] using congrArg Matrix.transpose hpB
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpos := Matrix.posSemidef_self_mul_conjTranspose (1 - completionProjection P)
    have ht : (1 - completionProjection P).conjTranspose = 1 - completionProjection P := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
        Matrix.transpose_one, hs]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi,
      sub_self, sub_zero] at hpos
    exact hpos
  · change G * secondMoment P * G.transpose = completionProjection P
    rw [hG, ← hBB, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, ← hp, hi]
  · rw [← hBB, ← Matrix.mul_assoc, hpB]
  · change B * (1 - completionProjection P) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, hBp, sub_self]

-- @node: completedVector_memLp
/-- For [a joint law with finite second moments](hyp:P), [the completed vector
has finite second moment under the completion measure](goal). -/
lemma completedVector_memLp {p m : ℕ} (P : JointLaws p m) :
    MemLp (completedVector P) 2 (completionMeasure P) := by
  have hf : MemLp id 2 (lawMeasure P) := P.carrier.property
  have hg : MemLp id 2 (ProbabilityTheory.multivariateGaussian (0 : Euc (p + m))
      (1 - completionProjection P)) := ProbabilityTheory.IsGaussian.memLp_two_id
  exact ((hf.continuousLinearMap_comp (matrixCLM _)).comp_fst _).add (hg.comp_snd _)

-- @node: singular_completion
/-- For [a joint law with finite second moments](hyp:P), [the complementary
projection is positive semidefinite, the completed vector has identity second-moment
matrix, and multiplying it by the original second-moment square root recovers the
original observation almost surely under the completion measure](goal). -/
lemma singular_completion {p m : ℕ} (P : JointLaws p m) :
    (1 - completionProjection P).PosSemidef ∧
    (∀ i j, (∫ z, completedVector P z i * completedVector P z j ∂completionMeasure P) =
      (1 : Mat (p + m) (p + m)) i j) ∧
    (∀ᵐ z ∂completionMeasure P, matrixCLM (CFC.sqrt (secondMoment P)) (completedVector P z) =
      z.1) := by
  obtain ⟨hpos, hG, hp, hB⟩ := completionProjection_facts P
  have hf : MemLp id 2 (lawMeasure P) := P.carrier.property
  let ν := ProbabilityTheory.multivariateGaussian (0 : Euc (p + m)) (1 - completionProjection P)
  have hg : MemLp id 2 ν := ProbabilityTheory.IsGaussian.memLp_two_id
  refine ⟨hpos, ?_, ?_⟩
  · intro i j
    have hadd := integral_prod_add_secondMoment (lawMeasure P) ν
      (fun z => matrixCLM (moorePenroseInverse (CFC.sqrt (secondMoment P))) z)
      (hf.continuousLinearMap_comp (matrixCLM _)) hg
      (gaussian_coordinate_mean_zero _) i j
    change (∫ z, (matrixCLM (moorePenroseInverse (CFC.sqrt (secondMoment P))) z.1 + z.2) i *
      (matrixCLM (moorePenroseInverse (CFC.sqrt (secondMoment P))) z.1 + z.2) j
      ∂(lawMeasure P).prod ν) = _
    rw [hadd, gaussian_coordinate_secondMoment _ hpos]
    have hlin := integral_linear_secondMoment (lawMeasure P) id hf
      (moorePenroseInverse (CFC.sqrt (secondMoment P))) i j
    simp only [id_eq] at hlin
    rw [hlin]
    change (moorePenroseInverse (CFC.sqrt (secondMoment P)) * secondMoment P *
      (moorePenroseInverse (CFC.sqrt (secondMoment P))).transpose) i j +
      (1 - completionProjection P) i j = _
    rw [hG]
    exact congrFun (congrFun (add_sub_cancel (completionProjection P) 1) i) j
  · have hz : ∀ᵐ z ∂lawMeasure P, matrixCLM (completionProjection P - 1) z = 0 := by
      apply linear_ae_zero_of_secondMoment _ id hf
      change (completionProjection P - 1) * secondMoment P * (completionProjection P - 1).transpose = 0
      rw [Matrix.sub_mul, hp, Matrix.one_mul, sub_self, Matrix.zero_mul]
    have hw : ∀ᵐ w ∂ν, matrixCLM (CFC.sqrt (secondMoment P)) w = 0 := by
      apply linear_ae_zero_of_secondMoment _ id hg
      have hm : (Matrix.of (fun i j => ∫ w : Euc (p + m), w i * w j ∂ν)) =
          1 - completionProjection P := by
        ext i j
        exact gaussian_coordinate_secondMoment _ hpos i j
      simp only [id_eq]
      rw [hm, hB, Matrix.zero_mul]
    have hz' := (Measure.quasiMeasurePreserving_fst (μ := lawMeasure P) (ν := ν)).ae hz
    have hw' := (Measure.quasiMeasurePreserving_snd (μ := lawMeasure P) (ν := ν)).ae hw
    filter_upwards [hz', hw'] with z hz hw
    change matrixCLM (CFC.sqrt (secondMoment P))
      (matrixCLM (moorePenroseInverse (CFC.sqrt (secondMoment P))) z.1 + z.2) = z.1
    rw [map_add, hw, add_zero]
    have he : matrixCLM (completionProjection P) z.1 = z.1 := by
      change Matrix.toEuclideanLin (completionProjection P - 1) z.1 = 0 at hz
      rw [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply] at hz
      exact sub_eq_zero.mp hz
    change Matrix.toEuclideanLin (CFC.sqrt (secondMoment P))
      (Matrix.toEuclideanLin (moorePenroseInverse (CFC.sqrt (secondMoment P))) z.1) = _
    rw [← LinearMap.comp_apply, ← euclideanLin_mul]
    exact he

-- @node: factor_law_realization
/-- For [a joint law with finite second moments](hyp:P) and [any square factor
matrix](hyp:B), [there exists a joint law whose second moment is the factor times
its transpose and whose Wasserstein distance from the original law is at most
the Frobenius distance between that factor and the original second-moment square root](goal). -/
lemma factor_law_realization {p m : ℕ} (P : JointLaws p m) (B : Mat (p + m) (p + m)) :
    ∃ Q : JointLaws p m, secondMoment Q = B * B.transpose ∧
      wassersteinDistance P Q ≤ frob (CFC.sqrt (secondMoment P) - B) := by
  let μ := completionMeasure P
  let f := fun z => matrixCLM B (completedVector P z)
  have hf : Measurable f := by fun_prop
  let pm : ProbabilityMeasure (Observation p m × Euc (p + m)) := ⟨μ, inferInstance⟩
  let qm := pm.map hf.aemeasurable
  have hq : MemLp id 2 (qm : Measure (Observation p m)) := by
    change MemLp id 2 (Measure.map f μ)
    rw [memLp_map_measure_iff (by fun_prop) hf.aemeasurable]
    exact (completedVector_memLp P).continuousLinearMap_comp (matrixCLM B)
  let Q : JointLaws p m := ⟨⟨qm, hq⟩⟩
  obtain ⟨_, hU, hreconstruct⟩ := singular_completion P
  have hm : (Matrix.of (fun i j => ∫ z, completedVector P z i * completedVector P z j ∂μ)) =
      (1 : Mat (p + m) (p + m)) := by
    ext i j
    exact hU i j
  refine ⟨Q, ?_, ?_⟩
  · ext i j
    change (∫ z : Observation p m, z i * z j ∂Measure.map f μ) = (B * B.transpose) i j
    rw [integral_map hf.aemeasurable (by fun_prop)]
    change (∫ z, matrixCLM B (completedVector P z) i *
      matrixCLM B (completedVector P z) j ∂μ) = _
    rw [integral_linear_secondMoment μ _ (completedVector_memLp P) B, hm, Matrix.mul_one]
  · let pi := pm.map (f := fun z => (z.1, f z)) (by fun_prop)
    have hpi : Measure.map Prod.fst (pi : Measure (Observation p m × Observation p m)) =
        lawMeasure P ∧
        Measure.map Prod.snd (pi : Measure (Observation p m × Observation p m)) = lawMeasure Q := by
      constructor
      · simp only [pi, ProbabilityMeasure.toMeasure_map]
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        change Measure.map Prod.fst ((lawMeasure P).prod _) = _
        simp
      · simp only [pi, ProbabilityMeasure.toMeasure_map]
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    apply (wasserstein_le_couplingCost P Q ⟨pi, hpi⟩).trans
    have hc : couplingCost pi = frob (CFC.sqrt (secondMoment P) - B) := by
      unfold couplingCost
      rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
      have hdiff : (fun z : Observation p m × Euc (p + m) => ‖z.1 - f z‖ ^ 2) =ᵐ[μ]
          (fun z => ‖matrixCLM (CFC.sqrt (secondMoment P) - B) (completedVector P z)‖ ^ 2) := by
        filter_upwards [hreconstruct] with z hz
        dsimp [f]
        rw [← hz]
        congr 2
        change _ = Matrix.toEuclideanLin (CFC.sqrt (secondMoment P) - B) (completedVector P z)
        rw [map_sub, LinearMap.sub_apply]
        rfl
      change Real.sqrt (∫ z, ‖z.1 - f z‖ ^ 2 ∂μ) = _
      rw [integral_congr_ae hdiff,
        integral_norm_sq_linear μ _ (completedVector_memLp P), hm, Matrix.mul_one,
        Matrix.trace_mul_comm, ← frob_sq_trace, Real.sqrt_sq (frob_nonneg _)]
    exact hc.le

end Papers.WassersteinRegretS2S3
