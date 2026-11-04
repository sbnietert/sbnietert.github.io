module
public import Papers.WassersteinRegretS2S3.Basic
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection
public import Papers.WassersteinRegretS2S3.Helpers.Transport.Couplings
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Population Wasserstein regret: Helpers/Symmetry

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

/-- For [a subgroup of feature and response orthogonal transformations](hyp:U), the
[measurable sets on the subgroup](goal) are its Borel sets. -/
instance blockOrthSubgroupMeasurableSpace {p m : ℕ} (U : Subgroup (BlockOrth p m)) :
    MeasurableSpace U := borel U

-- @node: normalizedHaar_exists
/-- If [a subgroup of feature and response orthogonal transformations is compact](hyp:hU),
[it admits a probability measure that is also a Haar measure](goal). -/
lemma normalizedHaar_exists {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) :
    ∃ mu : Measure U, IsProbabilityMeasure mu ∧ Measure.IsHaarMeasure mu := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : BorelSpace U := ⟨rfl⟩
  refine ⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts U), ?_, inferInstance⟩
  exact ⟨Measure.haarMeasure_self⟩
/-- For [a subgroup of feature and response orthogonal transformations](hyp:U) that
[is compact](hyp:hU), the [normalized Haar measure](goal) is a chosen Haar probability
measure on the subgroup. -/
noncomputable def normalizedHaar {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) : Measure U := Classical.choose (normalizedHaar_exists U hU)
-- @realizes \mu(normalized Haar measure on the compact subgroup)
/-- For [a subgroup of feature and response orthogonal transformations](hyp:U) that
[is compact](hyp:hU) and [a coefficient matrix A](hyp:A), the [averaged coefficient](goal)
is the Haar probability average of A multiplied on the left by the transposed response
transformation and on the right by the feature transformation. -/
noncomputable def averageCoefficient {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (A : Mat m p) : Mat m p :=
  ∫ u : U, u.val.2.val.transpose * A * u.val.1.val ∂normalizedHaar U hU
-- @realizes \bar{\bA}(Haar averaged coefficient)
/-- For [a subgroup of feature and response orthogonal transformations](hyp:U) and
[a coefficient matrix A](hyp:A), [coefficient invariance](goal) means that multiplying A
on the left by the transposed response transformation and on the right by the feature
transformation leaves A unchanged for every subgroup element. -/
def invariantCoefficient {p m : ℕ} (U : Subgroup (BlockOrth p m)) (A : Mat m p) : Prop :=
  ∀ u : U, u.val.2.val.transpose * A * u.val.1.val = A

-- @node: normalizedHaar_probability
/-- If [the subgroup is compact](hyp:hU), [its normalized Haar measure has total mass one](goal). -/
lemma normalizedHaar_probability {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) : IsProbabilityMeasure (normalizedHaar U hU) :=
  (Classical.choose_spec (normalizedHaar_exists U hU)).1

-- @node: normalizedHaar_haar
/-- If [the subgroup is compact](hyp:hU), [its normalized Haar measure is a Haar measure](goal). -/
lemma normalizedHaar_haar {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) : Measure.IsHaarMeasure (normalizedHaar U hU) :=
  (Classical.choose_spec (normalizedHaar_exists U hU)).2

-- @node: matrixFrobeniusContinuousENorm
/-- The [extended norm on real coefficient matrices is continuous](goal) for the
topology induced by the Frobenius norm. -/
noncomputable local instance matrixFrobeniusContinuousENorm {p m : ℕ} :
    ContinuousENorm (Mat m p) := SeminormedAddGroup.toContinuousENorm

-- @node: coefficientOrbit_continuous
/-- For a fixed coefficient matrix and a subgroup of block orthogonal transformations,
[the coefficient obtained by multiplying on the left by the transposed response
transformation and on the right by the feature transformation varies continuously
with the subgroup element](goal). -/
@[fun_prop] lemma coefficientOrbit_continuous {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (A : Mat m p) : Continuous (fun u : U => u.val.2.val.transpose * A * u.val.1.val) := by
  fun_prop

-- @node: coefficientOrbit_integrable
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU),
[the transformed coefficient matrix is integrable over the subgroup with respect
to normalized Haar measure](goal). -/
lemma coefficientOrbit_integrable {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (A : Mat m p) :
    Integrable (fun u : U => u.val.2.val.transpose * A * u.val.1.val)
      (normalizedHaar U hU) := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  exact (coefficientOrbit_continuous U A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

-- @node: normalizedHaar_rightInvariant
/-- If [the subgroup is compact](hyp:hU), [its normalized Haar measure is invariant
under right multiplication by any subgroup element](goal). -/
lemma normalizedHaar_rightInvariant {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) :
    (normalizedHaar U hU).IsMulRightInvariant := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  letI := normalizedHaar_haar U hU
  constructor
  intro u
  letI : IsProbabilityMeasure (Measure.map (fun x : U => x * u) (normalizedHaar U hU)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

-- @node: averageCoefficient_invariant
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU),
[the Haar-averaged coefficient is unchanged by every coefficient transformation
in the subgroup](goal). -/
lemma averageCoefficient_invariant {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (A : Mat m p) :
    invariantCoefficient U (averageCoefficient U hU A) := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_rightInvariant U hU
  intro v
  let L : Mat m p →ₗ[ℝ] Mat m p :=
    { toFun := fun B => v.val.2.val.transpose * B * v.val.1.val
      map_add' := by intros; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have hi := L.toContinuousLinearMap.integral_comp_comm (coefficientOrbit_integrable U hU A)
  change L (∫ u : U, u.val.2.val.transpose * A * u.val.1.val ∂normalizedHaar U hU) = _
  change (∫ u : U, L (u.val.2.val.transpose * A * u.val.1.val) ∂normalizedHaar U hU) =
    L (∫ u : U, u.val.2.val.transpose * A * u.val.1.val ∂normalizedHaar U hU) at hi
  rw [← hi]
  have horbit (u : U) : L (u.val.2.val.transpose * A * u.val.1.val) =
      (u * v).val.2.val.transpose * A * (u * v).val.1.val := by
    change v.val.2.val.transpose * (u.val.2.val.transpose * A * u.val.1.val) * v.val.1.val =
      (u.val.2.val * v.val.2.val).transpose * A * (u.val.1.val * v.val.1.val)
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  simp_rw [horbit]
  exact integral_mul_right_eq_self (μ := normalizedHaar U hU)
    (fun u : U => u.val.2.val.transpose * A * u.val.1.val) v

-- @node: orthogonal_matrixCLM_norm
/-- [Applying an orthogonal matrix to a Euclidean vector preserves its norm](goal). -/
lemma orthogonal_matrixCLM_norm {n : ℕ} (u : Orth n) (x : Euc n) :
    ‖matrixCLM u.val x‖ = ‖x‖ := by
  exact ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) u.property) x

-- @node: blockAction_feature_response
/-- [Applying a block orthogonal transformation to an observation transforms its
feature vector by the feature block and its response vector by the response block](goal). -/
lemma blockAction_feature_response {p m : ℕ} (u : BlockOrth p m) (z : Observation p m) :
    feature (matrixCLM (blockActionMatrix u) z) = matrixCLM u.1.val (feature z) ∧
    response (matrixCLM (blockActionMatrix u) z) = matrixCLM u.2.val (response z) := by
  constructor <;> ext i <;>
    simp [feature, response, matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec,
      dotProduct, blockActionMatrix, Fin.sum_univ_add]

-- @node: orthogonal_loss_transform
/-- [Squared prediction loss at a block-orthogonally transformed observation equals
loss at the original observation with the coefficient multiplied on the left by the
transposed response block and on the right by the feature block](goal). -/
lemma orthogonal_loss_transform {p m : ℕ} (u : BlockOrth p m) (A : Mat m p)
    (z : Observation p m) :
    ‖matrixCLM A (feature (matrixCLM (blockActionMatrix u) z)) -
        response (matrixCLM (blockActionMatrix u) z)‖ ^ 2 =
      ‖matrixCLM (u.2.val.transpose * A * u.1.val) (feature z) - response z‖ ^ 2 := by
  obtain ⟨hx, hy⟩ := blockAction_feature_response u z
  rw [hx, hy]
  have hu : u.2.val.transpose * u.2.val = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp u.2.property
  have hn := orthogonal_matrixCLM_norm (Matrix.UnitaryGroup.transpose u.2)
    (matrixCLM A (matrixCLM u.1.val (feature z)) - matrixCLM u.2.val (response z))
  change ‖matrixCLM u.2.val.transpose
    (matrixCLM A (matrixCLM u.1.val (feature z)) - matrixCLM u.2.val (response z))‖ = _ at hn
  have he : matrixCLM u.2.val.transpose
      (matrixCLM A (matrixCLM u.1.val (feature z)) - matrixCLM u.2.val (response z)) =
      matrixCLM (u.2.val.transpose * A * u.1.val) (feature z) - response z := by
    simp only [map_sub]
    have hmul {a b c : ℕ} (B : Mat a b) (C : Mat b c) (v : Euc c) :
        matrixCLM B (matrixCLM C v) = matrixCLM (B * C) v := by
      exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec v.ofLp B C)
    rw [hmul, hmul, hmul, hu]
    simp [matrixCLM, Matrix.toEuclideanLin_apply]
  rw [he] at hn
  exact congrArg (fun t : ℝ => t ^ 2) hn.symm

-- @node: risk_orthogonal_invariant
/-- If [a joint law is preserved by a block orthogonal transformation](hyp:hP),
[multiplying the coefficient on the left by the transposed response block and on
the right by the feature block preserves its risk under that law](goal). -/
lemma risk_orthogonal_invariant {p m : ℕ} (u : BlockOrth p m) (P : JointLaws p m)
    (hP : Measure.map (matrixCLM (blockActionMatrix u)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) : risk (u.2.val.transpose * A * u.1.val) P = risk A P := by
  have hi := integral_map (μ := lawMeasure P)
    (φ := matrixCLM (blockActionMatrix u))
    (f := fun z => ‖matrixCLM A (feature z) - response z‖ ^ 2)
    (by fun_prop) (by rw [hP]; exact (loss_integrable A P).aestronglyMeasurable)
  rw [hP] at hi
  exact (integral_congr_ae (Filter.Eventually.of_forall (fun z =>
    (orthogonal_loss_transform u A z).symm))).trans hi.symm

/-- For any joint law with finite second moments, [prediction risk is continuous
as a function of the coefficient matrix](goal). -/
@[fun_prop] lemma risk_continuous_coefficient {p m : ℕ} (P : JointLaws p m) :
    Continuous (fun A : Mat m p => risk A P) := by
  simp_rw [risk_eq_matrixRisk, matrixRisk]
  fun_prop

-- @node: risk_convex_coefficient
/-- For any joint law with finite second moments, [prediction risk is convex over
the entire space of coefficient matrices](goal). -/
lemma risk_convex_coefficient {p m : ℕ} (P : JointLaws p m) :
    ConvexOn ℝ Set.univ (fun A : Mat m p => risk A P) := by
  let S := CFC.sqrt (secondMoment P)
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  let L : Mat m p →ₗ[ℝ] Mat m (p + m) :=
    { toFun := fun A => A * X
      map_add' := by intros; exact Matrix.add_mul ..
      map_smul' := by intros; exact Matrix.smul_mul .. }
  let F : Mat m p →ᵃ[ℝ] Mat m (p + m) :=
    L.toAffineMap - AffineMap.const ℝ (Mat m p) Y
  have hc := ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set (Mat m (p + m))))).pow
    (fun _ _ => norm_nonneg _) 2).comp_affineMap F
  have hr (A : Mat m p) : risk A P = ‖F A‖ ^ 2 := by
    have hf : secondMoment P = S * S.transpose := psd_sqrt_factor (momentPSD P)
    rw [risk_eq_matrixRisk, hf, matrixRisk_gram_factor]
    change frob (A * X - Y) ^ 2 = ‖A * X - Y‖ ^ 2
    congr 1
    simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  change ConvexOn ℝ Set.univ (fun A => ‖F A‖ ^ 2) at hc
  simpa only [← hr] using hc

-- @node: regret_orthogonal_invariant
/-- If [a joint law is preserved by a block orthogonal transformation](hyp:hP),
[multiplying the coefficient on the left by the transposed response block and on
the right by the feature block preserves its regret under that law](goal). -/
lemma regret_orthogonal_invariant {p m : ℕ} (u : BlockOrth p m) (P : JointLaws p m)
    (hP : Measure.map (matrixCLM (blockActionMatrix u)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) : regret (u.2.val.transpose * A * u.1.val) P = regret A P := by
  unfold regret
  rw [risk_orthogonal_invariant u P hP A]

-- @node: averageCoefficient_risk_le
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the joint law](hyp:hP),
[Haar averaging a coefficient matrix cannot increase its risk under that law](goal). -/
lemma averageCoefficient_risk_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) : risk (averageCoefficient U hU A) P ≤ risk A P := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  have hc : Continuous (fun u : U => risk (u.val.2.val.transpose * A * u.val.1.val) P) := by
    fun_prop
  have hi := hc.integrable_of_hasCompactSupport (μ := normalizedHaar U hU)
    (HasCompactSupport.of_compactSpace _)
  have hj := (risk_convex_coefficient P).map_integral_le
    (risk_continuous_coefficient P).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (coefficientOrbit_integrable U hU A) hi
  change risk (averageCoefficient U hU A) P ≤ _ at hj
  have horbit (u : U) : risk (u.val.2.val.transpose * A * u.val.1.val) P = risk A P :=
    risk_orthogonal_invariant u.val P (hP u) A
  simpa [horbit] using hj

-- @node: averageCoefficient_regret_le
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the joint law](hyp:hP),
[Haar averaging a coefficient matrix cannot increase its regret under that law](goal). -/
lemma averageCoefficient_regret_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) : regret (averageCoefficient U hU A) P ≤ regret A P := by
  exact sub_le_sub_right (averageCoefficient_risk_le U hU P hP A) _

-- @node: matrixCLM_mul_apply
/-- [Applying a matrix product to a Euclidean vector equals applying the right
matrix first and then the left matrix](goal). -/
lemma matrixCLM_mul_apply {a b c : ℕ} (B : Mat a b) (C : Mat b c) (x : Euc c) :
    matrixCLM (B * C) x = matrixCLM B (matrixCLM C x) := by
  exact (congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec x.ofLp B C)).symm

-- @node: coefficientOrbit_norm_bound
/-- [The norm of the prediction from a coefficient transformed by orthogonal
feature and response blocks is at most the original coefficient's operator norm
times the feature vector's norm](goal). -/
lemma coefficientOrbit_norm_bound {p m : ℕ} (u : BlockOrth p m) (A : Mat m p)
    (x : Euc p) :
    ‖matrixCLM (u.2.val.transpose * A * u.1.val) x‖ ≤ opNorm A * ‖x‖ := by
  rw [matrixCLM_mul_apply, matrixCLM_mul_apply]
  have hn := orthogonal_matrixCLM_norm (Matrix.UnitaryGroup.transpose u.2)
    (matrixCLM A (matrixCLM u.1.val x))
  change ‖matrixCLM u.2.val.transpose (matrixCLM A (matrixCLM u.1.val x))‖ = _ at hn
  rw [hn]
  exact ((matrixCLM A).le_opNorm _).trans_eq
    (congrArg (fun t => opNorm A * t) (orthogonal_matrixCLM_norm u.1 x))

-- @node: averageCoefficient_opNorm_le
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU),
[Haar averaging a coefficient matrix cannot increase its operator norm](goal). -/
lemma averageCoefficient_opNorm_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (A : Mat m p) :
    opNorm (averageCoefficient U hU A) ≤ opNorm A := by
  letI := normalizedHaar_probability U hU
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let L : Mat m p →ₗ[ℝ] Euc m :=
    { toFun := fun B => matrixCLM B x
      map_add' := by intros; simp [matrixCLM, Matrix.toLpLin_apply]
      map_smul' := by intros; simp [matrixCLM, Matrix.toLpLin_apply] }
  have hi := L.toContinuousLinearMap.integral_comp_comm (coefficientOrbit_integrable U hU A)
  change (∫ u : U, L (u.val.2.val.transpose * A * u.val.1.val) ∂normalizedHaar U hU) =
    L (averageCoefficient U hU A) at hi
  change ‖L (averageCoefficient U hU A)‖ ≤ _
  rw [← hi]
  change ‖∫ u : U, matrixCLM (u.val.2.val.transpose * A * u.val.1.val) x
    ∂normalizedHaar U hU‖ ≤ opNorm A * ‖x‖
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := normalizedHaar U hU)
    (Filter.Eventually.of_forall (fun u : U => coefficientOrbit_norm_bound u.val A x))

-- @node: averageCoefficient_spectralRisk_le
/-- For [a nonnegative regularization radius](hyp:eps), if [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the joint law](hyp:hP), [Haar averaging
cannot increase risk plus the squared nonnegative radius times the squared operator
norm of the coefficient](goal). -/
lemma averageCoefficient_spectralRisk_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) (eps : ℝ≥0) :
    risk (averageCoefficient U hU A) P + (eps : ℝ) ^ 2 * opNorm (averageCoefficient U hU A) ^ 2 ≤
      risk A P + (eps : ℝ) ^ 2 * opNorm A ^ 2 := by
  apply add_le_add (averageCoefficient_risk_le U hU P hP A)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (averageCoefficient_opNorm_le U hU A) 2) (sq_nonneg _)

-- @node: averageCoefficient_risk_le_integral
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU),
[risk at the Haar-averaged coefficient is at most the Haar average of risk at the
transformed coefficients](goal), for any joint law with finite second moments. -/
lemma averageCoefficient_risk_le_integral {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m) (A : Mat m p) :
    risk (averageCoefficient U hU A) P ≤
      ∫ u : U, risk (u.val.2.val.transpose * A * u.val.1.val) P ∂normalizedHaar U hU := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  have hc : Continuous (fun u : U => risk (u.val.2.val.transpose * A * u.val.1.val) P) := by
    fun_prop
  exact (risk_convex_coefficient P).map_integral_le
    (risk_continuous_coefficient P).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (coefficientOrbit_integrable U hU A)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

-- @node: lawMapCLM
/-- For [a continuous linear transformation of observations](hyp:F) and [a joint
law with finite second moments](hyp:P), the [transformed joint law](goal) is the
distribution obtained by applying that transformation to an observation drawn from
the original law, and still has finite second moments. -/
noncomputable def lawMapCLM {p m : ℕ}
    (F : Observation p m →L[ℝ] Observation p m) (P : JointLaws p m) : JointLaws p m :=
  ⟨⟨P.carrier.val.map (f := F) (by fun_prop), by
    change MemLp id 2 (Measure.map F (lawMeasure P))
    rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
    exact P.carrier.property.continuousLinearMap_comp F⟩⟩

-- @node: lawMapCLM_measure
/-- [The probability measure underlying a linearly transformed joint law is the
pushforward of the original law's measure by that linear transformation](goal). -/
lemma lawMapCLM_measure {p m : ℕ}
    (F : Observation p m →L[ℝ] Observation p m) (P : JointLaws p m) :
    lawMeasure (lawMapCLM F P) = Measure.map F (lawMeasure P) := rfl

-- @node: wasserstein_lawMapCLM_le
/-- If [a continuous linear transformation preserves every observation's norm](hyp:hF)
and [preserves the reference law P](hyp:hP), [applying it to a law Q cannot increase
Q's Wasserstein distance from P](goal). -/
lemma wasserstein_lawMapCLM_le {p m : ℕ}
    (F : Observation p m →L[ℝ] Observation p m) (hF : ∀ z, ‖F z‖ = ‖z‖)
    (P Q : JointLaws p m) (hP : Measure.map F (lawMeasure P) = lawMeasure P) :
    wassersteinDistance P (lawMapCLM F Q) ≤ wassersteinDistance P Q := by
  obtain ⟨pi₀⟩ := couplings_nonempty P Q
  change wassersteinDistance P (lawMapCLM F Q) ≤
    sInf {c : ℝ | ∃ pi : Couplings P Q, couplingCost pi.val = c}
  refine le_csInf (s := {c : ℝ | ∃ pi : Couplings P Q, couplingCost pi.val = c})
    ⟨couplingCost pi₀.val, pi₀, rfl⟩ ?_
  rintro c ⟨pi, rfl⟩
  let gamma := pi.val.map (f := fun z => (F z.1, F z.2)) (by fun_prop)
  have hg : Measure.map Prod.fst (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure P ∧
      Measure.map Prod.snd (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure (lawMapCLM F Q) := by
    constructor
    · simp only [gamma, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      change Measure.map (F ∘ Prod.fst) _ = _
      rw [← Measure.map_map (by fun_prop) (by fun_prop), pi.property.1, hP]
    · simp only [gamma, ProbabilityMeasure.toMeasure_map, lawMapCLM_measure]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      change Measure.map (F ∘ Prod.snd) _ = _
      rw [← Measure.map_map (by fun_prop) (by fun_prop), pi.property.2]
  have hc : couplingCost gamma = couplingCost pi.val := by
    unfold couplingCost
    rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
    simp only [← map_sub, hF]
  exact (wasserstein_le_couplingCost P (lawMapCLM F Q) ⟨gamma, hg⟩).trans_eq hc

-- @node: observation_norm_sq_blocks
/-- [An observation's squared Euclidean norm is the sum of the squared norms of
its feature and response vectors](goal). -/
lemma observation_norm_sq_blocks {p m : ℕ} (z : Observation p m) :
    ‖z‖ ^ 2 = ‖feature z‖ ^ 2 + ‖response z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, feature, response, Fin.sum_univ_add]

-- @node: blockAction_norm
/-- [Applying orthogonal transformations separately to an observation's feature
and response vectors preserves the observation's Euclidean norm](goal). -/
lemma blockAction_norm {p m : ℕ} (u : BlockOrth p m) (z : Observation p m) :
    ‖matrixCLM (blockActionMatrix u) z‖ = ‖z‖ := by
  have hb := blockAction_feature_response u z
  have hs : ‖matrixCLM (blockActionMatrix u) z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [observation_norm_sq_blocks, hb.1, hb.2,
      orthogonal_matrixCLM_norm, orthogonal_matrixCLM_norm, ← observation_norm_sq_blocks]
  nlinarith [norm_nonneg (matrixCLM (blockActionMatrix u) z), norm_nonneg z]

-- @node: risk_lawMapCLM_blockAction
/-- [Risk at a coefficient under a block-orthogonally transformed law equals risk
under the original law at the coefficient multiplied on the left by the transposed
response block and on the right by the feature block](goal). -/
lemma risk_lawMapCLM_blockAction {p m : ℕ} (u : BlockOrth p m) (Q : JointLaws p m)
    (A : Mat m p) :
    risk A (lawMapCLM (matrixCLM (blockActionMatrix u)) Q) =
      risk (u.2.val.transpose * A * u.1.val) Q := by
  have hi :=
    (loss_integrable A (lawMapCLM (matrixCLM (blockActionMatrix u)) Q)).aestronglyMeasurable
  unfold risk
  rw [lawMapCLM_measure] at hi ⊢
  rw [integral_map (by fun_prop) hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (orthogonal_loss_transform u A))

-- @node: coefficientOrbit_surjective
/-- For any fixed pair of orthogonal feature and response transformations,
[every coefficient matrix can be obtained from some coefficient matrix by multiplying
on the left by the transposed response block and on the right by the feature block](goal). -/
lemma coefficientOrbit_surjective {p m : ℕ} (u : BlockOrth p m) :
    Function.Surjective (fun A : Mat m p => u.2.val.transpose * A * u.1.val) := by
  intro A
  refine ⟨u.2.val * A * u.1.val.transpose, ?_⟩
  have hy : u.2.val.transpose * u.2.val = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp u.2.property
  have hx : u.1.val.transpose * u.1.val = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mp u.1.property
  simp only [Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hy, Matrix.one_mul]

-- @node: regret_lawMapCLM_blockAction
/-- [Regret at a coefficient under a block-orthogonally transformed law equals regret
under the original law at the coefficient multiplied on the left by the transposed
response block and on the right by the feature block](goal). -/
lemma regret_lawMapCLM_blockAction {p m : ℕ} (u : BlockOrth p m) (Q : JointLaws p m)
    (A : Mat m p) :
    regret A (lawMapCLM (matrixCLM (blockActionMatrix u)) Q) =
      regret (u.2.val.transpose * A * u.1.val) Q := by
  unfold regret
  simp_rw [risk_lawMapCLM_blockAction]
  congr 1
  change sInf (Set.range (fun B : Mat m p => risk (u.2.val.transpose * B * u.1.val) Q)) =
    sInf (Set.range (fun B : Mat m p => risk B Q))
  congr 1
  ext t
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨u.2.val.transpose * B * u.1.val, rfl⟩
  · rintro ⟨B, rfl⟩
    obtain ⟨C, hC⟩ := coefficientOrbit_surjective u B
    exact ⟨C, congrArg (fun D => risk D Q) hC⟩

/-- For any joint law with finite second moments, [regret is continuous as a
function of the coefficient matrix](goal). -/
@[fun_prop] lemma regret_continuous_coefficient {p m : ℕ} (P : JointLaws p m) :
    Continuous (fun A : Mat m p => regret A P) := by
  unfold regret
  fun_prop

-- @node: averageCoefficient_regret_le_integral
/-- If [the subgroup of block orthogonal transformations is compact](hyp:hU),
[regret at the Haar-averaged coefficient is at most the Haar average of regret at
the transformed coefficients](goal), for any joint law with finite second moments. -/
lemma averageCoefficient_regret_le_integral {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m) (A : Mat m p) :
    regret (averageCoefficient U hU A) P ≤
      ∫ u : U, regret (u.val.2.val.transpose * A * u.val.1.val) P ∂normalizedHaar U hU := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  have hc : Continuous (fun u : U => risk (u.val.2.val.transpose * A * u.val.1.val) P) := by
    fun_prop
  have hi := hc.integrable_of_hasCompactSupport (μ := normalizedHaar U hU)
    (HasCompactSupport.of_compactSpace _)
  simp only [regret]
  rw [integral_sub hi (integrable_const _)]
  simpa using sub_le_sub_right (averageCoefficient_risk_le_integral U hU P A)
    (⨅ B : Mat m p, risk B P)

-- @node: ofReal_integral_le_ennreal_bound
/-- For a probability measure and [an extended nonnegative real bound B](hyp:B), if [a real-valued function is integrable](hyp:hf)
and [each value, converted to an extended nonnegative real by truncating negative
values to zero, is at most B](hyp:hB), [its integral, converted in the same way,
is also at most B](goal). -/
lemma ofReal_integral_le_ennreal_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ) (B : ℝ≥0∞)
    (hB : ∀ x, ENNReal.ofReal (f x) ≤ B) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ B := by
  by_cases hb : B = ∞
  · rw [hb]; exact le_top
  apply ENNReal.ofReal_le_of_le_toReal
  calc
    (∫ x, f x ∂μ) ≤ ∫ _, B.toReal ∂μ :=
      integral_mono hf (integrable_const _)
        (fun x => (ENNReal.ofReal_le_iff_le_toReal hb).mp (hB x))
    _ = B.toReal := by simp

-- @node: averageCoefficient_worstRisk_le
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the reference law](hyp:hP), [Haar averaging
a coefficient cannot increase its supremum risk over the Wasserstein ball of the
given nonnegative radius around that law, with risks viewed as extended nonnegative
reals](goal). -/
lemma averageCoefficient_worstRisk_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) (eps : ℝ≥0) :
    (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (risk (averageCoefficient U hU A) Q)) ≤
      ⨆ Q ∈ lawBall P eps, ENNReal.ofReal (risk A Q) := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  refine iSup₂_le fun Q hQ => (ENNReal.ofReal_le_ofReal
    (averageCoefficient_risk_le_integral U hU Q A)).trans ?_
  have hc : Continuous (fun u : U => risk (u.val.2.val.transpose * A * u.val.1.val) Q) := by
    fun_prop
  apply ofReal_integral_le_ennreal_bound _ _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro u
  let Q' := lawMapCLM (matrixCLM (blockActionMatrix u.val)) Q
  have hQ' : Q' ∈ lawBall P eps :=
    (wasserstein_lawMapCLM_le _ (blockAction_norm u.val) P Q (hP u)).trans hQ
  rw [← risk_lawMapCLM_blockAction]
  exact le_iSup₂_of_le Q' hQ' le_rfl

-- @node: averageCoefficient_worstRegret_le
/-- For [a nonnegative Wasserstein radius](hyp:eps), if [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the reference law](hyp:hP), [Haar averaging
a coefficient cannot increase its supremum regret over the Wasserstein ball of the
given nonnegative radius around that law, with regrets viewed as extended nonnegative
reals](goal). -/
lemma averageCoefficient_worstRegret_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) (eps : ℝ≥0) :
    (⨆ Q ∈ lawBall P eps, ENNReal.ofReal (regret (averageCoefficient U hU A) Q)) ≤
      ⨆ Q ∈ lawBall P eps, ENNReal.ofReal (regret A Q) := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : BorelSpace U := ⟨rfl⟩
  letI := normalizedHaar_probability U hU
  refine iSup₂_le fun Q hQ => (ENNReal.ofReal_le_ofReal
    (averageCoefficient_regret_le_integral U hU Q A)).trans ?_
  have hc : Continuous (fun u : U => regret (u.val.2.val.transpose * A * u.val.1.val) Q) := by
    fun_prop
  apply ofReal_integral_le_ennreal_bound _ _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro u
  let Q' := lawMapCLM (matrixCLM (blockActionMatrix u.val)) Q
  have hQ' : Q' ∈ lawBall P eps :=
    (wasserstein_lawMapCLM_le _ (blockAction_norm u.val) P Q (hP u)).trans hQ
  rw [← regret_lawMapCLM_blockAction]
  exact le_iSup₂_of_le Q' hQ' le_rfl

-- @node: averageCoefficient_objective_le
/-- For [a nonnegative radius governing the population objective](hyp:eps), if [the subgroup of block orthogonal transformations is compact](hyp:hU) and
[every subgroup transformation preserves the reference law](hyp:hP), [Haar averaging
a coefficient cannot increase any of the four population objectives at the given
nonnegative radius: risk, worst-case risk, worst-case regret, or risk plus the squared
radius times the squared operator norm](goal). -/
lemma averageCoefficient_objective_le {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) (eps : ℝ≥0) (o : Fin 4) :
    populationObjective o P eps (averageCoefficient U hU A) ≤ populationObjective o P eps A := by
  unfold populationObjective
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (averageCoefficient_risk_le U hU P hP A)
  · exact averageCoefficient_worstRisk_le U hU P hP A eps
  · exact averageCoefficient_worstRegret_le U hU P hP A eps
  · exact ENNReal.ofReal_le_ofReal (averageCoefficient_spectralRisk_le U hU P hP A eps)

-- @node: averageCoefficient_minimizer
/-- For [a nonnegative radius governing the population objective](hyp:eps), if [the subgroup of feature and response orthogonal transformations is compact](hyp:hU),
[every subgroup transformation preserves the reference law](hyp:hP), and
[a coefficient matrix globally minimizes the selected population objective at the given
nonnegative radius](hyp:hA), then [its Haar-averaged coefficient also globally minimizes
that objective at the same law and radius](goal). -/
lemma averageCoefficient_minimizer {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (hU : assDroSymmetryCompactGroup U) (P : JointLaws p m)
    (hP : ∀ u : U,
      Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P)
    (A : Mat m p) (eps : ℝ≥0) (o : Fin 4) (hA : A ∈ populationMinimizers o P eps) :
    averageCoefficient U hU A ∈ populationMinimizers o P eps := by
  intro B hB
  exact (averageCoefficient_objective_le U hU P hP A eps o).trans (hA hB)

-- @node: lem:dro-symmetry
/-- For [a nonnegative radius governing the population objective](hyp:eps), in positive feature and response dimensions, suppose [the squared response norm
equals the sum of squared response coordinates](hyp:hpin), [the subgroup of feature
and response orthogonal transformations is compact](hyp:hU), [every subgroup
transformation preserves both the target law P and the source law tilde P](hyp:hinv),
and [the selected objective has nonzero index, the radius is strictly positive, and
the given coefficient globally minimizes that objective under tilde P](hyp:hmin).
Then [the Haar-averaged coefficient remains a global minimizer under tilde P, is
unchanged by every subgroup coefficient transformation, and has no greater regret
under P than the original coefficient; moreover, restricting coefficients to those
unchanged by the subgroup leaves the infimum of the objective under tilde P unchanged,
and every real lower bound on regret under P for invariant minimizers also holds for
all minimizers under tilde P](goal). -/
lemma droSymmetry {p m : ℕ} [NeZero p] [NeZero m] (hpin : assPin1 m)
    (U : Subgroup (BlockOrth p m)) (hU : assDroSymmetryCompactGroup U)
    (P tildeP : JointLaws p m) (hinv : assDroSymmetryInvariantLaws U P tildeP)
    (eps : ℝ≥0) (o : Fin 4) (Ahat : Mat m p)
    (hmin : assDroSymmetryMinimizer o tildeP eps Ahat) :
    let barA := averageCoefficient U hU Ahat
    barA ∈ populationMinimizers o tildeP eps ∧ invariantCoefficient U barA ∧
    regret barA P ≤ regret Ahat P ∧
    (⨅ A : Mat m p, populationObjective o tildeP eps A) =
      ⨅ (A : Mat m p) (_ : invariantCoefficient U A), populationObjective o tildeP eps A ∧
    (∀ b : ℝ,
      (∀ A ∈ populationMinimizers o tildeP eps, invariantCoefficient U A → b ≤ regret A P) →
      ∀ A ∈ populationMinimizers o tildeP eps, b ≤ regret A P) := by
  have htarget := fun u : U => (hinv u).1
  have hsource := fun u : U => (hinv u).2
  refine ⟨averageCoefficient_minimizer U hU tildeP hsource Ahat eps o hmin.2.2,
    averageCoefficient_invariant U hU Ahat,
    averageCoefficient_regret_le U hU P htarget Ahat, ?_, ?_⟩
  · apply le_antisymm
    · refine le_iInf fun A => le_iInf fun _ => ?_
      exact iInf_le_of_le A le_rfl
    · refine le_iInf fun A => ?_
      calc
        (⨅ (B : Mat m p) (_ : invariantCoefficient U B), populationObjective o tildeP eps B) ≤
            populationObjective o tildeP eps (averageCoefficient U hU A) :=
          iInf_le_of_le (averageCoefficient U hU A)
            (iInf_le_of_le (averageCoefficient_invariant U hU A) le_rfl)
        _ ≤ populationObjective o tildeP eps A :=
          averageCoefficient_objective_le U hU tildeP hsource A eps o
  · intro b hb A hA
    exact (hb (averageCoefficient U hU A)
      (averageCoefficient_minimizer U hU tildeP hsource A eps o hA)
      (averageCoefficient_invariant U hU A)).trans
      (averageCoefficient_regret_le U hU P htarget A)

end Papers.WassersteinRegretS2S3
