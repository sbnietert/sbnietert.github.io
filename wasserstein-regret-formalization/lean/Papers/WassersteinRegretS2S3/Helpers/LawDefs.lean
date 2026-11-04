module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.CovarianceBilinDual
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Population Wasserstein regret: Helpers/LawDefs

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @env: S1
variable {p m : ℕ} [NeZero p] [NeZero m]

/-- A [joint observation](goal) is a Euclidean vector with
[a specified number of feature coordinates](hyp:p) followed by
[a specified number of response coordinates](hyp:m). -/
abbrev Observation (p m : ℕ) := Euc (p + m) -- @realizes Z(joint Euclidean observation)
/-- The [feature vector](goal) of [a joint observation](hyp:z) consists of its initial feature coordinates. -/
def feature {p m : ℕ} (z : Observation p m) : Euc p :=
  WithLp.toLp 2 (fun i => z (Fin.castAdd m i)) -- @realizes X(feature coordinates)
/-- The [response vector](goal) of [a joint observation](hyp:z) consists of its final response coordinates. -/
def response {p m : ℕ} (z : Observation p m) : Euc m :=
  WithLp.toLp 2 (fun i => z (Fin.natAdd p i)) -- @realizes Y(response coordinates)

-- @node: def:joint-laws
/-- The [class of joint laws](goal) for [a feature dimension](hyp:p) and
[a response dimension](hyp:m) consists of probability distributions of joint observations
with finite second moments. -/
structure JointLaws (p m : ℕ) where
  carrier : -- @realizes \cP_2(\R^d)(all finite uncentered)
    {P : ProbabilityMeasure (Observation p m) // MemLp id 2 (P : Measure (Observation p m))}

/-- The [underlying probability measure](goal) of [a joint law with finite second moments](hyp:P)
is the measure used to integrate functions of observations. -/
abbrev lawMeasure {p m : ℕ} (P : JointLaws p m) : Measure (Observation p m) := P.carrier.val
-- @realizes P(arbitrary finite second moment law)

-- @node: def:risk
/-- The [prediction risk](goal) of [a coefficient matrix](hyp:A) under
[a joint law](hyp:P) is the expected squared Euclidean distance between the linear prediction
and the response. -/
noncomputable def risk {p m : ℕ} (A : Mat m p) (P : JointLaws p m) : ℝ :=
  ∫ z, ‖matrixCLM A (feature z) - response z‖ ^ 2 ∂lawMeasure P
-- @realizes L(expected squared Euclidean prediction error)

-- @node: loss_integrable
/-- For [any linear coefficient matrix](hyp:A) and [any joint law with finite second moments](hyp:P),
[the squared Euclidean prediction error is integrable](goal). -/
lemma loss_integrable {p m : ℕ} (A : Mat m p) (P : JointLaws p m) :
    Integrable (fun z => ‖matrixCLM A (feature z) - response z‖ ^ 2) (lawMeasure P) := by
  let F : Observation p m →L[ℝ] Euc p :=
    (EuclideanSpace.equiv (Fin p) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (Fin.castAdd m i))
  let G : Observation p m →L[ℝ] Euc m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (Fin.natAdd p i))
  have hF : MemLp (fun z => feature z) 2 (lawMeasure P) :=
    P.carrier.property.continuousLinearMap_comp F
  have hG : MemLp (fun z => response z) 2 (lawMeasure P) :=
    P.carrier.property.continuousLinearMap_comp G
  exact ((hF.continuousLinearMap_comp (matrixCLM A)).sub hG).norm.integrable_sq

-- @node: def:regret
/-- The [regret](goal) of [a coefficient matrix](hyp:A) under [a joint law](hyp:P)
is its prediction risk minus the infimum of prediction risk over all linear coefficient matrices. -/
noncomputable def regret {p m : ℕ} (A : Mat m p) (P : JointLaws p m) : ℝ :=
  risk A P - ⨅ B : Mat m p, risk B P
-- @realizes R(risk minus infimum over all coefficient matrices)

-- @node: def:second-moment
/-- The [uncentered second-moment matrix](goal) of [a joint law](hyp:P)
has as each entry the expected product of the corresponding observation coordinates. -/
noncomputable def secondMoment {p m : ℕ} (P : JointLaws p m) : Mat (p + m) (p + m) :=
  fun i j => ∫ z, z i * z j ∂lawMeasure P
-- @realizes \bSigma_P(entrywise uncentered second moment)

/-- The [feature second-moment matrix](goal) of [a joint law](hyp:P)
is the feature-by-feature block of its uncentered second-moment matrix. -/
noncomputable abbrev secondMomentX {p m : ℕ} (P : JointLaws p m) := blockX p m (secondMoment P)
-- @realizes \bSigma_X^P(feature second moment)
/-- The [response second-moment matrix](goal) of [a joint law](hyp:P)
is the response-by-response block of its uncentered second-moment matrix. -/
noncomputable abbrev secondMomentY {p m : ℕ} (P : JointLaws p m) := blockY p m (secondMoment P)
-- @realizes \bSigma_Y^P(response second moment)
/-- The [feature-response cross-moment matrix](goal) of [a joint law](hyp:P)
records expected products with feature coordinates indexing rows and response coordinates indexing columns. -/
noncomputable abbrev secondMomentXY {p m : ℕ} (P : JointLaws p m) := blockXY p m (secondMoment P)
-- @realizes \bSigma_{XY}^P(raw cross second moment)
/-- The [response-feature cross-moment matrix](goal) of [a joint law](hyp:P)
records expected products with response coordinates indexing rows and feature coordinates indexing columns. -/
noncomputable abbrev secondMomentYX {p m : ℕ} (P : JointLaws p m) := blockYX p m (secondMoment P)
-- @realizes \bSigma_{YX}^P(transposed cross second moment)

-- @node: law_coordinate_memLp
/-- Under [a joint law with finite second moments](hyp:P),
[any observation coordinate](hyp:i) [has a finite second moment](goal). -/
lemma law_coordinate_memLp {p m : ℕ} (P : JointLaws p m) (i : Fin (p + m)) :
    MemLp (fun z : Observation p m => z i) 2 (lawMeasure P) :=
  P.carrier.property.continuousLinearMap_comp
    (EuclideanSpace.proj (𝕜 := ℝ) i : Observation p m →L[ℝ] ℝ)

-- @node: secondMoment_entry_integrable
/-- Under [a joint law with finite second moments](hyp:P), the product of
[any two observation coordinates](hyp:i,j) [is integrable](goal). -/
lemma secondMoment_entry_integrable {p m : ℕ} (P : JointLaws p m)
    (i j : Fin (p + m)) :
    Integrable (fun z : Observation p m => z i * z j) (lawMeasure P) :=
  (law_coordinate_memLp P i).integrable_mul (law_coordinate_memLp P j)

-- @node: secondMoment_posSemidef
/-- For [any joint law with finite second moments](hyp:P),
[the uncentered second-moment matrix is positive semidefinite](goal). -/
lemma secondMoment_posSemidef {p m : ℕ} (P : JointLaws p m) : (secondMoment P).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp [Matrix.conjTranspose_apply, secondMoment, mul_comm]
  · intro x
    have hquad : star x ⬝ᵥ (secondMoment P *ᵥ x) =
        ∫ z : Observation p m, (∑ i, x i * z i) ^ 2 ∂lawMeasure P := by
      calc
        _ = ∑ i, ∑ j, ∫ z : Observation p m,
            (x i * (z i * z j)) * x j ∂lawMeasure P := by
          simp only [dotProduct, mulVec, secondMoment, Finset.mul_sum,
            Pi.star_apply, star_trivial, integral_mul_const, integral_const_mul]
          simp only [mul_assoc]
        _ = ∫ z : Observation p m, ∑ i, ∑ j,
            (x i * (z i * z j)) * x j ∂lawMeasure P := by
          rw [integral_finsetSum _ (fun i _ =>
            integrable_finsetSum _ (fun j _ =>
              ((secondMoment_entry_integrable P i j).const_mul (x i)).mul_const (x j)))]
          apply Finset.sum_congr rfl
          intro i _
          exact (integral_finsetSum _ (fun j _ =>
            ((secondMoment_entry_integrable P i j).const_mul (x i)).mul_const (x j))).symm
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
/-- The [certified positive semidefinite moment matrix](goal) of [a joint law](hyp:P)
is its uncentered second-moment matrix together with its positive semidefiniteness guarantee. -/
noncomputable def momentPSD {p m : ℕ} (P : JointLaws p m) : PSD (p + m) :=
  ⟨secondMoment P, secondMoment_posSemidef P⟩

-- @node: def:nondegenerate-laws
/-- The [class of nondegenerate joint laws](goal) for [a feature dimension](hyp:p)
and [a response dimension](hyp:m) consists of finite-second-moment probability laws
whose feature second-moment matrix is positive definite. -/
structure NondegenerateLaws (p m : ℕ) where
  carrier : -- @realizes \cP^*(positive definite feature)
    {P : JointLaws p m // (secondMomentX P).PosDef}

-- @node: def:optimal-predictor
/-- The [optimal linear prediction coefficient](goal) for [a nondegenerate joint law](hyp:P)
is its response-feature cross-moment matrix multiplied by the inverse feature second-moment matrix. -/
noncomputable def optimalPredictor {p m : ℕ} (P : NondegenerateLaws p m) : Mat m p :=
  secondMomentYX P.carrier.val * (secondMomentX P.carrier.val)⁻¹
-- @realizes \bA_P(unique nondegenerate risk minimizer)

-- @node: def:residual-second-moment
/-- The [residual second-moment matrix](goal) for [a nondegenerate joint law](hyp:P)
records the expected products of response residuals from its optimal linear predictor. -/
noncomputable def residualSecondMoment {p m : ℕ} (P : NondegenerateLaws p m) : Mat m m :=
  fun i j => ∫ z,
    (response z - matrixCLM (optimalPredictor P) (feature z)) i *
    (response z - matrixCLM (optimalPredictor P) (feature z)) j ∂lawMeasure P.carrier.val
-- @realizes \bSigma_E^P(uncentered residual second moment)

/-- The [couplings](goal) of [a first joint law](hyp:P) and [a second joint law](hyp:Q)
are probability distributions on pairs of observations whose first and second marginals
are those respective laws. -/
abbrev Couplings {p m : ℕ} (P Q : JointLaws p m) :=
  {pi : ProbabilityMeasure (Observation p m × Observation p m) //
    Measure.map Prod.fst (pi : Measure (Observation p m × Observation p m)) = lawMeasure P ∧
    Measure.map Prod.snd (pi : Measure (Observation p m × Observation p m)) = lawMeasure Q}
-- @realizes \Pi(P,Q)(probability couplings with exact marginals)

/-- The [transport cost](goal) of [a probability distribution on observation pairs](hyp:pi)
is the square root of the expected squared Euclidean distance between the paired observations. -/
noncomputable def couplingCost {p m : ℕ}
    (pi : ProbabilityMeasure (Observation p m × Observation p m)) : ℝ :=
  Real.sqrt (∫ z : Observation p m × Observation p m, ‖z.1 - z.2‖ ^ 2 ∂(pi : Measure
    (Observation p m × Observation p m)))

-- @node: def:wasserstein-distance
/-- The [quadratic Wasserstein distance](goal) between [a first joint law](hyp:P)
and [a second joint law](hyp:Q) is the infimum of root mean squared transport costs
over all couplings of the two laws. -/
noncomputable def wassersteinDistance {p m : ℕ} (P Q : JointLaws p m) : ℝ :=
  sInf {c : ℝ | ∃ pi : Couplings P Q, couplingCost pi.val = c}
-- @realizes \Wtwo(infimum root mean square coupling cost)

-- @node: def:wasserstein-ball
/-- The [Wasserstein ball](goal) centered at [a joint law](hyp:P) with
[a nonnegative radius](hyp:eps) consists of finite-second-moment joint laws whose
quadratic Wasserstein distance from the center is at most that radius. -/
structure WassersteinBall {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) where
  carrier : -- @realizes \cB_\eps(P)(all finite second) @realizes Q(arbitrary law in)
    {Q : JointLaws p m // wassersteinDistance P Q ≤ eps}

-- @node: ass:pin-1
/-- The [Euclidean norm identity](goal) in [a given dimension](hyp:m) asserts that
every vector's squared norm equals the sum of its squared coordinates. -/
def assPin1 (m : ℕ) : Prop := ∀ v : Euc m, ‖v‖ ^ 2 = ∑ i, v i * v i

-- @node: assPin1_valid
/-- In [any dimension](hyp:m), [every Euclidean vector's squared norm equals the sum
of its squared coordinates](goal). -/
lemma assPin1_valid (m : ℕ) : assPin1 m := by
  intro v
  simpa only [pow_two] using EuclideanSpace.real_norm_sq_eq v

-- @node: dilation_measurable
/-- For [any real scaling factor](hyp:a), [uniform scaling of Euclidean vectors is measurable](goal). -/
@[fun_prop] lemma dilation_measurable {n : ℕ} (a : ℝ) : Measurable (fun z : Euc n => a • z) :=
  by fun_prop
-- @node: dilation_memLp
/-- For [a joint law with finite second moments](hyp:P) and [any real scaling factor](hyp:a),
[the law obtained by scaling every observation still has finite second moments](goal). -/
lemma dilation_memLp {p m : ℕ} (P : JointLaws p m) (a : ℝ) :
    MemLp id 2 ((P.carrier.val.map (dilation_measurable a).aemeasurable) : Measure (Observation
      p m)) := by
  change MemLp id 2 (Measure.map (fun z : Observation p m => a • z) (lawMeasure P))
  rw [memLp_map_measure_iff (by fun_prop) (dilation_measurable a).aemeasurable]
  exact P.carrier.property.const_smul a
/-- The [dilated joint law](goal) for [a real scaling factor](hyp:a) and
[a joint law with finite second moments](hyp:P) is the distribution obtained by
multiplying every feature and response coordinate by that factor. -/
noncomputable def dilateLaw {p m : ℕ} (a : ℝ) (P : JointLaws p m) : JointLaws p m :=
  ⟨⟨P.carrier.val.map (dilation_measurable a).aemeasurable, dilation_memLp P a⟩⟩
-- @realizes P_\lambda(pushforward under uniform dilation)
-- @realizes Q_\lambda(pushforward under uniform dilation)

end Papers.WassersteinRegretS2S3
