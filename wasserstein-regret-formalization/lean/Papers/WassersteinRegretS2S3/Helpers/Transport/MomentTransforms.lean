module
public import Papers.WassersteinRegretS2S3.Helpers.Transport.Couplings
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Second moments of linear transformations

Coordinate integral identities used in the singular completion construction.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: integral_linear_secondMoment
/-- For [a measure](hyp:μ), [a Euclidean-vector-valued function](hyp:f) that
[has finite second moment](hyp:hf), [a linear transformation matrix](hyp:A),
and [two output coordinates](hyp:i,j), [the integral of the product of the
transformed coordinates equals the corresponding entry of the original
second-moment matrix multiplied on the left by the transformation matrix
and on the right by its transpose](goal). -/
lemma integral_linear_secondMoment {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (f : Ω → Euc n) (hf : MemLp f 2 μ) (A : Mat k n) (i j : Fin k) :
    (∫ z, matrixCLM A (f z) i * matrixCLM A (f z) j ∂μ) =
      (A * (Matrix.of (fun a b => ∫ z, f z a * f z b ∂μ)) * A.transpose) i j := by
  have hc (a : Fin n) : MemLp (fun z => f z a) 2 μ :=
    hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) a : Euc n →L[ℝ] ℝ)
  have hi (a b : Fin n) : Integrable (fun z => A i a * (f z a * f z b) * A j b) μ :=
    (((hc a).integrable_mul (hc b)).const_mul _).mul_const _
  calc
    _ = ∫ z, ∑ a, ∑ b, A i a * (f z a * f z b) * A j b ∂μ := by
      congr 1
      funext z
      change (A *ᵥ (f z).ofLp) i * (A *ᵥ (f z).ofLp) j = _
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, ∫ z, A i a * (f z a * f z b) * A j b ∂μ := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum _ (fun b _ => hi a b)
    _ = _ := by
      simp only [integral_mul_const, integral_const_mul, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]

-- @node: integral_norm_sq_linear
/-- For [a measure](hyp:μ), [a Euclidean-vector-valued function](hyp:f) that
[has finite second moment](hyp:hf), and [a linear transformation matrix](hyp:A),
[the integral of the squared norm of the transformed function equals the
trace of the original second-moment matrix multiplied on the left by the
transformation matrix and on the right by its transpose](goal). -/
lemma integral_norm_sq_linear {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (f : Ω → Euc n) (hf : MemLp f 2 μ) (A : Mat k n) :
    (∫ z, ‖matrixCLM A (f z)‖ ^ 2 ∂μ) =
      Matrix.trace (A * (Matrix.of (fun a b => ∫ z, f z a * f z b ∂μ)) * A.transpose) := by
  have hc (i : Fin k) : MemLp (fun z => matrixCLM A (f z) i) 2 μ :=
    (hf.continuousLinearMap_comp (matrixCLM A)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) i : Euc k →L[ℝ] ℝ)
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [integral_finsetSum _ (fun i _ => (hc i).integrable_sq)]
  simp only [sq]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_linear_secondMoment μ f hf A i i

-- @node: linear_ae_zero_of_secondMoment
/-- For [a measure](hyp:μ), [a Euclidean-vector-valued function](hyp:f) that
[has finite second moment](hyp:hf), and [a linear transformation matrix](hyp:A),
if [multiplying the function's second-moment matrix on the left by the
transformation matrix and on the right by its transpose gives zero](hyp:hA),
[the transformed function is zero almost everywhere under the measure](goal). -/
lemma linear_ae_zero_of_secondMoment {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (f : Ω → Euc n) (hf : MemLp f 2 μ) (A : Mat k n)
    (hA : A * (Matrix.of (fun a b => ∫ z, f z a * f z b ∂μ)) * A.transpose = 0) :
    ∀ᵐ z ∂μ, matrixCLM A (f z) = 0 := by
  have hi := (hf.continuousLinearMap_comp (matrixCLM A)).norm.integrable_sq
  have hz : (∫ z, ‖matrixCLM A (f z)‖ ^ 2 ∂μ) = 0 := by
    rw [integral_norm_sq_linear μ f hf A, hA, Matrix.trace_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hi).mp hz
  filter_upwards [hae] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

-- @node: gaussian_coordinate_mean_zero
/-- For [a square real matrix specifying a zero-mean multivariate Gaussian
measure](hyp:S) and [a coordinate](hyp:i), [the integral of that coordinate
under this measure is zero](goal). -/
lemma gaussian_coordinate_mean_zero {n : ℕ} (S : Mat n n) (i : Fin n) :
    (∫ z : Euc n, z i ∂ProbabilityTheory.multivariateGaussian 0 S) = 0 := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i : Euc n →L[ℝ] ℝ).integral_comp_id_comm
    (μ := ProbabilityTheory.multivariateGaussian 0 S) ProbabilityTheory.IsGaussian.integrable_id
  simpa using h

-- @node: gaussian_coordinate_secondMoment
/-- For [a square real matrix](hyp:S) that [is positive semidefinite](hyp:hS)
and [two coordinates](hyp:i,j), [the expected product of these coordinates
under the zero-mean Gaussian with this covariance matrix equals the
corresponding matrix entry](goal). -/
lemma gaussian_coordinate_secondMoment {n : ℕ} (S : Mat n n) (hS : S.PosSemidef)
    (i j : Fin n) :
    (∫ z : Euc n, z i * z j ∂ProbabilityTheory.multivariateGaussian 0 S) = S i j := by
  have hc (i : Fin n) : MemLp (fun z : Euc n => z i) 2
      (ProbabilityTheory.multivariateGaussian 0 S) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) i : Euc n →L[ℝ] ℝ)
  have h := ProbabilityTheory.covariance_eval_multivariateGaussian (μ := (0 : Euc n)) hS i j
  rw [ProbabilityTheory.covariance_eq_sub (hc i) (hc j)] at h
  simpa only [gaussian_coordinate_mean_zero, zero_mul, sub_zero, Pi.mul_apply] using h

-- @node: integral_prod_add_secondMoment
/-- For [a probability measure on an underlying sample space](hyp:μ),
[a probability measure on Euclidean vectors](hyp:ν), and [a Euclidean-vector-valued
function on the first space](hyp:f), assume [the function has finite second
moment under the first measure](hyp:hf), [the vectors have finite second
moment under the second measure](hyp:hg), and [each coordinate has mean zero
under the second measure](hyp:hmean). For [two coordinates](hyp:i,j), [the
second cross moment of the sum of the function and an independent vector,
under the product measure, equals the sum of their individual second cross moments](goal). -/
lemma integral_prod_add_secondMoment {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (Euc n)) [IsProbabilityMeasure ν]
    (f : Ω → Euc n) (hf : MemLp f 2 μ) (hg : MemLp id 2 ν)
    (hmean : ∀ i, (∫ w : Euc n, w i ∂ν) = 0) (i j : Fin n) :
    (∫ z : Ω × Euc n, (f z.1 + z.2) i * (f z.1 + z.2) j ∂μ.prod ν) =
      (∫ x, f x i * f x j ∂μ) + (∫ w : Euc n, w i * w j ∂ν) := by
  have hc (i : Fin n) : MemLp (fun x => f x i) 2 μ :=
    hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i : Euc n →L[ℝ] ℝ)
  have hd (i : Fin n) : MemLp (fun w : Euc n => w i) 2 ν :=
    hg.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i : Euc n →L[ℝ] ℝ)
  have ha := (hc i).comp_fst ν
  have hb := (hc j).comp_fst ν
  have he := (hd i).comp_snd μ
  have hh := (hd j).comp_snd μ
  calc
    _ = ∫ z : Ω × Euc n, ((f z.1 i * f z.1 j + f z.1 i * z.2 j) +
        f z.1 j * z.2 i) + z.2 i * z.2 j ∂μ.prod ν := by
      congr 1
      funext z
      simp only [PiLp.add_apply]
      ring
    _ = _ := by
      have h1 := integral_add ((ha.integrable_mul hb).add (ha.integrable_mul hh) |>.add
          (hb.integrable_mul he)) (he.integrable_mul hh)
      have h2 := integral_add ((ha.integrable_mul hb).add (ha.integrable_mul hh)) (hb.integrable_mul he)
      have h3 := integral_add (ha.integrable_mul hb) (ha.integrable_mul hh)
      simp only [Pi.add_apply, Pi.mul_apply] at h1 h2 h3
      rw [h1, h2, h3]
      rw [integral_prod_mul (fun x => f x i) (fun w : Euc n => w j),
        integral_prod_mul (fun x => f x j) (fun w : Euc n => w i)]
      simp only [hmean, mul_zero, add_zero]
      rw [integral_fun_fst (fun x => f x i * f x j),
        integral_fun_snd (fun w : Euc n => w i * w j)]
      simp

end Papers.WassersteinRegretS2S3
