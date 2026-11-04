module
public import Papers.WassersteinRegretS2S3.Helpers.DROConstruction
public import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# Gaussian pushforwards for the lower-bound symmetries

Linear images include singular covariance matrices. Commuting linear maps
preserve invariance after the deterministic feature contraction.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory ProbabilityTheory

-- @node: multivariateGaussian_map_matrixCLM
/-- For [a square linear transformation C](hyp:C) and [a covariance matrix S](hyp:S) that
[is positive semidefinite](hyp:hS), [transforming a centered Gaussian vector by C gives
a centered Gaussian law with covariance C times S times the transpose of C](goal). -/
lemma multivariateGaussian_map_matrixCLM {n : ℕ} (C S : Mat n n)
    (hS : S.PosSemidef) :
    Measure.map (matrixCLM C) (multivariateGaussian 0 S) =
      multivariateGaussian 0 (C * S * C.transpose) := by
  let L := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C
  change Measure.map L (multivariateGaussian 0 S) = _
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) IsGaussian.integrable_id.aestronglyMeasurable]
    calc
      (∫ x, L x ∂multivariateGaussian 0 S) =
          L (∫ x, x ∂multivariateGaussian 0 S) :=
        L.integral_comp_comm IsGaussian.integrable_id
      _ = ∫ x, id x ∂multivariateGaussian 0 (C * S * C.transpose) := by simp
  · have hop : L.adjoint = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.transpose := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      change star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C) = _
      rw [← map_star]
      rfl
    have hadj (u : Euc n) : L.adjoint u = WithLp.toLp 2 (C.transpose *ᵥ u.ofLp) := by
      rw [hop]
      rfl
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian]
    · rw [hadj, hadj]
      simp only [WithLp.ofLp_toLp]
      rw [Matrix.mulVec_transpose]
      nth_rewrite 1 [dotProduct_mulVec]
      rw [Matrix.vecMul_vecMul]
      rw [dotProduct_mulVec, Matrix.vecMul_vecMul]
      exact (Matrix.dotProduct_mulVec u.ofLp (C * S * C.transpose) v.ofLp).symm
    · exact hS.mul_mul_conjTranspose_same (B := C)

-- @node: gaussianLaw_invariant_of_secondMoment
/-- If [a joint law P](hyp:P) [is centered Gaussian with covariance equal to its second
moment](hyp:hP), and [a square linear transformation C](hyp:C) [preserves that second moment
under multiplication by C and its transpose](hyp:hC), then [applying C preserves P's
probability measure](goal). -/
lemma gaussianLaw_invariant_of_secondMoment {p m : ℕ} (P : JointLaws p m)
    (hP : lawMeasure P = multivariateGaussian 0 (secondMoment P))
    (C : Mat (p + m) (p + m))
    (hC : C * secondMoment P * C.transpose = secondMoment P) :
    Measure.map (matrixCLM C) (lawMeasure P) = lawMeasure P := by
  rw [hP, multivariateGaussian_map_matrixCLM C _ (secondMoment_posSemidef P), hC]

-- @node: lawMapCLM_invariant_of_commute
/-- For [a joint law P](hyp:P) and [square linear transformations C](hyp:C) and [D](hyp:D),
if [C and D commute](hyp:hCD) and [applying C preserves P's probability measure](hyp:hP),
then [applying C also preserves the probability measure obtained by transforming P by D](goal). -/
lemma lawMapCLM_invariant_of_commute {p m : ℕ} (P : JointLaws p m)
    (C D : Mat (p + m) (p + m)) (hCD : C * D = D * C)
    (hP : Measure.map (matrixCLM C) (lawMeasure P) = lawMeasure P) :
    Measure.map (matrixCLM C) (lawMeasure (lawMapCLM (matrixCLM D) P)) =
      lawMeasure (lawMapCLM (matrixCLM D) P) := by
  rw [lawMapCLM_measure, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (matrixCLM C) ∘ (matrixCLM D) = (matrixCLM D) ∘ (matrixCLM C) := by
    funext z
    simp only [Function.comp_apply, ← matrixCLM_mul_apply, hCD]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hP]

-- @node: blockActionMatrix_diagonal
/-- For [a pair u of orthogonal feature and response transformations](hyp:u), [feature
diagonal entries x](hyp:x), and [response diagonal entries y](hyp:y), if [the feature
transformation is diagonal with entries x](hyp:hx) and [the response transformation is
diagonal with entries y](hyp:hy), then [the joint block transformation is diagonal with
entries given by x followed by y](goal). -/
lemma blockActionMatrix_diagonal {p m : ℕ} (u : BlockOrth p m)
    (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : u.1.val = Matrix.diagonal x) (hy : u.2.val = Matrix.diagonal y) :
    blockActionMatrix u = Matrix.diagonal (Fin.addCases x y) := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  all_goals simp [blockActionMatrix, hx, hy, Matrix.diagonal_apply]
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

end Papers.WassersteinRegretS2S3
