module
public import Papers.WassersteinRegretS2S3.Helpers.RealAttainment
public import Toolkit.Foundations.LinearAlgebra.Matrix.BlockContraction

/-!
# Population Wasserstein regret: Helpers/RealContraction

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

open scoped ComplexOrder

-- @node: realPart_sandwich
/-- [The real part of a complex matrix sandwiched between the complexifications
of real matrices R and S equals R times the real part of the middle matrix times S](goal). -/
lemma realPart_sandwich {n : ℕ} (R S : Mat n n) (L : Matrix (Fin n) (Fin n) ℂ) :
    realPart (complexify R * L * complexify S) = R * realPart L * S := by
  ext i j
  simp [realPart, complexify, Matrix.mul_apply, Complex.re_sum, Finset.sum_mul,
    Complex.mul_re]
-- @node: embedEuclidean_isometry
/-- [Embedding real Euclidean vectors as complex vectors with zero imaginary
coordinates preserves all distances](goal). -/
lemma embedEuclidean_isometry {n : ℕ} : Isometry (@embedEuclidean n) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, embedEuclidean, PiLp.sub_apply, ← Complex.ofReal_sub]
-- @node: realEuclidean_norm_le
/-- [The Euclidean norm of the coordinatewise real part of a complex vector is
at most the norm of that vector](goal). -/
lemma realEuclidean_norm_le {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    ‖realEuclidean z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  simpa [realEuclidean, Real.norm_eq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (z i)) 2
-- @node: realPart_action
/-- [Multiplying a real vector by the real part of a complex matrix gives the
real part of the complex matrix applied to the vector's complex embedding](goal). -/
lemma realPart_action {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) (x : Euc n) :
    matrixCLM (realPart L) x = realEuclidean (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) L
      (embedEuclidean x)) := by
  ext i
  change (∑ j, (L i j).re * x j) = (∑ j, L i j * (x j : ℂ)).re
  simp [Complex.re_sum, Complex.mul_re]
-- @node: realPart_opNorm_le
/-- [The real Euclidean operator norm of the real part of a complex square
matrix is at most its complex Euclidean operator norm](goal). -/
lemma realPart_opNorm_le {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) :
    opNorm (realPart L) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) L‖ := by
  unfold opNorm
  apply ContinuousLinearMap.opNorm_le_bound (matrixCLM (realPart L)) (norm_nonneg _)
  intro x
  rw [realPart_action]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) L (embedEuclidean x)‖ :=
      realEuclidean_norm_le _
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) L‖ * ‖embedEuclidean x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by
      rw [embedEuclidean_isometry.norm_map_of_map_zero
        (by ext i; simp [embedEuclidean]) x]
-- @node: complexify_psd_block
/-- If [the real block matrix with positive semidefinite diagonal blocks A and B
and off-diagonal blocks C and its transpose is positive semidefinite](hyp:hBlock),
then [the complex block matrix with diagonal blocks given by the complexifications
of A and B, upper-right block given by the complexification of C, and lower-left
block given by its conjugate transpose is positive semidefinite](goal). -/
lemma complexify_psd_block {n : ℕ} (A B : PSD n) (C : Mat n n)
    (hBlock : (Matrix.fromBlocks A.val C C.transpose B.val).PosSemidef) :
    (Matrix.fromBlocks (complexify A.val) (complexify C) (complexify C).conjTranspose
      (complexify B.val)).PosSemidef := by
  classical
  let H := Matrix.fromBlocks A.val C C.transpose B.val
  let S := CFC.sqrt H
  have hS : S.transpose * S = H := by
    rw [show S.transpose = S from (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self H hBlock.nonneg
  let T := S.map Complex.ofRealHom
  have hGram : T.conjTranspose * T = H.map Complex.ofRealHom := by
    rw [← hS, Matrix.map_mul]
    congr 1
    ext i j
    simp [T, Matrix.conjTranspose_apply]
  have h := Matrix.posSemidef_conjTranspose_mul_self T
  rw [hGram] at h
  convert h using 1
  ext i j
  cases i <;> cases j <;> simp [H, complexify, Matrix.conjTranspose_apply]


end Papers.WassersteinRegretS2S3
