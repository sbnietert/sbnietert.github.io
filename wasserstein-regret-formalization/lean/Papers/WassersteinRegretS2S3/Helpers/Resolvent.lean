module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Population Wasserstein regret: Helpers/Resolvent

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal

open scoped Matrix.Norms.L2Operator

-- @node: resolvent_isUnit
/-- For [a square matrix A of positive dimension](hyp:A) and [a real number
eta](hyp:eta), if [the Euclidean operator norm of A is less than eta](hyp:heta),
then [eta times the identity minus A is invertible](goal). -/
lemma resolvent_isUnit {n : ℕ} [NeZero n] (A : Mat n n) (eta : ℝ)
    (heta : ‖A‖ < eta) : IsUnit (eta • (1 : Mat n n) - A) := by
  have hpos : 0 < eta := lt_of_le_of_lt (norm_nonneg A) heta
  have h := spectrum.mem_resolventSet_of_norm_lt (𝕜 := ℝ) (a := A) (k := eta)
    (by simpa only [Real.norm_eq_abs, abs_of_pos hpos] using heta)
  simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] using h

-- @node: lem:rectangular-resolvent-identities
/-- For [a rectangular matrix M with positive row and column counts](hyp:M)
and [a real number eta](hyp:eta) such that [the squared Euclidean operator norm
of M is less than eta](hyp:heta), [the inverse of eta times the identity minus
the column Gram matrix, multiplied by the transpose of M, equals that
transpose times the analogous row-Gram inverse; M times the column-Gram
inverse equals the row-Gram inverse times M; the column Gram matrix times
its shifted inverse equals the transpose of M times the row-Gram inverse
times M; and eta times the column-Gram inverse equals the identity plus
that same product](goal). -/
lemma rectangularResolventIdentities {r d : ℕ} [NeZero r] [NeZero d]
    (M : Mat r d) (eta : ℝ) (heta : assRectangularResolventIdentitiesEta M eta) :
    (eta • (1 : Mat d d) - M.transpose * M)⁻¹ * M.transpose =
      M.transpose * (eta • (1 : Mat r r) - M * M.transpose)⁻¹ ∧
    M * (eta • (1 : Mat d d) - M.transpose * M)⁻¹ =
      (eta • (1 : Mat r r) - M * M.transpose)⁻¹ * M ∧
    M.transpose * M * (eta • (1 : Mat d d) - M.transpose * M)⁻¹ =
      M.transpose * (eta • (1 : Mat r r) - M * M.transpose)⁻¹ * M ∧
    eta • (eta • (1 : Mat d d) - M.transpose * M)⁻¹ =
      1 + M.transpose * (eta • (1 : Mat r r) - M * M.transpose)⁻¹ * M  := by
  have hnorm : ‖M‖ ^ 2 < eta := heta
  have ht : ‖M.transpose‖ = ‖M‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using M.l2_opNorm_conjTranspose
  have hd : IsUnit (eta • (1 : Mat d d) - M.transpose * M) :=
    resolvent_isUnit _ eta (lt_of_le_of_lt
      (by simpa only [ht, pow_two] using Matrix.l2_opNorm_mul M.transpose M) hnorm)
  have hr : IsUnit (eta • (1 : Mat r r) - M * M.transpose) :=
    resolvent_isUnit _ eta (lt_of_le_of_lt
      (by simpa only [ht, pow_two] using Matrix.l2_opNorm_mul M M.transpose) hnorm)
  let D := eta • (1 : Mat d d) - M.transpose * M
  let R := eta • (1 : Mat r r) - M * M.transpose
  have hd' : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det _).mp hd
  have hr' : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hr
  have hcomm : D * M.transpose = M.transpose * R := by
    dsimp [D, R]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hfirst : D⁻¹ * M.transpose = M.transpose * R⁻¹ := by
    have h := congrArg (fun X => D⁻¹ * X * R⁻¹) hcomm
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left D _ hd',
      Matrix.mul_nonsing_inv R hr', Matrix.mul_one] using h.symm
  have hcomm' : M * D = R * M := by
    dsimp [D, R]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hsecond : M * D⁻¹ = R⁻¹ * M := by
    have h := congrArg (fun X => R⁻¹ * X * D⁻¹) hcomm'
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left R _ hr',
      Matrix.mul_nonsing_inv D hd', Matrix.mul_one] using h.symm
  have hthird : M.transpose * M * D⁻¹ = M.transpose * R⁻¹ * M := by
    simpa only [Matrix.mul_assoc] using congrArg (fun X => M.transpose * X) hsecond
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  have h := Matrix.mul_nonsing_inv D hd'
  change (eta • (1 : Mat d d) - M.transpose * M) * D⁻¹ = 1 at h
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
  change eta • D⁻¹ = 1 + M.transpose * R⁻¹ * M
  rw [← hthird]
  exact sub_eq_iff_eq_add.mp h


end Papers.WassersteinRegretS2S3
