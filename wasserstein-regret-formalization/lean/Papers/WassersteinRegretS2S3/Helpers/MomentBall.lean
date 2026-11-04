module
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.Convex.Mul

/-!
# Compact convex moment balls and the matrix risk

The block Gram certificate is the second-moment form of mixing transport couplings.
It applies to singular moments and to radius zero.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: frob_eq_matrix_norm
/-- For [a real rectangular matrix A](hyp:A), [its Frobenius norm equals its matrix norm](goal). -/
lemma frob_eq_matrix_norm {a b : ℕ} (A : Mat a b) : frob A = ‖A‖ := by
  simp [frob, Matrix.frobenius_norm_def, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

-- @node: bures_ball_compact
/-- For [a positive semidefinite center B](hyp:B) and [a nonnegative radius](hyp:eps),
[the set of positive semidefinite matrices within that Bures distance of B is compact](goal). -/
lemma bures_ball_compact {n : ℕ} (B : PSD n) (eps : ℝ≥0) :
    IsCompact {A : Mat n n | A.PosSemidef ∧ buresDistance A B.val ≤ eps} := by
  have heq : {A : Mat n n | A.PosSemidef ∧ buresDistance A B.val ≤ eps} =
      (fun D : Mat n n => (CFC.sqrt B.val + D) * (CFC.sqrt B.val + D).transpose) ''
        Metric.closedBall 0 (eps : ℝ) := by
    ext A
    constructor
    · rintro ⟨hA, hd⟩
      obtain ⟨D, hD, he⟩ := ((buresProcrustes ⟨A, hA⟩ B).2.2.1 eps).mp hd
      exact ⟨D, by simpa [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using hD,
        he.symm⟩
    · rintro ⟨D, hD, rfl⟩
      have hA : ((CFC.sqrt B.val + D) * (CFC.sqrt B.val + D).transpose).PosSemidef :=
        Matrix.posSemidef_self_mul_conjTranspose _
      refine ⟨hA, ((buresProcrustes ⟨_, hA⟩ B).2.2.1 eps).mpr ⟨D, ?_, rfl⟩⟩
      simpa [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using hD
  rw [heq]
  apply (isCompact_closedBall (0 : Mat n n) (eps : ℝ)).image
  fun_prop

-- @node: gram_difference_trace
/-- For [two real rectangular matrices S and T of the same dimensions](hyp:S,T),
[the squared Frobenius distance between them equals the trace of S times its transpose
plus the trace of T times its transpose, minus twice the trace of S times the transpose of T](goal). -/
lemma gram_difference_trace {n r : ℕ} (S T : Mat n r) :
    frob (S - T) ^ 2 = Matrix.trace (S * S.transpose) +
      Matrix.trace (T * T.transpose) - 2 * Matrix.trace (S * T.transpose) := by
  rw [frob_sq_trace_rows]
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  have htr : Matrix.trace (T * S.transpose) = Matrix.trace (S * T.transpose) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [htr]
  ring

-- @node: bures_ball_block_certificate
/-- For [positive semidefinite matrices A and B](hyp:A,B) and [a nonnegative radius](hyp:eps),
[their Bures distance is at most the radius if and only if there is a cross block C
such that the block matrix with diagonal blocks A and B and off-diagonal blocks C and
its transpose is positive semidefinite, and the sum of the traces of A and B minus
twice the trace of C is at most the squared radius](goal). -/
lemma bures_ball_block_certificate {n : ℕ} (A B : PSD n) (eps : ℝ≥0) :
    buresDistance A.val B.val ≤ eps ↔
      ∃ C : Mat n n, (Matrix.fromBlocks A.val C C.transpose B.val).PosSemidef ∧
        Matrix.trace A.val + Matrix.trace B.val - 2 * Matrix.trace C ≤ (eps : ℝ) ^ 2 := by
  constructor
  · intro hd
    obtain ⟨S, T, hS, hT, hc⟩ := (buresProcrustes A B).2.1.1
    refine ⟨S * T.transpose, ?_, ?_⟩
    · have h := Matrix.posSemidef_self_mul_conjTranspose (Matrix.fromRows S T)
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_fromRows,
        Matrix.fromRows_mul_fromCols, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← hS, ← hT] using h
    · have he := gram_difference_trace S T
      rw [← hS, ← hT, hc] at he
      rw [← he]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hd 2
  · rintro ⟨C, hC, hb⟩
    have ht := trace_block_cross_le A B C hC
    have hs := bures_distance_sq A B
    have hsq : buresDistance A.val B.val ^ 2 ≤ (eps : ℝ) ^ 2 := by
      rw [hs]
      linarith
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) eps.property).mp hsq

-- @node: bures_ball_convex
/-- For [a positive semidefinite center B](hyp:B) and [a nonnegative radius](hyp:eps),
[the set of positive semidefinite matrices within that Bures distance of B is convex](goal). -/
lemma bures_ball_convex {n : ℕ} (B : PSD n) (eps : ℝ≥0) :
    Convex ℝ {A : Mat n n | A.PosSemidef ∧ buresDistance A B.val ≤ eps} := by
  intro A hA D hD a b ha hb hab
  have hM : (a • A + b • D).PosSemidef := (hA.1.smul ha).add (hD.1.smul hb)
  refine ⟨hM, (bures_ball_block_certificate ⟨_, hM⟩ B eps).mpr ?_⟩
  obtain ⟨C, hC, hc⟩ := (bures_ball_block_certificate ⟨A, hA.1⟩ B eps).mp hA.2
  obtain ⟨E, hE, he⟩ := (bures_ball_block_certificate ⟨D, hD.1⟩ B eps).mp hD.2
  refine ⟨a • C + b • E, ?_, ?_⟩
  · have hh := (hC.smul ha).add (hE.smul hb)
    have hB : a • B.val + b • B.val = B.val := by rw [← add_smul, hab, one_smul]
    simpa only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
      Matrix.transpose_add, Matrix.transpose_smul, hB] using hh
  · simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    calc
      _ = a * (Matrix.trace A + Matrix.trace B.val - 2 * Matrix.trace C) +
          b * (Matrix.trace D + Matrix.trace B.val - 2 * Matrix.trace E) := by
        nlinarith [congrArg (fun t : ℝ => t * Matrix.trace B.val) hab]
      _ ≤ a * (eps : ℝ) ^ 2 + b * (eps : ℝ) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hc ha) (mul_le_mul_of_nonneg_left he hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

-- @node: matrixRisk_joint_continuous
/-- [Matrix regression risk is jointly continuous in the coefficient matrix and the
joint second-moment matrix](goal). -/
@[fun_prop] lemma matrixRisk_joint_continuous {p m : ℕ} :
    Continuous (fun x : Mat m p × Mat (p + m) (p + m) => matrixRisk x.1 x.2) := by
  unfold matrixRisk blockX blockXY blockY rawBlocks
  fun_prop

-- @node: matrixRisk_affine_moment
/-- For [a coefficient matrix A](hyp:A), [joint moment matrices S and T](hyp:S,T),
and [real weights a and b](hyp:a,b), [risk at the weighted sum of S and T equals the
same weighted sum of their risks at A](goal). -/
lemma matrixRisk_affine_moment {p m : ℕ} (A : Mat m p)
    (S T : Mat (p + m) (p + m)) (a b : ℝ) :
    matrixRisk A (a • S + b • T) = a * matrixRisk A S + b * matrixRisk A T := by
  simp only [matrixRisk, blockX, blockXY, blockY, rawBlocks,
    Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply,
    Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

-- @node: matrixRisk_convex_coefficient
/-- For [a positive semidefinite joint second-moment matrix S](hyp:S),
[matrix regression risk is convex over all coefficient matrices](goal). -/
lemma matrixRisk_convex_coefficient {p m : ℕ} (S : PSD (p + m)) :
    ConvexOn ℝ Set.univ (fun A : Mat m p => matrixRisk A S.val) := by
  let X := (factorBlocks p m (CFC.sqrt S.val)).1
  let Y := (factorBlocks p m (CFC.sqrt S.val)).2
  let L : Mat m p →ₗ[ℝ] Mat m (p + m) :=
    { toFun := fun A => A * X
      map_add' := by intros; exact Matrix.add_mul ..
      map_smul' := by intros; exact Matrix.smul_mul .. }
  let F : Mat m p →ᵃ[ℝ] Mat m (p + m) :=
    L.toAffineMap - AffineMap.const ℝ (Mat m p) Y
  have hc := ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set (Mat m (p + m))))).pow
    (fun _ _ => norm_nonneg _) 2).comp_affineMap F
  have hr (A : Mat m p) : matrixRisk A S.val = ‖F A‖ ^ 2 := by
    rw [psd_sqrt_factor S, matrixRisk_gram_factor, frob_eq_matrix_norm]
    rfl
  change ConvexOn ℝ Set.univ (fun A => ‖F A‖ ^ 2) at hc
  simpa only [← hr] using hc

end Papers.WassersteinRegretS2S3
