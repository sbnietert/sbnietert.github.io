module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs

/-!
# Population Wasserstein regret: Helpers/MatrixNorms

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: frob_nonneg
/-- [The Frobenius norm of any real rectangular matrix is nonnegative](goal). -/
lemma frob_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ frob A := Real.sqrt_nonneg _

-- @node: frob_sq
/-- [The squared Frobenius norm of a real matrix equals the sum of the squares of all
its entries](goal). -/
lemma frob_sq {a b : ℕ} (A : Mat a b) :
    frob A ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

-- @node: frob_transpose
/-- [Transposing a real matrix leaves its Frobenius norm unchanged](goal). -/
lemma frob_transpose {a b : ℕ} (A : Mat a b) : frob A.transpose = frob A := by
  unfold frob
  congr 1
  exact Finset.sum_comm

-- @node: opNorm_mul_le
/-- [The operator norm of a product of compatible real matrices is at most the product
of their operator norms](goal). -/
lemma opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  exact Matrix.l2_opNorm_mul A B

-- @node: opNorm_transpose
/-- [Transposing a real matrix leaves its Euclidean operator norm unchanged](goal). -/
lemma opNorm_transpose {a b : ℕ} (A : Mat a b) : opNorm A.transpose = opNorm A := by
  have h : A.transpose = A.conjTranspose := by ext; simp
  exact h ▸ Matrix.l2_opNorm_conjTranspose A

-- @node: frob_mul_left_le
/-- [The Frobenius norm of a product of compatible real matrices is at most the
operator norm of the left factor times the Frobenius norm of the right factor](goal). -/
lemma frob_mul_left_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    frob (A * B) ≤ opNorm A * frob B := by
  have hcol (j : Fin c) :
      (∑ i, (A * B) i j ^ 2) ≤ opNorm A ^ 2 * ∑ i, B i j ^ 2 := by
    have h := (matrixCLM A).le_opNorm (WithLp.toLp 2 (fun i => B i j))
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa [EuclideanSpace.real_norm_sq_eq, mul_pow, opNorm, matrixCLM,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hs
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg (norm_nonneg _) (frob_nonneg _))).mp
  rw [mul_pow, frob_sq, frob_sq, Finset.sum_comm]
  calc
    ∑ j, ∑ i, (A * B) i j ^ 2 ≤ ∑ j, opNorm A ^ 2 * ∑ i, B i j ^ 2 :=
      Finset.sum_le_sum fun j _ => hcol j
    _ = opNorm A ^ 2 * ∑ i, ∑ j, B i j ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

-- @node: frob_mul_right_le
/-- [The Frobenius norm of a product of compatible real matrices is at most the
Frobenius norm of the left factor times the operator norm of the right factor](goal). -/
lemma frob_mul_right_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    frob (A * B) ≤ frob A * opNorm B := by
  have h := frob_mul_left_le B.transpose A.transpose
  simpa [← Matrix.transpose_mul, frob_transpose, opNorm_transpose, mul_comm] using h

-- @node: frob_sq_trace
/-- [The squared Frobenius norm of a real matrix equals the trace of its transpose
times itself](goal). -/
lemma frob_sq_trace {a b : ℕ} (A : Mat a b) :
    frob A ^ 2 = Matrix.trace (A.transpose * A) := by
  rw [frob_sq, Matrix.trace, Finset.sum_comm]
  simp [Matrix.mul_apply, pow_two]

-- @node: frob_inner_le
/-- [The absolute value of the sum of entrywise products of two equally sized real
matrices is at most the product of their Frobenius norms](goal). -/
lemma frob_inner_le {a b : ℕ} (A B : Mat a b) :
    |∑ i, ∑ j, A i j * B i j| ≤ frob A * frob B := by
  let x : EuclideanSpace ℝ (Fin a × Fin b) := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  let y : EuclideanSpace ℝ (Fin a × Fin b) := WithLp.toLp 2 (fun ij => B ij.1 ij.2)
  have hx : ‖x‖ = frob A := by
    simp [x, EuclideanSpace.norm_eq, frob, Fintype.sum_prod_type]
  have hy : ‖y‖ = frob B := by
    simp [y, EuclideanSpace.norm_eq, frob, Fintype.sum_prod_type]
  have h := abs_real_inner_le_norm x y
  simpa [hx, hy, x, y, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm] using h

-- @node: opNorm_le_frob
/-- [The Euclidean operator norm of a real matrix is at most its Frobenius norm](goal). -/
lemma opNorm_le_frob {a b : ℕ} (A : Mat a b) : opNorm A ≤ frob A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (frob_nonneg _)
  intro x
  have hrow (i : Fin a) : ((matrixCLM A x) i) ^ 2 ≤
      (∑ j, A i j ^ 2) * ‖x‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)
    simpa [matrixCLM, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.real_norm_sq_eq] using h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (frob_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, frob_sq]
  exact (Finset.sum_le_sum fun i _ => hrow i).trans_eq (Finset.sum_mul ..).symm

-- @node: frob_le_sqrt_rank_opNorm
/-- [The Frobenius norm of a real matrix is at most the square root of its rank times
its Euclidean operator norm](goal). -/
lemma frob_le_sqrt_rank_opNorm {a b : ℕ} (A : Mat a b) :
    frob A ≤ Real.sqrt (Matrix.rank A : ℝ) * opNorm A := by
  classical
  let G := A.transpose * A
  have hG : G.IsHermitian := by
    simpa [G] using Matrix.isHermitian_conjTranspose_mul_self A
  have he (i : Fin b) : hG.eigenvalues i ≤ opNorm A ^ 2 := by
    have hn := Matrix.l2_opNorm_conjTranspose_mul_self A
    have hbound := (matrixCLM G).le_opNorm (hG.eigenvectorBasis i)
    have heq : matrixCLM G (hG.eigenvectorBasis i) =
        hG.eigenvalues i • hG.eigenvectorBasis i := by
      apply PiLp.ext
      intro j
      exact congrFun (hG.mulVec_eigenvectorBasis i) j
    rw [heq, norm_smul, hG.eigenvectorBasis.norm_eq_one, mul_one, mul_one] at hbound
    have hn' : opNorm G = opNorm A ^ 2 := by
      change opNorm (A.conjTranspose * A) = opNorm A * opNorm A at hn
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using hn
    exact (le_abs_self _).trans (hbound.trans_eq hn')
  have hsum : Matrix.trace G ≤ (Matrix.rank G : ℝ) * opNorm A ^ 2 := by
    rw [hG.trace_eq_sum_eigenvalues, hG.rank_eq_card_non_zero_eigs]
    calc
      ∑ i, hG.eigenvalues i = ∑ i : {i // hG.eigenvalues i ≠ 0}, hG.eigenvalues i := by
        have hz : (∑ i : {i // ¬ hG.eigenvalues i ≠ 0}, hG.eigenvalues i) = 0 :=
          Finset.sum_eq_zero fun i _ => not_not.mp i.property
        simpa only [hz, add_zero] using
          (Fintype.sum_subtype_add_sum_subtype (fun i => hG.eigenvalues i ≠ 0)
            hG.eigenvalues).symm
      _ ≤ ∑ _i : {i // hG.eigenvalues i ≠ 0}, opNorm A ^ 2 :=
        Finset.sum_le_sum fun i _ => he i
      _ = _ := by simp
  have hr : (Matrix.rank G : ℝ) ≤ Matrix.rank A := by
    exact_mod_cast Matrix.rank_mul_le_right A.transpose A
  have hs : frob A ^ 2 ≤ (Matrix.rank A : ℝ) * opNorm A ^ 2 :=
    (frob_sq_trace A).trans_le (hsum.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _)))
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa [opNorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (Matrix.rank A))] using hs

-- @node: frob_projection_pythagoras
/-- If [P is symmetric and idempotent, hence an orthogonal projection](hyp:hP), then
[the squared Frobenius norm of M equals the sum of the squared Frobenius norms of
its products with P and the complementary projection](goal). -/
lemma frob_projection_pythagoras {a b : ℕ} (M : Mat a b) (P : Mat b b)
    (hP : assBasicMatrixNormsProjection P) :
    frob M ^ 2 = frob (M * P) ^ 2 + frob (M * (1 - P)) ^ 2 := by
  have hcross : Matrix.trace ((M * P).transpose * (M * (1 - P))) = 0 := by
    rw [Matrix.transpose_mul, hP.1]
    calc
      Matrix.trace (P * M.transpose * (M * (1 - P))) =
          Matrix.trace (((1 - P) * P) * (M.transpose * M)) := by
        rw [← Matrix.mul_assoc (P * M.transpose) M (1 - P)]
        rw [Matrix.trace_mul_comm _ (1 - P)]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP.2, sub_self, Matrix.zero_mul]; simp
  have hcross' : Matrix.trace ((M * (1 - P)).transpose * (M * P)) = 0 := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hcross
  have hsum : M * P + M * (1 - P) = M := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  calc
    frob M ^ 2 = Matrix.trace ((M * P + M * (1 - P)).transpose *
        (M * P + M * (1 - P))) := by rw [hsum, frob_sq_trace]
    _ = frob (M * P) ^ 2 + frob (M * (1 - P)) ^ 2 := by
      simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
        hcross, hcross', add_zero, zero_add, ← frob_sq_trace]

-- @node: lem:basic-matrix-norms
/-- [For compatible real matrices, a three-factor product has Frobenius norm at most
the operator norms of its outer factors times the Frobenius norm of its middle
factor; operator norms are submultiplicative, and a two-factor product has Frobenius
norm at most the left operator norm times the right Frobenius norm. The operator
norm is bounded by the Frobenius norm, which is bounded by the square root of rank
times the operator norm; right multiplication by an orthogonal projection contracts
the Frobenius norm and gives a Pythagorean decomposition with its complement; and
the absolute entrywise inner product is bounded by the product of Frobenius norms](goal). -/
lemma basicMatrixNorms :
    (∀ (a b c e : ℕ)
      (A : Mat a b) -- @realizes \bA(arbitrary real rectangular matrix)
      (B : Mat b c) -- @realizes \bB(compatible real rectangular matrix)
      (C : Mat c e), -- @realizes \bC(compatible real rectangular matrix)
      frob (A * B * C) ≤ opNorm A * frob B * opNorm C) ∧
    (∀ (a b c : ℕ) (A : Mat a b) (B : Mat b c), opNorm (A * B) ≤ opNorm A * opNorm B) ∧
    (∀ (a b c : ℕ) (A : Mat a b) (B : Mat b c), frob (A * B) ≤ opNorm A * frob B) ∧
    (∀ (a b : ℕ) (A : Mat a b), opNorm A ≤ frob A ∧
      frob A ≤ Real.sqrt (Matrix.rank A : ℝ) * opNorm A) ∧
    (∀ (a b : ℕ) (M : Mat a b) (Pi : Mat b b), assBasicMatrixNormsProjection Pi →
      frob (M * Pi) ≤ frob M ∧
      frob M ^ 2 = frob (M * Pi) ^ 2 + frob (M * (1 - Pi)) ^ 2) ∧
    (∀ (a b : ℕ) (A B : Mat a b), |∑ i, ∑ j, A i j * B i j| ≤ frob A * frob B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c e A B C
    exact (frob_mul_right_le (A * B) C).trans
      (mul_le_mul_of_nonneg_right (frob_mul_left_le A B) (norm_nonneg _))
  · intro a b c A B
    exact opNorm_mul_le A B
  · intro a b c A B
    exact frob_mul_left_le A B
  · intro a b A
    exact ⟨opNorm_le_frob A, frob_le_sqrt_rank_opNorm A⟩
  · intro a b M Pi hPi
    have hp := frob_projection_pythagoras M Pi hPi
    refine ⟨?_, hp⟩
    apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
    linarith [sq_nonneg (frob (M * (1 - Pi)))]
  · intro a b A B
    exact frob_inner_le A B

-- @node: symmetric_block_properties
/-- [For a symmetric joint matrix partitioned into p feature and m response
coordinates, both diagonal blocks are symmetric and the feature–response block is
the transpose of the response–feature block](goal). -/
lemma symmetric_block_properties (p m : ℕ) (Sigma : Sym (p + m)) :
    (blockX p m Sigma.val).IsHermitian ∧ (blockY p m Sigma.val).IsHermitian ∧
      blockXY p m Sigma.val = (blockYX p m Sigma.val).transpose := by
  have hs : Sigma.val.IsHermitian := Sigma.property
  refine ⟨hs.submatrix _, hs.submatrix _, ?_⟩
  ext i j
  simpa [blockXY, blockYX, rawBlocks] using
    (hs.apply (Fin.castAdd m i) (Fin.natAdd p j)).symm

end Papers.WassersteinRegretS2S3
