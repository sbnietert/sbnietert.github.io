module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs

/-!
# Population Wasserstein regret: Helpers/Pseudoinverse

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: singularValueConvention_proved
/-- [Every real matrix with positive row and column counts has nonincreasing,
nonnegative singular values, and its minimum singular value is the entry in
position equal to the smaller dimension in that ordering](goal). -/
lemma singularValueConvention_proved : assSingularValueConvention := by
  intro a b _ _ M
  exact ⟨(Matrix.toEuclideanLin M).singularValues_antitone,
    (Matrix.toEuclideanLin M).singularValues_nonneg, rfl⟩

-- @node: euclideanLin_mul
/-- For [a real matrix A](hyp:A) and [a real matrix B whose row count equals
the column count of A](hyp:B), [the Euclidean linear map induced by their product
is the composition of the map induced by B followed by the map induced by A](goal). -/
lemma euclideanLin_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  exact Matrix.toLin_mul (EuclideanSpace.basisFun (Fin c) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin b) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin a) ℝ).toBasis A B

-- @node: range_mul_of_inner_inverse
/-- For [a real matrix A](hyp:A) and [a matrix G with the reversed dimensions](hyp:G),
if [multiplying A by G and then by A gives A again](hyp:h), then
[the column space of A times G equals the column space of A](goal). -/
lemma range_mul_of_inner_inverse {a b : ℕ} (A : Mat a b) (G : Mat b a)
    (h : A * G * A = A) :
    LinearMap.range (Matrix.toEuclideanLin (A * G)) =
      LinearMap.range (Matrix.toEuclideanLin A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨Matrix.toEuclideanLin G x, by rw [euclideanLin_mul]; rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨Matrix.toEuclideanLin A x, ?_⟩
    have hh := congrArg (fun B => Matrix.toEuclideanLin B x) h
    simpa only [euclideanLin_mul, LinearMap.comp_apply] using hh

-- @node: penrose_projectors
/-- For [a real rectangular matrix M](hyp:M), [its pseudoinverse times M is a
symmetric, idempotent matrix with range equal to the row space of M, and M times
its pseudoinverse is a symmetric, idempotent matrix with range equal to the
column space of M](goal). -/
lemma penrose_projectors {a b : ℕ} (M : Mat a b) :
    assBasicMatrixNormsProjection (rowProjector M) ∧
    LinearMap.range (Matrix.toEuclideanLin (rowProjector M)) =
      LinearMap.range (Matrix.toEuclideanLin M.transpose) ∧
    assBasicMatrixNormsProjection (rangeProjector M) ∧
    LinearMap.range (Matrix.toEuclideanLin (rangeProjector M)) =
      LinearMap.range (Matrix.toEuclideanLin M) := by
  have h := moorePenroseInverse_spec M
  have ht : M.transpose * (moorePenroseInverse M).transpose = rowProjector M := by
    simpa only [Matrix.transpose_mul, rowProjector] using h.2.2.2
  refine ⟨⟨(rowProjection_penrose M).2, (rowProjection_penrose M).1⟩, ?_,
    ⟨(rangeProjection_penrose M).2, (rangeProjection_penrose M).1⟩,
    range_mul_of_inner_inverse M _ h.1⟩
  rw [← ht]
  apply range_mul_of_inner_inverse
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h.1

-- @node: penrose_transpose
/-- For [a real rectangular matrix M](hyp:M), [the Moore–Penrose pseudoinverse
of its transpose equals the transpose of its Moore–Penrose pseudoinverse](goal). -/
lemma penrose_transpose {a b : ℕ} (M : Mat a b) :
    moorePenroseInverse M.transpose = (moorePenroseInverse M).transpose := by
  have h := moorePenroseInverse_spec M
  apply isMoorePenroseInverse_unique (moorePenroseInverse_spec _) 
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h.1
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h.2.1
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      congrArg Matrix.transpose h.2.2.2
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      congrArg Matrix.transpose h.2.2.1

-- @node: penrose_gram
/-- For [a real rectangular matrix M](hyp:M), [the pseudoinverse of its row Gram
matrix, formed by multiplying M by its transpose, equals the transpose of the
pseudoinverse of M multiplied by the pseudoinverse of M](goal). -/
lemma penrose_gram {a b : ℕ} (M : Mat a b) :
    moorePenroseInverse (M * M.transpose) =
      (moorePenroseInverse M).transpose * moorePenroseInverse M := by
  let G := moorePenroseInverse M
  have h := moorePenroseInverse_spec M
  have hs : M.transpose * G.transpose = G * M := by
    simpa only [Matrix.transpose_mul] using h.2.2.2
  have hprod : (M * M.transpose) * (G.transpose * G) = M * G := by
    calc
      _ = M * (M.transpose * G.transpose) * G := by simp only [Matrix.mul_assoc]
      _ = M * (G * M) * G := by rw [hs]
      _ = M * G := by rw [Matrix.mul_assoc M, h.2.1]
  have hprod' : (G.transpose * G) * (M * M.transpose) = M * G := by
    have ht := congrArg Matrix.transpose hprod
    rw [show (M * G).transpose = M * G from h.2.2.1] at ht
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
  apply isMoorePenroseInverse_unique (moorePenroseInverse_spec _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprod, ← Matrix.mul_assoc, h.1]
  · rw [Matrix.mul_assoc, hprod]
    calc
      _ = G.transpose * (G * M * G) := by simp only [G, Matrix.mul_assoc]
      _ = G.transpose * G := by rw [h.2.1]
  · rw [hprod]; exact h.2.2.1
  · rw [hprod']; exact h.2.2.1

-- @node: penrose_transpose_gram_formula
/-- For [a real rectangular matrix M](hyp:M), [its pseudoinverse equals its
transpose times the pseudoinverse of its row Gram matrix, formed by multiplying
M by its transpose](goal). -/
lemma penrose_transpose_gram_formula {a b : ℕ} (M : Mat a b) :
    moorePenroseInverse M = M.transpose * moorePenroseInverse (M * M.transpose) := by
  have h := moorePenroseInverse_spec M
  rw [penrose_gram, ← Matrix.mul_assoc]
  rw [← Matrix.transpose_mul, h.2.2.2]
  exact h.2.1.symm

-- @node: penrose_full_row_projection
/-- For [a real rectangular matrix M](hyp:M), if [M has full row rank](hyp:hM),
then [M times its Moore–Penrose pseudoinverse is the identity matrix](goal). -/
lemma penrose_full_row_projection {a b : ℕ} (M : Mat a b)
    (hM : assPseudoinverseProjectionFactsRowRank M) :
    M * moorePenroseInverse M = 1 := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hM y
  have h := congrArg (fun B => Matrix.toEuclideanLin B x) (moorePenroseInverse_spec M).1
  simpa only [euclideanLin_mul, LinearMap.comp_apply, Matrix.toLpLin_one,
    LinearMap.id_apply] using h

-- @node: penrose_full_row_formula
/-- For [a real rectangular matrix M](hyp:M), if [M has full row rank](hyp:hM),
then [its Moore–Penrose pseudoinverse equals its transpose times the inverse
of its row Gram matrix, M times its transpose](goal). -/
lemma penrose_full_row_formula {a b : ℕ} (M : Mat a b)
    (hM : assPseudoinverseProjectionFactsRowRank M) :
    moorePenroseInverse M = M.transpose * (M * M.transpose)⁻¹ := by
  have hp := penrose_full_row_projection M hM
  have hs := (moorePenroseInverse_spec M).2.2.2
  have hinv : (M * M.transpose) *
      ((moorePenroseInverse M).transpose * moorePenroseInverse M) = 1 := by
    calc
      _ = M * (M.transpose * (moorePenroseInverse M).transpose) *
          moorePenroseInverse M := by simp only [Matrix.mul_assoc]
      _ = M * (moorePenroseInverse M * M) * moorePenroseInverse M := by
        rw [← Matrix.transpose_mul, hs]
      _ = (M * moorePenroseInverse M) * (M * moorePenroseInverse M) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hp, Matrix.one_mul]
  rw [penrose_transpose_gram_formula M, penrose_gram, Matrix.inv_eq_right_inv hinv]

-- @node: penrose_full_row_norm
/-- For [a real matrix M with at least one row](hyp:M), if [M has full row rank](hyp:hM),
then [the Euclidean operator norm of its Moore–Penrose pseudoinverse is the
reciprocal of its minimum singular value](goal). -/
lemma penrose_full_row_norm {a b : ℕ} [NeZero a] (M : Mat a b)
    (hM : assPseudoinverseProjectionFactsRowRank M) :
    opNorm (moorePenroseInverse M) = (minSV M)⁻¹ := by
  let T := Matrix.toEuclideanLin M
  have hr : Module.finrank ℝ T.range = a := by
    rw [LinearMap.range_eq_top.mpr hM]
    simp
  have hab : a ≤ b := by
    have h := LinearMap.finrank_range_le T
    simpa only [hr, finrank_euclideanSpace, Fintype.card_fin] using h
  have hrank : M.rank = a := by
    rw [M.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin a) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin b) ℝ).toBasis]
    exact hr
  have hsig : minSV M = T.singularValues (a - 1) := by
    simp only [minSV, Nat.min_eq_left hab, singularValue, T]
  have hs : 0 < minSV M := by
    rw [hsig, T.singularValues_pos_iff_lt_finrank_range, hr]
    exact Nat.sub_one_lt (NeZero.ne a)
  apply le_antisymm
  · exact norm_moorePenroseInverse_le_inv M hrank hs (le_of_eq hsig)
  · -- A unit right singular vector for the least positive singular value attains the bound.
    let j : Fin (Module.finrank ℝ (Euc b)) :=
      ⟨a - 1, by
        simp only [finrank_euclideanSpace, Fintype.card_fin]
        have ha := NeZero.pos a
        omega⟩
    let x := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j
    have hxnorm : ‖x‖ = 1 :=
      T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl |>.norm_eq_one j
    have heigen : T.adjoint (T x) = (minSV M) ^ 2 • x := by
      have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl j
      rw [← T.sq_singularValues_fin rfl j] at h
      simpa only [LinearMap.comp_apply, j, ← hsig, RCLike.ofReal_real_eq_id,
        id_eq] using h
    have hnorm : ‖T x‖ = minSV M := by
      apply (sq_eq_sq₀ (norm_nonneg _) hs.le).mp
      calc
        ‖T x‖ ^ 2 = inner ℝ (T x) (T x) := (real_inner_self_eq_norm_sq _).symm
        _ = inner ℝ x (T.adjoint (T x)) := (T.adjoint_inner_right x (T x)).symm
        _ = (minSV M) ^ 2 := by
          rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq, hxnorm]
          ring
    have hxrange : x ∈ LinearMap.range (Matrix.toEuclideanLin (rowProjector M)) := by
      rw [(penrose_projectors M).2.1]
      refine ⟨((minSV M) ^ 2)⁻¹ • T x, ?_⟩
      have ht : Matrix.toEuclideanLin M.transpose = T.adjoint := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
      rw [ht, map_smul, heigen, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hs.ne'), one_smul]
    have hxfix : matrixCLM (moorePenroseInverse M) (T x) = x := by
      obtain ⟨z, hz⟩ := hxrange
      change Matrix.toEuclideanLin (moorePenroseInverse M) (Matrix.toEuclideanLin M x) = x
      rw [← LinearMap.comp_apply, ← euclideanLin_mul]
      change Matrix.toEuclideanLin (rowProjector M) x = x
      rw [← hz]
      have h := congrArg (fun B => Matrix.toEuclideanLin B z) (penrose_projectors M).1.2
      simpa only [euclideanLin_mul, LinearMap.comp_apply] using h
    have hbound := (matrixCLM (moorePenroseInverse M)).le_opNorm (T x)
    rw [hxfix, hxnorm, hnorm] at hbound
    simpa only [one_div, opNorm] using (div_le_iff₀ hs).mpr hbound

-- @node: penrose_psd_square
/-- For [a real square matrix B](hyp:B), if [B is positive semidefinite](hyp:hB),
then [the Moore–Penrose pseudoinverse of B times the square of B equals B](goal). -/
lemma penrose_psd_square {n : ℕ} (B : Mat n n) (hB : B.PosSemidef) :
    moorePenroseInverse B * B ^ 2 = B := by
  have hs : B.transpose = B := hB.isHermitian.eq
  have hg : (moorePenroseInverse B).transpose = moorePenroseInverse B := by
    rw [← penrose_transpose, hs]
  have hc : moorePenroseInverse B * B = B * moorePenroseInverse B := by
    simpa only [Matrix.transpose_mul, hs, hg] using (moorePenroseInverse_spec B).2.2.1
  rw [pow_two, ← Matrix.mul_assoc, hc]
  exact (moorePenroseInverse_spec B).1

-- @node: lem:pseudoinverse-projection-facts
/-- Assuming [singular values are nonincreasing and nonnegative, with the minimum
in the position given by the smaller matrix dimension](hyp:_hsv), [every real
matrix with positive row and column counts has symmetric, idempotent row and
column projectors onto its row and column spaces, and its pseudoinverse equals
its transpose times the pseudoinverse of its row Gram matrix; when it has full
row rank, the Gram pseudoinverse can be replaced by the inverse, the matrix times
its pseudoinverse is the identity, and the pseudoinverse has operator norm equal
to the reciprocal of the minimum singular value; moreover, every positive
semidefinite matrix has its pseudoinverse times its square equal to itself](goal). -/
lemma pseudoinverseProjectionFacts (_hsv : assSingularValueConvention) :
    (∀ (r d : ℕ) [NeZero r] [NeZero d] (M : Mat r d),
      assBasicMatrixNormsProjection (rowProjector M) ∧
      LinearMap.range (Matrix.toEuclideanLin (rowProjector M)) =
        LinearMap.range (Matrix.toEuclideanLin M.transpose) ∧
      assBasicMatrixNormsProjection (rangeProjector M) ∧
      LinearMap.range (Matrix.toEuclideanLin (rangeProjector M)) =
        LinearMap.range (Matrix.toEuclideanLin M) ∧
      moorePenroseInverse M = M.transpose * moorePenroseInverse (M * M.transpose) ∧
      (assPseudoinverseProjectionFactsRowRank M →
        moorePenroseInverse M = M.transpose * (M * M.transpose)⁻¹ ∧
        M * moorePenroseInverse M = 1 ∧ opNorm (moorePenroseInverse M) = (minSV M)⁻¹)) ∧
    (∀ (n : ℕ) (B : Mat n n), assPseudoinverseProjectionFactsPositive B →
      moorePenroseInverse B * B ^ 2 = B) := by
  constructor
  · intro r d _ _ M
    have hp := penrose_projectors M
    refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
      penrose_transpose_gram_formula M, ?_⟩
    intro hM
    exact ⟨penrose_full_row_formula M hM, penrose_full_row_projection M hM,
      penrose_full_row_norm M hM⟩
  · intro n B hB
    exact penrose_psd_square B hB

end Papers.WassersteinRegretS2S3
