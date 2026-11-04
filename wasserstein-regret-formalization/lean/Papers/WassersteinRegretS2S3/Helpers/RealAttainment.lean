module
public import Papers.WassersteinRegretS2S3.Helpers.RealComplex

/-!
# Population Wasserstein regret: Helpers/RealAttainment

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: real_range_isometry_of_gram_eq
/-- If [M and N have the same column Gram matrix](hyp:hGram), [there is a real
linear isometry from the range of M into Euclidean space that sends M times x
to N times x for every vector x](goal). -/
lemma real_range_isometry_of_gram_eq {n : ℕ} (M N : Mat n n)
    (hGram : M.transpose * M = N.transpose * N) :
    ∃ L : LinearMap.range (Matrix.toEuclideanLin M) →ₗᵢ[ℝ] Euc n,
      ∀ x, L ((Matrix.toEuclideanLin M).rangeRestrict x) = Matrix.toEuclideanLin N x := by
  classical
  have hinner (A : Mat n n) (x y : Euc n) :
      inner ℝ (toEuclideanLin A x) (toEuclideanLin A y) =
        star (WithLp.ofLp x) ⬝ᵥ ((Aᴴ * A) *ᵥ WithLp.ofLp y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (A *ᵥ WithLp.ofLp y) ⬝ᵥ star (A *ᵥ WithLp.ofLp x) = _
    rw [dotProduct_comm, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
      ← dotProduct_mulVec]
  have hMN (x y : Euc n) :
      inner ℝ (toEuclideanLin M x) (toEuclideanLin M y) =
        inner ℝ (toEuclideanLin N x) (toEuclideanLin N y) := by
    rw [hinner, hinner, show M.conjTranspose * M = N.conjTranspose * N from hGram]
  have hker : LinearMap.ker (toEuclideanLin M) ≤ LinearMap.ker (toEuclideanLin N) := by
    intro x hx
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← hMN, LinearMap.mem_ker.mp hx, inner_zero_left]
  let f := ((LinearMap.ker (toEuclideanLin M)).liftQ (toEuclideanLin N) hker).comp
    (toEuclideanLin M).quotKerEquivRange.symm.toLinearMap
  have hf (x : Euc n) :
      f ((toEuclideanLin M).rangeRestrict x) = toEuclideanLin N x := by
    change (LinearMap.ker (toEuclideanLin M)).liftQ (toEuclideanLin N) hker
      ((toEuclideanLin M).quotKerEquivRange.symm ⟨toEuclideanLin M x, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨f.isometryOfInner ?_, hf⟩
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
  change inner ℝ (f ((toEuclideanLin M).rangeRestrict x))
    (f ((toEuclideanLin M).rangeRestrict y)) = _
  rw [hf, hf, ← hMN]
  rfl

-- @node: real_orthogonal_left_of_gram_eq
/-- If [M and N have the same column Gram matrix](hyp:hGram), [there is a real
orthogonal matrix U such that M equals U times N](goal). -/
lemma real_orthogonal_left_of_gram_eq {n : ℕ} (M N : Mat n n)
    (hGram : M.transpose * M = N.transpose * N) :
    ∃ U : Orth n, M = U.val * N := by
  classical
  obtain ⟨L, hL⟩ := real_range_isometry_of_gram_eq N M hGram.symm
  let e := L.extend.toLinearIsometryEquiv rfl
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let U := e.toLinearEquiv.toLinearMap.toMatrix b b
  refine ⟨⟨U, ?_⟩, ?_⟩
  · exact e.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin n) ℝ)
  · apply (Matrix.toLin b b).injective
    rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix]
    apply LinearMap.ext
    intro x
    change toEuclideanLin M x = L.extend (toEuclideanLin N x)
    rw [← hL x, ← LinearIsometry.extend_apply]
    rfl

-- @node: real_orthogonal_polar
/-- [Every real square matrix X equals a real orthogonal matrix times the
positive semidefinite square root of the column Gram matrix of X](goal). -/
lemma real_orthogonal_polar {n : ℕ} (X : Mat n n) :
    ∃ U : Orth n, X = U.val * CFC.sqrt (X.transpose * X)
       := by
  have hG : (X.transpose * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hP : (CFC.sqrt (X.transpose * X)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  apply real_orthogonal_left_of_gram_eq
  rw [show (CFC.sqrt (X.transpose * X)).transpose = CFC.sqrt (X.transpose * X) from
    hP.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hG.nonneg]
-- @realizes \bU(real orthogonal polar)

-- @node: real_procrustes_lower
/-- For positive semidefinite matrices A and B and an orthogonal matrix U,
[the Bures distance between A and B is at most the Frobenius norm of the square
root of A minus the square root of B times U](goal). -/
lemma real_procrustes_lower {n : ℕ} (A B : PSD n) (U : Orth n) :
    buresDistance A.val B.val ≤ frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) := by
  have h := (Toolkit.Foundations.LinearAlgebra.Matrix.bures_eq_min_frobenius
    (complexify_posSemidef A) (complexify_posSemidef B)).2.2
      ⟨complexify U.val, complexify_orthogonal U, rfl⟩
  simpa only [complexify_sqrt, ← complexify_mul, ← complexify_sub,
    complexify_frob, complexify_bures] using h
-- @node: real_factor_lower
/-- If [A equals S times its transpose](hyp:hS) and [B equals T times its
transpose](hyp:hT), [the Bures distance between A and B is at most the Frobenius
distance between S and T](goal). -/
lemma real_factor_lower {n : ℕ} (A B : PSD n) (S T : Mat n n)
    (hS : A.val = S * S.transpose) (hT : B.val = T * T.transpose) :
    buresDistance A.val B.val ≤ frob (S - T) := by
  have hS' : complexify S * (complexify S).conjTranspose = complexify A.val := by
    rw [← complexify_transpose, ← complexify_mul, ← hS]
  have hT' : complexify T * (complexify T).conjTranspose = complexify B.val := by
    rw [← complexify_transpose, ← complexify_mul, ← hT]
  have h := (Toolkit.Foundations.LinearAlgebra.Matrix.bures_eq_min_frobenius
    (complexify_posSemidef A) (complexify_posSemidef B)).1.2
      ⟨complexify S, complexify T, hS', hT', rfl⟩
  simpa only [← complexify_sub, complexify_frob, complexify_bures] using h
-- @node: real_procrustes_attainment
/-- For positive semidefinite matrices A and B, [there is a real orthogonal
matrix U for which the Frobenius norm of the square root of A minus the square
root of B times U equals the Bures distance between A and B](goal). -/
lemma real_procrustes_attainment {n : ℕ} (A B : PSD n) :
    ∃ U : Orth n, frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) = buresDistance A.val B.val :=
      by
  have hSA : (CFC.sqrt A.val).transpose = CFC.sqrt A.val :=
    (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq
  have hSB : (CFC.sqrt B.val).transpose = CFC.sqrt B.val :=
    (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq
  obtain ⟨U, hpolar⟩ := real_orthogonal_polar (CFC.sqrt B.val * CFC.sqrt A.val)
  have hG : (CFC.sqrt B.val * CFC.sqrt A.val).transpose *
      (CFC.sqrt B.val * CFC.sqrt A.val) = CFC.sqrt A.val * B.val * CFC.sqrt A.val := by
    rw [Matrix.transpose_mul, hSA, hSB, Matrix.mul_assoc,
      ← Matrix.mul_assoc (CFC.sqrt B.val), CFC.sqrt_mul_sqrt_self B.val B.property.nonneg,
      ← Matrix.mul_assoc]
  rw [hG] at hpolar
  have hcross : U.val.transpose * (CFC.sqrt B.val * CFC.sqrt A.val) =
      CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val) := by
    conv_lhs => rw [hpolar, ← Matrix.mul_assoc,
      show U.val.transpose * U.val = 1 from U.property.1, Matrix.one_mul]
  have hcost := Toolkit.Foundations.LinearAlgebra.Matrix.frobeniusNorm_sub_mul_unitary_sq
    (complexify (CFC.sqrt A.val)) (complexify (CFC.sqrt B.val)) (complexify_orthogonal U)
  rw [← complexify_mul, ← complexify_sub, complexify_frob,
    ← complexify_transpose, ← complexify_transpose, ← complexify_transpose,
    ← complexify_mul, ← complexify_mul, ← complexify_mul, ← complexify_mul,
    hSA, hSB, CFC.sqrt_mul_sqrt_self A.val A.property.nonneg,
    CFC.sqrt_mul_sqrt_self B.val B.property.nonneg, hcross,
    complexify_trace, complexify_trace, complexify_trace] at hcost
  refine ⟨U, ?_⟩
  unfold buresDistance
  rw [← hcost]
  exact (Real.sqrt_sq (show 0 ≤ frob _ from Real.sqrt_nonneg _)).symm

-- @node: real_factor_attainment
/-- For positive semidefinite matrices A and B, [there are real square factors S
and T such that A equals S times its transpose, B equals T times its transpose,
and the Frobenius distance between S and T equals the Bures distance between A
and B](goal). -/
lemma real_factor_attainment {n : ℕ} (A B : PSD n) :
    ∃ S T : Mat n n, A.val =
      S * S.transpose ∧ B.val
       = T * T.transpose ∧ -- @realizes \bS(real Gram factor) @realizes \bT(real Gram factor)
      frob (S - T) = buresDistance A.val B.val := by
  obtain ⟨U, hU⟩ := real_procrustes_attainment A B
  refine ⟨CFC.sqrt A.val, CFC.sqrt B.val * U.val, ?_, ?_, hU⟩
  · rw [show (CFC.sqrt A.val).transpose = CFC.sqrt A.val from
      (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self A.val A.property.nonneg]
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U.val,
      show U.val * U.val.transpose = 1 from U.property.2, Matrix.one_mul,
      show (CFC.sqrt B.val).transpose = CFC.sqrt B.val from
        (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self B.val B.property.nonneg]

end Papers.WassersteinRegretS2S3
