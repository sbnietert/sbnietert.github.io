module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs
public import Toolkit.Foundations.LinearAlgebra.Matrix.BuresWasserstein

/-!
# Population Wasserstein regret: Helpers/RealComplex

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

open scoped ComplexOrder

/-- For [a real matrix A](hyp:A), its [complexification](goal) is the complex matrix
with the same entries, each having zero imaginary part. -/
def complexify {a b : ℕ} (A : Mat a b) : Matrix (Fin a) (Fin b) ℂ := fun i j => (A i j : ℂ)
/-- For [a complex matrix A](hyp:A), its [real part](goal) is the real matrix
obtained by taking the real part of each entry. -/
def realPart {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Mat a b := fun i j => (A i j).re

/-- For [a real Euclidean vector x](hyp:x), its [complex Euclidean embedding](goal)
has the same coordinates, each with zero imaginary part. -/
def embedEuclidean {n : ℕ} (x : Euc n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => (x i : ℂ))
/-- For [a complex Euclidean vector z](hyp:z), its [real Euclidean part](goal)
is the vector of real parts of its coordinates. -/
def realEuclidean {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) : Euc n :=
  WithLp.toLp 2 (fun i => (z i).re)

-- @node: complexify_mul
/-- [Complexifying a product of two real matrices gives the product of their
complexifications](goal). -/
lemma complexify_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply, Complex.ofReal_sum]
-- @node: complexify_transpose
/-- [Complexifying the transpose of a real matrix gives the conjugate transpose
of its complexification](goal). -/
lemma complexify_transpose {a b : ℕ} (A : Mat a b) :
    complexify A.transpose = (complexify A).conjTranspose := by
  ext i j
  simp [complexify]
-- @node: complexify_sub
/-- [Complexifying the difference of two real matrices gives the difference of
their complexifications](goal). -/
lemma complexify_sub {a b : ℕ} (A B : Mat a b) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  simp [complexify]

-- @node: complexify_orthogonal
/-- [The complexification of a real orthogonal matrix is unitary](goal). -/
lemma complexify_orthogonal {n : ℕ} (U : Orth n) :
    complexify U.val ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change complexify U.val * (complexify U.val).conjTranspose = 1
  rw [← complexify_transpose, ← complexify_mul,
    show U.val * U.val.transpose = 1 from U.property.2]
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.one_apply, h]

-- @node: complexify_posSemidef
/-- [The complexification of a real positive semidefinite matrix is positive
semidefinite over the complex numbers](goal). -/
lemma complexify_posSemidef {n : ℕ} (A : PSD n) : (complexify A.val).PosSemidef := by
  have hS : (CFC.sqrt A.val).transpose = CFC.sqrt A.val :=
    (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq
  have hGram : (complexify (CFC.sqrt A.val)).conjTranspose *
      complexify (CFC.sqrt A.val) = complexify A.val := by
    rw [← complexify_transpose, hS, ← complexify_mul,
      CFC.sqrt_mul_sqrt_self A.val A.property.nonneg]
  rw [← hGram]
  exact Matrix.posSemidef_conjTranspose_mul_self _
-- @node: complexify_sqrt
/-- [The positive semidefinite square root of the complexification of a real
positive semidefinite matrix equals the complexification of its square root](goal). -/
lemma complexify_sqrt {n : ℕ} (A : PSD n) :
    CFC.sqrt (complexify A.val) = complexify (CFC.sqrt A.val) := by
  apply (CFC.sqrt_eq_iff _ _ (complexify_posSemidef A).nonneg
    (complexify_posSemidef ⟨_, (CFC.sqrt_nonneg A.val).posSemidef⟩).nonneg).mpr
  rw [← complexify_mul, CFC.sqrt_mul_sqrt_self A.val A.property.nonneg]
-- @node: complexify_sandwich_sqrt
/-- [For real positive semidefinite matrices A and B, the square root of the
product formed by sandwiching the complexification of B between two square roots
of the complexification of A equals the complexification of the square root of
the real product formed by sandwiching B between two square roots of A](goal). -/
lemma complexify_sandwich_sqrt {n : ℕ} (A B : PSD n) :
    CFC.sqrt (CFC.sqrt (complexify A.val) * complexify B.val * CFC.sqrt (complexify A.val)) =
    complexify (CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val)) := by
  have hS : (CFC.sqrt A.val).IsHermitian := (CFC.sqrt_nonneg A.val).posSemidef.isHermitian
  have hPSD : (CFC.sqrt A.val * B.val * CFC.sqrt A.val).PosSemidef := by
    simpa only [hS.eq, Matrix.conjTranspose_eq_transpose_of_trivial] using
      B.property.mul_mul_conjTranspose_same (CFC.sqrt A.val)
  rw [complexify_sqrt, ← complexify_mul, ← complexify_mul]
  exact complexify_sqrt ⟨_, hPSD⟩
-- @node: complexify_trace
/-- [The real part of the trace of a complexified real square matrix equals the
trace of the original matrix](goal). -/
lemma complexify_trace {n : ℕ} (A : Mat n n) : (Matrix.trace (complexify A)).re = Matrix.trace
  A := by
  simp [Matrix.trace, complexify, Complex.re_sum]
-- @node: complexify_frob
/-- [Complexifying a real matrix preserves its Frobenius norm](goal). -/
lemma complexify_frob {a b : ℕ} (A : Mat a b) :
    Toolkit.Foundations.LinearAlgebra.Matrix.frobeniusNorm (complexify A) = frob A := by
  simp [Toolkit.Foundations.LinearAlgebra.Matrix.frobeniusNorm, frob, complexify,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
-- @node: complexify_bures
/-- [The complex Bures distance between the complexifications of two real
positive semidefinite matrices equals their real Bures distance](goal). -/
lemma complexify_bures {n : ℕ} (A B : PSD n) :
    Toolkit.Foundations.LinearAlgebra.Matrix.buresDistance (complexify A.val) (complexify B.val) =
    buresDistance A.val B.val := by
  unfold Toolkit.Foundations.LinearAlgebra.Matrix.buresDistance buresDistance
  rw [complexify_sandwich_sqrt, complexify_trace, complexify_trace, complexify_trace]

end Papers.WassersteinRegretS2S3
