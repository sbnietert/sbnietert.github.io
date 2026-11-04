module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Population Wasserstein regret: Helpers/Kronecker

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:kronecker-fact
/-- For [a square matrix A](hyp:A), [a square matrix B](hyp:B), and [a compatible rectangular
matrix C](hyp:C), [the trace of A times C times B times the transpose of C equals the
quadratic form of the column-stacked entries of C with matrix given by the Kronecker
product of the transpose of B and A](goal). -/
lemma kroneckerFact {a b : ℕ}
    (A : Mat a a) -- @realizes \bA(real square trace factor)
    (B : Mat b b) -- @realizes \bB(real square Kronecker factor)
    (C : Mat a b) : -- @realizes \bC(arbitrary compatible rectangle)
    Matrix.trace (A * C * B * C.transpose) =
      Matrix.vec C ⬝ᵥ ((Matrix.kronecker B.transpose A) *ᵥ Matrix.vec C) := by
  rw [Matrix.kronecker, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    Matrix.vec_dotProduct_vec]
  exact Matrix.trace_mul_comm (A * C * B) C.transpose

end Papers.WassersteinRegretS2S3
