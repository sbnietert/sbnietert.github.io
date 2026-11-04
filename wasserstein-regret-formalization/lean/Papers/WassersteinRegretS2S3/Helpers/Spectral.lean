module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs
public import Causalean.Mathlib.Analysis.SingularValueWeyl

/-!
# Population Wasserstein regret: Helpers/Spectral

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:factor-perturbation-cited-inequality
/-- [The absolute difference between corresponding singular values of two real
rectangular matrices is at most the operator norm of their difference](goal).

Horn and Johnson (1991), Topics in Matrix Analysis, Theorem 3.3.16(c),
doi:10.1017/CBO9780511840371. Local wrapper of Causalean's installed Weyl inequality. -/
lemma factorPerturbationCitedInequality
    {r d : ℕ} [NeZero r] [NeZero d]
    (S : Mat r d) -- @realizes \bS(arbitrary rectangular factor)
    (barS : Mat r d) -- @realizes \bar{\bS}(arbitrary rectangular comparison)
    (j : ℕ) :
    |singularValue barS j - singularValue S j| ≤ opNorm (barS - S) := by
  have h := abs_singularValues_add_sub_singularValues_le_opNorm
    (Matrix.toEuclideanLin S) (Matrix.toEuclideanLin (barS - S)) j
  simpa [singularValue, opNorm, matrixCLM, map_sub] using h

-- @node: lem:factor-perturbation
/-- [The absolute difference between the minimum singular values of two real
rectangular matrices is at most the operator norm of their difference](goal). -/
lemma factorPerturbation
    {r d : ℕ} [NeZero r] [NeZero d]
    (S : Mat r d) -- @realizes \bS(arbitrary rectangular matrix)
    (barS : Mat r d) : -- @realizes \bar{\bS}(arbitrary rectangular comparison)
    |minSV barS - minSV S| ≤ opNorm (barS - S) := by
  exact factorPerturbationCitedInequality S barS (min r d - 1)
-- @realizes \bar{\bS}(arbitrary real rectangular perturbation)

end Papers.WassersteinRegretS2S3
