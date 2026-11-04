module
public import Papers.WassersteinRegretS2S3.Helpers.RefinedStability

/-!
# Variational spectral bounds for the alternative condition number

The bounds use uncentered PSD moments, including singular residual moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: rayleigh_values_nonempty
/-- For [a square matrix A](hyp:A) in positive dimension, [the set of quadratic-form
values over unit vectors is nonempty](goal). -/
lemma rayleigh_values_nonempty {n : ℕ} [NeZero n] (A : Mat n n) :
    {t : ℝ | ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = t}.Nonempty := by
  let x := EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)
  exact ⟨_, x, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one _, rfl⟩

-- @node: rayleigh_values_bddAbove
/-- For [a square matrix A](hyp:A), [its quadratic-form values over unit vectors
are bounded above](goal). -/
lemma rayleigh_values_bddAbove {n : ℕ} (A : Mat n n) :
    BddAbove {t : ℝ | ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = t} := by
  refine ⟨opNorm A, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  calc
    _ ≤ ‖x‖ * ‖matrixCLM A x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (opNorm A * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((matrixCLM A).le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [hx]; ring

-- @node: rayleigh_le_lambdaMax
/-- For [a square matrix A](hyp:A) and [a vector x](hyp:x), if [x has unit
norm](hyp:hx), then [its quadratic-form value is at most the supremum of A's
quadratic-form values over unit vectors](goal). -/
lemma rayleigh_le_lambdaMax {n : ℕ} (A : Mat n n) (x : Euc n) (hx : ‖x‖ = 1) :
    inner ℝ x (matrixCLM A x) ≤ lambdaMax A :=
  le_csSup (rayleigh_values_bddAbove A) ⟨x, hx, rfl⟩

-- @node: lambdaMax_le_opNorm
/-- For [a square matrix A](hyp:A) in positive dimension, [the supremum of its
quadratic-form values over unit vectors is at most its Euclidean operator norm](goal). -/
lemma lambdaMax_le_opNorm {n : ℕ} [NeZero n] (A : Mat n n) :
    lambdaMax A ≤ opNorm A :=
by
  apply csSup_le (rayleigh_values_nonempty A)
  rintro t ⟨x, hx, rfl⟩
  calc
    _ ≤ ‖x‖ * ‖matrixCLM A x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (opNorm A * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((matrixCLM A).le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [hx]; ring

-- @node: psd_rayleigh_nonneg
/-- If [a square matrix A](hyp:A) is [positive semidefinite](hyp:hA), then
[its quadratic-form value at any vector x is nonnegative](goal), for
[an arbitrary vector x](hyp:x). -/
lemma psd_rayleigh_nonneg {n : ℕ} (A : Mat n n) (hA : A.PosSemidef) (x : Euc n) :
    0 ≤ inner ℝ x (matrixCLM A x) := by
  simpa [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM, Matrix.toLpLin_apply, dotProduct_comm]
    using hA.dotProduct_mulVec_nonneg (fun i => x i)

-- @node: lambdaMax_mono_rayleigh
/-- For [square matrices A and B](hyp:A,B) in positive dimension, if [A's
quadratic form is everywhere at most B's](hyp:h), then [the supremum of A's
quadratic form over unit vectors is at most the corresponding supremum for B](goal). -/
lemma lambdaMax_mono_rayleigh {n : ℕ} [NeZero n] (A B : Mat n n)
    (h : ∀ x : Euc n, inner ℝ x (matrixCLM A x) ≤ inner ℝ x (matrixCLM B x)) :
    lambdaMax A ≤ lambdaMax B := by
  apply csSup_le (rayleigh_values_nonempty A)
  rintro t ⟨x, hx, rfl⟩
  exact (h x).trans (rayleigh_le_lambdaMax B x hx)

-- @node: lambdaMax_add_le
/-- For [square matrices A and B](hyp:A,B) in positive dimension, [the supremum
of the quadratic form of their sum over unit vectors is at most the sum of
their separate suprema](goal). -/
lemma lambdaMax_add_le {n : ℕ} [NeZero n] (A B : Mat n n) :
    lambdaMax (A + B) ≤ lambdaMax A + lambdaMax B := by
  apply csSup_le (rayleigh_values_nonempty (A + B))
  rintro t ⟨x, hx, rfl⟩
  simpa [matrixCLM, map_add, inner_add_right] using
    add_le_add (rayleigh_le_lambdaMax A x hx) (rayleigh_le_lambdaMax B x hx)

-- @node: lambdaMax_smul_nonneg
/-- For [a square matrix A](hyp:A) in positive dimension and [a real scalar c](hyp:c)
that is [nonnegative](hyp:hc), [scaling A by c scales the supremum of its
quadratic form over unit vectors by c](goal). -/
lemma lambdaMax_smul_nonneg {n : ℕ} [NeZero n] (A : Mat n n) (c : ℝ) (hc : 0 ≤ c) :
    lambdaMax (c • A) = c * lambdaMax A := by
  have hu : lambdaMax (c • A) ≤ c * lambdaMax A := by
    apply csSup_le (rayleigh_values_nonempty (c • A))
    rintro t ⟨x, hx, rfl⟩
    simpa [matrixCLM, map_smul, real_inner_smul_right] using
      mul_le_mul_of_nonneg_left (rayleigh_le_lambdaMax A x hx) hc
  apply le_antisymm hu
  by_cases hz : c = 0
  · subst c
    obtain ⟨t, x, hx, ht⟩ := rayleigh_values_nonempty (0 : Mat n n)
    have hl := rayleigh_le_lambdaMax (0 : Mat n n) x hx
    simpa [lambdaMax, matrixCLM] using hl
  · have hp : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
    rw [mul_comm c]
    apply (le_div_iff₀ hp).mp
    apply csSup_le (rayleigh_values_nonempty A)
    rintro t ⟨x, hx, rfl⟩
    apply (le_div_iff₀ hp).mpr
    have hl := rayleigh_le_lambdaMax (c • A) x hx
    simpa [matrixCLM, map_smul, real_inner_smul_right, mul_comm] using hl

-- @node: lambdaMax_gram
/-- For [a rectangular matrix A](hyp:A) with a positive number of rows,
[the largest eigenvalue of A times its transpose equals the square of A's
Euclidean operator norm](goal). -/
lemma lambdaMax_gram {m d : ℕ} [NeZero m] (A : Mat m d) :
    lambdaMax (A * A.transpose) = opNorm A ^ 2 := by
  have hn : opNorm (A * A.transpose) = opNorm A ^ 2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self A.transpose
    change opNorm (A.transpose.conjTranspose * A.transpose) =
      opNorm A.transpose * opNorm A.transpose at h
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      opNorm_transpose, pow_two] using h
  apply le_antisymm ((lambdaMax_le_opNorm _).trans_eq hn)
  have h := pow_le_pow_left₀ (norm_nonneg _) (refined_gram_opNorm_le_sqrt_lambdaMax A) 2
  have hp : 0 ≤ lambdaMax (A * A.transpose) := by
    obtain ⟨t, x, hx, ht⟩ := rayleigh_values_nonempty (A * A.transpose)
    have hA : (A * A.transpose).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose A
    exact (psd_rayleigh_nonneg _ hA x).trans (rayleigh_le_lambdaMax _ x hx)
  rwa [Real.sq_sqrt hp] at h

-- @node: lambdaMax_psd_sum_bounds
/-- For [square matrices A and B](hyp:A,B) in positive dimension, if [A is
positive semidefinite](hyp:hA) and [B is positive semidefinite](hyp:hB), then
[the largest eigenvalue of their sum lies between the larger of their largest
eigenvalues and the sum of those eigenvalues](goal). -/
lemma lambdaMax_psd_sum_bounds {n : ℕ} [NeZero n] (A B : Mat n n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    max (lambdaMax A) (lambdaMax B) ≤ lambdaMax (A + B) ∧
      lambdaMax (A + B) ≤ lambdaMax A + lambdaMax B := by
  refine ⟨max_le ?_ ?_, lambdaMax_add_le A B⟩
  · apply lambdaMax_mono_rayleigh
    intro x
    simpa [matrixCLM, map_add, inner_add_right] using
      le_add_of_nonneg_right (psd_rayleigh_nonneg B hB x)
        (a := inner ℝ x (matrixCLM A x))
  · apply lambdaMax_mono_rayleigh
    intro x
    simpa [matrixCLM, map_add, inner_add_right] using
      le_add_of_nonneg_left (psd_rayleigh_nonneg A hA x)
        (a := inner ℝ x (matrixCLM B x))

-- @node: lambdaMin_nonneg_of_psd
/-- For [a square matrix A](hyp:A) in positive dimension, if [A is positive
semidefinite](hyp:hA), then [its smallest eigenvalue is nonnegative](goal). -/
lemma lambdaMin_nonneg_of_psd {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.PosSemidef) : 0 ≤ lambdaMin A := by
  apply le_csInf (rayleigh_values_nonempty A)
  rintro t ⟨x, hx, rfl⟩
  exact psd_rayleigh_nonneg A hA x

-- @node: conditionSpectral_bounds
/-- For [a joint second-moment matrix Sigma with a positive definite feature
block](hyp:Sigma) and positive feature and response dimensions, [the spectral
condition expression lies between the lower and upper condition expressions](goal).

The lower expression is one plus the maximum of the squared canonical coefficient
operator norm and the residual-to-feature spectral ratio; the upper expression
is one plus their sum. -/
lemma conditionSpectral_bounds {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : NondegenerateSecondMoments p m) :
    conditionLower Sigma.carrier.val.val ≤ conditionSpectral Sigma.carrier.val.val ∧
      conditionSpectral Sigma.carrier.val.val ≤ conditionUpper Sigma.carrier.val.val := by
  let S := Sigma.carrier.val.val
  let A := canonicalCoefficient S
  let c := (lambdaMin (blockX p m S))⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr
    (lambdaMin_nonneg_of_psd _ Sigma.carrier.property.posSemidef)
  have hE : (matrixResidual S).PosSemidef :=
    Sigma.carrier.val.property.mul_mul_conjTranspose_same (quadraticRegressionMatrix A)
  have hA : (A * A.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  have hb := lambdaMax_psd_sum_bounds (A * A.transpose) (c • matrixResidual S)
    hA (hE.smul hc)
  rw [lambdaMax_gram, lambdaMax_smul_nonneg _ c hc] at hb
  constructor
  · simpa only [conditionLower, conditionSpectral, S, A, c, div_eq_mul_inv,
      mul_comm, add_comm] using add_le_add_left hb.1 1
  · simpa only [conditionUpper, conditionSpectral, S, A, c, div_eq_mul_inv,
      mul_comm, add_assoc, add_comm, add_left_comm] using add_le_add_left hb.2 1

end Papers.WassersteinRegretS2S3
