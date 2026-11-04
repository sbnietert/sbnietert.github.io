module
public import Papers.WassersteinRegretS2S3.Helpers.SpectralBounds
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Attained Rayleigh extrema

Unit eigenvectors for the concrete variational spectral quantities used in the
condition-number formula. No simplicity of an eigenvalue is required.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: rayleigh_values_bddBelow
/-- For [a square matrix A](hyp:A), [its quadratic-form values over unit vectors
are bounded below](goal). -/
lemma rayleigh_values_bddBelow {n : ℕ} (A : Mat n n) :
    BddBelow {t : ℝ | ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = t} := by
  refine ⟨-opNorm A, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  have h := abs_real_inner_le_norm x (matrixCLM A x)
  have hb := (matrixCLM A).le_opNorm x
  rw [hx, one_mul] at h
  rw [hx, mul_one] at hb
  exact (neg_le_of_abs_le (h.trans hb))

-- @node: lambdaMin_le_rayleigh
/-- For [a square matrix A](hyp:A) and [a vector x](hyp:x), if [x has unit
norm](hyp:hx), then [the infimum of A's quadratic-form values over unit vectors
is at most its value at x](goal). -/
lemma lambdaMin_le_rayleigh {n : ℕ} (A : Mat n n) (x : Euc n) (hx : ‖x‖ = 1) :
    lambdaMin A ≤ inner ℝ x (matrixCLM A x) :=
  csInf_le (rayleigh_values_bddBelow A) ⟨x, hx, rfl⟩

-- @node: lambdaMin_attained
/-- For [a square matrix A](hyp:A) in positive dimension, [there is a unit vector
whose quadratic-form value equals the infimum over all unit vectors](goal). -/
lemma lambdaMin_attained {n : ℕ} [NeZero n] (A : Mat n n) :
    ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = lambdaMin A := by
  obtain ⟨_, x₀, hx₀, _⟩ := rayleigh_values_nonempty A
  have hne : (Metric.sphere (0 : Euc n) 1).Nonempty := ⟨x₀, by simpa using hx₀⟩
  have hc : Continuous (fun x : Euc n => inner ℝ x (matrixCLM A x)) := by fun_prop
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : Euc n) 1).exists_isMinOn hne hc.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm ?_ (lambdaMin_le_rayleigh A x hx')⟩
  apply le_csInf (rayleigh_values_nonempty A)
  rintro t ⟨y, hy, rfl⟩
  exact hmin (by simpa using hy)

-- @node: lambdaMax_attained
/-- For [a square matrix A](hyp:A) in positive dimension, [there is a unit vector
whose quadratic-form value equals the supremum over all unit vectors](goal). -/
lemma lambdaMax_attained {n : ℕ} [NeZero n] (A : Mat n n) :
    ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = lambdaMax A := by
  obtain ⟨_, x₀, hx₀, _⟩ := rayleigh_values_nonempty A
  have hne : (Metric.sphere (0 : Euc n) 1).Nonempty := ⟨x₀, by simpa using hx₀⟩
  have hc : Continuous (fun x : Euc n => inner ℝ x (matrixCLM A x)) := by fun_prop
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : Euc n) 1).exists_isMaxOn hne hc.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm (rayleigh_le_lambdaMax A x hx') ?_⟩
  apply csSup_le (rayleigh_values_nonempty A)
  rintro t ⟨y, hy, rfl⟩
  exact hmax (by simpa using hy)

-- @node: lambdaMin_pos_of_posDef
/-- For [a square matrix A](hyp:A) in positive dimension, if [A is positive
definite](hyp:hA), then [its smallest eigenvalue is strictly positive](goal). -/
lemma lambdaMin_pos_of_posDef {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.PosDef) : 0 < lambdaMin A := by
  obtain ⟨x, hx, he⟩ := lambdaMin_attained A
  have hne : (fun i => x i) ≠ 0 := by
    intro hz
    have : x = 0 := by ext i; exact congrFun hz i
    simp [this] at hx
  rw [← he]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM, Matrix.toLpLin_apply,
    dotProduct_comm] using hA.dotProduct_mulVec_pos hne

-- @node: matrixCLM_isSelfAdjoint
/-- If [a real square matrix A](hyp:A) is [symmetric](hyp:hA), then [the linear
operator it induces on Euclidean space is self-adjoint](goal). -/
lemma matrixCLM_isSelfAdjoint {n : ℕ} (A : Mat n n) (hA : A.IsHermitian) :
    IsSelfAdjoint (matrixCLM A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA

-- @node: lambdaMin_unit_eigenvector
/-- For [a real square matrix A](hyp:A) in positive dimension, if [A is
symmetric](hyp:hA), then [there is a unit eigenvector with eigenvalue equal to
the infimum of A's quadratic form over unit vectors](goal). -/
lemma lambdaMin_unit_eigenvector {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.IsHermitian) :
    ∃ x : Euc n, ‖x‖ = 1 ∧ matrixCLM A x = lambdaMin A • x := by
  obtain ⟨x, hx, he⟩ := lambdaMin_attained A
  have hmin : IsMinOn (matrixCLM A).reApplyInnerSelf (Metric.sphere 0 ‖x‖) x := by
    intro y hy
    have hy' : ‖y‖ = 1 := by simpa [hx] using hy
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm, he] using
      lambdaMin_le_rayleigh A y hy'
  have heig := (matrixCLM_isSelfAdjoint A hA).eq_smul_self_of_isLocalExtrOn
    (Or.inl hmin.localize)
  refine ⟨x, hx, ?_⟩
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    real_inner_comm, hx, he] using heig

-- @node: lambdaMax_unit_eigenvector
/-- For [a real square matrix A](hyp:A) in positive dimension, if [A is
symmetric](hyp:hA), then [there is a unit eigenvector with eigenvalue equal to
the supremum of A's quadratic form over unit vectors](goal). -/
lemma lambdaMax_unit_eigenvector {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.IsHermitian) :
    ∃ x : Euc n, ‖x‖ = 1 ∧ matrixCLM A x = lambdaMax A • x := by
  obtain ⟨x, hx, he⟩ := lambdaMax_attained A
  have hmax : IsMaxOn (matrixCLM A).reApplyInnerSelf (Metric.sphere 0 ‖x‖) x := by
    intro y hy
    have hy' : ‖y‖ = 1 := by simpa [hx] using hy
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm, he] using
      rayleigh_le_lambdaMax A y hy'
  have heig := (matrixCLM_isSelfAdjoint A hA).eq_smul_self_of_isLocalExtrOn
    (Or.inr hmax.localize)
  refine ⟨x, hx, ?_⟩
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    real_inner_comm, hx, he] using heig

-- @node: matrixCLM_inv_eigenvector
/-- For [a square matrix A](hyp:A) that is [positive definite](hyp:hA),
[a vector x](hyp:x), and [a real scalar t](hyp:t), if [t is nonzero](hyp:ht)
and [A maps x to t times x](hyp:hx), then [the inverse of A maps x to x
scaled by the reciprocal of t](goal). -/
lemma matrixCLM_inv_eigenvector {n : ℕ} (A : Mat n n) (hA : A.PosDef)
    (x : Euc n) (t : ℝ) (ht : t ≠ 0) (hx : matrixCLM A x = t • x) :
    matrixCLM A⁻¹ x = t⁻¹ • x := by
  have hid : matrixCLM A⁻¹ (matrixCLM A x) = x := by
    ext i
    change (A⁻¹ *ᵥ (A *ᵥ x.ofLp)) i = x i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  rw [hx, map_smul] at hid
  calc
    matrixCLM A⁻¹ x = t⁻¹ • (t • matrixCLM A⁻¹ x) := by
      rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = t⁻¹ • x := by rw [hid]

-- @node: lambdaMax_inv_eq_inv_lambdaMin
/-- For [a square matrix A](hyp:A) in positive dimension, if [A is positive
definite](hyp:hA), then [the largest eigenvalue of its inverse is the reciprocal
of its smallest eigenvalue](goal). -/
lemma lambdaMax_inv_eq_inv_lambdaMin {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.PosDef) : lambdaMax A⁻¹ = (lambdaMin A)⁻¹ := by
  have hp := lambdaMin_pos_of_posDef A hA
  obtain ⟨x, hx, hex⟩ := lambdaMin_unit_eigenvector A hA.isHermitian
  have hix := matrixCLM_inv_eigenvector A hA x _ hp.ne' hex
  have hl : (lambdaMin A)⁻¹ ≤ lambdaMax A⁻¹ := by
    have hr := rayleigh_le_lambdaMax A⁻¹ x hx
    simpa [hix, real_inner_smul_right, real_inner_self_eq_norm_sq, hx] using hr
  have hi : 0 < lambdaMax A⁻¹ := (inv_pos.mpr hp).trans_le hl
  obtain ⟨y, hy, hey⟩ := lambdaMax_unit_eigenvector A⁻¹ hA.inv.isHermitian
  have hiy := matrixCLM_inv_eigenvector A⁻¹ hA.inv y _ hi.ne' hey
  rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] at hiy
  have hm : lambdaMin A ≤ (lambdaMax A⁻¹)⁻¹ := by
    have hr := lambdaMin_le_rayleigh A y hy
    simpa [hiy, real_inner_smul_right, real_inner_self_eq_norm_sq, hy] using hr
  exact le_antisymm ((le_inv_comm₀ hi hp).mpr hm) hl

-- @node: rayleigh_le_lambdaMax_mul_norm_sq
/-- For [a square matrix A](hyp:A) and [any vector x](hyp:x), [A's quadratic-form
value at x is at most the supremum over unit vectors multiplied by the squared
norm of x](goal). -/
lemma rayleigh_le_lambdaMax_mul_norm_sq {n : ℕ} (A : Mat n n) (x : Euc n) :
    inner ℝ x (matrixCLM A x) ≤ lambdaMax A * ‖x‖ ^ 2 := by
  by_cases hz : x = 0
  · simp [hz]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
  let y := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
  have he : x = ‖x‖ • y := by simp [y, smul_smul, hn.ne']
  have hquad : inner ℝ x (matrixCLM A x) = ‖x‖ ^ 2 * inner ℝ y (matrixCLM A y) := by
    conv_lhs => rw [he]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hquad]
  exact (mul_le_mul_of_nonneg_left (rayleigh_le_lambdaMax A y hy) (sq_nonneg ‖x‖)).trans_eq
    (mul_comm _ _)

-- @node: lambdaMax_spectral_envelope
/-- For [a real square matrix A](hyp:A), if [A is symmetric](hyp:hA), then
[the identity matrix scaled by A's largest eigenvalue, minus A, is positive
semidefinite](goal). -/
lemma lambdaMax_spectral_envelope {n : ℕ} (A : Mat n n) (hA : A.IsHermitian) :
    (lambdaMax A • (1 : Mat n n) - A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (by exact star_trivial _)).sub hA)
  intro v
  let x : Euc n := WithLp.toLp 2 v
  have hb := rayleigh_le_lambdaMax_mul_norm_sq A x
  have hi : inner ℝ x (matrixCLM (lambdaMax A • (1 : Mat n n) - A) x) =
      lambdaMax A * ‖x‖ ^ 2 - inner ℝ x (matrixCLM A x) := by
    simp [matrixCLM, map_sub, map_smul, inner_sub_right, real_inner_smul_right,
      Matrix.toLpLin_apply]
  have hp : 0 ≤ inner ℝ x (matrixCLM (lambdaMax A • (1 : Mat n n) - A) x) := by
    rw [hi]; exact sub_nonneg.mpr hb
  simpa [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM, Matrix.toLpLin_apply,
    x, dotProduct_comm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul] using hp

-- @node: inverse_feature_spectral_envelope
/-- For [a square matrix A](hyp:A) in positive dimension, if [A is positive
definite](hyp:hA), then [the identity matrix scaled by the reciprocal of A's
smallest eigenvalue, minus the inverse of A, is positive semidefinite](goal). -/
lemma inverse_feature_spectral_envelope {n : ℕ} [NeZero n] (A : Mat n n)
    (hA : A.PosDef) : ((lambdaMin A)⁻¹ • (1 : Mat n n) - A⁻¹).PosSemidef := by
  rw [← lambdaMax_inv_eq_inv_lambdaMin A hA]
  exact lambdaMax_spectral_envelope A⁻¹ hA.inv.isHermitian

end Papers.WassersteinRegretS2S3
