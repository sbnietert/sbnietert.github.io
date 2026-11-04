module
public import Papers.WassersteinRegretS2S3.Helpers.SpectralExtrema
public import Papers.WassersteinRegretS2S3.Helpers.Kronecker

/-!
# Dominant block of the condition-number Kronecker sum

The inverse feature moment selects the largest residual-plus-regression block.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: condition_vec_dot_self
/-- [The squared Euclidean length of the vectorized matrix B equals the squared
Frobenius norm of B](goal). -/
lemma condition_vec_dot_self {m p : ℕ} (B : Mat m p) :
    Matrix.vec B ⬝ᵥ Matrix.vec B = frob B ^ 2 := by
  rw [Matrix.vec_dotProduct_vec, frob_sq_trace]

-- @node: condition_kronecker_rayleigh_upper
/-- If [H is symmetric](hyp:hH), [E is positive semidefinite](hyp:hE), and [G is
symmetric](hyp:hG), then [the quadratic form at the vectorized B of the Kronecker sum
of H with E and the identity with G is at most the largest eigenvalue of the matrix
obtained by adding the largest eigenvalue of H times E to G, multiplied by the squared
Frobenius norm of B](goal). -/
lemma condition_kronecker_rayleigh_upper {m p : ℕ} (H : Mat p p) (E G : Mat m m)
    (hH : H.IsHermitian) (hE : E.PosSemidef) (hG : G.IsHermitian) (B : Mat m p) :
    Matrix.vec B ⬝ᵥ ((Matrix.kronecker H E + Matrix.kronecker (1 : Mat p p) G) *ᵥ
      Matrix.vec B) ≤ lambdaMax (G + lambdaMax H • E) * frob B ^ 2 := by
  let c := lambdaMax H
  let K := G + c • E
  have hK : K.IsHermitian := hG.add (hE.isHermitian.smul (by exact star_trivial _))
  have hp := ((Matrix.PosSemidef.one : (1 : Mat p p).PosSemidef).kronecker
    (lambdaMax_spectral_envelope K hK)).add
      ((lambdaMax_spectral_envelope H hH).kronecker hE)
  have he : Matrix.kronecker (1 : Mat p p) (lambdaMax K • (1 : Mat m m) - K) +
      Matrix.kronecker (c • (1 : Mat p p) - H) E =
      lambdaMax K • (1 : Matrix (Fin p × Fin m) (Fin p × Fin m) ℝ) -
        (Matrix.kronecker H E + Matrix.kronecker (1 : Mat p p) G) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kronecker, Matrix.kroneckerMap_apply, K, Matrix.one_apply]
    by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj] <;> ring
  change (Matrix.kronecker (1 : Mat p p) (lambdaMax K • (1 : Mat m m) - K) +
    Matrix.kronecker (c • (1 : Mat p p) - H) E).PosSemidef at hp
  rw [he] at hp
  have hb := hp.dotProduct_mulVec_nonneg (Matrix.vec B)
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    condition_vec_dot_self, sub_nonneg, K, c] using hb

-- @node: condition_outer_frob_sq
/-- [The squared Frobenius norm of the outer product of y with x equals the product of
their squared Euclidean norms](goal). -/
lemma condition_outer_frob_sq {m p : ℕ} (x : Euc p) (y : Euc m) :
    frob (Matrix.vecMulVec y.ofLp x.ofLp) ^ 2 = ‖y‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [frob_sq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.vecMulVec_apply, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

-- @node: condition_outer_kronecker_eigenvector
/-- If [H maps x to c times x](hyp:hx) and [G plus c times E maps y to t times y](hyp:hy),
then [the Kronecker sum of H with E and the identity with G maps the vectorized outer
product of y with x to t times that same vector](goal). -/
lemma condition_outer_kronecker_eigenvector {m p : ℕ}
    (H : Mat p p) (E G : Mat m m) (x : Euc p) (y : Euc m) (c t : ℝ)
    (hx : matrixCLM H x = c • x) (hy : matrixCLM (G + c • E) y = t • y) :
    (Matrix.kronecker H E + Matrix.kronecker (1 : Mat p p) G) *ᵥ
      Matrix.vec (Matrix.vecMulVec y.ofLp x.ofLp) =
        t • Matrix.vec (Matrix.vecMulVec y.ofLp x.ofLp) := by
  have hx' : H *ᵥ x.ofLp = c • x.ofLp := congrArg WithLp.ofLp hx
  have hy' : (G + c • E) *ᵥ y.ofLp = t • y.ofLp := congrArg WithLp.ofLp hy
  rw [Matrix.add_mulVec, Matrix.kronecker,
    Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec]
  ext ⟨j, i⟩
  change ((E * Matrix.vecMulVec y.ofLp x.ofLp * H.transpose) i j +
    (G * Matrix.vecMulVec y.ofLp x.ofLp * (1 : Mat p p).transpose) i j) =
      t * (y i * x j)
  simp only [Matrix.transpose_one, Matrix.mul_one]
  have he : (E * Matrix.vecMulVec y.ofLp x.ofLp * H.transpose) i j =
      (E *ᵥ y.ofLp) i * (H *ᵥ x.ofLp) j := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    simp only [Matrix.vecMulVec_apply, Matrix.vecMul_transpose]
  have hg : (G * Matrix.vecMulVec y.ofLp x.ofLp) i j = (G *ᵥ y.ofLp) i * x j := by
    rw [Matrix.mul_vecMulVec]
    rfl
  rw [he, hg, hx']
  have hi := congrFun hy' i
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hi ⊢
  nlinarith [congrArg (fun a : ℝ => a * x j) hi]

-- @node: condition_kronecker_rayleigh_attained
/-- In positive feature and response dimensions, if [H is symmetric](hyp:hH), [E is
positive semidefinite](hyp:hE), and [G is symmetric](hyp:hG), then [there exists a matrix
B of Frobenius norm one whose vectorization gives a quadratic form for the Kronecker
sum of H with E and the identity with G equal to the largest eigenvalue of the matrix
obtained by adding the largest eigenvalue of H times E to G](goal). -/
lemma condition_kronecker_rayleigh_attained {m p : ℕ} [NeZero m] [NeZero p]
    (H : Mat p p) (E G : Mat m m)
    (hH : H.IsHermitian) (hE : E.PosSemidef) (hG : G.IsHermitian) :
    ∃ B : Mat m p, frob B = 1 ∧
      Matrix.vec B ⬝ᵥ ((Matrix.kronecker H E + Matrix.kronecker (1 : Mat p p) G) *ᵥ
        Matrix.vec B) = lambdaMax (G + lambdaMax H • E) := by
  obtain ⟨x, hx, hex⟩ := lambdaMax_unit_eigenvector H hH
  have hK : (G + lambdaMax H • E).IsHermitian :=
    hG.add (hE.isHermitian.smul (by exact star_trivial _))
  obtain ⟨y, hy, hey⟩ := lambdaMax_unit_eigenvector _ hK
  let B := Matrix.vecMulVec y.ofLp x.ofLp
  have hB : frob B = 1 := by
    have hs := condition_outer_frob_sq x y
    rw [hx, hy] at hs
    nlinarith [frob_nonneg B]
  refine ⟨B, hB, ?_⟩
  rw [condition_outer_kronecker_eigenvector H E G x y _ _ hex hey,
    dotProduct_smul, condition_vec_dot_self, hB]
  simp

-- @node: condition_kronecker_spectral_sup
/-- In positive feature and response dimensions, if [H is symmetric](hyp:hH), [E is
positive semidefinite](hyp:hE), and [G is symmetric](hyp:hG), then [the supremum over B
of Frobenius norm one of one plus the quadratic form at the vectorized B of the
Kronecker sum of H with E and the identity with G equals one plus the largest eigenvalue
of the matrix obtained by adding the largest eigenvalue of H times E to G, with both
sides interpreted in the extended nonnegative reals](goal). -/
lemma condition_kronecker_spectral_sup {m p : ℕ} [NeZero m] [NeZero p]
    (H : Mat p p) (E G : Mat m m)
    (hH : H.IsHermitian) (hE : E.PosSemidef) (hG : G.IsHermitian) :
    (⨆ (B : Mat m p) (_ : frob B = 1),
      ENNReal.ofReal (1 + Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker H E + Matrix.kronecker (1 : Mat p p) G) *ᵥ Matrix.vec B))) =
      ENNReal.ofReal (1 + lambdaMax (G + lambdaMax H • E)) := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ENNReal.ofReal_le_ofReal ?_
    have hb := condition_kronecker_rayleigh_upper H E G hH hE hG B
    rw [hB, one_pow, mul_one] at hb
    linarith only [hb]
  · obtain ⟨B, hB, he⟩ := condition_kronecker_rayleigh_attained H E G hH hE hG
    exact le_iSup_of_le B (le_iSup_of_le hB (by rw [he]))

end Papers.WassersteinRegretS2S3
