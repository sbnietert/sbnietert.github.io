module
public import Papers.WassersteinRegretS2S3.Helpers.Cited
public import Papers.WassersteinRegretS2S3.Helpers.Spectral
public import Papers.WassersteinRegretS2S3.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Population Wasserstein regret: Helpers/BuresGeometry

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: frob_mul_orthogonal
/-- [Multiplying a real square matrix on the right by an orthogonal matrix preserves
its Frobenius norm](goal). -/
lemma frob_mul_orthogonal {n : ℕ} (M : Mat n n) (U : Orth n) :
    frob (M * U.val) = frob M := by
  have h := Toolkit.Foundations.LinearAlgebra.Matrix.frobeniusNorm_mul_unitary
    (complexify M) (complexify_orthogonal U)
  simpa only [← complexify_mul, complexify_frob] using h

-- @node: real_alignment_sq
/-- For positive semidefinite matrices A and B and an orthogonal matrix U, [the
squared Frobenius distance from the square root of A to the square root of B
multiplied by U equals the sum of the traces of A and B minus twice the trace of
the transpose of U times the square root of B times the square root of A](goal). -/
lemma real_alignment_sq {n : ℕ} (A B : PSD n) (U : Orth n) :
    frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) ^ 2 =
      Matrix.trace A.val + Matrix.trace B.val -
        2 * Matrix.trace (U.val.transpose * (CFC.sqrt B.val * CFC.sqrt A.val)) := by
  have hSA : (CFC.sqrt A.val).transpose = CFC.sqrt A.val :=
    (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq
  have hSB : (CFC.sqrt B.val).transpose = CFC.sqrt B.val :=
    (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq
  have h := Toolkit.Foundations.LinearAlgebra.Matrix.frobeniusNorm_sub_mul_unitary_sq
    (complexify (CFC.sqrt A.val)) (complexify (CFC.sqrt B.val)) (complexify_orthogonal U)
  simpa only [← complexify_mul, ← complexify_sub, complexify_frob,
    ← complexify_transpose, hSA, hSB,
    CFC.sqrt_mul_sqrt_self A.val A.property.nonneg,
    CFC.sqrt_mul_sqrt_self B.val B.property.nonneg, complexify_trace] using h

-- @node: bures_radicand_nonneg
/-- For positive semidefinite matrices A and B, [the sum of their traces minus twice
the trace of the square root of the square root of A times B times the square root
of A is nonnegative](goal). -/
lemma bures_radicand_nonneg {n : ℕ} (A B : PSD n) :
    0 ≤ Matrix.trace A.val + Matrix.trace B.val -
      2 * Matrix.trace (CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val)) := by
  obtain ⟨U, hpolar⟩ := real_orthogonal_polar (CFC.sqrt B.val * CFC.sqrt A.val)
  have hSA : (CFC.sqrt A.val).transpose = CFC.sqrt A.val :=
    (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq
  have hSB : (CFC.sqrt B.val).transpose = CFC.sqrt B.val :=
    (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq
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
  rw [← hcross, ← real_alignment_sq A B U]
  exact sq_nonneg _

-- @node: bures_distance_sq
/-- For positive semidefinite matrices A and B, [their squared Bures distance equals
the sum of their traces minus twice the trace of the square root of the square root
of A times B times the square root of A](goal). -/
lemma bures_distance_sq {n : ℕ} (A B : PSD n) :
    buresDistance A.val B.val ^ 2 = Matrix.trace A.val + Matrix.trace B.val -
      2 * Matrix.trace (CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val)) := by
  exact Real.sq_sqrt (bures_radicand_nonneg A B)

-- @node: lem:bures-procrustes
/-- For positive semidefinite matrices A and B, [the Bures distance is the attained
minimum Frobenius distance both between orthogonally aligned square roots and between
arbitrary square factors of A and B; it is at most a nonnegative radius exactly when
A has a factor obtained by perturbing the square root of B by at most that radius
in Frobenius norm; and, if A and B share an orthogonal diagonalization, it equals
the Frobenius distance between their square roots](goal). -/
lemma buresProcrustes {n : ℕ} (A B : PSD n) :
    IsLeast {v : ℝ | ∃ U : Orth n, frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) = v}
      (buresDistance A.val B.val) ∧
    IsLeast {v : ℝ | ∃ S T : Mat n n, A.val = S * S.transpose ∧ B.val = T * T.transpose ∧
      frob (S - T) = v} (buresDistance A.val B.val) ∧
    (∀ eps : ℝ≥0, buresDistance A.val B.val ≤ eps ↔
      ∃ Delta : Mat n n, frob Delta ≤ eps ∧ -- @realizes \bDelta(real full matrix)
        A.val = (CFC.sqrt B.val + Delta) * (CFC.sqrt B.val + Delta).transpose) ∧
    ((∃ U : Orth n, ∃ a b : Fin n → ℝ,
      A.val = U.val * Matrix.diagonal a * U.val.transpose ∧
      B.val = U.val * Matrix.diagonal b * U.val.transpose) →
      frob (CFC.sqrt A.val - CFC.sqrt B.val) = buresDistance A.val B.val) := by
  obtain ⟨horth, hfactor⟩ := CitedProcrustesIdentity A B
  refine ⟨horth, hfactor, ?_, ?_⟩
  · intro eps
    constructor
    · intro heps
      obtain ⟨U, hU⟩ := horth.1
      let Delta := CFC.sqrt A.val * U.val.transpose - CFC.sqrt B.val
      have hnorm : frob Delta = frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) := by
        rw [← frob_mul_orthogonal Delta U]
        congr 1
        dsimp [Delta]
        rw [Matrix.sub_mul, Matrix.mul_assoc,
          show U.val.transpose * U.val = 1 from U.property.1, Matrix.mul_one]
      refine ⟨Delta, hnorm.trans_le (hU.trans_le heps), ?_⟩
      dsimp [Delta]
      rw [add_sub_cancel, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc, ← Matrix.mul_assoc U.val.transpose,
        show U.val.transpose * U.val = 1 from U.property.1, Matrix.one_mul,
        show (CFC.sqrt A.val).transpose = CFC.sqrt A.val from
          (CFC.sqrt_nonneg A.val).posSemidef.isHermitian.eq,
        CFC.sqrt_mul_sqrt_self A.val A.property.nonneg]
    · rintro ⟨Delta, hDelta, hA⟩
      have hB : B.val = CFC.sqrt B.val * (CFC.sqrt B.val).transpose := by
        rw [show (CFC.sqrt B.val).transpose = CFC.sqrt B.val from
          (CFC.sqrt_nonneg B.val).posSemidef.isHermitian.eq,
          CFC.sqrt_mul_sqrt_self B.val B.property.nonneg]
      have hb := hfactor.2 ⟨CFC.sqrt B.val + Delta, CFC.sqrt B.val, hA, hB, rfl⟩
      simpa only [add_sub_cancel_left] using hb.trans (by simpa using hDelta)
  · rintro ⟨U, a, b, hA, hB⟩
    have hAB : Commute A.val B.val := by
      change A.val * B.val = B.val * A.val
      rw [hA, hB]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.val.transpose U.val,
        show U.val.transpose * U.val = 1 from U.property.1, Matrix.one_mul]
      rw [← Matrix.mul_assoc (Matrix.diagonal a), Matrix.diagonal_mul_diagonal,
        ← Matrix.mul_assoc (Matrix.diagonal b), Matrix.diagonal_mul_diagonal]
      congr 2
      exact congrArg Matrix.diagonal (funext fun i => mul_comm (a i) (b i))
    have hSS : Commute (CFC.sqrt A.val) (CFC.sqrt B.val) := by
      simpa only [CFC.sqrt_eq_cfc] using
        ((hAB.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm
    have hP : 0 ≤ CFC.sqrt B.val * CFC.sqrt A.val :=
      Commute.mul_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _) hSS.symm
    have hG : CFC.sqrt A.val * B.val * CFC.sqrt A.val =
        (CFC.sqrt B.val * CFC.sqrt A.val) * (CFC.sqrt B.val * CFC.sqrt A.val) := by
      calc
        _ = CFC.sqrt A.val * (CFC.sqrt B.val * CFC.sqrt B.val) * CFC.sqrt A.val := by
          rw [CFC.sqrt_mul_sqrt_self B.val B.property.nonneg]
        _ = _ := by
          simp only [← Matrix.mul_assoc]
          rw [hSS.eq]
    have hroot : CFC.sqrt (CFC.sqrt A.val * B.val * CFC.sqrt A.val) =
        CFC.sqrt B.val * CFC.sqrt A.val := by
      rw [hG, CFC.sqrt_mul_self _ hP]
    have hcost := real_alignment_sq A B (1 : Orth n)
    simp only [OneMemClass.coe_one, Matrix.mul_one, Matrix.transpose_one,
      Matrix.one_mul] at hcost
    refine (sq_eq_sq₀ (a := frob (CFC.sqrt A.val - CFC.sqrt B.val))
      (b := buresDistance A.val B.val) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp ?_
    rw [bures_distance_sq, hroot]
    exact hcost

-- @node: blockX_factor_gram
/-- For a matrix factor with feature and response rows, [the feature principal block
of the factor times its transpose equals the feature-row factor times its own
transpose](goal). -/
lemma blockX_factor_gram {p m k : ℕ} (S : Mat (p + m) k) :
    blockX p m (S * S.transpose) =
      (factorBlocks p m S).1 * (factorBlocks p m S).1.transpose := by
  ext i j
  rfl

-- @node: frob_factorBlocks_sq
/-- [The squared Frobenius norm of a matrix factor equals the sum of the squared
Frobenius norms of its feature-row and response-row blocks](goal). -/
lemma frob_factorBlocks_sq {p m k : ℕ} (S : Mat (p + m) k) :
    frob S ^ 2 = frob (factorBlocks p m S).1 ^ 2 +
      frob (factorBlocks p m S).2 ^ 2 := by
  simp only [frob_sq, factorBlocks, Matrix.submatrix_apply, id_eq]
  exact Fin.sum_univ_add _

-- @node: opNorm_factorX_sub_le_frob
/-- For two matrix factors, [the operator norm of the difference between their
feature-row blocks is at most the Frobenius norm of the difference between the
full factors](goal). -/
lemma opNorm_factorX_sub_le_frob {p m k : ℕ} (S T : Mat (p + m) k) :
    opNorm ((factorBlocks p m S).1 - (factorBlocks p m T).1) ≤ frob (S - T) := by
  have hblock : (factorBlocks p m S).1 - (factorBlocks p m T).1 =
      (factorBlocks p m (S - T)).1 := rfl
  rw [hblock]
  refine (opNorm_le_frob _).trans ?_
  have h := frob_factorBlocks_sq (S - T)
  have hn := frob_nonneg (factorBlocks p m (S - T)).1
  have ht := frob_nonneg (S - T)
  nlinarith [sq_nonneg (frob (factorBlocks p m (S - T)).2)]

-- @node: bures_factor_minSV_bound
/-- Assuming [singular values are nonnegative and ordered from largest to smallest,
with the smallest indexed by the smaller matrix dimension minus one](hyp:hsv),
[any two positive semidefinite
joint moment matrices admit square factors for which the absolute difference of
the smallest singular values of the feature-row blocks is at most the Bures
distance between the moment matrices](goal). -/
lemma bures_factor_minSV_bound (hsv : assSingularValueConvention)
    {p m : ℕ} [NeZero p] [NeZero m] (Sigma barSigma : PSD (p + m)) :
    ∃ S T : Mat (p + m) (p + m),
      Sigma.val = S * S.transpose ∧ barSigma.val = T * T.transpose ∧
      |minSV (factorBlocks p m T).1 - minSV (factorBlocks p m S).1| ≤
        buresDistance barSigma.val Sigma.val := by
  obtain ⟨T, S, hT, hS, hc⟩ := (buresProcrustes barSigma Sigma).2.1.1
  refine ⟨S, T, hS, hT, ?_⟩
  exact (factorPerturbation (factorBlocks p m S).1 (factorBlocks p m T).1).trans
    ((opNorm_factorX_sub_le_frob T S).trans hc.le)

-- @node: lambdaMin_gram_transpose
/-- For a real matrix with a positive number of rows, [the smallest eigenvalue of
the matrix times its transpose equals the square of the singular value of its
transpose indexed by the number of rows minus one, using zero-based indexing](goal). -/
lemma lambdaMin_gram_transpose {r k : ℕ} [NeZero r] (S : Mat r k) :
    lambdaMin (S * S.transpose) = singularValue S.transpose (r - 1) ^ 2 := by
  classical
  let A := Matrix.toEuclideanLin S.transpose
  have hn : Module.finrank ℝ (Euc r) = r := by simp
  let j : Fin r := ⟨r - 1, by have := NeZero.pos r; omega⟩
  let hT := A.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis hn
  let lam := hT.eigenvalues hn
  have hgram : Matrix.toEuclideanLin (S * S.transpose) = A.adjoint ∘ₗ A := by
    have hadj : A.adjoint = Matrix.toEuclideanLin S := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp
    rw [hadj]
    exact Matrix.toLpLin_mul 2 2 2 S S.transpose
  have heig (i : Fin r) : (matrixCLM (S * S.transpose)) (b i) = lam i • b i := by
    change Matrix.toEuclideanLin (S * S.transpose) (b i) = _
    rw [hgram]
    exact hT.apply_eigenvectorBasis hn i
  have hlower (x : Euc r) (hx : ‖x‖ = 1) :
      lam j ≤ inner ℝ x (matrixCLM (S * S.transpose) x) := by
    have hsum : inner ℝ x (matrixCLM (S * S.transpose) x) =
        ∑ i, lam i * ‖inner ℝ (b i) x‖ ^ 2 := by
      rw [← b.sum_inner_mul_inner x (matrixCLM (S * S.transpose) x)]
      apply Finset.sum_congr rfl
      intro i _
      have hs : inner ℝ (b i) (matrixCLM (S * S.transpose) x) =
          inner ℝ (matrixCLM (S * S.transpose) (b i)) x := by
        change inner ℝ (b i) (Matrix.toEuclideanLin (S * S.transpose) x) =
          inner ℝ (Matrix.toEuclideanLin (S * S.transpose) (b i)) x
        rw [hgram]
        exact (hT (b i) x).symm
      rw [hs, heig]
      simp only [real_inner_smul_left, Real.norm_eq_abs, sq_abs]
      rw [real_inner_comm x (b i)]
      ring
    have hnorm := b.sum_sq_norm_inner_right x
    rw [hx, one_pow] at hnorm
    rw [hsum, ← mul_one (lam j), ← hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hn (show i ≤ j by change i.val ≤ r - 1; omega)) (sq_nonneg _)
  have hmem : lam j ∈ {t : ℝ | ∃ x : Euc r, ‖x‖ = 1 ∧
      inner ℝ x (matrixCLM (S * S.transpose) x) = t} := by
    refine ⟨b j, b.orthonormal.1 j, ?_⟩
    rw [heig]
    simp [real_inner_smul_right, b.orthonormal.1 j]
  have hinf : lambdaMin (S * S.transpose) = lam j := by
    apply le_antisymm
    · exact csInf_le ⟨lam j, by rintro t ⟨x, hx, rfl⟩; exact hlower x hx⟩ hmem
    · exact le_csInf ⟨lam j, hmem⟩ (by rintro t ⟨x, hx, rfl⟩; exact hlower x hx)
  rw [hinf]
  exact (A.sq_singularValues_fin hn j).symm

-- @node: sqrt_lambdaMin_factorX
/-- For a square joint factor with a positive number of feature rows, [the square
root of the smallest eigenvalue of its feature second-moment block equals the
smallest singular value of the transpose of its feature-row factor](goal). -/
lemma sqrt_lambdaMin_factorX {p m : ℕ} [NeZero p] (S : Mat (p + m) (p + m)) :
    Real.sqrt (lambdaMin (blockX p m (S * S.transpose))) =
      minSV (factorBlocks p m S).1.transpose := by
  rw [blockX_factor_gram, lambdaMin_gram_transpose]
  have hn : 0 ≤ singularValue (factorBlocks p m S).1.transpose (p - 1) :=
    (Matrix.toEuclideanLin (factorBlocks p m S).1.transpose).singularValues_nonneg _
  rw [Real.sqrt_sq hn]
  simp only [minSV, min_eq_right (Nat.le_add_right p m)]

-- @node: lem:bures-lambda-min-continuity
/-- Assuming [singular values are nonnegative and ordered from largest to smallest,
with the smallest indexed by the smaller matrix dimension minus one](hyp:hsv),
[the square root of the smallest
feature-block eigenvalue changes by at most the Bures distance between positive
semidefinite joint moments, and the smallest feature-block eigenvalue is continuous
in Bures distance: every positive error tolerance is met throughout some positive
Bures neighborhood of each joint moment matrix](goal). -/
lemma buresLambdaMinContinuity (hsv : assSingularValueConvention)
    {p m : ℕ} [NeZero p] [NeZero m] :
    (∀ Sigma barSigma : PSD (p + m),
      |Real.sqrt (lambdaMin (blockX p m barSigma.val)) -
        Real.sqrt (lambdaMin (blockX p m Sigma.val))| ≤ buresDistance barSigma.val Sigma.val) ∧
    (∀ Sigma : PSD (p + m), ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ barSigma : PSD (p + m), buresDistance barSigma.val Sigma.val < delta →
        |lambdaMin (blockX p m barSigma.val) - lambdaMin (blockX p m Sigma.val)| < eta) := by
  have hbound : ∀ Sigma barSigma : PSD (p + m),
      |Real.sqrt (lambdaMin (blockX p m barSigma.val)) -
        Real.sqrt (lambdaMin (blockX p m Sigma.val))| ≤
        buresDistance barSigma.val Sigma.val := by
    intro Sigma barSigma
    obtain ⟨T, S, hT, hS, hc⟩ := (buresProcrustes barSigma Sigma).2.1.1
    conv_lhs => rw [hT, hS, sqrt_lambdaMin_factorX, sqrt_lambdaMin_factorX]
    have h := factorPerturbation (factorBlocks p m S).1.transpose
      (factorBlocks p m T).1.transpose
    rw [← Matrix.transpose_sub, opNorm_transpose] at h
    exact h.trans ((opNorm_factorX_sub_le_frob T S).trans hc.le)
  have hnonneg (Sigma : PSD (p + m)) : 0 ≤ lambdaMin (blockX p m Sigma.val) := by
    obtain ⟨S, T, hS, _, _⟩ := (buresProcrustes Sigma Sigma).2.1.1
    rw [hS, blockX_factor_gram, lambdaMin_gram_transpose]
    exact sq_nonneg _
  refine ⟨hbound, ?_⟩
  intro Sigma eta heta
  let b := Real.sqrt (lambdaMin (blockX p m Sigma.val))
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hden : 0 < 2 * b + 1 := by positivity
  refine ⟨min 1 (eta / (2 * b + 1)), lt_min zero_lt_one (div_pos heta hden), ?_⟩
  intro barSigma hdist
  let a := Real.sqrt (lambdaMin (blockX p m barSigma.val))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hd : |a - b| < min 1 (eta / (2 * b + 1)) :=
    (hbound Sigma barSigma).trans_lt hdist
  have hd1 : |a - b| < 1 := hd.trans_le (min_le_left _ _)
  have hdeta : |a - b| * (2 * b + 1) < eta :=
    (lt_div_iff₀ hden).mp (hd.trans_le (min_le_right _ _))
  have hab : a + b ≤ 2 * b + 1 := by
    have := le_abs_self (a - b)
    linarith
  have hprod : |a - b| * (a + b) < eta :=
    (mul_le_mul_of_nonneg_left hab (abs_nonneg _)).trans_lt hdeta
  have hsq : |a ^ 2 - b ^ 2| = |a - b| * (a + b) := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
      abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  rw [← Real.sq_sqrt (hnonneg barSigma), ← Real.sq_sqrt (hnonneg Sigma)]
  exact hsq.trans_lt hprod
-- @realizes \bar{\bSigma}_X(perturbed feature principal block; no definiteness assumption)


end Papers.WassersteinRegretS2S3
