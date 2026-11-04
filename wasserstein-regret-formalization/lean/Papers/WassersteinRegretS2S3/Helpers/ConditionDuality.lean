module
public import Papers.WassersteinRegretS2S3.Helpers.MatrixNorms
public import Papers.WassersteinRegretS2S3.Helpers.Kronecker

/-!
# Dual sensitivity calculation

The feature and response contributions in the closed-form condition-number proof.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: condition_frob_stacked_sq
/-- [The squared Frobenius norm of the matrix obtained by stacking U above V equals the
sum of their squared Frobenius norms](goal). -/
lemma condition_frob_stacked_sq {p m d : ℕ} (U : Mat p d) (V : Mat m d) :
    @frob (p + m) d (fun i j => Fin.addCases (fun k => U k j) (fun k => V k j) i) ^ 2 =
      frob U ^ 2 + frob V ^ 2 := by
  unfold frob
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

-- @node: condition_trace_pairing_le
/-- [The absolute trace pairing of U and V is at most the product of their Frobenius
norms](goal). -/
lemma condition_trace_pairing_le {a b : ℕ} (U V : Mat a b) :
    |Matrix.trace (U.transpose * V)| ≤ frob U * frob V := by
  have ht : Matrix.trace (U.transpose * V) = ∑ i, ∑ j, U i j * V i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [ht]
  exact frob_inner_le U V

-- @node: condition_dual_ball_attains
/-- [There is a matrix V with Frobenius norm at most one whose squared trace pairing with
U equals the squared Frobenius norm of U](goal). -/
lemma condition_dual_ball_attains {a b : ℕ} (U : Mat a b) :
    ∃ V : Mat a b, frob V ≤ 1 ∧
      Matrix.trace (U.transpose * V) ^ 2 = frob U ^ 2 := by
  by_cases hz : frob U = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [frob]
    · simp [hz]
  · have hp : 0 < frob U := lt_of_le_of_ne (frob_nonneg U) (Ne.symm hz)
    let V : Mat a b := (frob U)⁻¹ • U
    have hv : frob V ^ 2 = 1 := by
      rw [frob_sq]
      simp only [V, Matrix.smul_apply, smul_eq_mul, mul_pow,
        ← Finset.mul_sum, ← frob_sq]
      field_simp
    have ht : Matrix.trace (U.transpose * V) = frob U := by
      rw [show U.transpose * V = (frob U)⁻¹ • (U.transpose * U) by
        simp [V, Matrix.mul_smul]]
      rw [Matrix.trace_smul, ← frob_sq_trace]
      simp only [smul_eq_mul]
      field_simp
    refine ⟨V, ?_, by rw [ht]⟩
    nlinarith [frob_nonneg V]

-- @node: condition_dual_ball_sup
/-- [The supremum of the squared trace pairing with U over matrices of Frobenius norm
at most one equals the squared Frobenius norm of U](goal). -/
lemma condition_dual_ball_sup {a b : ℕ} (U : Mat a b) :
    sSup {r : ℝ | ∃ V : Mat a b, frob V ≤ 1 ∧
      r = Matrix.trace (U.transpose * V) ^ 2} = frob U ^ 2 := by
  obtain ⟨V, hV, he⟩ := condition_dual_ball_attains U
  have hmem : frob U ^ 2 ∈ {r : ℝ | ∃ V : Mat a b, frob V ≤ 1 ∧
      r = Matrix.trace (U.transpose * V) ^ 2} := ⟨V, hV, he.symm⟩
  have hub : ∀ r ∈ {r : ℝ | ∃ V : Mat a b, frob V ≤ 1 ∧
      r = Matrix.trace (U.transpose * V) ^ 2}, r ≤ frob U ^ 2 := by
    rintro r ⟨W, hW, rfl⟩
    have ht := condition_trace_pairing_le U W
    have hb : |Matrix.trace (U.transpose * W)| ≤ frob U :=
      ht.trans (by nlinarith [frob_nonneg U])
    nlinarith [sq_abs (Matrix.trace (U.transpose * W)), abs_nonneg (Matrix.trace (U.transpose * W))]
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub)
    (le_csSup ⟨_, hub⟩ hmem)

-- @node: condition_dual_ball_iSup
/-- [The supremum, in the extended nonnegative reals, of the squared trace pairing with
U over the Frobenius unit ball equals the squared Frobenius norm of U](goal). -/
lemma condition_dual_ball_iSup {a b : ℕ} (U : Mat a b) :
    (⨆ (V : Mat a b) (_ : frob V ≤ 1),
      ENNReal.ofReal (Matrix.trace (U.transpose * V) ^ 2)) =
      ENNReal.ofReal (frob U ^ 2) := by
  obtain ⟨V, hV, he⟩ := condition_dual_ball_attains U
  apply le_antisymm
  · refine iSup_le fun W => iSup_le fun hW => ENNReal.ofReal_le_ofReal ?_
    have ht := condition_trace_pairing_le U W
    have hb : |Matrix.trace (U.transpose * W)| ≤ frob U :=
      ht.trans (by nlinarith [frob_nonneg U])
    nlinarith [sq_abs (Matrix.trace (U.transpose * W)),
      abs_nonneg (Matrix.trace (U.transpose * W))]
  · rw [← he]
    exact le_iSup_of_le V (le_iSup_of_le hV le_rfl)

-- @node: condition_adjoint_ball_sup
/-- If [the trace pairing of V with L applied to U equals that of G applied to V with U,
for every U and V](hyp:hpair), then [L and G have equal suprema of squared output Frobenius
norms over their respective Frobenius unit balls, in the extended nonnegative reals](goal). -/
lemma condition_adjoint_ball_sup {a b c d : ℕ}
    (L : Mat a b → Mat c d) (G : Mat c d → Mat a b)
    (hpair : ∀ U V, Matrix.trace (V.transpose * L U) =
      Matrix.trace ((G V).transpose * U)) :
    (⨆ (U : Mat a b) (_ : frob U ≤ 1), ENNReal.ofReal (frob (L U) ^ 2)) =
      ⨆ (V : Mat c d) (_ : frob V ≤ 1), ENNReal.ofReal (frob (G V) ^ 2) := by
  have hsymm : ∀ (V : Mat c d) (W : Mat c d),
      Matrix.trace (V.transpose * W) = Matrix.trace (W.transpose * V) := by
    intro V W
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = ⨆ (U : Mat a b) (_ : frob U ≤ 1),
        ⨆ (V : Mat c d) (_ : frob V ≤ 1),
          ENNReal.ofReal (Matrix.trace ((G V).transpose * U) ^ 2) := by
      apply iSup_congr; intro U
      apply iSup_congr; intro hU
      rw [← condition_dual_ball_iSup (L U)]
      apply iSup_congr; intro V
      apply iSup_congr; intro hV
      rw [hsymm, hpair]
    _ = ⨆ (V : Mat c d) (_ : frob V ≤ 1),
        ⨆ (U : Mat a b) (_ : frob U ≤ 1),
          ENNReal.ofReal (Matrix.trace ((G V).transpose * U) ^ 2) := by
      apply le_antisymm
      · refine iSup_le fun U => iSup_le fun hU => iSup_le fun V => iSup_le fun hV => ?_
        exact le_iSup_of_le V (le_iSup_of_le hV
          (le_iSup_of_le U (le_iSup_of_le hU le_rfl)))
      · refine iSup_le fun V => iSup_le fun hV => iSup_le fun U => iSup_le fun hU => ?_
        exact le_iSup_of_le U (le_iSup_of_le hU
          (le_iSup_of_le V (le_iSup_of_le hV le_rfl)))
    _ = _ := by
      apply iSup_congr; intro V
      apply iSup_congr; intro hV
      exact condition_dual_ball_iSup (G V)

-- @node: condition_stacked_pairing
/-- [The trace pairing of the matrix obtained by stacking U above V with D equals the
pairing of U with the upper block of D plus the pairing of V with its lower block](goal). -/
lemma condition_stacked_pairing {p m d : ℕ} (U : Mat p d) (V : Mat m d)
    (D : Mat (p + m) d) :
    Matrix.trace (Matrix.transpose (fun i j =>
      Fin.addCases (fun k => U k j) (fun k => V k j) i) * D) =
      Matrix.trace (U.transpose * (factorBlocks p m D).1) +
        Matrix.trace (V.transpose * (factorBlocks p m D).2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_add, Finset.sum_add_distrib, factorBlocks, Matrix.submatrix_apply, id_eq]
  simp only [Matrix.transpose, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

-- @node: condition_whitened_gram
/-- If [H is symmetric](hyp:hH) and [multiplying the feature Gram matrix on both sides
by H gives the identity](hyp:hwhite), then [the matrix formed by multiplying the transpose
of X by H has orthonormal columns](goal). -/
lemma condition_whitened_gram {p d : ℕ} (X : Mat p d) (H : Mat p p)
    (hH : H.transpose = H) (hwhite : H * (X * X.transpose) * H = 1) :
    (X.transpose * H).transpose * (X.transpose * H) = 1 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hH,
    Matrix.mul_assoc] using hwhite

-- @node: condition_residual_whitened_orthogonal
/-- If [the feature-response cross moment equals A times the feature Gram matrix](hyp:hnormal),
then [the residual Y minus AX multiplied by the transpose of X and then H is zero](goal). -/
lemma condition_residual_whitened_orthogonal {m p d : ℕ}
    (A : Mat m p) (X : Mat p d) (Y : Mat m d) (H : Mat p p)
    (hnormal : Y * X.transpose = A * (X * X.transpose)) :
    (Y - A * X) * (X.transpose * H) = 0 := by
  rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, hnormal, sub_self,
    Matrix.zero_mul]

-- @node: condition_primal_whitened_rewrite
/-- [Multiplying the sum of the perturbed residual times the transpose of X and the
residual times the transpose of DX by H gives the residual times the transpose of DX
times H, minus A times DX times the transpose of X times H, plus DY times the transpose
of X times H](goal). Here the residual is Y minus AX and its perturbation is DY minus A times DX. -/
lemma condition_primal_whitened_rewrite {m p d : ℕ}
    (A : Mat m p) (X DX : Mat p d) (Y DY : Mat m d) (H : Mat p p) :
    ((DY - A * DX) * X.transpose + (Y - A * X) * DX.transpose) * H =
      (Y - A * X) * DX.transpose * H - A * DX * (X.transpose * H) +
        DY * (X.transpose * H) := by
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

-- @node: condition_frob_sub_sq_of_cross_zero
/-- If [U and V have zero trace pairing](hyp:h), then [the squared Frobenius norm of
their difference equals the sum of their squared Frobenius norms](goal). -/
lemma condition_frob_sub_sq_of_cross_zero {a b : ℕ} (U V : Mat a b)
    (h : Matrix.trace (U.transpose * V) = 0) :
    frob (U - V) ^ 2 = frob U ^ 2 + frob V ^ 2 := by
  have h' : Matrix.trace (V.transpose * U) = 0 := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact h
  simp only [frob_sq_trace, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, h, h']
  ring

-- @node: condition_frob_coisometry
/-- If [Q has orthonormal columns](hyp:hQ), then [multiplying B by the transpose of Q
preserves its squared Frobenius norm](goal). -/
lemma condition_frob_coisometry {m p d : ℕ} (B : Mat m p) (Q : Mat d p)
    (hQ : Q.transpose * Q = 1) :
    frob (B * Q.transpose) ^ 2 = frob B ^ 2 := by
  rw [frob_sq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul, ← frob_sq_trace]

-- @node: condition_dual_cross_zero
/-- If [E times Q is zero](hyp:hEQ), then [the trace pairing between H times the transpose
of B times E and the transpose of A times B times the transpose of Q is zero](goal). -/
lemma condition_dual_cross_zero {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hEQ : E * Q = 0) :
    Matrix.trace ((H * B.transpose * E).transpose * (A.transpose * B * Q.transpose)) = 0 := by
  rw [Matrix.transpose_mul]
  calc
    _ = Matrix.trace (Q.transpose * E.transpose * ((H * B.transpose).transpose *
        (A.transpose * B))) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (E.transpose * (H * B.transpose).transpose *
          (A.transpose * B)) Q.transpose
    _ = 0 := by
      rw [← Matrix.transpose_mul, hEQ, Matrix.transpose_zero, Matrix.zero_mul]
      simp

-- @node: condition_dual_norm_decomposition
/-- If [Q has orthonormal columns](hyp:hQ) and [E times Q is zero](hyp:hEQ), then [the
squared Frobenius norm of H times the transpose of B times E minus the transpose of A
times B times the transpose of Q, plus the squared norm of B times the transpose of Q,
equals the sum of the squared norms of H times the transpose of B times E, the transpose
of A times B, and B](goal). -/
lemma condition_dual_norm_decomposition {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    frob (H * B.transpose * E - A.transpose * B * Q.transpose) ^ 2 +
        frob (B * Q.transpose) ^ 2 =
      frob (H * B.transpose * E) ^ 2 + frob (A.transpose * B) ^ 2 + frob B ^ 2 := by
  rw [condition_frob_sub_sq_of_cross_zero _ _ (condition_dual_cross_zero A B H E Q hEQ),
    condition_frob_coisometry _ Q hQ, condition_frob_coisometry _ Q hQ]

-- @node: condition_dual_trace_decomposition
/-- If [H is symmetric](hyp:hH), [Q has orthonormal columns](hyp:hQ), and [E times Q is
zero](hyp:hEQ), then [the sum of squared Frobenius norms of H times the transpose of B
times E minus the transpose of A times B times the transpose of Q and of B times the
transpose of Q equals the trace of H squared times the transpose of B times the residual
Gram matrix times B, plus the trace of the regression Gram matrix times B times its
transpose, plus the squared Frobenius norm of B](goal). The residual and regression
Gram matrices are E times its transpose and A times its transpose, respectively. -/
lemma condition_dual_trace_decomposition {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    frob (H * B.transpose * E - A.transpose * B * Q.transpose) ^ 2 +
        frob (B * Q.transpose) ^ 2 =
      Matrix.trace (H * H * B.transpose * (E * E.transpose) * B) +
        Matrix.trace ((A * A.transpose) * B * B.transpose) + frob B ^ 2 := by
  rw [condition_dual_norm_decomposition A B H E Q hQ hEQ]
  have he : frob (H * B.transpose * E) ^ 2 =
      Matrix.trace (H * H * B.transpose * (E * E.transpose) * B) := by
    rw [frob_sq_trace, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hH]
    calc
      _ = Matrix.trace (B * (H * H * B.transpose * (E * E.transpose))) := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm E.transpose (B * H * H * B.transpose * E)
      _ = _ := by
        rw [Matrix.trace_mul_comm B]
  have ha : frob (A.transpose * B) ^ 2 =
      Matrix.trace ((A * A.transpose) * B * B.transpose) := by
    rw [frob_sq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm B.transpose (A * A.transpose * B)
  rw [he, ha]

-- @node: condition_dual_pairing
/-- If [H is symmetric](hyp:hH), then [pairing B with E times the transpose of DX times H
minus A times DX times Q plus DY times Q equals the sum of the pairing of H times the
transpose of B times E minus the transpose of A times B times the transpose of Q with
DX and the pairing of B times the transpose of Q with DY](goal). -/
lemma condition_dual_pairing {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (DX : Mat p d) (DY : Mat m d) (hH : H.transpose = H) :
    Matrix.trace (B.transpose * (E * DX.transpose * H - A * DX * Q + DY * Q)) =
      Matrix.trace ((H * B.transpose * E - A.transpose * B * Q.transpose).transpose * DX) +
        Matrix.trace ((B * Q.transpose).transpose * DY) := by
  have he : Matrix.trace (B.transpose * (E * DX.transpose * H)) =
      Matrix.trace ((H * B.transpose * E).transpose * DX) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH]
    calc
      _ = Matrix.trace (DX.transpose * (H * B.transpose * E)) := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (B.transpose * E) (DX.transpose * H)
      _ = _ := by
        rw [← Matrix.trace_transpose, Matrix.transpose_mul,
          Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH]
        simp only [Matrix.mul_assoc, Matrix.transpose_transpose]
  have ha : Matrix.trace (B.transpose * (A * DX * Q)) =
      Matrix.trace ((A.transpose * B * Q.transpose).transpose * DX) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (B.transpose * A * DX) Q
  have hy : Matrix.trace (B.transpose * (DY * Q)) =
      Matrix.trace ((B * Q.transpose).transpose * DY) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B.transpose * DY) Q
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.transpose_sub, Matrix.sub_mul]
  rw [he, ha, hy]

-- @node: condition_feature_kronecker
/-- If [T is symmetric](hyp:hT), then [the trace of T times the transpose of B times E
times B plus the trace of A times its transpose times B times its transpose equals the
quadratic form at the vectorized B of the Kronecker sum of T with E and the identity
with A times its transpose](goal). -/
lemma condition_feature_kronecker {m p : ℕ} (A B : Mat m p) (T : Mat p p)
    (E : Mat m m) (hT : T.transpose = T) :
    Matrix.trace (T * B.transpose * E * B) +
        Matrix.trace ((A * A.transpose) * B * B.transpose) =
      Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker T E + Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ
          Matrix.vec B) := by
  have he : Matrix.trace (T * B.transpose * E * B) =
      Matrix.trace (E * B * T * B.transpose) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (T * B.transpose) (E * B)
  rw [he, kroneckerFact E T B]
  have ha := kroneckerFact (A * A.transpose) (1 : Mat p p) B
  simp only [Matrix.mul_one, Matrix.transpose_one] at ha
  rw [ha, hT, Matrix.add_mulVec, dotProduct_add]

-- @node: condition_dual_kronecker_decomposition
/-- If [H is symmetric](hyp:hH), [Q has orthonormal columns](hyp:hQ), and [E times Q is
zero](hyp:hEQ), then [the sum of squared Frobenius norms of H times the transpose of B
times E minus the transpose of A times B times the transpose of Q and of B times the
transpose of Q equals the quadratic form at the vectorized B of the Kronecker sum of
H squared with E times its transpose and the identity with A times its transpose,
plus the squared Frobenius norm of B](goal). -/
lemma condition_dual_kronecker_decomposition {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    frob (H * B.transpose * E - A.transpose * B * Q.transpose) ^ 2 +
        frob (B * Q.transpose) ^ 2 =
      Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker (H * H) (E * E.transpose) +
          Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ Matrix.vec B) +
        frob B ^ 2 := by
  rw [condition_dual_trace_decomposition A B H E Q hH hQ hEQ,
    condition_feature_kronecker A B (H * H) (E * E.transpose)
      (by rw [Matrix.transpose_mul, hH])]

-- @node: condition_stacked_dual_kronecker
/-- If [H is symmetric](hyp:hH), [Q has orthonormal columns](hyp:hQ), and [E times Q is
zero](hyp:hEQ), then [the squared Frobenius norm obtained by stacking H times the
transpose of B times E minus the transpose of A times B times the transpose of Q above
B times the transpose of Q equals the quadratic form at the vectorized B of the
Kronecker sum of H squared with E times its transpose and the identity with A times its
transpose, plus the squared Frobenius norm of B](goal). -/
lemma condition_stacked_dual_kronecker {m p d : ℕ}
    (A B : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    @frob (p + m) d (fun i j => Fin.addCases
      (fun k => (H * B.transpose * E - A.transpose * B * Q.transpose) k j)
      (fun k => (B * Q.transpose) k j) i) ^ 2 =
      Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker (H * H) (E * E.transpose) +
          Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ Matrix.vec B) +
        frob B ^ 2 := by
  change frob (fun i j => Fin.addCases
    (fun k => (H * B.transpose * E - A.transpose * B * Q.transpose) k j)
    (fun k => (B * Q.transpose) k j) i) ^ 2 = _
  rw [condition_frob_stacked_sq]
  exact condition_dual_kronecker_decomposition A B H E Q hH hQ hEQ

-- @node: condition_whitened_dual_kronecker
/-- If [H is symmetric](hyp:hH), [H whitens the feature Gram matrix](hyp:hwhite), and
[A satisfies the normal equations for X and Y](hyp:hnormal), then [the sum of squared
Frobenius norms of H times the transpose of B times the residual minus the transpose
of A times B times the transpose of the whitened feature matrix and of B times that
transpose equals the quadratic form at the vectorized B of the Kronecker sum of H
squared with the residual Gram matrix and the identity with A times its transpose,
plus the squared Frobenius norm of B](goal). The residual is Y minus AX, and the
whitened feature matrix is the transpose of X times H. -/
lemma condition_whitened_dual_kronecker {m p d : ℕ}
    (A B : Mat m p) (X : Mat p d) (Y : Mat m d) (H : Mat p p)
    (hH : H.transpose = H) (hwhite : H * (X * X.transpose) * H = 1)
    (hnormal : Y * X.transpose = A * (X * X.transpose)) :
    frob (H * B.transpose * (Y - A * X) -
        A.transpose * B * (X.transpose * H).transpose) ^ 2 +
      frob (B * (X.transpose * H).transpose) ^ 2 =
      Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker (H * H) ((Y - A * X) * (Y - A * X).transpose) +
          Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ Matrix.vec B) +
        frob B ^ 2 := by
  exact condition_dual_kronecker_decomposition A B H (Y - A * X) (X.transpose * H)
    hH (condition_whitened_gram X H hH hwhite)
    (condition_residual_whitened_orthogonal A X Y H hnormal)

-- @node: condition_primal_dual_ball_sup
/-- If [H is symmetric](hyp:hH), then [the supremum of the squared Frobenius norm of
E times the transpose of the upper perturbation block times H minus A times that block
times Q plus the lower block times Q, over stacked perturbations of Frobenius norm at
most one, equals the supremum over B of Frobenius norm at most one of the sum of squared
norms of H times the transpose of B times E minus the transpose of A times B times the
transpose of Q and of B times the transpose of Q](goal). Both suprema are taken in the
extended nonnegative reals. -/
lemma condition_primal_dual_ball_sup {m p d : ℕ}
    (A : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) :
    (⨆ (D : Mat (p + m) d) (_ : frob D ≤ 1),
      ENNReal.ofReal (frob (E * (factorBlocks p m D).1.transpose * H -
        A * (factorBlocks p m D).1 * Q + (factorBlocks p m D).2 * Q) ^ 2)) =
    ⨆ (B : Mat m p) (_ : frob B ≤ 1),
      ENNReal.ofReal (frob (H * B.transpose * E - A.transpose * B * Q.transpose) ^ 2 +
        frob (B * Q.transpose) ^ 2) := by
  let L : Mat (p + m) d → Mat m p := fun D =>
    E * (factorBlocks p m D).1.transpose * H -
      A * (factorBlocks p m D).1 * Q + (factorBlocks p m D).2 * Q
  let G : Mat m p → Mat (p + m) d := fun B i j => Fin.addCases
    (fun k => (H * B.transpose * E - A.transpose * B * Q.transpose) k j)
    (fun k => (B * Q.transpose) k j) i
  have hp : ∀ D B, Matrix.trace (B.transpose * L D) =
      Matrix.trace ((G B).transpose * D) := by
    intro D B
    rw [show Matrix.trace ((G B).transpose * D) = _ from
      condition_stacked_pairing _ _ D]
    exact condition_dual_pairing A B H E Q _ _ hH
  calc
    _ = ⨆ (B : Mat m p) (_ : frob B ≤ 1),
        ENNReal.ofReal (frob (G B) ^ 2) := condition_adjoint_ball_sup L G hp
    _ = _ := by
      apply iSup_congr; intro B
      apply iSup_congr; intro hB
      rw [show frob (G B) ^ 2 = _ from condition_frob_stacked_sq _ _]

-- @node: condition_primal_kronecker_ball_sup
/-- If [H is symmetric](hyp:hH), [Q has orthonormal columns](hyp:hQ), and [E times Q is
zero](hyp:hEQ), then [the supremum of the squared Frobenius norm of E times the transpose
of the upper perturbation block times H minus A times that block times Q plus the lower
block times Q, over stacked perturbations of Frobenius norm at most one, equals the
supremum over B of Frobenius norm at most one of the quadratic form at the vectorized B
of the Kronecker sum of H squared with E times its transpose and the identity with A
times its transpose, plus the squared Frobenius norm of B](goal). Both suprema are taken
in the extended nonnegative reals. -/
lemma condition_primal_kronecker_ball_sup {m p d : ℕ}
    (A : Mat m p) (H : Mat p p) (E : Mat m d) (Q : Mat d p)
    (hH : H.transpose = H) (hQ : Q.transpose * Q = 1) (hEQ : E * Q = 0) :
    (⨆ (D : Mat (p + m) d) (_ : frob D ≤ 1),
      ENNReal.ofReal (frob (E * (factorBlocks p m D).1.transpose * H -
        A * (factorBlocks p m D).1 * Q + (factorBlocks p m D).2 * Q) ^ 2)) =
    ⨆ (B : Mat m p) (_ : frob B ≤ 1),
      ENNReal.ofReal (Matrix.vec B ⬝ᵥ
        ((Matrix.kronecker (H * H) (E * E.transpose) +
          Matrix.kronecker (1 : Mat p p) (A * A.transpose)) *ᵥ Matrix.vec B) +
        frob B ^ 2) := by
  rw [condition_primal_dual_ball_sup A H E Q hH]
  apply iSup_congr; intro B
  apply iSup_congr; intro hB
  rw [condition_dual_kronecker_decomposition A B H E Q hH hQ hEQ]

end Papers.WassersteinRegretS2S3
