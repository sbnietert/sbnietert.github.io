module
public import Papers.WassersteinRegretS2S3.Helpers.LawDefs
public import Papers.WassersteinRegretS2S3.Helpers.MatrixNorms
public import Papers.WassersteinRegretS2S3.Helpers.RealContraction
public import Toolkit.Foundations.Optimization.Optimality.SLemma

/-!
# Population Wasserstein regret: Helpers/Cited

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:bures-procrustes-cited-identity
/-- For two positive semidefinite matrices, [their Bures distance is the attained
minimum Frobenius distance both between orthogonally aligned square roots and
between arbitrary square factors of the two matrices](goal).

Bhatia, Jain and Lim (2019), Theorem 1, doi:10.1016/j.exmath.2018.01.002,
arXiv:1712.01504. Real attainment is local work; singular matrices are included. -/
lemma CitedProcrustesIdentity {n : ℕ}
    (A : PSD n) -- @realizes \bA(PSD Bures argument, singular allowed)
    (B : PSD n) : -- @realizes \bB(PSD Bures argument, singular allowed)
    IsLeast {v : ℝ | ∃ U : Orth n, frob (CFC.sqrt A.val - CFC.sqrt B.val * U.val) = v}
      (buresDistance A.val B.val) ∧
    IsLeast {v : ℝ | ∃ S T : Mat n n, A.val = S * S.transpose ∧ B.val = T * T.transpose ∧
      frob (S - T) = v} (buresDistance A.val B.val) := by
  constructor
  · refine ⟨real_procrustes_attainment A B, ?_⟩
    rintro v ⟨U, rfl⟩
    exact real_procrustes_lower A B U
  · refine ⟨real_factor_attainment A B, ?_⟩
    rintro v ⟨S, T, hS, hT, rfl⟩
    exact real_factor_lower A B S T hS hT

-- @node: lem:w2-bures-block-contraction
/-- If [the symmetric block matrix with positive semidefinite diagonal blocks A and B
and off-diagonal blocks C and its transpose is positive semidefinite](hyp:hBlock),
then [C factors as the square root of A times a real matrix of operator norm at
most one times the square root of B](goal).

Bhatia (2009), Positive Definite Matrices, Proposition 1.3.2,
doi:10.1515/9781400827787. The contraction norm is on real Euclidean space. -/
lemma CitedBlockContraction {n : ℕ} (A B : PSD n) (C : Mat n n)
    (hBlock : (Matrix.fromBlocks A.val C C.transpose B.val).PosSemidef) :
    ∃ K : Mat n n, opNorm K ≤ 1 ∧ C = CFC.sqrt A.val * K * CFC.sqrt B.val := by
  obtain ⟨L, hL, hC⟩ :=
    Toolkit.Foundations.LinearAlgebra.Matrix.exists_contraction_of_posSemidef_fromBlocks
      (complexify_posSemidef A) (complexify_posSemidef B)
      (complexify_psd_block A B C hBlock)
  refine ⟨realPart L, (realPart_opNorm_le L).trans hL, ?_⟩
  rw [complexify_sqrt, complexify_sqrt] at hC
  have h := congrArg realPart hC
  rw [realPart_sandwich] at h
  exact h
-- @realizes \bK(real Euclidean contraction, including singular diagonal blocks)

-- @node: affine_frob_sq_quadraticForm
/-- For a matrix of linear coordinate maps and a constant matrix, [there exists a
quadratic form on the input space augmented by one real coordinate whose value
at each input with augmented coordinate one is the squared Frobenius norm of the
matrix of affine coordinates](goal). -/
lemma affine_frob_sq_quadraticForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : ℕ} (L : Fin a → Fin b → V →ₗ[ℝ] ℝ) (C : Mat a b) :
    ∃ Q : QuadraticForm ℝ (V × ℝ), ∀ x : V,
      Q (x, 1) = frob (Matrix.of fun i j => L i j x + C i j) ^ 2 := by
  classical
  let l (i : Fin a) (j : Fin b) : (V × ℝ) →ₗ[ℝ] ℝ :=
    (L i j).comp (LinearMap.fst ℝ V ℝ) + C i j • LinearMap.snd ℝ V ℝ
  refine ⟨∑ i, ∑ j, QuadraticMap.linMulLin (l i j) (l i j), ?_⟩
  intro x
  rw [frob_sq (Matrix.of fun i j => L i j x + C i j)]
  simp [l, pow_two, add_mul, mul_add]

-- @node: lem:quadratic-ball-s-lemma
/-- If [the squared radius of a Frobenius ball is positive](hyp:ht) and [gamma is the
attained maximum of the squared Frobenius norm of M times W over that ball centered
at the given center](hyp:hmax), then [there is a nonnegative multiplier such that,
for every W, gamma minus the squared norm of M times W minus the multiplier times
the difference between the squared radius and the squared distance from W to the
center is nonnegative](goal).

Pólik and Terlaky (2007), Theorem 2.2, doi:10.1137/S003614450444614X.
Only the multiplier assertion is imported through the toolkit S-lemma. -/
lemma CitedQuadraticBallSLemma {k d r : ℕ} [NeZero k] [NeZero d] [NeZero r]
    (M : Mat k d) (center : Mat d r) (t gamma : ℝ) (ht : 0 < t)
    (hmax : IsGreatest {v : ℝ | ∃ W : Mat d r,
      frob (W - center) ^ 2 ≤ t ∧ frob (M * W) ^ 2 = v} gamma) :
    ∃ eta : ℝ, 0 ≤ eta ∧ ∀ W : Mat d r,
      0 ≤ gamma - frob (M * W) ^ 2 - eta * (t - frob (W - center) ^ 2) := by
  classical
  let L (i : Fin k) (j : Fin r) : Mat d r →ₗ[ℝ] ℝ :=
    { toFun := fun W => (M * W) i j
      map_add' := by intros; simp [Matrix.mul_add]
      map_smul' := by intros; simp [Matrix.mul_smul] }
  let I (i : Fin d) (j : Fin r) : Mat d r →ₗ[ℝ] ℝ :=
    { toFun := fun W => W i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  obtain ⟨Q, hQ⟩ := affine_frob_sq_quadraticForm L (0 : Mat k r)
  obtain ⟨R, hR⟩ := affine_frob_sq_quadraticForm I (-center)
  have hQ' (W : Mat d r) : Q (W, 1) = frob (M * W) ^ 2 := by
    rw [hQ]
    congr 2
    ext i j
    simp [L]
  have hR' (W : Mat d r) : R (W, 1) = frob (W - center) ^ 2 := by
    rw [hR]
    congr 2
  let z : (Mat d r × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ _ _
  let Z := QuadraticMap.linMulLin z z
  let F : QuadraticForm ℝ (Mat d r × ℝ) := gamma • Z - Q
  let G : QuadraticForm ℝ (Mat d r × ℝ) := R - t • Z
  have hF (W : Mat d r) : F (W, 1) = gamma - frob (M * W) ^ 2 := by
    simp [F, Z, z, hQ']
  have hG (W : Mat d r) : G (W, 1) = frob (W - center) ^ 2 - t := by
    simp [G, Z, z, hR']
  have hslice : ¬∃ W : Mat d r, F (W, 1) < 0 ∧ G (W, 1) < 0 := by
    rintro ⟨W, hf, hg⟩
    rw [hF] at hf
    rw [hG] at hg
    have hbound := hmax.2 (show frob (M * W) ^ 2 ∈ _ from
      ⟨W, by linarith, rfl⟩)
    linarith
  have hhom := Toolkit.Foundations.Optimization.Optimality.no_strict_pair_of_no_strict_pair_slice
    F G hslice
  obtain ⟨eta, heta, hcert⟩ :=
    Toolkit.Foundations.Optimization.Optimality.exists_nonneg_multiplier_of_convex
      (Toolkit.Foundations.Optimization.Optimality.convex_joint_quadratic_range F G)
      (show ∃ v ∈ Set.range (fun w => (F w, G w)), v.2 < 0 from
        ⟨(F (center, 1), G (center, 1)), ⟨(center, 1), rfl⟩, by
          simpa [hG, frob] using neg_lt_zero.mpr ht⟩)
      (by rintro v ⟨w, rfl⟩ hw; exact hhom ⟨w, hw⟩)
  refine ⟨eta, heta, fun W => ?_⟩
  have hc := hcert (F (W, 1), G (W, 1)) ⟨(W, 1), rfl⟩
  change 0 ≤ F (W, 1) + eta * G (W, 1) at hc
  rw [hF, hG] at hc
  nlinarith
-- @realizes \gamma(compact constrained maximum) @realizes t(strictly positive S-lemma threshold)

end Papers.WassersteinRegretS2S3
