module
public import Papers.WassersteinRegretS2S3.Helpers.Pseudoinverse
public import Papers.WassersteinRegretS2S3.Helpers.MatrixNorms

/-!
# Population Wasserstein regret: Helpers/RowSpacePerturbation

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:sin-thm-variant
/-- Assuming [singular values are nonnegative and ordered decreasingly, with the minimum
at the smaller matrix dimension](hyp:hsv), and [the reference matrix has full row
rank](hyp:hrank), [the Frobenius norm of the perturbed row-space projector outside the
reference row space is at most that of the reference projector outside the perturbed
row space, which in turn is at most the perturbation's Frobenius norm divided by the
reference matrix's minimum singular value](goal). -/
lemma sinThmVariant (hsv : assSingularValueConvention) {r d : ℕ} [NeZero r] [NeZero d]
    (M0 : Mat r d) -- @realizes \bM_0(real reference rectangle)
    (Delta : Mat r d) -- @realizes \bDelta(arbitrary rectangular perturbation)
    (hrank : assSinThmVariantRowRank M0) :
    let M1 := M0 + Delta -- @realizes \bM_1(M0 plus Delta)
    let Pi0 := rowProjector M0 -- @realizes \bPi_0(reference row projector)
    let Pi1 := rowProjector M1 -- @realizes \bPi_1(perturbed row projector)
    frob ((1 - Pi0) * Pi1) ≤ frob ((1 - Pi1) * Pi0) ∧
    frob ((1 - Pi1) * Pi0) ≤ frob Delta / minSV M0 := by
  dsimp only
  let M1 := M0 + Delta
  let P := rowProjector M0
  let Q := rowProjector M1
  have hP : assBasicMatrixNormsProjection P := (penrose_projectors M0).1
  have hQ : assBasicMatrixNormsProjection Q := (penrose_projectors M1).1
  have htraceP : frob P ^ 2 = (r : ℝ) := by
    rw [frob_sq_trace, hP.1, hP.2]
    change Matrix.trace (moorePenroseInverse M0 * M0) = _
    rw [Matrix.trace_mul_comm, penrose_full_row_projection M0 hrank, Matrix.trace_one]
    simp
  have hQnorm : opNorm Q ≤ 1 := (rowProjection_norms_le_one M1).1
  have hQrank : Q.rank ≤ r :=
    (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height M1)
  have hQfrob : frob Q ≤ Real.sqrt (r : ℝ) := by
    calc
      frob Q ≤ Real.sqrt (Q.rank : ℝ) * opNorm Q := frob_le_sqrt_rank_opNorm Q
      _ ≤ Real.sqrt (Q.rank : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hQnorm (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (r : ℝ) := by
        simpa only [mul_one] using
          Real.sqrt_le_sqrt (show (Q.rank : ℝ) ≤ r by exact_mod_cast hQrank)
  have hsize : frob Q ^ 2 ≤ frob P ^ 2 := by
    rw [htraceP]
    have h := pow_le_pow_left₀ (frob_nonneg Q) hQfrob 2
    simpa only [Real.sq_sqrt (Nat.cast_nonneg r)] using h
  have hcross : frob (Q * P) = frob (P * Q) := by
    rw [← frob_transpose (Q * P), Matrix.transpose_mul, hP.1, hQ.1]
  have hleft : frob (Q * (1 - P)) = frob ((1 - P) * Q) := by
    rw [← frob_transpose (Q * (1 - P)), Matrix.transpose_mul,
      Matrix.transpose_sub, Matrix.transpose_one, hP.1, hQ.1]
  have hright : frob (P * (1 - Q)) = frob ((1 - Q) * P) := by
    rw [← frob_transpose (P * (1 - Q)), Matrix.transpose_mul,
      Matrix.transpose_sub, Matrix.transpose_one, hQ.1, hP.1]
  constructor
  · apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
    have hp := frob_projection_pythagoras Q P hP
    have hq := frob_projection_pythagoras P Q hQ
    rw [hcross, hleft] at hp
    rw [hright] at hq
    linarith
  · have hkill : (1 - Q) * M1.transpose = 0 := by
      have h := congrArg Matrix.transpose (moorePenroseInverse_spec M1).1
      have hs := (moorePenroseInverse_spec M1).2.2.2
      have hfix : Q * M1.transpose = M1.transpose := by
        have hs' : M1.transpose * (moorePenroseInverse M1).transpose = Q := by
          simpa only [Matrix.transpose_mul, Q, rowProjector] using hs
        simpa only [Matrix.transpose_mul, ← Matrix.mul_assoc, hs'] using h
      rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]
    have hfactor : (1 - Q) * P =
        -((1 - Q) * Delta.transpose) * (moorePenroseInverse M0).transpose := by
      have hPform : P = M0.transpose * (moorePenroseInverse M0).transpose := by
        simpa only [P, rowProjector, Matrix.transpose_mul] using
          (moorePenroseInverse_spec M0).2.2.2.symm
      have hdiff : (1 - Q) * M0.transpose = -((1 - Q) * Delta.transpose) := by
        have hz : (1 - Q) * M0.transpose + (1 - Q) * Delta.transpose = 0 := by
          rw [← Matrix.mul_add, ← Matrix.transpose_add]
          exact hkill
        exact eq_neg_of_add_eq_zero_left hz
      rw [hPform, ← Matrix.mul_assoc, hdiff]
    have hcontract : frob ((1 - Q) * Delta.transpose) ≤ frob Delta := by
      have hp := frob_projection_pythagoras Delta Q hQ
      have ht : frob ((1 - Q) * Delta.transpose) = frob (Delta * (1 - Q)) := by
        rw [← frob_transpose (Delta * (1 - Q)), Matrix.transpose_mul,
          Matrix.transpose_sub, Matrix.transpose_one, hQ.1]
      rw [ht]
      apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
      linarith [sq_nonneg (frob (Delta * Q))]
    rw [hfactor]
    calc
      frob (-((1 - Q) * Delta.transpose) * (moorePenroseInverse M0).transpose) ≤
          frob (-((1 - Q) * Delta.transpose)) *
            opNorm (moorePenroseInverse M0).transpose := frob_mul_right_le _ _
      _ = frob ((1 - Q) * Delta.transpose) * (minSV M0)⁻¹ := by
        rw [opNorm_transpose, penrose_full_row_norm M0 hrank]
        congr 1
        simp [frob]
      _ ≤ frob Delta * (minSV M0)⁻¹ :=
        mul_le_mul_of_nonneg_right hcontract (inv_nonneg.mpr ((hsv r d M0).2.1 _))
      _ = frob Delta / minSV M0 := (div_eq_mul_inv _ _).symm

end Papers.WassersteinRegretS2S3
