module
public import Papers.WassersteinRegretS2S3.Helpers.MinimaxConvex
public import Papers.WassersteinRegretS2S3.Helpers.Transport.MomentGeometry
public import Papers.WassersteinRegretS2S3.Helpers.MomentBall

/-!
# Population Wasserstein regret: Helpers/DROMinimax

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:dro-minimax
/-- For [a nonnegative Wasserstein radius](hyp:eps) and [a reference joint law with finite second moments](hyp:hatP), under [the Euclidean squared-norm identity for responses](hyp:hpin) and
[the convention that singular values are nonnegative and decreasing with the
smallest at the last index](hyp:hsv), if [the reference law lies within the given
Wasserstein radius of a nondegenerate joint law](hyp:hhat), then [there exists a
law in the Wasserstein ball of that radius around the reference law whose minimum
regression risk equals the minimum worst-case risk over the ball and is at least
the minimum regression risk of every other law in the ball](goal). -/
lemma droMinimax {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (eps : ℝ≥0)
    (P : NondegenerateLaws p m) (hatP : JointLaws p m) (hhat : hatP ∈ lawBall P.carrier.val
      eps) : -- @realizes \hat{P}(law in the)
    ∃ Q ∈ lawBall hatP eps,
      (⨅ A : Mat m p, ⨆ T ∈ lawBall hatP eps, ENNReal.ofReal (risk A T)) =
        ⨅ A : Mat m p, ENNReal.ofReal (risk A Q) ∧
      ∀ T ∈ lawBall hatP eps,
        (⨅ A : Mat m p, ENNReal.ofReal (risk A T)) ≤ ⨅ A : Mat m p, ENNReal.ofReal (risk A Q)
          := by
  let K : Set (Mat (p + m) (p + m)) :=
    {S | S.PosSemidef ∧ buresDistance S (secondMoment hatP) ≤ eps}
  have himage : secondMoment '' lawBall hatP eps = K :=
    (w2BuresEquivalence hsv hatP eps).1
  have hself : hatP ∈ lawBall hatP eps := by
    change wassersteinDistance hatP hatP ≤ eps
    rw [wasserstein_self]
    exact eps.property
  have hne : K.Nonempty := by
    rw [← himage]
    exact ⟨secondMoment hatP, hatP, hself, rfl⟩
  obtain ⟨S, hS, heq⟩ := finiteDimensional_convex_affine_minimax_ennreal K
    (bures_ball_compact (momentPSD hatP) eps)
    (bures_ball_convex (momentPSD hatP) eps) hne
    (fun A S => matrixRisk A S) matrixRisk_joint_continuous
    (fun S hS => matrixRisk_convex_coefficient ⟨S, hS.1⟩)
    (fun A S _ T _ a b _ _ _ => matrixRisk_affine_moment A S T a b)
  have hsup (A : Mat m p) :
      (⨆ T ∈ lawBall hatP eps, ENNReal.ofReal (risk A T)) =
        ⨆ S ∈ K, ENNReal.ofReal (matrixRisk A S) := by
    rw [← himage, iSup_image]
    simp_rw [risk_eq_matrixRisk]
  rw [← himage] at hS
  obtain ⟨Q, hQ, hQS⟩ := hS
  have hvalue : (⨅ A : Mat m p, ⨆ T ∈ lawBall hatP eps, ENNReal.ofReal (risk A T)) =
      ⨅ A : Mat m p, ENNReal.ofReal (risk A Q) := by
    simp_rw [hsup]
    rw [heq, ← hQS]
    simp_rw [risk_eq_matrixRisk]
  refine ⟨Q, hQ, hvalue, ?_⟩
  intro T hT
  rw [← hvalue]
  exact iInf_mono fun A => le_iSup₂_of_le T hT le_rfl

end Papers.WassersteinRegretS2S3
