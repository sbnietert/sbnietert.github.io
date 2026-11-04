module
public import Papers.WassersteinRegretS2S3.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Existence under a spectral quadratic penalty

A positive operator-norm penalty bounds every objective sublevel in the finite-dimensional
coefficient space. No nondegeneracy or uniqueness of the unpenalized minimum is required.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped Matrix.Norms.Frobenius

-- @node: coefficientOperatorEquiv
/-- For [a response dimension m](hyp:m) and [a feature dimension p](hyp:p), the
[continuous linear correspondence between coefficient matrices and Euclidean
linear operators](goal) identifies each matrix with its action from feature
space to response space and has a continuous linear inverse. -/
noncomputable def coefficientOperatorEquiv (m p : ℕ) :
    Mat m p ≃L[ℝ] (Euc p →L[ℝ] Euc m) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin p)).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

-- @node: coefficient_opNorm_continuous
/-- [The Euclidean operator norm is a continuous function of the entries of a
rectangular coefficient matrix](goal). -/
@[fun_prop] lemma coefficient_opNorm_continuous {m p : ℕ} :
    Continuous (@opNorm m p) := by
  change Continuous (fun A => ‖coefficientOperatorEquiv m p A‖)
  fun_prop

-- @node: spectral_penalty_minimum
/-- For [a real-valued objective f on coefficient matrices](hyp:f) that is
[continuous](hyp:hf) and [nonnegative everywhere](hyp:hn), and [a real penalty
scale eps](hyp:eps) that is [strictly positive](hyp:heps), [there exists a global
minimizer of f plus eps squared times the squared Euclidean operator norm](goal). -/
lemma spectral_penalty_minimum {m p : ℕ} (f : Mat m p → ℝ)
    (hf : Continuous f) (hn : ∀ A, 0 ≤ f A) (eps : ℝ) (heps : 0 < eps) :
    ∃ A, ∀ B, f A + eps ^ 2 * opNorm A ^ 2 ≤ f B + eps ^ 2 * opNorm B ^ 2 := by
  let F : Mat m p → ℝ := fun A => f A + eps ^ 2 * opNorm A ^ 2
  have hF : Continuous F := by fun_prop
  apply hF.exists_forall_le_of_isBounded 0
  apply (isBounded_iff_forall_norm_le).mpr
  let C := Real.sqrt (F 0 / eps ^ 2)
  let inv : (Euc p →L[ℝ] Euc m) →L[ℝ] Mat m p :=
    (coefficientOperatorEquiv m p).symm.toContinuousLinearMap
  obtain ⟨D, hDpos, hD⟩ := inv.bound
  refine ⟨D * C, ?_⟩
  intro A hA
  have hpen : eps ^ 2 * opNorm A ^ 2 ≤ F 0 := by
    have := hn A
    change f A + eps ^ 2 * opNorm A ^ 2 ≤ F 0 at hA
    linarith
  have hop : opNorm A ≤ C := by
    apply Real.le_sqrt_of_sq_le
    exact (le_div_iff₀ (sq_pos_of_pos heps)).mpr (by simpa [mul_comm] using hpen)
  have hmap := hD (coefficientOperatorEquiv m p A)
  change ‖(coefficientOperatorEquiv m p).symm ((coefficientOperatorEquiv m p) A)‖ ≤
    D * opNorm A at hmap
  rw [ContinuousLinearEquiv.symm_apply_apply] at hmap
  exact hmap.trans (mul_le_mul_of_nonneg_left hop (le_of_lt hDpos))

end Papers.WassersteinRegretS2S3
