module
public import Papers.WassersteinRegretS2S3.Helpers.GaussianSymmetry
public import Papers.WassersteinRegretS2S3.Helpers.LowerBSymmetry

/-!
# Gaussian reflection invariance for the second DRO lower bound
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory

-- @node: droLowerB_cross_moment
/-- If [the feature second-moment matrix is the identity](hyp:hPX) and
[the canonical regression coefficient is zero except for a in the first response–feature
entry](hyp:hPA), then [the response–feature cross-moment matrix has that same single
nonzero entry a](goal). -/
lemma droLowerB_cross_moment {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (a : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0) :
    secondMomentYX P = fun i j => if i = 0 ∧ j = 0 then a else 0 := by
  have hcan : canonicalCoefficient (secondMoment P) = secondMomentYX P := by
    unfold canonicalCoefficient
    rw [show blockX p m (secondMoment P) = 1 from hPX,
      penrose_eq_inverse_of_isUnit _ isUnit_one]
    simp [secondMomentYX]
  exact hcan.symm.trans hPA

-- @node: droLowerB_response_moment
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is zero except for a in its first entry](hyp:hPA),
and [the residual second-moment matrix is diagonal with first entry zero and all other
entries s](hyp:hPE), then [the response second-moment matrix is diagonal with first
entry a squared and all other diagonal entries s](goal). -/
lemma droLowerB_response_moment {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (s a : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0)
    (hPE : matrixResidual (secondMoment P) =
      Matrix.diagonal (fun i => if i = 0 then 0 else s)) :
    secondMomentY P = Matrix.diagonal (fun i => if i = 0 then a ^ 2 else s) := by
  have hyx := droLowerB_cross_moment P a hPX hPA
  have hcross (i : Fin p) (j : Fin m) :
      secondMoment P (Fin.castAdd m i) (Fin.natAdd p j) = secondMomentYX P j i := by
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p j) (Fin.castAdd m i))
      (secondMoment_posSemidef P).isHermitian.eq
  ext i j
  have hr := congrArg (fun M : Mat m m => M i j) hPE
  rw [matrixResidual, hPA] at hr
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadraticRegressionMatrix,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right] at hr
  have hx : secondMoment P (Fin.castAdd m 0) (Fin.castAdd m 0) = 1 := by
    exact congrArg (fun M : Mat p p => M 0 0) hPX
  have hy (i : Fin m) : secondMoment P (Fin.natAdd p i) (Fin.castAdd m 0) =
      if i = 0 then a else 0 := by
    simpa only [secondMomentYX, blockYX, rawBlocks, Matrix.submatrix_apply,
      and_true] using congrArg (fun M : Mat m p => M i 0) hyx
  have hxy (i : Fin m) : secondMoment P (Fin.castAdd m 0) (Fin.natAdd p i) =
      if i = 0 then a else 0 := by
    rw [hcross, hyx]
    simp
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  all_goals
    simp [hi, hj, Matrix.one_apply, hx, hy, hxy, Matrix.diagonal_apply, eq_comm] at hr ⊢
    simp only [secondMomentY, blockY, rawBlocks, Matrix.submatrix_apply]
    nlinarith [hr]

-- @node: droLowerB_diagonal_moment_invariant
/-- Suppose [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is zero except for a in its first entry](hyp:hPA),
and [the residual second-moment matrix is diagonal with first entry zero and remaining
diagonal entries s](hyp:hPE). If [each feature multiplier squares to one](hyp:hx),
[each response multiplier squares to one](hyp:hy), and [the first feature](hyp:hx0)
and [first response](hyp:hy0) multipliers equal one, then [simultaneously applying
these coordinate multipliers leaves the joint second-moment matrix unchanged](goal). -/
lemma droLowerB_diagonal_moment_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (s a : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0)
    (hPE : matrixResidual (secondMoment P) =
      Matrix.diagonal (fun i => if i = 0 then 0 else s))
    (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i * x i = 1) (hy : ∀ i, y i * y i = 1)
    (hx0 : x 0 = 1) (hy0 : y 0 = 1) :
    let D := Matrix.diagonal (Fin.addCases x y)
    D * secondMoment P * D.transpose = secondMoment P := by
  have hYX := droLowerB_cross_moment P a hPX hPA
  have hY := droLowerB_response_moment P s a hPX hPA hPE
  have hxx (i j : Fin p) :
      secondMoment P (Fin.castAdd m i) (Fin.castAdd m j) = if i = j then 1 else 0 := by
    exact congrArg (fun M : Mat p p => M i j) hPX
  have hyx (i : Fin m) (j : Fin p) :
      secondMoment P (Fin.natAdd p i) (Fin.castAdd m j) =
        if i = 0 ∧ j = 0 then a else 0 := by
    exact congrArg (fun M : Mat m p => M i j) hYX
  have hxy (i : Fin p) (j : Fin m) :
      secondMoment P (Fin.castAdd m i) (Fin.natAdd p j) =
        if j = 0 ∧ i = 0 then a else 0 := by
    rw [← hyx j i]
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p j) (Fin.castAdd m i))
      (secondMoment_posSemidef P).isHermitian.eq
  have hyy (i j : Fin m) :
      secondMoment P (Fin.natAdd p i) (Fin.natAdd p j) =
        if i = j then (if i = 0 then a ^ 2 else s) else 0 := by
    exact congrArg (fun M : Mat m m => M i j) hY
  dsimp only
  ext i j
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left, hxx]
    by_cases hij : i = j
    · subst j; simp [hx]
    · simp [hij]
  · simp only [Fin.addCases_left, Fin.addCases_right, hxy]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, hx0, hy0]
  · simp only [Fin.addCases_left, Fin.addCases_right, hyx]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, hx0, hy0]
  · simp only [Fin.addCases_right, hyy]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      rw [mul_right_comm, hy, one_mul]
    · simp [hij]

-- @node: droTailSignSubgroup_diagonal
/-- [Every member of the tail-sign subgroup is a diagonal matrix whose entries square
to one and whose first diagonal entry is one](goal). -/
lemma droTailSignSubgroup_diagonal {n : ℕ} [NeZero n]
    (u : droTailSignSubgroup n) :
    ∃ x : Fin n → ℝ, u.val.val = Matrix.diagonal x ∧
      (∀ i, x i * x i = 1) ∧ x 0 = 1 := by
  rcases u.property with h | h
  · refine ⟨fun _ => 1, ?_, by simp, rfl⟩
    rw [h]
    simp
  · refine ⟨fun i => if i = 0 then 1 else -1, ?_, ?_, by simp⟩
    · rw [h]; rfl
    · intro i
      by_cases hi : i = 0 <;> simp [hi]

-- @node: droLowerB_gaussian_invariant
/-- Suppose [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is zero except for a in its first entry](hyp:hPA),
[the residual second-moment matrix is diagonal with first entry zero and remaining
diagonal entries s](hyp:hPE), and [the joint law is the centered Gaussian with its own
second-moment matrix](hyp:hGaussian). Then [both this law and the law obtained by
scaling its first feature by c are invariant under independent feature-tail and
response-tail reflections](goal). -/
lemma droLowerB_gaussian_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (s a c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i = 0 ∧ j = 0 then a else 0)
    (hPE : matrixResidual (secondMoment P) =
      Matrix.diagonal (fun i => if i = 0 then 0 else s))
    (hGaussian : lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P)) :
    assDroSymmetryInvariantLaws (droLowerBSymmetryGroup p m) P
      (contractFeatureLaw 0 c P) := by
  intro u
  rcases u.property with ⟨hxmem, hymem⟩
  obtain ⟨x, hx, hx2, hx0⟩ := droTailSignSubgroup_diagonal ⟨u.val.1, hxmem⟩
  obtain ⟨y, hy, hy2, hy0⟩ := droTailSignSubgroup_diagonal ⟨u.val.2, hymem⟩
  have hD := blockActionMatrix_diagonal u.val x y hx hy
  have hmoment : blockActionMatrix u.val * secondMoment P *
      (blockActionMatrix u.val).transpose = secondMoment P := by
    rw [hD]
    exact droLowerB_diagonal_moment_invariant P s a hPX hPA hPE x y hx2 hy2 hx0 hy0
  have htarget := gaussianLaw_invariant_of_secondMoment P hGaussian _ hmoment
  refine ⟨htarget, ?_⟩
  apply lawMapCLM_invariant_of_commute P _ _ ?_ htarget
  rw [hD]
  simp only [coordinateScalingMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Papers.WassersteinRegretS2S3
