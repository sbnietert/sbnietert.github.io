module
public import Papers.WassersteinRegretS2S3.Helpers.LowerAObjective
public import Papers.WassersteinRegretS2S3.Helpers.GaussianSymmetry

/-!
# Gaussian sign symmetries for the first DRO lower bound

Full uncentered moment identities certify simultaneous coordinate reflections,
including the singular residual coordinates and both rectangular tails.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

-- @node: rectangular_identity_gram
/-- For [any real scale](hyp:b), [the rectangular matrix with that scale on matching
row and column indices and zero elsewhere has a row Gram matrix that is diagonal,
with the squared scale on rows having a matching column and zero on all other rows](goal). -/
lemma rectangular_identity_gram {p m : ℕ} (b : ℝ) :
    let A : Mat m p := fun i j => if i.val = j.val then b else 0
    A * A.transpose = Matrix.diagonal (fun i => if i.val < p then b ^ 2 else 0) := by
  dsimp only
  ext i j
  by_cases hi : i.val < p
  · let k : Fin p := ⟨i.val, hi⟩
    have hs : (∑ l : Fin p, (if i.val = l.val then b else 0) *
        (if j.val = l.val then b else 0)) =
        b * (if j.val = i.val then b else 0) := by
      rw [Finset.sum_eq_single k]
      · simp [k]
      · intro l _ hl
        have hne : i.val ≠ l.val := by
          intro he
          apply hl
          exact Fin.ext he.symm
        simp [hne]
      · simp
    change (∑ l : Fin p, (if i.val = l.val then b else 0) *
      (if j.val = l.val then b else 0)) = _
    rw [hs]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply, hi, pow_two]
    · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      simp [Matrix.diagonal_apply, hij, hval]
  · have hz : ∀ l : Fin p, i.val ≠ l.val := by
      intro l he
      exact hi (he ▸ l.isLt)
    change (∑ l : Fin p, (if i.val = l.val then b else 0) *
      (if j.val = l.val then b else 0)) = _
    simp only [hz, if_false, zero_mul, Finset.sum_const_zero]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply, hi]
    · simp [Matrix.diagonal_apply, hij]

-- @node: identity_feature_cross_moment
/-- For [a joint law](hyp:P) with [identity feature second-moment matrix](hyp:hPX),
[the response-feature cross-moment matrix equals the canonical regression coefficient](goal). -/
lemma identity_feature_cross_moment {p m : ℕ} (P : JointLaws p m)
    (hPX : secondMomentX P = 1) :
    secondMomentYX P = canonicalCoefficient (secondMoment P) := by
  unfold canonicalCoefficient
  rw [show blockX p m (secondMoment P) = 1 from hPX,
    penrose_eq_inverse_of_isUnit _ isUnit_one]
  simp [secondMomentYX]

-- @node: identity_feature_response_moment
/-- For [a joint law](hyp:P) with [identity feature second-moment matrix](hyp:hPX),
[the response second-moment matrix equals the canonical regression coefficient times
its transpose plus the residual second-moment matrix](goal). -/
lemma identity_feature_response_moment {p m : ℕ} (P : JointLaws p m)
    (hPX : secondMomentX P = 1) :
    secondMomentY P = canonicalCoefficient (secondMoment P) *
      (canonicalCoefficient (secondMoment P)).transpose + matrixResidual (secondMoment P) := by
  let S := CFC.sqrt (secondMoment P)
  have hf : secondMoment P = S * S.transpose :=
    psd_sqrt_factor (momentPSD P)
  let X := (factorBlocks p m S).1
  let Y := (factorBlocks p m S).2
  let A := canonicalCoefficient (secondMoment P)
  obtain ⟨hX, hYX, hXY, hY⟩ := factor_gram_blocks S
  rw [← hf] at hX hYX hXY hY
  have hxx : X * X.transpose = 1 := hX.symm.trans hPX
  have hyx : Y * X.transpose = A := hYX.symm.trans (identity_feature_cross_moment P hPX)
  have hxy : X * Y.transpose = A.transpose := by
    rw [← hyx, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hr : matrixResidual (secondMoment P) =
      (A * X - Y) * (A * X - Y).transpose := by
    unfold matrixResidual
    rw [hf, ← Matrix.mul_assoc, quadraticRegressionMatrix_factor,
      Matrix.mul_assoc, ← Matrix.transpose_mul, quadraticRegressionMatrix_factor, ← hf]
  rw [hr, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_sub]
  have ht : A * X * (X.transpose * A.transpose) = A * A.transpose := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc A X X.transpose, hxx, Matrix.mul_one]
  rw [ht, ← Matrix.mul_assoc Y X.transpose, hyx,
    Matrix.mul_assoc A X Y.transpose, hxy]
  change secondMomentY P = _
  rw [← hY]
  abel

-- @node: droLowerA_response_moment
/-- For [a joint law](hyp:P) and [a real regression scale](hyp:b), assume
[the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has that scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
and [the residual second moment is diagonal, with the squared scale on matched coordinates
other than the first and zero elsewhere](hyp:hPE).
Then [the response second moment is diagonal, with each entry equal to the squared scale
if that response has a matching feature, plus another squared scale if it is a matched
coordinate other than the first](goal). -/
lemma droLowerA_response_moment {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)) :
    secondMomentY P = Matrix.diagonal (fun i =>
      (if i.val < p then b ^ 2 else 0) +
        (if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)) := by
  rw [identity_feature_response_moment P hPX, hPA, rectangular_identity_gram, hPE,
    ← Matrix.diagonal_add]

-- @node: droLowerA_diagonal_moment_invariant
/-- For [a joint law](hyp:P) and [a real regression scale](hyp:b), assume
[the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has that scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
and [the residual second moment is diagonal, with the squared scale on matched coordinates
other than the first and zero elsewhere](hyp:hPE).
If [feature multipliers](hyp:x) and [response multipliers](hyp:y)
[each square to one on every feature coordinate](hyp:hx) and
[each square to one on every response coordinate](hyp:hy), and
[agree on matching feature and response indices](hyp:hmatch),
[simultaneously multiplying the observation coordinates by these signs leaves the joint
second-moment matrix unchanged](goal). -/
lemma droLowerA_diagonal_moment_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i * x i = 1) (hy : ∀ i, y i * y i = 1)
    (hmatch : ∀ (i : Fin m) (j : Fin p), i.val = j.val → y i = x j) :
    let D := Matrix.diagonal (Fin.addCases x y)
    D * secondMoment P * D.transpose = secondMoment P := by
  have hYX := (identity_feature_cross_moment P hPX).trans hPA
  have hY := droLowerA_response_moment P b hPX hPA hPE
  have hxx (i j : Fin p) :
      secondMoment P (Fin.castAdd m i) (Fin.castAdd m j) = if i = j then 1 else 0 := by
    exact congrArg (fun M : Mat p p => M i j) hPX
  have hyx (i : Fin m) (j : Fin p) :
      secondMoment P (Fin.natAdd p i) (Fin.castAdd m j) =
        if i.val = j.val then b else 0 := by
    exact congrArg (fun M : Mat m p => M i j) hYX
  have hxy (i : Fin p) (j : Fin m) :
      secondMoment P (Fin.castAdd m i) (Fin.natAdd p j) =
        if j.val = i.val then b else 0 := by
    rw [← hyx j i]
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p j) (Fin.castAdd m i))
      (secondMoment_posSemidef P).isHermitian.eq
  have hyy (i j : Fin m) :
      secondMoment P (Fin.natAdd p i) (Fin.natAdd p j) =
        if i = j then
          (if i.val < p then b ^ 2 else 0) +
            (if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)
        else 0 := by
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
    by_cases hij : j.val = i.val
    · rw [if_pos hij, hmatch j i hij, mul_right_comm, hx, one_mul]
    · simp [hij]
  · simp only [Fin.addCases_left, Fin.addCases_right, hyx]
    by_cases hij : i.val = j.val
    · rw [if_pos hij, hmatch i j hij, mul_right_comm, hx, one_mul]
    · simp [hij]
  · simp only [Fin.addCases_right, hyy]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      rw [mul_right_comm, hy, one_mul]
    · simp [hij]

-- @node: droLowerA_diagonal_gaussian_invariant
/-- For [a joint law](hyp:P), [a regression scale and a first-feature contraction factor](hyp:b,c),
assume [the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has the given scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
[the residual second moment is diagonal, with the squared regression scale on matched
coordinates other than the first and zero elsewhere](hyp:hPE), and
[the law is centered Gaussian with covariance equal to its second-moment matrix](hyp:hGaussian).
For [an orthogonal transformation acting separately on features and responses](hyp:u),
let [feature multipliers](hyp:x) and [response multipliers](hyp:y)
[give its diagonal feature action](hyp:hx) and [its diagonal response action](hyp:hy),
with [every feature multiplier squaring to one](hyp:hx2),
[every response multiplier squaring to one](hyp:hy2), and
[multipliers agreeing at matching feature and response indices](hyp:hmatch).
Then [this transformation preserves both the original law and the law obtained by
scaling its first feature by the given factor](goal). -/
lemma droLowerA_diagonal_gaussian_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (hGaussian : lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P))
    (u : BlockOrth p m) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : u.1.val = Matrix.diagonal x) (hy : u.2.val = Matrix.diagonal y)
    (hx2 : ∀ i, x i * x i = 1) (hy2 : ∀ i, y i * y i = 1)
    (hmatch : ∀ (i : Fin m) (j : Fin p), i.val = j.val → y i = x j) :
    Measure.map (matrixCLM (blockActionMatrix u)) (lawMeasure P) = lawMeasure P ∧
      Measure.map (matrixCLM (blockActionMatrix u))
        (lawMeasure (contractFeatureLaw 0 c P)) = lawMeasure (contractFeatureLaw 0 c P) := by
  have hD := blockActionMatrix_diagonal u x y hx hy
  have hmoment : blockActionMatrix u * secondMoment P *
      (blockActionMatrix u).transpose = secondMoment P := by
    rw [hD]
    exact droLowerA_diagonal_moment_invariant P b hPX hPA hPE x y hx2 hy2 hmatch
  have htarget := gaussianLaw_invariant_of_secondMoment P hGaussian _ hmoment
  refine ⟨htarget, ?_⟩
  apply lawMapCLM_invariant_of_commute P _ _ ?_ htarget
  rw [hD]
  simp only [coordinateScalingMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Papers.WassersteinRegretS2S3
