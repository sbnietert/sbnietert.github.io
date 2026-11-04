module
public import Papers.WassersteinRegretS2S3.Helpers.LowerAGaussian

/-!
# Coordinate reflections for the first DRO lower bound

Simultaneous reflections remove every off-diagonal coefficient, including
coefficients involving the extra feature columns or response rows.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

-- @node: droCoordinateReflection
/-- In [dimension n](hyp:n), the [coordinate reflection](goal) reverses the sign
of [coordinate k](hyp:k) and leaves all other coordinates unchanged; it is the
identity when k is outside the coordinate range. -/
noncomputable def droCoordinateReflection (n k : ℕ) : Orth n :=
  ⟨Matrix.diagonal (fun i : Fin n => if i.val = k then (-1 : ℝ) else 1), by
    apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
    ext i j
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    by_cases hi : i.val = k <;> simp [hi, Matrix.diagonal_apply, Matrix.one_apply]⟩

-- @node: droLowerAReflection
/-- For [p features](hyp:p), [m responses](hyp:m), and [coordinate k](hyp:k),
the [joint coordinate reflection](goal) reverses coordinate k in both blocks
where that coordinate exists. -/
noncomputable def droLowerAReflection (p m k : ℕ) : BlockOrth p m :=
  (droCoordinateReflection p k, droCoordinateReflection m k)

-- @node: droCoordinateReflection_coefficient
/-- [Simultaneously reflecting coordinate k in the feature and response blocks
multiplies coefficient (i,j) by a minus sign for each of its row and column
indices that equals k](goal). -/
lemma droCoordinateReflection_coefficient {p m : ℕ} (k : ℕ)
    (A : Mat m p) (i : Fin m) (j : Fin p) :
    ((droCoordinateReflection m k).val.transpose * A *
      (droCoordinateReflection p k).val) i j =
      (if i.val = k then -1 else 1) * A i j * (if j.val = k then -1 else 1) := by
  simp [droCoordinateReflection, Matrix.diagonal_mul, Matrix.mul_diagonal]

-- @node: droLowerA_reflection_invariant_iff
/-- [A rectangular coefficient matrix is unchanged by every simultaneous
feature and response coordinate reflection if and only if every entry whose
row and column indices differ is zero](goal). -/
lemma droLowerA_reflection_invariant_iff {p m : ℕ} (A : Mat m p) :
    (∀ k : ℕ, (droCoordinateReflection m k).val.transpose * A *
      (droCoordinateReflection p k).val = A) ↔
      ∀ (i : Fin m) (j : Fin p), i.val ≠ j.val → A i j = 0 := by
  constructor
  · intro hA i j hij
    have h := congrArg (fun B : Mat m p => B i j) (hA i.val)
    rw [droCoordinateReflection_coefficient] at h
    have hji : j.val ≠ i.val := Ne.symm hij
    simp only [ite_true, hji, if_false, neg_one_mul, mul_one] at h
    linarith
  · intro hA k
    ext i j
    rw [droCoordinateReflection_coefficient]
    by_cases hij : i.val = j.val
    · by_cases hi : i.val = k
      · simp [hi, show j.val = k by omega]
      · simp [hi, show j.val ≠ k by omega]
    · rw [hA i j hij]
      simp

-- @node: droLowerA_reflection_gaussian_invariant
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), [the residual second-moment matrix is diagonal with zero
in the first coordinate, b squared in the other matched coordinates, and zero
elsewhere](hyp:hPE), and [the joint law is centered Gaussian with its specified
second-moment matrix](hyp:hGaussian), [simultaneously reflecting coordinate k
in the feature and response blocks preserves both the original law and the
law obtained by scaling the first feature by c](goal). -/
lemma droLowerA_reflection_gaussian_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (hGaussian : lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P))
    (k : ℕ) :
    Measure.map (matrixCLM (blockActionMatrix (droLowerAReflection p m k)))
      (lawMeasure P) = lawMeasure P ∧
      Measure.map (matrixCLM (blockActionMatrix (droLowerAReflection p m k)))
        (lawMeasure (contractFeatureLaw 0 c P)) = lawMeasure (contractFeatureLaw 0 c P) := by
  apply droLowerA_diagonal_gaussian_invariant P b c hPX hPA hPE hGaussian
    (droLowerAReflection p m k)
    (fun i => if i.val = k then -1 else 1)
    (fun i => if i.val = k then -1 else 1) rfl rfl
  · intro i; split_ifs <;> norm_num
  · intro i; split_ifs <;> norm_num
  · intro i j hij; rw [hij]

end Papers.WassersteinRegretS2S3
