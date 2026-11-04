module
public import Papers.WassersteinRegretS2S3.T2
public import Papers.WassersteinRegretS2S3.Helpers.DROScalarA
public import Papers.WassersteinRegretS2S3.Helpers.DROConstruction
public import Papers.WassersteinRegretS2S3.Helpers.FactorRegression

/-!
# Matrix objective for the first DRO lower bound

The two-parameter diagonal family has the scalar dual objective used in the
lower-bound certificate. Coordinate computations use uncentered second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: droLowerACoefficient
/-- The [two-parameter rectangular diagonal coefficient matrix](goal) has
[coefficient alpha on the first matched coordinate](hyp:alpha),
[coefficient beta on every remaining matched coordinate](hyp:beta), and zero elsewhere. -/
def droLowerACoefficient {p m : ℕ} (alpha beta : ℝ) : Mat m p :=
  fun i j => if i.val = j.val then (if i.val = 0 then alpha else beta) else 0

-- @node: coordinateResidual_single_row
/-- If [response row i uses only feature k, with coefficient d](hyp:hrow),
[its residual second moment is d squared times the second moment of feature k,
minus d times each of the two feature–response cross moments, plus the second
moment of response i](goal). -/
lemma coordinateResidual_single_row {p m : ℕ} (P : JointLaws p m)
    (A : Mat m p) (i : Fin m) (k : Fin p) (d : ℝ)
    (hrow : ∀ j, A i j = if j = k then d else 0) :
    coordinateResidual P A i = d ^ 2 * secondMomentX P k k -
      d * secondMoment P (Fin.castAdd m k) (Fin.natAdd p i) -
      d * secondMomentYX P i k + secondMomentY P i i := by
  rw [coordinateResidual_eq_secondMoment]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadraticRegressionMatrix,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, hrow]
  simp [Matrix.one_apply, secondMomentX, secondMomentYX, secondMomentY,
    blockX, blockYX, blockY, rawBlocks, Matrix.submatrix_apply, pow_two]
  ring

-- @node: droLowerA_coefficient_gram
/-- [The row Gram matrix of the two-parameter coefficient matrix is diagonal,
with alpha squared in the first matched row, beta squared in the other matched
rows, and zero in response rows beyond the feature dimension](goal). -/
lemma droLowerA_coefficient_gram {p m : ℕ} (alpha beta : ℝ) :
    (droLowerACoefficient alpha beta : Mat m p) *
      (droLowerACoefficient alpha beta).transpose = Matrix.diagonal
        (fun i : Fin m => if i.val < p then (if i.val = 0 then alpha else beta) ^ 2 else 0) := by
  ext i j
  by_cases hi : i.val < p
  · let k : Fin p := ⟨i.val, hi⟩
    have hrow (l : Fin p) :
        droLowerACoefficient alpha beta i l =
          if l = k then (if i.val = 0 then alpha else beta) else 0 := by
      have he : i.val = l.val ↔ l = k := by
        constructor
        · intro h; exact Fin.ext h.symm
        · intro h; subst l; rfl
      simp [droLowerACoefficient, he]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hij : i = j
    · subst j
      by_cases hz : i.val = 0 <;>
        simp [droLowerACoefficient, k, hi, pow_two, hz, show 0 < p by omega]
    · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      simp [droLowerACoefficient, k, hij, hval]
  · have hz (l : Fin p) : i.val ≠ l.val := by
      intro he; exact hi (he ▸ l.isLt)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, droLowerACoefficient,
      hz, if_false, zero_mul, Finset.sum_const_zero]
    by_cases hij : i = j
    · subst j; simp [hi]
    · simp [hij]

-- @node: sum_fin_prefix
/-- If [q is at most m](hyp:hq), [summing t over the first q positions of an
m-position vector, with zero in all other positions, gives q times t](goal). -/
lemma sum_fin_prefix (m q : ℕ) (hq : q ≤ m) (t : ℝ) :
    (∑ i : Fin m, if i.val < q then t else 0) = (q : ℝ) * t := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < q then t else 0) m,
    ← Finset.sum_filter]
  have he : (Finset.range m).filter (fun i => i < q) = Finset.range q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  simp

-- @node: droLowerA_diagonal_threshold
/-- If [there are at least two matched feature–response coordinates](hyp:hq),
[the largest squared diagonal coefficient in the two-parameter family is the
maximum of alpha squared and beta squared](goal). -/
lemma droLowerA_diagonal_threshold {p m : ℕ} [NeZero m]
    (hq : 2 ≤ min p m) (alpha beta : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin m =>
        (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2) =
      max (alpha ^ 2) (beta ^ 2) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · simpa using (sq_nonneg alpha).trans (le_max_left (alpha ^ 2) (beta ^ 2))
  · apply max_le
    · have h := Finset.le_sup'
        (fun i : Fin m =>
          (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2)
        (Finset.mem_univ (0 : Fin m))
      simpa only [Fin.val_zero, show 0 < p by omega, if_true] using h
    · let j : Fin m := ⟨1, by omega⟩
      have h := Finset.le_sup'
        (fun i : Fin m =>
          (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2)
        (Finset.mem_univ j)
      simpa only [j, show 1 < p by omega, if_true, show (1 : ℕ) ≠ 0 by omega, if_false] using h

-- @node: droLowerA_residual_sum
/-- If [there is at least one matched feature–response coordinate](hyp:hq),
[the sum of the coordinate residual fractions equals the first-coordinate term
(alpha c minus b) squared divided by eta minus one minus alpha squared, plus
min(p,m) minus one copies of the bulk term, whose numerator is
(beta minus b) squared plus b squared and whose denominator is eta minus one
minus beta squared](goal). -/
lemma droLowerA_residual_sum {p m : ℕ} [NeZero m] (hq : 1 ≤ min p m)
    (b c alpha beta eta : ℝ) :
    (∑ i : Fin m,
      (if i = 0 then (alpha * c - b) ^ 2 else
        if i.val < min p m then (beta - b) ^ 2 + b ^ 2 else 0) /
      (eta - 1 - (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2)) =
      (alpha * c - b) ^ 2 / (eta - 1 - alpha ^ 2) +
        (((min p m : ℕ) : ℝ) - 1) * ((beta - b) ^ 2 + b ^ 2) /
          (eta - 1 - beta ^ 2) := by
  let bulk := ((beta - b) ^ 2 + b ^ 2) / (eta - 1 - beta ^ 2)
  have he (i : Fin m) :
      (if i = 0 then (alpha * c - b) ^ 2 else
        if i.val < min p m then (beta - b) ^ 2 + b ^ 2 else 0) /
      (eta - 1 - (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2) =
        (if i.val < min p m then bulk else 0) +
          if i = 0 then (alpha * c - b) ^ 2 / (eta - 1 - alpha ^ 2) - bulk else 0 := by
    by_cases hi : i = 0
    · subst i
      simp [show 0 < p by omega, show 0 < min p m by omega]
    · have hiz : i.val ≠ 0 := by simpa using hi
      by_cases hlt : i.val < min p m
      · simp [hi, hiz, hlt, show i.val < p by omega, bulk]
      · simp [hi, hlt]
  simp_rw [he]
  rw [Finset.sum_add_distrib, sum_fin_prefix m (min p m) (min_le_right _ _)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  dsimp [bulk]
  ring

-- @node: droLowerA_matrix_objective
/-- If [there are at least two matched feature–response coordinates](hyp:hq)
and [the coordinate residual second moments are (alpha c minus b) squared in
the first coordinate, (beta minus b) squared plus b squared in the remaining
matched coordinates, and zero elsewhere](hyp:hres), [the population DRO
objective with both scale and radius equal to one equals the scalar lower-bound
A objective with bulk multiplicity min(p,m) minus one](goal). -/
lemma droLowerA_matrix_objective {p m : ℕ} [NeZero p] [NeZero m]
    (hq : 2 ≤ min p m) (P : JointLaws p m) (b c alpha beta : ℝ)
    (hres : ∀ i : Fin m, coordinateResidual P (droLowerACoefficient alpha beta) i =
      if i = 0 then (alpha * c - b) ^ 2 else
        if i.val < min p m then (beta - b) ^ 2 + b ^ 2 else 0) :
    populationObjective 1 P 1 (droLowerACoefficient alpha beta) =
      droLowerAObjective (((min p m : ℕ) : ℝ) - 1) b c alpha beta := by
  have hgram : (droLowerACoefficient alpha beta : Mat m p) *
      (droLowerACoefficient alpha beta).transpose = Matrix.diagonal
        (fun i : Fin m =>
          (if i.val < p then (if i.val = 0 then alpha else beta) else 0) ^ 2) := by
    rw [droLowerA_coefficient_gram]
    congr 1
    funext i
    split_ifs <;> simp
  have hd := (droStrongDualityDiagonal (assPin1_valid m) assSingularValueConvention_valid
    P 1 (droLowerACoefficient alpha beta)
    (fun i : Fin m => if i.val < p then (if i.val = 0 then alpha else beta) else 0)
    ⟨by norm_num, hgram⟩).2
  rw [droLowerA_diagonal_threshold hq] at hd
  change (⨆ Q ∈ lawBall P 1, ENNReal.ofReal (risk (droLowerACoefficient alpha beta) Q)) = _
  rw [hd]
  unfold droLowerAObjective
  apply iInf_congr
  intro eta
  apply iInf_congr
  intro heta
  simp_rw [hres, droLowerA_residual_sum (by omega : 1 ≤ min p m)]
  norm_num only [NNReal.coe_one, one_pow]
  unfold droLowerADual
  rw [add_assoc]

-- @node: droLowerA_response_diagonal
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), and [the residual second-moment matrix is diagonal with
zero in the first coordinate, b squared in the other matched coordinates, and
zero elsewhere](hyp:hPE), [the second moment of response i is b squared when
i has a matching feature, plus b squared when i is a nonfirst matched
coordinate](goal). -/
lemma droLowerA_response_diagonal {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (i : Fin m) :
    secondMomentY P i i = (if i.val < p then b ^ 2 else 0) +
      (if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0) := by
  have hcan : canonicalCoefficient (secondMoment P) = secondMomentYX P := by
    unfold canonicalCoefficient
    rw [show blockX p m (secondMoment P) = 1 from hPX,
      penrose_eq_inverse_of_isUnit _ isUnit_one]
    simp [secondMomentYX]
  have hyx := hcan.symm.trans hPA
  have hcross (k : Fin p) :
      secondMoment P (Fin.castAdd m k) (Fin.natAdd p i) = secondMomentYX P i k := by
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p i) (Fin.castAdd m k))
      (momentPSD P).property.isHermitian.eq
  have hr : coordinateResidual P (canonicalCoefficient (secondMoment P)) i =
      if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0 := by
    rw [coordinateResidual_eq_secondMoment]
    change matrixResidual (secondMoment P) i i = _
    rw [hPE, Matrix.diagonal_apply_eq]
  by_cases hi : i.val < p
  · let k : Fin p := ⟨i.val, hi⟩
    have hrow (j : Fin p) : canonicalCoefficient (secondMoment P) i j =
        if j = k then b else 0 := by
      rw [hPA]
      have he : i.val = j.val ↔ j = k := by
        constructor
        · intro h; exact Fin.ext h.symm
        · intro h; subst j; rfl
      simp only [he]
    rw [coordinateResidual_single_row P _ i k b hrow, hPX, hcross, hyx] at hr
    simp only [Matrix.one_apply_eq, k, ite_true, mul_one] at hr
    rw [if_pos hi]
    linarith
  · have hrow (j : Fin p) : canonicalCoefficient (secondMoment P) i j =
        if j = 0 then (0 : ℝ) else 0 := by
      simp [hPA, show i.val ≠ j.val by omega]
    rw [coordinateResidual_single_row P _ i 0 0 hrow] at hr
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, zero_add] at hr
    simpa only [hi, if_false, zero_add] using hr

-- @node: droLowerA_contracted_residual
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), and [the residual second-moment matrix is diagonal with
zero in the first coordinate, b squared in the other matched coordinates, and
zero elsewhere](hyp:hPE), [scaling the first feature by c gives the two-parameter
predictor residual second moments (alpha c minus b) squared in the first
coordinate, (beta minus b) squared plus b squared in the other matched
coordinates, and zero elsewhere](goal). -/
lemma droLowerA_contracted_residual {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c alpha beta : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (i : Fin m) :
    coordinateResidual (contractFeatureLaw 0 c P) (droLowerACoefficient alpha beta) i =
      if i = 0 then (alpha * c - b) ^ 2 else
        if i.val < min p m then (beta - b) ^ 2 + b ^ 2 else 0 := by
  have hcan : canonicalCoefficient (secondMoment P) = secondMomentYX P := by
    unfold canonicalCoefficient
    rw [show blockX p m (secondMoment P) = 1 from hPX,
      penrose_eq_inverse_of_isUnit _ isUnit_one]
    simp [secondMomentYX]
  have hyx := hcan.symm.trans hPA
  have hcross (k : Fin p) :
      secondMoment (contractFeatureLaw 0 c P) (Fin.castAdd m k) (Fin.natAdd p i) =
        secondMomentYX (contractFeatureLaw 0 c P) i k := by
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p i) (Fin.castAdd m k))
      (momentPSD (contractFeatureLaw 0 c P)).property.isHermitian.eq
  have hY := droLowerA_response_diagonal P b hPX hPA hPE i
  by_cases hi : i.val < p
  · let k : Fin p := ⟨i.val, hi⟩
    let d := if i.val = 0 then alpha else beta
    have hrow (j : Fin p) : droLowerACoefficient alpha beta i j =
        if j = k then d else 0 := by
      have he : i.val = j.val ↔ j = k := by
        constructor
        · intro h; exact Fin.ext h.symm
        · intro h; subst j; rfl
      simp only [droLowerACoefficient, he, d]
    rw [coordinateResidual_single_row _ _ i k d hrow, hcross,
      contractFeatureLaw_feature_moment, contractFeatureLaw_cross_moment,
      contractFeatureLaw_response_moment, hPX, hyx, hY]
    have hk0 : k = 0 ↔ i = 0 := by
      constructor
      · intro h
        apply Fin.ext
        exact congrArg (Fin.val : Fin p → ℕ) h
      · intro h
        apply Fin.ext
        exact congrArg (Fin.val : Fin m → ℕ) h
    have hlt : i.val < min p m := by omega
    simp only [hk0]
    by_cases hi0 : i = 0
    · subst i
      simp [k, d, NeZero.pos p]
      ring
    · have hv0 : i.val ≠ 0 := by simpa using hi0
      simp [k, d, hi0, hv0, hi, hlt]
      ring
  · have hrow (j : Fin p) : droLowerACoefficient alpha beta i j =
        if j = 0 then (0 : ℝ) else 0 := by
      simp [droLowerACoefficient, show i.val ≠ j.val by omega]
    rw [coordinateResidual_single_row _ _ i 0 0 hrow,
      contractFeatureLaw_response_moment, hY]
    have hlt : ¬i.val < min p m := by omega
    have hi0 : i ≠ 0 := by intro he; subst i; exact hi (NeZero.pos p)
    simp [hi, hlt, hi0]

-- @node: droLowerA_coefficient_frob
/-- [The squared Frobenius norm of the two-parameter coefficient matrix is alpha
squared plus min(p,m) minus one times beta squared](goal). -/
lemma droLowerA_coefficient_frob {p m : ℕ} [NeZero p] [NeZero m]
    (alpha beta : ℝ) :
    frob (droLowerACoefficient alpha beta : Mat m p) ^ 2 =
      alpha ^ 2 + (((min p m : ℕ) : ℝ) - 1) * beta ^ 2 := by
  rw [frob_sq_trace_rows, droLowerA_coefficient_gram, Matrix.trace_diagonal]
  have he (i : Fin m) :
      (if i.val < p then (if i.val = 0 then alpha else beta) ^ 2 else 0) =
        (if i.val < min p m then beta ^ 2 else 0) +
          if i = 0 then alpha ^ 2 - beta ^ 2 else 0 := by
    by_cases hi : i = 0
    · subst i
      simp [NeZero.pos p, show 0 < min p m by exact lt_min (NeZero.pos p) (NeZero.pos m)]
    · have hv : i.val ≠ 0 := by simpa using hi
      have hlt : i.val < min p m ↔ i.val < p := by omega
      simp [hi, hv, hlt]
  simp_rw [he]
  rw [Finset.sum_add_distrib, sum_fin_prefix m (min p m) (min_le_right _ _)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

-- @node: droLowerA_target_regret
/-- If [the feature second-moment matrix is the identity](hyp:hPX) and
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), [the two-parameter predictor's regret is (alpha minus b)
squared plus min(p,m) minus one times (beta minus b) squared](goal). -/
lemma droLowerA_target_regret {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b alpha beta : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0) :
    regret (droLowerACoefficient alpha beta) P =
      (alpha - b) ^ 2 + (((min p m : ℕ) : ℝ) - 1) * (beta - b) ^ 2 := by
  rw [(law_matrix_risk_regret P (droLowerACoefficient alpha beta)).2]
  change matrixRegret (droLowerACoefficient alpha beta) (momentPSD P).val = _
  rw [matrixRegret_feature_sqrt (momentPSD P)]
  change frob ((droLowerACoefficient alpha beta - canonicalCoefficient (secondMoment P)) *
    CFC.sqrt (secondMomentX P)) ^ 2 = _
  rw [hPX, CFC.sqrt_one, Matrix.mul_one]
  have hdiff : droLowerACoefficient alpha beta - canonicalCoefficient (secondMoment P) =
      (droLowerACoefficient (alpha - b) (beta - b) : Mat m p) := by
    rw [hPA]
    ext i j
    change ((if i.val = j.val then (if i.val = 0 then alpha else beta) else 0) -
      (if i.val = j.val then b else 0)) =
      (if i.val = j.val then (if i.val = 0 then alpha - b else beta - b) else 0)
    split_ifs <;> simp
  rw [hdiff, droLowerA_coefficient_frob]

end Papers.WassersteinRegretS2S3
