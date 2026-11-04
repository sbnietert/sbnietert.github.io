module
public import Papers.WassersteinRegretS2S3.Helpers.ParameterDerivative
public import Papers.WassersteinRegretS2S3.Helpers.MomentBall

/-!
# Factor perturbations for the alternative condition number

The exact covariance expansion, displacement bound, and homogeneity
of the leading sensitivity term used in the factor-space Taylor argument.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: factorPerturbedMoment
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma) and [a square factor
perturbation D](hyp:D), the [perturbed second-moment matrix](goal) is the product of the
positive semidefinite square root of Sigma plus D with its transpose. -/
noncomputable def factorPerturbedMoment {n : ℕ} (Sigma : PSD n) (D : Mat n n) : PSD n :=
  ⟨(CFC.sqrt Sigma.val + D) * (CFC.sqrt Sigma.val + D).transpose, by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (CFC.sqrt Sigma.val + D)⟩

-- @node: factor_covariance_expansion
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a factor perturbation D](hyp:D),
[the product of the square root of Sigma plus D with its transpose equals Sigma plus the
linear factor tangent plus D times its transpose](goal). -/
lemma factor_covariance_expansion {n : ℕ} (Sigma : PSD n) (D : Mat n n) :
    (CFC.sqrt Sigma.val + D) * (CFC.sqrt Sigma.val + D).transpose =
      Sigma.val + (factorTangent Sigma D).val + D * D.transpose := by
  have hs : (CFC.sqrt Sigma.val).transpose = CFC.sqrt Sigma.val := by
    simpa using (CFC.sqrt_nonneg Sigma.val).isHermitian.eq
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hs,
    CFC.sqrt_mul_sqrt_self Sigma.val Sigma.property.nonneg]
  change Sigma.val + CFC.sqrt Sigma.val * D.transpose +
    (D * CFC.sqrt Sigma.val + D * D.transpose) = _
  simp only [factorTangent]
  abel

-- @node: factor_covariance_displacement_bound
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a factor perturbation D](hyp:D),
[the Frobenius norm of the induced second-moment change is at most twice the product of the
Frobenius norms of the square root of Sigma and D, plus the squared Frobenius norm of D](goal). -/
lemma factor_covariance_displacement_bound {n : ℕ} (Sigma : PSD n) (D : Mat n n) :
    frob ((CFC.sqrt Sigma.val + D) * (CFC.sqrt Sigma.val + D).transpose - Sigma.val) ≤
      2 * frob (CFC.sqrt Sigma.val) * frob D + frob D ^ 2 := by
  rw [factor_covariance_expansion]
  have he : Sigma.val + (factorTangent Sigma D).val + D * D.transpose - Sigma.val =
      (CFC.sqrt Sigma.val * D.transpose + D * CFC.sqrt Sigma.val) + D * D.transpose := by
    simp only [factorTangent]; abel
  rw [he]
  simp only [frob_eq_matrix_norm]
  calc
    _ ≤ (‖CFC.sqrt Sigma.val * D.transpose‖ + ‖D * CFC.sqrt Sigma.val‖) +
        ‖D * D.transpose‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (‖CFC.sqrt Sigma.val‖ * ‖D‖ + ‖D‖ * ‖CFC.sqrt Sigma.val‖) + ‖D‖ * ‖D‖ := by
      exact add_le_add (add_le_add
        (by simpa using Matrix.frobenius_norm_mul (CFC.sqrt Sigma.val) D.transpose)
        (Matrix.frobenius_norm_mul D (CFC.sqrt Sigma.val)))
        (by simpa using Matrix.frobenius_norm_mul D D.transpose)
    _ = _ := by ring

-- @node: derivative_factor_exact_remainder
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma) and [a factor
perturbation D](hyp:D), [the derivative of the parameter map at Sigma applied to the full
second-moment change equals its value on the linear factor tangent plus its value on
D times its transpose](goal). -/
lemma derivative_factor_exact_remainder {p m : ℕ} (Sigma : PSD (p + m))
    (D : Mat (p + m) (p + m)) :
    fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
      (symOfPSD (factorPerturbedMoment Sigma D) - symOfPSD Sigma) =
    fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) (factorTangent Sigma D) +
    fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
      (symOfPSD ⟨D * D.transpose, by
        simpa using Matrix.posSemidef_self_mul_conjTranspose D⟩) := by
  have he : symOfPSD (factorPerturbedMoment Sigma D) - symOfPSD Sigma =
      factorTangent Sigma D + symOfPSD ⟨D * D.transpose, by
        simpa using Matrix.posSemidef_self_mul_conjTranspose D⟩ := by
    apply Subtype.ext
    change (CFC.sqrt Sigma.val + D) * (CFC.sqrt Sigma.val + D).transpose - Sigma.val = _
    rw [factor_covariance_expansion]
    change Sigma.val + (factorTangent Sigma D).val + D * D.transpose - Sigma.val =
      (factorTangent Sigma D).val + D * D.transpose
    abel
  rw [he, map_add]

-- @node: factor_quadratic_norm_bound
/-- For [a square matrix D](hyp:D), [the Frobenius norm of D times its transpose is at most
the squared Frobenius norm of D](goal). -/
lemma factor_quadratic_norm_bound {n : ℕ} (D : Mat n n) :
    frob (D * D.transpose) ≤ frob D ^ 2 := by
  simpa [frob_eq_matrix_norm, pow_two] using Matrix.frobenius_norm_mul D D.transpose

-- @node: factorTangent_norm_bound
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a factor perturbation D](hyp:D),
[the Frobenius norm of the linear factor tangent is at most twice the product of the
Frobenius norms of the square root of Sigma and D](goal). -/
lemma factorTangent_norm_bound {n : ℕ} (Sigma : PSD n) (D : Mat n n) :
    frob (factorTangent Sigma D).val ≤ 2 * frob (CFC.sqrt Sigma.val) * frob D := by
  change frob (CFC.sqrt Sigma.val * D.transpose + D * CFC.sqrt Sigma.val) ≤ _
  simp only [frob_eq_matrix_norm]
  calc
    _ ≤ ‖CFC.sqrt Sigma.val * D.transpose‖ + ‖D * CFC.sqrt Sigma.val‖ := norm_add_le _ _
    _ ≤ ‖CFC.sqrt Sigma.val‖ * ‖D‖ + ‖D‖ * ‖CFC.sqrt Sigma.val‖ :=
      add_le_add (by simpa using Matrix.frobenius_norm_mul (CFC.sqrt Sigma.val) D.transpose)
        (Matrix.frobenius_norm_mul D (CFC.sqrt Sigma.val))
    _ = _ := by ring

-- @node: derivative_factor_quadratic_bound
/-- At [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), consider [a factor
perturbation D](hyp:D). If [C is nonnegative](hyp:hC) and [the parameter derivative sends
every symmetric perturbation to a matrix with Frobenius norm at most C times the perturbation's
Frobenius norm](hyp:hbound), then [its value on D times its transpose has Frobenius norm at
most C times the squared Frobenius norm of D](goal). -/
lemma derivative_factor_quadratic_bound {p m : ℕ} (Sigma : PSD (p + m))
    (D : Mat (p + m) (p + m)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ H : Sym (p + m),
      frob (fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) H) ≤ C * frob H.val) :
    frob (fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
      (symOfPSD ⟨D * D.transpose, by
        simpa using Matrix.posSemidef_self_mul_conjTranspose D⟩)) ≤ C * frob D ^ 2 := by
  exact (hbound _).trans
    (mul_le_mul_of_nonneg_left (factor_quadratic_norm_bound D) hC)

-- @node: factor_taylor_error_transfer
/-- At [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), consider [a factor
perturbation D](hyp:D). If [C is nonnegative](hyp:hC), [the parameter derivative is bounded
in Frobenius norm by C times the norm of every symmetric direction](hyp:hbound), and [the
Taylor error using the full induced second-moment change is at most e](hyp:herr), then
[the Taylor error using only the linear factor tangent is at most e plus C times the squared
Frobenius norm of D](goal). -/
lemma factor_taylor_error_transfer {p m : ℕ} (Sigma : PSD (p + m))
    (D : Mat (p + m) (p + m)) {C e : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ H : Sym (p + m),
      frob (fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) H) ≤ C * frob H.val)
    (herr : frob (parameterMap (symOfPSD (factorPerturbedMoment Sigma D)) -
      parameterMap (symOfPSD Sigma) -
      fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
        (symOfPSD (factorPerturbedMoment Sigma D) - symOfPSD Sigma)) ≤ e) :
    frob (parameterMap (symOfPSD (factorPerturbedMoment Sigma D)) -
      parameterMap (symOfPSD Sigma) -
      fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) (factorTangent Sigma D)) ≤
      e + C * frob D ^ 2 := by
  rw [derivative_factor_exact_remainder] at herr
  have he : parameterMap (symOfPSD (factorPerturbedMoment Sigma D)) -
      parameterMap (symOfPSD Sigma) -
      fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) (factorTangent Sigma D) =
      (parameterMap (symOfPSD (factorPerturbedMoment Sigma D)) -
      parameterMap (symOfPSD Sigma) -
      (fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) (factorTangent Sigma D) +
      fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
        (symOfPSD ⟨D * D.transpose, by
          simpa using Matrix.posSemidef_self_mul_conjTranspose D⟩))) +
      fderiv ℝ (@parameterMap p m) (symOfPSD Sigma)
        (symOfPSD ⟨D * D.transpose, by
          simpa using Matrix.posSemidef_self_mul_conjTranspose D⟩) := by abel
  rw [he]
  exact (show frob (_ + _) ≤ frob _ + frob _ from by simpa only [frob_eq_matrix_norm] using norm_add_le _ _).trans
    (add_le_add herr (derivative_factor_quadratic_bound Sigma D hC hbound))

-- @node: factor_squared_loss_remainder_bound
/-- For [a matrix A](hyp:A) and [an equally sized perturbation E](hyp:E), [the absolute change
in squared Frobenius norm upon adding E is at most twice the product of their Frobenius
norms plus the squared Frobenius norm of E](goal). -/
lemma factor_squared_loss_remainder_bound {a b : ℕ} (A E : Mat a b) :
    |frob (A + E) ^ 2 - frob A ^ 2| ≤ 2 * frob A * frob E + frob E ^ 2 := by
  simp only [frob_eq_matrix_norm]
  have hupper := norm_add_le A E
  have hlower := norm_sub_norm_le A (A + E)
  have he : A - (A + E) = -E := by abel
  rw [he, norm_neg] at hlower
  have hnonA := norm_nonneg A
  have hnonE := norm_nonneg E
  have hnonSum := norm_nonneg (A + E)
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (‖A‖ - ‖A + E‖),
      mul_nonneg (sub_nonneg.mpr hlower) (add_nonneg hnonA hnonSum)]
  · nlinarith [sq_nonneg (‖A‖ + ‖E‖ - ‖A + E‖),
      mul_nonneg (sub_nonneg.mpr hupper) (by positivity : 0 ≤ ‖A‖ + ‖E‖ + ‖A + E‖)]

-- @node: factor_weighted_squared_loss_remainder_bound
/-- For [a matrix A](hyp:A), [an equally sized perturbation E](hyp:E), and [a compatible
right weighting matrix W](hyp:W), [the absolute change in squared Frobenius norm between
A times W and the product of A plus E with W is at most twice the product of the norms of A and E plus
the squared norm of E, all multiplied by the squared norm of W](goal). -/
lemma factor_weighted_squared_loss_remainder_bound {a b c : ℕ}
    (A E : Mat a b) (W : Mat b c) :
    |frob ((A + E) * W) ^ 2 - frob (A * W) ^ 2| ≤
      (2 * frob A * frob E + frob E ^ 2) * frob W ^ 2 := by
  rw [Matrix.add_mul]
  have hA : frob (A * W) ≤ frob A * frob W :=
    by simpa [frob_eq_matrix_norm] using Matrix.frobenius_norm_mul A W
  have hE : frob (E * W) ≤ frob E * frob W :=
    by simpa [frob_eq_matrix_norm] using Matrix.frobenius_norm_mul E W
  have hnA : 0 ≤ frob A := by simpa [frob_eq_matrix_norm] using norm_nonneg A
  have hnE : 0 ≤ frob E := by simpa [frob_eq_matrix_norm] using norm_nonneg E
  have hnW : 0 ≤ frob W := by simpa [frob_eq_matrix_norm] using norm_nonneg W
  calc
    _ ≤ 2 * frob (A * W) * frob (E * W) + frob (E * W) ^ 2 :=
      factor_squared_loss_remainder_bound (A * W) (E * W)
    _ ≤ 2 * (frob A * frob W) * (frob E * frob W) +
        (frob E * frob W) ^ 2 := by
      gcongr <;> first | fun_prop | assumption | positivity | simpa [frob_eq_matrix_norm] using norm_nonneg (E * W)
    _ = _ := by ring

-- @node: factor_scaled_squared_loss_remainder_bound
/-- For [a matrix A](hyp:A), [a perturbation E of the same size](hyp:E), and [a compatible
right weighting matrix W](hyp:W), suppose [C is nonnegative](hyp:hC), [e is nonnegative](hyp:he),
[r is nonnegative](hyp:hr), [the Frobenius norm of A is at most C times r](hyp:hA), and
[the Frobenius norm of E is at most e times r](hyp:hE). Then [the absolute change in squared
Frobenius norm after adding E and right multiplying by W is at most the product of
twice C times e plus e squared, the squared Frobenius norm of W, and r squared](goal). -/
lemma factor_scaled_squared_loss_remainder_bound {a b c : ℕ}
    (A E : Mat a b) (W : Mat b c) {C e r : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hr : 0 ≤ r)
    (hA : frob A ≤ C * r) (hE : frob E ≤ e * r) :
    |frob ((A + E) * W) ^ 2 - frob (A * W) ^ 2| ≤
      ((2 * C * e + e ^ 2) * frob W ^ 2) * r ^ 2 := by
  calc
    _ ≤ (2 * frob A * frob E + frob E ^ 2) * frob W ^ 2 :=
      factor_weighted_squared_loss_remainder_bound A E W
    _ ≤ (2 * (C * r) * (e * r) + (e * r) ^ 2) * frob W ^ 2 := by
      gcongr <;> first | fun_prop | assumption | positivity | simpa [frob_eq_matrix_norm] using norm_nonneg E
    _ = _ := by ring

-- @node: factorTangent_smul
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma), [a real scalar r](hyp:r), and
[a factor direction D](hyp:D), [multiplying D by r multiplies the linear factor tangent
at Sigma by r](goal). -/
lemma factorTangent_smul {n : ℕ} (Sigma : PSD n) (r : ℝ) (D : Mat n n) :
    factorTangent Sigma (r • D) = r • factorTangent Sigma D := by
  apply Subtype.ext
  simp [factorTangent, Matrix.transpose_smul, smul_add]

-- @node: derivativeSensitivity_smul
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), [a real scalar r](hyp:r),
and [a factor direction D](hyp:D), [the derivative sensitivity in direction r times D equals
r squared times the sensitivity in direction D](goal). -/
lemma derivativeSensitivity_smul {p m : ℕ} (Sigma : PSD (p + m))
    (r : ℝ) (D : Mat (p + m) (p + m)) :
    derivativeSensitivity Sigma (r • D) = r ^ 2 * derivativeSensitivity Sigma D := by
  simp only [derivativeSensitivity, factorTangent_smul, map_smul, Matrix.smul_mul,
    frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

-- @node: derivativeSensitivity_continuous
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), [derivative
sensitivity is a continuous function of the factor direction](goal). -/
@[fun_prop] lemma derivativeSensitivity_continuous {p m : ℕ} (Sigma : PSD (p + m)) :
    Continuous (derivativeSensitivity Sigma) := by
  unfold derivativeSensitivity
  simp only [frob_eq_matrix_norm]
  have ht : Continuous (factorTangent Sigma) := by
    unfold factorTangent
    fun_prop
  fun_prop

-- @node: derivativeSensitivity_attains_max
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), [there exists a
factor direction with Frobenius norm at most one whose derivative sensitivity is at least
that of every other direction with Frobenius norm at most one](goal). -/
lemma derivativeSensitivity_attains_max {p m : ℕ} (Sigma : PSD (p + m)) :
    ∃ D : Mat (p + m) (p + m), frob D ≤ 1 ∧
      ∀ E : Mat (p + m) (p + m), frob E ≤ 1 →
        derivativeSensitivity Sigma E ≤ derivativeSensitivity Sigma D := by
  obtain ⟨D, hD, hmax⟩ := (isCompact_closedBall (0 : Mat (p + m) (p + m)) 1).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr (by norm_num))
    (derivativeSensitivity_continuous Sigma).continuousOn
  refine ⟨D, ?_, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using hD
  · intro E hE
    apply hmax
    simpa [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using hE

-- @node: derivativeSensitivity_sup_ne_top
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), [the supremum of
derivative sensitivity over factor directions with Frobenius norm at most one is finite
when viewed as a nonnegative extended real number](goal). -/
lemma derivativeSensitivity_sup_ne_top {p m : ℕ} (Sigma : PSD (p + m)) :
    (⨆ (D : Mat (p + m) (p + m)) (_ : frob D ≤ 1),
      ENNReal.ofReal (derivativeSensitivity Sigma D)) ≠ ⊤ := by
  obtain ⟨D, hD, hmax⟩ := derivativeSensitivity_attains_max Sigma
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  exact iSup_le fun E => iSup_le fun hE => ENNReal.ofReal_le_ofReal (hmax E hE)

-- @node: derivativeSensitivity_radius_scaling
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma) and [a radius r](hyp:r)
with [r strictly positive](hyp:hr), [the supremum of derivative sensitivity over the
Frobenius ball of radius r equals r squared times its supremum over the unit ball, with
both suprema viewed as nonnegative extended real numbers](goal). -/
lemma derivativeSensitivity_radius_scaling {p m : ℕ} (Sigma : PSD (p + m))
    (r : ℝ) (hr : 0 < r) :
    (⨆ (D : Mat (p + m) (p + m)) (_ : frob D ≤ r),
      ENNReal.ofReal (derivativeSensitivity Sigma D)) =
      ENNReal.ofReal (r ^ 2) *
        ⨆ (D : Mat (p + m) (p + m)) (_ : frob D ≤ 1),
          ENNReal.ofReal (derivativeSensitivity Sigma D) := by
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun hD => ?_
    have hn : frob (r⁻¹ • D) ≤ 1 := by
      simp only [frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_iff₀ hr).mpr (by simpa [frob_eq_matrix_norm] using hD)
    have he : D = r • (r⁻¹ • D) := by simp [smul_smul, hr.ne']
    calc
      _ = ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (derivativeSensitivity Sigma (r⁻¹ • D)) := by
        conv_lhs => rw [he, derivativeSensitivity_smul]
        rw [ENNReal.ofReal_mul (sq_nonneg r)]
      _ ≤ _ := by
        apply mul_le_mul' le_rfl
        apply le_iSup_of_le (r⁻¹ • D)
        exact le_iSup_of_le hn le_rfl
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun D => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hD => ?_
    have hn : frob (r • D) ≤ r := by
      simp only [frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simpa using mul_le_mul_of_nonneg_left
        (show ‖D‖ ≤ 1 by simpa [frob_eq_matrix_norm] using hD) hr.le
    apply le_iSup_of_le (r • D)
    apply le_iSup_of_le hn
    rw [derivativeSensitivity_smul, ENNReal.ofReal_mul (sq_nonneg r)]

-- @node: derivativeSensitivity_sup_error_bound
/-- For [a positive semidefinite second-moment matrix Sigma](hyp:Sigma), [a real-valued
function f of factor directions](hyp:f), and [an error tolerance e](hyp:e), suppose [e is
nonnegative](hyp:he), [f is nonnegative on the Frobenius unit ball](hyp:hn), and [f differs
from derivative sensitivity by at most e everywhere on that ball](hyp:herr). Then [the
nonnegative extended-real supremum of f on the ball is finite, and its real value differs
from the real value of the sensitivity supremum by at most e](goal). -/
lemma derivativeSensitivity_sup_error_bound {p m : ℕ} (Sigma : PSD (p + m))
    (f : Mat (p + m) (p + m) → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hn : ∀ D, frob D ≤ 1 → 0 ≤ f D)
    (herr : ∀ D, frob D ≤ 1 → |f D - derivativeSensitivity Sigma D| ≤ e) :
    (⨆ D, ⨆ (_ : frob D ≤ 1), ENNReal.ofReal (f D)) ≠ ⊤ ∧
    |(⨆ D, ⨆ (_ : frob D ≤ 1), ENNReal.ofReal (f D)).toReal -
      (⨆ D, ⨆ (_ : frob D ≤ 1),
        ENNReal.ofReal (derivativeSensitivity Sigma D)).toReal| ≤ e := by
  obtain ⟨D, hD, hmax⟩ := derivativeSensitivity_attains_max Sigma
  have hnon : 0 ≤ derivativeSensitivity Sigma D := by
    unfold derivativeSensitivity
    positivity
  have hsup : (⨆ E, ⨆ (_ : frob E ≤ 1),
      ENNReal.ofReal (derivativeSensitivity Sigma E)) =
      ENNReal.ofReal (derivativeSensitivity Sigma D) := by
    apply le_antisymm
    · exact iSup_le fun E => iSup_le fun hE => ENNReal.ofReal_le_ofReal (hmax E hE)
    · exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hu : (⨆ E, ⨆ (_ : frob E ≤ 1), ENNReal.ofReal (f E)) ≤
      ENNReal.ofReal (derivativeSensitivity Sigma D + e) := by
    refine iSup_le fun E => iSup_le fun hE => ENNReal.ofReal_le_ofReal ?_
    have hb := (abs_le.mp (herr E hE)).2
    have hm := hmax E hE
    linarith
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  refine ⟨hfinite, ?_⟩
  rw [hsup, ENNReal.toReal_ofReal hnon]
  have hupper := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (add_nonneg hnon he)] at hupper
  have hlower := ENNReal.toReal_mono hfinite
    (le_iSup_of_le D (le_iSup_of_le hD le_rfl) :
      ENNReal.ofReal (f D) ≤ ⨆ E, ⨆ (_ : frob E ≤ 1), ENNReal.ofReal (f E))
  rw [ENNReal.toReal_ofReal (hn D hD)] at hlower
  have hb := (abs_le.mp (herr D hD)).1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Papers.WassersteinRegretS2S3
