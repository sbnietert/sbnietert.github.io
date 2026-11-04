module
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection
public import Papers.WassersteinRegretS2S3.Helpers.SpectralPenaltyExistence
public import Papers.WassersteinRegretS2S3.Helpers.MomentBall
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Population minimizer existence

Existence is separate from the arbitrary argmin selections used by estimator theorems.
All four objectives have minimizers for every finite-second-moment law, including singular laws.
For positive-radius robust objectives, a nondegenerate comparison law bounds a closed sublevel;
compactness gives attainment without imposing a tie-breaking rule.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: risk_continuous_coefficient
@[fun_prop] lemma risk_continuous_coefficient {p m : ℕ} (P : JointLaws p m) :
    Continuous (fun A : Mat m p => risk A P) := by
  simp_rw [risk_eq_matrixRisk]
  unfold matrixRisk
  fun_prop

@[fun_prop] lemma regret_continuous_coefficient {p m : ℕ} (P : JointLaws p m) :
    Continuous (fun A : Mat m p => regret A P) := by
  unfold regret
  fun_prop

-- @node: regret_le_risk
/-- For [a joint law P](hyp:P) and [a coefficient matrix A](hyp:A),
[the regret of A under P is at most its risk under P](goal). -/
lemma regret_le_risk {p m : ℕ} (P : JointLaws p m) (A : Mat m p) :
    regret A P ≤ risk A P := by
  unfold regret
  exact sub_le_self _ (le_ciInf (risk_nonneg P))

-- @node: risk_uniformly_bounded_on_lawBall
/-- For [a reference joint law P](hyp:P), [a nonnegative Wasserstein radius](hyp:eps),
and [a fixed coefficient matrix A](hyp:A), [there is a finite real upper bound on
the risk of A under every law in the Wasserstein ball around P](goal). -/
lemma risk_uniformly_bounded_on_lawBall {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) (A : Mat m p) :
    ∃ C : ℝ, ∀ Q ∈ lawBall P eps, risk A Q ≤ C := by
  have hc : Continuous (fun S : Mat (p + m) (p + m) => matrixRisk A S) := by
    fun_prop
  obtain ⟨C, hC⟩ := (bures_ball_compact (momentPSD P) eps).bddAbove_image hc.continuousOn
  refine ⟨C, ?_⟩
  intro Q hQ
  rw [risk_eq_matrixRisk]
  apply hC
  apply Set.mem_image_of_mem
  have himage := (w2BuresEquivalence assSingularValueConvention_valid P eps).1
  exact himage ▸ (Set.mem_image_of_mem secondMoment hQ)

-- @node: populationObjective_lt_top
/-- For [any of the four objective indices](hyp:o), [a reference joint law P](hyp:P),
[a nonnegative radius](hyp:eps), and [a coefficient matrix A](hyp:A),
[the population objective at A is finite](goal). -/
lemma populationObjective_lt_top {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) (A : Mat m p) :
    populationObjective o P eps A < ⊤ := by
  obtain ⟨C, hC⟩ := risk_uniformly_bounded_on_lawBall P eps A
  unfold populationObjective
  split_ifs
  · exact ENNReal.ofReal_lt_top
  · apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    exact iSup_le fun Q => iSup_le fun hQ => ENNReal.ofReal_le_ofReal (hC Q hQ)
  · apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    exact iSup_le fun Q => iSup_le fun hQ =>
      ENNReal.ofReal_le_ofReal ((regret_le_risk Q A).trans (hC Q hQ))
  · exact ENNReal.ofReal_lt_top

-- @node: populationObjective_lowerSemicontinuous
/-- For [any of the four objective indices](hyp:o), [a reference joint law P](hyp:P),
and [a nonnegative radius](hyp:eps), [the population objective is lower
semicontinuous as a function of the coefficient matrix](goal). -/
lemma populationObjective_lowerSemicontinuous {p m : ℕ}
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) :
    LowerSemicontinuous (populationObjective o P eps) := by
  unfold populationObjective
  split_ifs
  · exact (ENNReal.continuous_ofReal.comp (risk_continuous_coefficient P)).lowerSemicontinuous
  · apply lowerSemicontinuous_biSup
    intro Q _
    exact (ENNReal.continuous_ofReal.comp (risk_continuous_coefficient Q)).lowerSemicontinuous
  · apply lowerSemicontinuous_biSup
    intro Q _
    exact (ENNReal.continuous_ofReal.comp (regret_continuous_coefficient Q)).lowerSemicontinuous
  · apply Continuous.lowerSemicontinuous
    apply ENNReal.continuous_ofReal.comp
    fun_prop

-- @node: populationObjective_sublevel_closed
/-- For [any of the four objective indices](hyp:o), [a reference joint law P](hyp:P),
[a nonnegative radius](hyp:eps), and [an extended nonnegative threshold c](hyp:c),
[the set of coefficient matrices whose population objective is at most c is closed](goal). -/
lemma populationObjective_sublevel_closed {p m : ℕ}
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) (c : ℝ≥0∞) :
    IsClosed {A : Mat m p | populationObjective o P eps A ≤ c} := by
  exact (populationObjective_lowerSemicontinuous o P eps).isClosed_preimage c

-- @node: populationObjective_sublevel_compact
/-- For [any of the four objective indices](hyp:o), [a reference joint law P](hyp:P),
[a nonnegative radius](hyp:eps), and [an extended nonnegative threshold c](hyp:c),
if [the set of coefficient matrices with population objective at most c is bounded](hyp:hb),
then [that sublevel set is compact](goal). -/
lemma populationObjective_sublevel_compact {p m : ℕ}
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) (c : ℝ≥0∞)
    (hb : Bornology.IsBounded {A : Mat m p | populationObjective o P eps A ≤ c}) :
    IsCompact {A : Mat m p | populationObjective o P eps A ≤ c} := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨populationObjective_sublevel_closed o P eps c, hb⟩

-- @node: population_minimizers_nonempty_of_isBounded
/-- For [any of the four objective indices](hyp:o), [a reference joint law P](hyp:P),
[a nonnegative radius](hyp:eps), and [a reference coefficient matrix](hyp:A₀),
if [the coefficients with objective no greater than that of the reference coefficient
form a bounded set](hyp:hb), then [the population objective has a global minimizer](goal).

Only this one sublevel is needed, without assuming that the objective is finite or
that its supremum over comparison laws is attained. -/
lemma population_minimizers_nonempty_of_isBounded {p m : ℕ}
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) (A₀ : Mat m p)
    (hb : Bornology.IsBounded
      {A : Mat m p | populationObjective o P eps A ≤ populationObjective o P eps A₀}) :
    (populationMinimizers o P eps).Nonempty := by
  obtain ⟨A, hA, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := {A : Mat m p | populationObjective o P eps A ≤ populationObjective o P eps A₀})
    ⟨A₀, show populationObjective o P eps A₀ ≤ populationObjective o P eps A₀ from le_rfl⟩ (populationObjective_sublevel_compact o P eps _ hb)
    ((populationObjective_lowerSemicontinuous o P eps).lowerSemicontinuousOn _)
  refine ⟨A, ?_⟩
  intro B _
  by_cases hB : populationObjective o P eps B ≤ populationObjective o P eps A₀
  · exact hmin hB
  · exact hA.trans (le_of_not_ge hB)

-- @node: lawBall_contains_nondegenerate
/-- For [any reference joint law P](hyp:P) and [a nonnegative Wasserstein radius](hyp:eps),
if [the radius is strictly positive](hyp:heps), then [the ball around P contains
a joint law with positive definite feature second moment](goal). -/
lemma lawBall_contains_nondegenerate {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) (heps : 0 < eps) :
    ∃ Q : NondegenerateLaws p m, Q.carrier.val ∈ lawBall P eps := by
  let S := CFC.sqrt (secondMoment P)
  let t : ℝ := (eps : ℝ) / (2 * (‖(1 : Mat (p + m) (p + m))‖ + 1))
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by exact_mod_cast heps) (by positivity)
  let D : Mat (p + m) (p + m) := t • 1
  have hD : frob D ≤ (eps : ℝ) := by
    rw [frob_eq_matrix_norm, show D = t • (1 : Mat (p + m) (p + m)) from rfl,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (‖(1 : Mat (p + m) (p + m))‖ + 1))).mpr
    apply mul_le_mul_of_nonneg_left _ eps.property
    linarith [norm_nonneg (1 : Mat (p + m) (p + m))]
  have hSD : (S + D).PosDef :=
    Matrix.PosDef.posSemidef_add (CFC.sqrt_nonneg _).posSemidef (Matrix.PosDef.one.smul ht)
  let T := (S + D) * (S + D).transpose
  have hT : T.PosDef := by
    have h := hSD.isUnit.posDef_star_right_conjugate_iff.mpr
      (Matrix.PosDef.one : (1 : Mat (p + m) (p + m)).PosDef)
    simpa only [Matrix.mul_one, star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using h
  have hb : T ∈ secondMoment '' lawBall P eps := by
    rw [(w2BuresEquivalence assSingularValueConvention_valid P eps).1]
    exact ⟨hT.posSemidef,
      ((buresProcrustes ⟨T, hT.posSemidef⟩ (momentPSD P)).2.2.1 eps).mpr ⟨D, hD, rfl⟩⟩
  obtain ⟨Q, hQ, hmoment⟩ := hb
  have hX : (secondMomentX Q).PosDef := by
    rw [secondMomentX, hmoment]
    exact hT.submatrix (Fin.castAdd_injective p m)
  exact ⟨⟨⟨Q, hX⟩⟩, hQ⟩

-- @node: nondegenerate_regret_sublevel_bounded
/-- For [a joint law P with positive definite feature second moment](hyp:P) and
[a real threshold c](hyp:c), [the coefficient matrices with regret under P at most c
form a bounded set](goal). -/
lemma nondegenerate_regret_sublevel_bounded {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) (c : ℝ) :
    Bornology.IsBounded {A : Mat m p | regret A P.carrier.val ≤ c} := by
  let S := CFC.sqrt (secondMoment P.carrier.val)
  let X := (factorBlocks p m S).1
  let C := canonicalCoefficient (secondMoment P.carrier.val)
  let L : Mat m p →ₗ[ℝ] Mat m (p + m) :=
    { toFun := fun A => A * X
      map_add' := fun _ _ => Matrix.add_mul ..
      map_smul' := fun _ _ => Matrix.smul_mul .. }
  have hf : secondMoment P.carrier.val = S * S.transpose := psd_sqrt_factor (momentPSD P.carrier.val)
  have hX : blockX p m (secondMoment P.carrier.val) = X * X.transpose := by
    rw [hf]
    exact (factor_gram_blocks S).1
  have hinj : Function.Injective L := by
    intro A B hab
    have hzero : (A - B) * X = 0 := by
      change A * X = B * X at hab
      rw [Matrix.sub_mul, hab, sub_self]
    have hmul : (A - B) * blockX p m (secondMoment P.carrier.val) = 0 := by
      rw [hX, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp P.carrier.property.isUnit
    have hcancel := congrArg (fun M => M * (blockX p m (secondMoment P.carrier.val))⁻¹) hmul
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.zero_mul] at hcancel
    exact sub_eq_zero.mp hcancel
  obtain ⟨K, _, hK⟩ := L.injective_iff_antilipschitz.mp hinj
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨(K : ℝ) * Real.sqrt c + ‖C‖, ?_⟩
  intro A hA
  have hreg : regret A P.carrier.val = ‖L (A - C)‖ ^ 2 := by
    have hg := ((regretProjectionFormula (assPin1_valid m) assSingularValueConvention_valid
      (momentPSD P.carrier.val) S hf).2.2.2.2.2.2 A).2.2
    dsimp only [momentPSD] at hg
    rw [(law_matrix_risk_regret P.carrier.val A).2, hg, frob_eq_matrix_norm]
    rfl
  have hnorm : ‖L (A - C)‖ ≤ Real.sqrt c := by
    apply Real.le_sqrt_of_sq_le
    exact hreg ▸ hA
  have hdist := hK.le_mul_dist (A - C) 0
  simp only [map_zero, dist_zero_right] at hdist
  have hb : ‖A - C‖ ≤ (K : ℝ) * Real.sqrt c :=
    hdist.trans (mul_le_mul_of_nonneg_left hnorm K.property)
  have htri : ‖A‖ ≤ ‖A - C‖ + ‖C‖ := norm_le_norm_sub_add A C
  linarith only [hb, htri]

-- @node: population_robust_sublevel_bounded
/-- For [an objective index](hyp:o) that [selects worst-case risk or worst-case
regret](hyp:ho), [a reference joint law P](hyp:P), [a nonnegative radius](hyp:eps)
that [is strictly positive](hyp:heps), and [a reference coefficient matrix](hyp:A₀),
[the coefficients with population objective no greater than that of the reference
coefficient form a bounded set](goal). -/
lemma population_robust_sublevel_bounded {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (ho : o = 1 ∨ o = 2) (P : JointLaws p m) (eps : ℝ≥0)
    (heps : 0 < eps) (A₀ : Mat m p) :
    Bornology.IsBounded
      {A : Mat m p | populationObjective o P eps A ≤ populationObjective o P eps A₀} := by
  obtain ⟨Q, hQ⟩ := lawBall_contains_nondegenerate P eps heps
  have hfinite := (populationObjective_lt_top o P eps A₀).ne
  apply (nondegenerate_regret_sublevel_bounded Q (populationObjective o P eps A₀).toReal).subset
  intro A hA
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
  apply le_trans _ hA
  rcases ho with rfl | rfl
  · rw [populationObjective, if_neg (by decide : (1 : Fin 4) ≠ 0), if_pos rfl]
    exact le_iSup_of_le Q.carrier.val (le_iSup_of_le hQ
      (ENNReal.ofReal_le_ofReal (regret_le_risk Q.carrier.val A)))
  · rw [populationObjective, if_neg (by decide : (2 : Fin 4) ≠ 0),
      if_neg (by decide : (2 : Fin 4) ≠ 1), if_pos rfl]
    exact le_iSup_of_le Q.carrier.val (le_iSup_of_le hQ le_rfl)

-- @node: population_snr_minimizers_nonempty
/-- For [any joint law P](hyp:P) and [a nonnegative radius](hyp:eps),
[risk under P plus the squared radius times the squared operator norm of the
coefficient matrix has a global minimizer](goal). -/
lemma population_snr_minimizers_nonempty {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (eps : ℝ≥0) : (populationMinimizers 3 P eps).Nonempty := by
  by_cases heps : eps = 0
  · subst eps
    exact ⟨canonicalCoefficient (secondMoment P), canonical_mem_population_zero 3 P⟩
  · have hp : 0 < (eps : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr heps)
    obtain ⟨A, hA⟩ := spectral_penalty_minimum (fun B => risk B P)
      (risk_continuous_coefficient P) (risk_nonneg P) (eps : ℝ) hp
    refine ⟨A, ?_⟩
    intro B _
    change populationObjective 3 P eps A ≤ populationObjective 3 P eps B
    simp only [populationObjective, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, if_false]
    exact ENNReal.ofReal_le_ofReal (hA B)

-- @node: matrix_snr_minimizers_nonempty
/-- For [any positive semidefinite joint second-moment matrix Sigma](hyp:Sigma)
and [a nonnegative radius](hyp:eps), [the matrix risk regularized by the squared
radius times the squared operator norm of the coefficient matrix has a global
minimizer](goal). -/
lemma matrix_snr_minimizers_nonempty {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : PSD (p + m)) (eps : ℝ≥0) : (matrixMinimizers 3 Sigma eps).Nonempty := by
  obtain ⟨P, hP⟩ := psd_law_realization Sigma
  have he : momentPSD P = Sigma := Subtype.ext hP
  have h := population_snr_minimizers_nonempty P eps
  rwa [law_matrix_estimators assSingularValueConvention_valid P eps 3, he] at h

-- @node: population_minimizers_nonempty
/-- For [any of the four objective indices](hyp:o), [any joint law P](hyp:P),
and [a nonnegative radius](hyp:eps), [the corresponding population objective
has a global minimizer](goal). -/
lemma population_minimizers_nonempty {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) : (populationMinimizers o P eps).Nonempty := by
  by_cases ho : o = 0
  · subst o
    exact ⟨canonicalCoefficient (secondMoment P), canonical_mem_population_erm P eps⟩
  · by_cases heps : eps = 0
    · subst eps
      exact ⟨canonicalCoefficient (secondMoment P), canonical_mem_population_zero o P⟩
    · by_cases hsnr : o = 3
      · subst o
        exact population_snr_minimizers_nonempty P eps
      · apply population_minimizers_nonempty_of_isBounded o P eps 0
        have hrob : o = 1 ∨ o = 2 := by omega
        exact population_robust_sublevel_bounded o hrob P eps
          (pos_iff_ne_zero.mpr heps) 0

-- @node: matrix_minimizers_nonempty
/-- For [any of the four objective indices](hyp:o), [any positive semidefinite
joint second-moment matrix Sigma](hyp:Sigma), and [a nonnegative radius](hyp:eps),
[the corresponding matrix objective has a global minimizer](goal). -/
lemma matrix_minimizers_nonempty {p m : ℕ} [NeZero p] [NeZero m]
    (o : Fin 4) (Sigma : PSD (p + m)) (eps : ℝ≥0) :
    (matrixMinimizers o Sigma eps).Nonempty := by
  obtain ⟨P, hP⟩ := psd_law_realization Sigma
  have he : momentPSD P = Sigma := Subtype.ext hP
  have h := population_minimizers_nonempty o P eps
  rwa [law_matrix_estimators assSingularValueConvention_valid P eps o, he] at h

end Papers.WassersteinRegretS2S3
