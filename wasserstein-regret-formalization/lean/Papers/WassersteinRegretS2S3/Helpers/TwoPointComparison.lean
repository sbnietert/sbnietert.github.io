module
public import Papers.WassersteinRegretS2S3.Helpers.FactorRegression
public import Papers.WassersteinRegretS2S3.Helpers.Scalar

/-!
# Two-point bounds for the local minimax comparison

Opposite factor perturbations are admissible comparison moments. Their predictor
separation gives a lower bound uniform over every candidate predictor.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lowerAsymptotic_le_matrixCondition
/-- For [a joint second-moment matrix with positive definite feature block](hyp:Sigma),
[the lower asymptotic minimax coefficient is at most the matrix condition number](goal). -/
lemma lowerAsymptotic_le_matrixCondition {p m : ℕ}
    (Sigma : NondegenerateSecondMoments p m) :
    lowerAsymptoticCoefficient Sigma ≤ matrixCondition Sigma.carrier.val := by
  exact Filter.liminf_le_limsup

-- @node: weighted_two_point_lower
/-- For [a candidate coefficient matrix](hyp:A), [two comparison coefficient
matrices](hyp:B,C), and [a common weighting matrix](hyp:W), [the larger squared
weighted Frobenius error is at least one quarter of the squared weighted
Frobenius separation between the comparison matrices](goal). -/
lemma weighted_two_point_lower {m p q : ℕ} (A B C : Mat m p) (W : Mat p q) :
    (1 / 4 : ℝ) * frob ((B - C) * W) ^ 2 ≤
      max (frob ((A - B) * W) ^ 2) (frob ((A - C) * W) ^ 2) := by
  have hb : BddBelow (Set.range (fun X : Mat m q =>
      max (‖X - B * W‖ ^ 2) (‖X - C * W‖ ^ 2))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨X, rfl⟩
    exact (sq_nonneg _).trans (le_max_left _ _)
  have hi := ciInf_le hb (A * W)
  rw [(elementaryScalarIneqs (V := Mat m q)).2.2 (B * W) (C * W)] at hi
  simpa only [Matrix.sub_mul, frob_eq_matrix_norm] using hi

-- @node: weighted_two_point_minimax
/-- For [two comparison coefficient matrices](hyp:B,C) and [a common weighting
matrix](hyp:W), [the infimum over coefficient matrices of the larger squared
weighted Frobenius error equals one quarter of the squared weighted separation
between the comparison matrices](goal). -/
lemma weighted_two_point_minimax {m p q : ℕ} (B C : Mat m p) (W : Mat p q) :
    (⨅ A : Mat m p, ENNReal.ofReal
      (max (frob ((A - B) * W) ^ 2) (frob ((A - C) * W) ^ 2))) =
      ENNReal.ofReal ((1 / 4 : ℝ) * frob ((B - C) * W) ^ 2) := by
  apply le_antisymm
  · let A := (1 / 2 : ℝ) • (B + C)
    have hB : A - B = (1 / 2 : ℝ) • (C - B) := by dsimp [A]; module
    have hC : A - C = (1 / 2 : ℝ) • (B - C) := by dsimp [A]; module
    apply (iInf_le _ A).trans_eq
    congr 1
    rw [hB, hC]
    simp only [Matrix.smul_mul, frob_eq_matrix_norm, norm_smul, Real.norm_eq_abs,
      Matrix.sub_mul, norm_sub_rev]
    norm_num
    ring
  · exact le_iInf fun A => ENNReal.ofReal_le_ofReal (weighted_two_point_lower A B C W)

-- @node: weighted_frob_sq_psd_comparison
/-- For [a coefficient matrix](hyp:A), [two positive semidefinite weighting
matrices](hyp:X,Y), and [a real scale](hyp:c), if [the second weighting matrix
minus the scaled first is positive semidefinite](hyp:hXY), then [the squared
Frobenius norm weighted by the second square root is at least the scale times
the squared norm weighted by the first square root](goal). -/
lemma weighted_frob_sq_psd_comparison {m p : ℕ} (A : Mat m p)
    (X Y : PSD p) (c : ℝ) (hXY : (Y.val - c • X.val).PosSemidef) :
    c * frob (A * CFC.sqrt X.val) ^ 2 ≤ frob (A * CFC.sqrt Y.val) ^ 2 := by
  have h := (hXY.mul_mul_conjTranspose_same A).trace_nonneg
  have hx := psd_sqrt_factor X
  have hy := psd_sqrt_factor Y
  rw [frob_sq_trace_rows, frob_sq_trace_rows]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt X.val), ← hx,
    ← Matrix.mul_assoc (CFC.sqrt Y.val), ← hy]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_assoc, smul_eq_mul] at h
  linarith

-- @node: matrixMinimax_two_point_lower
/-- For [a reference moment matrix and two comparison moment matrices](hyp:Sigma,T,U)
and [a nonnegative radius](hyp:eps), suppose [the first comparison lies in the
reference Bures ball](hyp:hT) and [the second does too](hyp:hU). For [a real
scale](hyp:c) that [is nonnegative](hyp:hc), if [the first comparison feature
block dominates the scaled reference feature block](hyp:hTX) and [the second
comparison feature block does too](hyp:hUX), then [matrix minimax regret is at
least the scale times one quarter of the squared separation of the two canonical
coefficients, weighted by the reference feature square root](goal). -/
lemma matrixMinimax_two_point_lower {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma T U : PSD (p + m)) (eps : ℝ≥0)
    (hT : T ∈ matrixBall Sigma eps) (hU : U ∈ matrixBall Sigma eps)
    (c : ℝ) (hc : 0 ≤ c)
    (hTX : (blockX p m T.val - c • blockX p m Sigma.val).PosSemidef)
    (hUX : (blockX p m U.val - c • blockX p m Sigma.val).PosSemidef) :
    ENNReal.ofReal (c * ((1 / 4 : ℝ) * frob
      ((canonicalCoefficient T.val - canonicalCoefficient U.val) *
        CFC.sqrt (blockX p m Sigma.val)) ^ 2)) ≤ matrixMinimaxValue Sigma eps := by
  apply le_iInf
  intro A
  have hbound (V : PSD (p + m))
      (hV : (blockX p m V.val - c • blockX p m Sigma.val).PosSemidef) :
      c * frob ((A - canonicalCoefficient V.val) *
        CFC.sqrt (blockX p m Sigma.val)) ^ 2 ≤ matrixRegret A V.val := by
    rw [matrixRegret_feature_sqrt]
    exact weighted_frob_sq_psd_comparison _
      ⟨_, Sigma.property.submatrix (Fin.castAdd m)⟩
      ⟨_, V.property.submatrix (Fin.castAdd m)⟩ c hV
  have ht := hbound T hTX
  have hu := hbound U hUX
  have hl := mul_le_mul_of_nonneg_left
    (weighted_two_point_lower A (canonicalCoefficient T.val)
      (canonicalCoefficient U.val) (CFC.sqrt (blockX p m Sigma.val))) hc
  have hm : c * max
      (frob ((A - canonicalCoefficient T.val) * CFC.sqrt (blockX p m Sigma.val)) ^ 2)
      (frob ((A - canonicalCoefficient U.val) * CFC.sqrt (blockX p m Sigma.val)) ^ 2) ≤
      max (matrixRegret A T.val) (matrixRegret A U.val) := by
    rw [mul_max_of_nonneg _ _ hc]
    exact max_le_max ht hu
  calc
    _ ≤ ENNReal.ofReal (max (matrixRegret A T.val) (matrixRegret A U.val)) :=
      ENNReal.ofReal_le_ofReal (hl.trans hm)
    _ ≤ matrixWorstRegret Sigma eps A := by
      rw [ENNReal.ofReal_max]
      exact max_le (le_iSup_of_le T (le_iSup_of_le hT le_rfl))
        (le_iSup_of_le U (le_iSup_of_le hU le_rfl))

-- @node: opposite_factor_moments_mem_ball
/-- For [a positive semidefinite reference moment matrix](hyp:Sigma), [a factor
direction](hyp:D) with [Frobenius norm at most one](hyp:hD), and [a nonnegative
radius](hyp:eps), [both moments obtained by adding and subtracting the radius
times that direction from the reference square-root factor lie in the reference
Bures ball of that radius](goal). -/
lemma opposite_factor_moments_mem_ball {n : ℕ} (Sigma : PSD n)
    (D : Mat n n) (hD : frob D ≤ 1) (eps : ℝ≥0) :
    factorPerturbedMoment Sigma ((eps : ℝ) • D) ∈ matrixBall Sigma eps ∧
    factorPerturbedMoment Sigma (-((eps : ℝ) • D)) ∈ matrixBall Sigma eps := by
  have hd : frob ((eps : ℝ) • D) ≤ eps := by
    simpa [frob_eq_matrix_norm, norm_smul] using
      mul_le_mul_of_nonneg_left hD eps.property
  constructor
  · exact ((buresProcrustes _ Sigma).2.2.1 eps).mpr ⟨_, hd, rfl⟩
  · apply ((buresProcrustes _ Sigma).2.2.1 eps).mpr
    exact ⟨_, by simpa only [frob_eq_matrix_norm, norm_neg] using hd, rfl⟩

-- @node: opposite_factor_covariance_difference
/-- For [a positive semidefinite reference moment matrix](hyp:Sigma), [a factor
direction](hyp:D), and [a real perturbation size](hyp:t), [the difference between
the moments from the positive and negative factor perturbations equals twice
the perturbation size times the induced moment tangent](goal). -/
lemma opposite_factor_covariance_difference {n : ℕ} (Sigma : PSD n)
    (D : Mat n n) (t : ℝ) :
    (factorPerturbedMoment Sigma (t • D)).val -
      (factorPerturbedMoment Sigma (-(t • D))).val =
        (2 * t) • (factorTangent Sigma D).val := by
  change (CFC.sqrt Sigma.val + t • D) * (CFC.sqrt Sigma.val + t • D).transpose -
    (CFC.sqrt Sigma.val + -(t • D)) * (CFC.sqrt Sigma.val + -(t • D)).transpose = _
  rw [factor_covariance_expansion, factor_covariance_expansion]
  rw [show -(t • D) = (-t) • D by simp, factorTangent_smul, factorTangent_smul]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, neg_mul_neg]
  change Sigma.val + t • (factorTangent Sigma D).val + (t * t) • (D * D.transpose) -
    (Sigma.val + (-t) • (factorTangent Sigma D).val + (t * t) • (D * D.transpose)) = _
  module

-- @node: opposite_factor_parameterMap_uniform_taylor
/-- For [a set of joint moment matrices with positive definite feature blocks](hyp:K)
that [is compact](hyp:hK), and [a positive error tolerance](hyp:he), [there is a
positive factor-perturbation threshold, uniform over the set, such that the
coefficient difference between opposite perturbations differs from twice its
derivative in the induced moment direction by at most twice the tolerance times
the perturbation's Frobenius norm](goal). -/
lemma opposite_factor_parameterMap_uniform_taylor {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ K, ∀ D : Mat (p + m) (p + m), frob D < δ →
      frob (parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
        parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val (-D))) -
        (2 : ℝ) • fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
          (factorTangent S.carrier.val D)) ≤ 2 * e * frob D := by
  obtain ⟨δ, hδ, hb⟩ := factor_parameterMap_uniform_taylor K hK he
  refine ⟨δ, hδ, ?_⟩
  intro S hS D hD
  have hp := hb S hS D hD
  have hn := hb S hS (-D) (by simpa only [frob_eq_matrix_norm, norm_neg] using hD)
  have ht : factorTangent S.carrier.val (-D) = -factorTangent S.carrier.val D := by
    simpa only [neg_one_smul] using factorTangent_smul S.carrier.val (-1) D
  rw [ht, map_neg] at hn
  simp only [frob_eq_matrix_norm, norm_neg] at hp hn ⊢
  have heq : parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
      parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val (-D))) -
      (2 : ℝ) • fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
        (factorTangent S.carrier.val D) =
      (parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
        parameterMap (symOfPSD S.carrier.val) -
        fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
          (factorTangent S.carrier.val D)) -
      (parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val (-D))) -
        parameterMap (symOfPSD S.carrier.val) -
        -fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
          (factorTangent S.carrier.val D)) := by module
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

-- @node: factor_feature_domination_eventually
/-- For [a joint moment matrix with positive definite feature block](hyp:S),
if [a real scale is less than one](hyp:hc), then [every sufficiently small factor
perturbation has a feature block whose difference from the scaled reference
feature block is positive definite](goal). -/
lemma factor_feature_domination_eventually {p m : ℕ}
    (S : NondegenerateSecondMoments p m) {c : ℝ} (hc : c < 1) :
    ∀ᶠ D : Mat (p + m) (p + m) in nhds 0,
      (blockX p m (factorPerturbedMoment S.carrier.val D).val -
        c • blockX p m S.carrier.val.val).PosDef := by
  let f : Mat (p + m) (p + m) → Sym p := fun D =>
    ⟨blockX p m (factorPerturbedMoment S.carrier.val D).val -
      c • blockX p m S.carrier.val.val,
      (psd_selfAdjoint (⟨_, (factorPerturbedMoment S.carrier.val D).property.submatrix
        (Fin.castAdd m)⟩ : PSD p)).sub
        (IsSelfAdjoint.smul (by exact rfl) (psd_selfAdjoint
          (⟨_, S.carrier.val.property.submatrix (Fin.castAdd m)⟩ : PSD p)))⟩
  have hf : Continuous f := by
    unfold f factorPerturbedMoment blockX
    fun_prop
  have hz : (f 0).val = (1 - c) • blockX p m S.carrier.val.val := by
    dsimp [f, factorPerturbedMoment]
    rw [add_zero, ← psd_sqrt_factor]
    module
  have hpos : (f 0).val.PosDef := by
    rw [hz]
    exact S.carrier.property.smul (sub_pos.mpr hc)
  exact hf.continuousAt.eventually ((sym_posDef_isOpen p).mem_nhds hpos)

-- @node: opposite_factor_feature_domination
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D), if [a real scale is less than one](hyp:hc), then
[at all sufficiently small positive radii, both opposite factor perturbations
have feature blocks dominating the scaled reference feature block in the
positive semidefinite order](goal). -/
lemma opposite_factor_feature_domination {p m : ℕ}
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m))
    {c : ℝ} (hc : c < 1) :
    ∀ᶠ eps : ℝ≥0 in positiveRadii,
      (blockX p m (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D)).val -
        c • blockX p m S.carrier.val.val).PosSemidef ∧
      (blockX p m (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D))).val -
        c • blockX p m S.carrier.val.val).PosSemidef := by
  have hr : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ) • D)
      positiveRadii (nhds 0) := by simpa using hr.smul_const D
  have hn : Filter.Tendsto (fun eps : ℝ≥0 => -((eps : ℝ) • D))
      positiveRadii (nhds 0) := by simpa using ht.neg
  filter_upwards [ht.eventually (factor_feature_domination_eventually S hc),
    hn.eventually (factor_feature_domination_eventually S hc)] with eps hp hn
  exact ⟨hp.posSemidef, hn.posSemidef⟩

-- @node: opposite_factor_matrixMinimax_lower_eventually
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D) with [Frobenius norm at most one](hyp:hD), take a scale
that [is nonnegative](hyp:hc) and [less than one](hyp:hc1). Then [at all sufficiently
small positive radii, matrix minimax regret is at least that scale times one
quarter of the squared separation of the canonical coefficients at opposite
factor perturbations, weighted by the reference feature square root](goal). -/
lemma opposite_factor_matrixMinimax_lower_eventually {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m))
    (hD : frob D ≤ 1) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ∀ᶠ eps : ℝ≥0 in positiveRadii,
      ENNReal.ofReal (c * ((1 / 4 : ℝ) * frob
        ((canonicalCoefficient (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D)).val -
          canonicalCoefficient (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D))).val) *
            CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2)) ≤
        matrixMinimaxValue S.carrier.val eps := by
  filter_upwards [opposite_factor_feature_domination S D hc1] with eps heps
  have hb := opposite_factor_moments_mem_ball S.carrier.val D hD eps
  exact matrixMinimax_two_point_lower S.carrier.val _ _ eps hb.1 hb.2 c hc heps.1 heps.2

-- @node: opposite_factor_parameterMap_normalized_tendsto
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D), [the regression parameter difference at opposite
factor perturbations, divided by twice the radius, converges as the radius
decreases to zero to the parameter derivative in the induced moment direction](goal). -/
lemma opposite_factor_parameterMap_normalized_tendsto {p m : ℕ}
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m)) :
    Filter.Tendsto (fun eps : ℝ≥0 => (2 * (eps : ℝ))⁻¹ •
      (parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D))) -
        parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D))))))
      positiveRadii (nhds (fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
        (factorTangent S.carrier.val D))) := by
  have hr : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ) • D)
      positiveRadii (nhds 0) := by simpa using hr.smul_const D
  have hnorm : Filter.Tendsto (fun eps : ℝ≥0 => frob ((eps : ℝ) • D))
      positiveRadii (nhds 0) := by
    simpa [frob_eq_matrix_norm] using ht.norm
  apply Metric.tendsto_nhds.mpr
  intro e he
  have hnD := frob_nonneg D
  let a := e / (2 * (frob D + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ, hδ, hb⟩ := opposite_factor_parameterMap_uniform_taylor
    {S} isCompact_singleton ha
  have hp : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  filter_upwards [hp, hnorm.eventually (eventually_lt_nhds hδ)] with eps heps hd
  have hrpos : 0 < (eps : ℝ) := by exact_mod_cast heps
  have htaylor := hb S (Set.mem_singleton S) ((eps : ℝ) • D) hd
  rw [factorTangent_smul, map_smul, smul_smul] at htaylor
  let L := fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
    (factorTangent S.carrier.val D)
  have hid (B : Mat m p) : (2 * (eps : ℝ))⁻¹ • B - L =
      (2 * (eps : ℝ))⁻¹ • (B - (2 * (eps : ℝ)) • L) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (by positivity : 2 * (eps : ℝ) ≠ 0), one_smul]
  rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * (eps : ℝ)))]
  have hn : frob ((eps : ℝ) • D) = (eps : ℝ) * frob D := by
    simp [frob_eq_matrix_norm, norm_smul, abs_of_pos hrpos]
  have hbnd : ‖parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D))) -
      parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D)))) -
      (2 * (eps : ℝ)) • L‖ ≤ 2 * a * ((eps : ℝ) * frob D) := by
    simpa only [hn, frob_eq_matrix_norm] using htaylor
  calc
    _ ≤ (2 * (eps : ℝ))⁻¹ * (2 * a * ((eps : ℝ) * frob D)) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = a * frob D := by field_simp
    _ < e := by
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (frob D + 1))).mpr
      nlinarith

-- @node: factor_canonical_eq_parameterMap_eventually
/-- For [a joint moment matrix with positive definite feature block](hyp:S),
[the canonical coefficient equals the regression parameter map at every
sufficiently small factor perturbation](goal). -/
lemma factor_canonical_eq_parameterMap_eventually {p m : ℕ}
    (S : NondegenerateSecondMoments p m) :
    ∀ᶠ D : Mat (p + m) (p + m) in nhds 0,
      canonicalCoefficient (factorPerturbedMoment S.carrier.val D).val =
        parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) := by
  filter_upwards [factor_feature_domination_eventually S (c := 0) (by norm_num)] with D hD
  simp only [zero_smul, sub_zero] at hD
  exact canonicalCoefficient_eq_parameterMap _ hD

-- @node: opposite_factor_canonical_normalized_tendsto
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D), [the canonical coefficient difference at opposite
factor perturbations, divided by twice the radius, converges as the radius
decreases to zero to the regression parameter derivative in the induced moment direction](goal). -/
lemma opposite_factor_canonical_normalized_tendsto {p m : ℕ}
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m)) :
    Filter.Tendsto (fun eps : ℝ≥0 => (2 * (eps : ℝ))⁻¹ •
      (canonicalCoefficient (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D)).val -
        canonicalCoefficient (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D))).val))
      positiveRadii (nhds (fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
        (factorTangent S.carrier.val D))) := by
  have hr : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ) • D)
      positiveRadii (nhds 0) := by simpa using hr.smul_const D
  have hn : Filter.Tendsto (fun eps : ℝ≥0 => -((eps : ℝ) • D))
      positiveRadii (nhds 0) := by simpa using ht.neg
  apply (opposite_factor_parameterMap_normalized_tendsto S D).congr'
  filter_upwards [ht.eventually (factor_canonical_eq_parameterMap_eventually S),
    hn.eventually (factor_canonical_eq_parameterMap_eventually S)] with eps hp hn
  rw [hp, hn]

-- @node: opposite_factor_separation_normalized_tendsto
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D), [one quarter of the squared canonical coefficient
separation at opposite factor perturbations, weighted by the reference feature
square root and divided by the squared radius, converges to the derivative
sensitivity as the radius decreases to zero](goal). -/
lemma opposite_factor_separation_normalized_tendsto {p m : ℕ}
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m)) :
    Filter.Tendsto (fun eps : ℝ≥0 => ((1 / 4 : ℝ) * frob
      ((canonicalCoefficient (factorPerturbedMoment S.carrier.val ((eps : ℝ) • D)).val -
        canonicalCoefficient (factorPerturbedMoment S.carrier.val (-((eps : ℝ) • D))).val) *
          CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2) / (eps : ℝ) ^ 2)
      positiveRadii (nhds (derivativeSensitivity S.carrier.val D)) := by
  have ht := opposite_factor_canonical_normalized_tendsto S D
  have hc : Continuous (fun B : Mat m p =>
      ‖B * CFC.sqrt (blockX p m S.carrier.val.val)‖ ^ 2) := by fun_prop
  have hw := hc.continuousAt.tendsto.comp ht
  simp only [← frob_eq_matrix_norm] at hw
  change Filter.Tendsto _ _ (nhds (derivativeSensitivity S.carrier.val D)) at hw
  apply hw.congr'
  have hp : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  filter_upwards [hp] with eps heps
  have hrpos : 0 < (eps : ℝ) := by exact_mod_cast heps
  simp only [Function.comp_apply, Matrix.smul_mul, norm_smul, Real.norm_eq_abs, mul_pow,
    frob_eq_matrix_norm, sq_abs]
  field_simp
  ring

-- @node: scaled_derivativeSensitivity_le_lowerAsymptotic
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D) with [Frobenius norm at most one](hyp:hD), if a scale
[is nonnegative](hyp:hc) and [less than one](hyp:hc1), then [the scale times the
derivative sensitivity is at most the lower asymptotic minimax coefficient](goal). -/
lemma scaled_derivativeSensitivity_le_lowerAsymptotic {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m))
    (hD : frob D ≤ 1) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ENNReal.ofReal (c * derivativeSensitivity S.carrier.val D) ≤
      lowerAsymptoticCoefficient S := by
  have hreal := (opposite_factor_separation_normalized_tendsto S D).const_mul c
  have hconv := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [← hconv.liminf_eq]
  refine Filter.liminf_le_liminf ?_
  have hp : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  filter_upwards [hp, opposite_factor_matrixMinimax_lower_eventually S D hD hc hc1]
    with eps heps hb
  have hrpos : 0 < (eps : ℝ) := by exact_mod_cast heps
  dsimp only [Function.comp_apply]
  rw [← mul_div_assoc, ENNReal.ofReal_div_of_pos (sq_pos_of_pos hrpos)]
  simp only [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow,
    div_eq_mul_inv, ENNReal.inv_pow]
  rw [mul_comm]
  exact mul_le_mul' le_rfl hb

-- @node: derivativeSensitivity_le_lowerAsymptotic
/-- For [a joint moment matrix with positive definite feature block](hyp:S) and
[a factor direction](hyp:D) with [Frobenius norm at most one](hyp:hD), [the derivative
sensitivity is at most the lower asymptotic minimax coefficient](goal). -/
lemma derivativeSensitivity_le_lowerAsymptotic {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) (D : Mat (p + m) (p + m))
    (hD : frob D ≤ 1) :
    ENNReal.ofReal (derivativeSensitivity S.carrier.val D) ≤
      lowerAsymptoticCoefficient S := by
  have hr : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hr).mul_const (derivativeSensitivity S.carrier.val D))
  simp only [sub_zero, one_mul] at ht
  apply le_of_tendsto ht
  have hp : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  filter_upwards [hp, hr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with eps heps hsmall
  have hrpos : 0 < (eps : ℝ) := by exact_mod_cast heps
  exact scaled_derivativeSensitivity_le_lowerAsymptotic S D hD
    (sub_nonneg.mpr hsmall.le) (by linarith)

end Papers.WassersteinRegretS2S3
