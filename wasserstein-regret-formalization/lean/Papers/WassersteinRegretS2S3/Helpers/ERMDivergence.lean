module
public import Papers.WassersteinRegretS2S3.Helpers.MinimaxLower

/-!
# Population Wasserstein regret: Helpers/ERMDivergence

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

/-- If [P has second moment equal to S times its transpose](hyp:hS) and
[T is within Frobenius distance eps of S](hyp:hST), for [nonnegative radius
eps](hyp:eps), [there is a law Q within Wasserstein distance eps of P whose
second moment is T times its transpose](goal). -/
-- @node: rectangular_factor_comparison_law
lemma rectangular_factor_comparison_law {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (S T : Mat (p + m) p)
    (hS : secondMoment P = S * S.transpose) (eps : ℝ≥0)
    (hST : frob (T - S) ≤ eps) :
    ∃ Q ∈ lawBall P eps, secondMoment Q = T * T.transpose := by
  let pad (F : Mat (p + m) p) : Mat (p + m) (p + m) :=
    fun i j => Fin.addCases (F i) (fun _ => 0) j
  have hgram (F : Mat (p + m) p) : pad F * (pad F).transpose = F * F.transpose := by
    ext i j
    change (∑ k, pad F i k * pad F j k) = ∑ k, F i k * F j k
    simp [pad, Fin.sum_univ_add]
  have hnorm : frob (pad T - pad S) = frob (T - S) := by
    apply (sq_eq_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
    simp only [frob_sq]
    change (∑ i, ∑ j, (pad T i j - pad S i j) ^ 2) = _
    simp [pad, Fin.sum_univ_add]
  have hT : (T * T.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose T
  have hdist : buresDistance (T * T.transpose) (secondMoment P) ≤ eps := by
    apply ((buresProcrustes ⟨_, hT⟩ (momentPSD P)).2.1.2
      ⟨pad T, pad S, (hgram T).symm, hS.trans (hgram S).symm, rfl⟩).trans
    exact hnorm.trans_le hST
  have hmem : T * T.transpose ∈ secondMoment '' lawBall P eps := by
    rw [(w2BuresEquivalence assSingularValueConvention_valid P eps).1]
    exact ⟨hT, hdist⟩
  exact hmem

/-- If [Q has second moment equal to T times its transpose](hyp:hT),
[B maps the feature block of T exactly to its response block](hyp:hB), and
[A is a population ERM minimizer for Q at radius eps](hyp:hA), with
[nonnegative radius eps](hyp:eps), then [A also maps the feature block of T
exactly to its response block](goal). -/
-- @node: erm_interpolates_factor
lemma erm_interpolates_factor {p m r : ℕ} (Q : JointLaws p m)
    (T : Mat (p + m) r) (hT : secondMoment Q = T * T.transpose)
    (B A : Mat m p) (hB : B * (factorBlocks p m T).1 = (factorBlocks p m T).2)
    (eps : ℝ≥0) (hA : A ∈ populationMinimizers 0 Q eps) :
    A * (factorBlocks p m T).1 = (factorBlocks p m T).2 := by
  have hzero : risk B Q = 0 := by
    rw [risk_eq_matrixRisk, hT, matrixRisk_gram_factor, hB, sub_self]
    simp [frob]
  have hle := hA (Set.mem_univ B)
  change populationObjective 0 Q eps A ≤ populationObjective 0 Q eps B at hle
  simp only [populationObjective, ite_true, hzero, ENNReal.ofReal_zero] at hle
  have hz : risk A Q = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp hle))
    (risk_nonneg Q A)
  rw [risk_eq_matrixRisk, hT, matrixRisk_gram_factor] at hz
  exact sub_eq_zero.mp ((frob_eq_zero_iff _).mp (sq_eq_zero_iff.mp hz))

/-- If [a is positive](hyp:ha), [P has second moment equal to S times its
transpose](hyp:hS), and [S has feature block a times the identity and zero
response block](hyp:hblocks), then [P has positive definite feature second
moment, condition number one, and regret equal to a squared times the squared
Frobenius norm of the predictor for every predictor](goal). -/
-- @node: noiseless_isotropic_gram
lemma noiseless_isotropic_gram {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (S : Mat (p + m) p) (a : ℝ) (ha : 0 < a)
    (hS : secondMoment P = S * S.transpose)
    (hblocks : factorBlocks p m S = (a • 1, 0)) :
    (secondMomentX P).PosDef ∧ conditionNumber P = 1 ∧
      ∀ A : Mat m p, regret A P = a ^ 2 * frob A ^ 2 := by
  have hx : secondMomentX P = (a ^ 2) • 1 := by
    rw [secondMomentX, hS, (factor_gram_blocks S).1, hblocks]
    simp [Matrix.transpose_smul, smul_smul, pow_two]
  have hpos : (secondMomentX P).PosDef := by
    rw [hx]
    exact Matrix.PosDef.one.smul (sq_pos_of_pos ha)
  have hcanon : canonicalCoefficient (secondMoment P) = 0 := by
    rw [canonicalCoefficient, hS, (factor_gram_blocks S).2.1, hblocks]
    simp
  let P' : NondegenerateLaws p m := ⟨⟨P, hpos⟩⟩
  have hpred : optimalPredictor P' = 0 := (optimalPredictor_eq_canonical P').trans hcanon
  have hzero : quadraticRegressionMatrix (0 : Mat m p) * S = 0 := by
    rw [quadraticRegressionMatrix_factor, hblocks]
    simp
  have hres : residualSecondMoment P' = 0 := by
    rw [(residual_law_matrix P').1, matrixResidual, hcanon, hS,
      ← Matrix.mul_assoc, hzero, Matrix.zero_mul, Matrix.zero_mul]
  have hop : opNorm (0 : Mat m m) = 0 := by
    have he : (fun (i j : Fin m) => if i = 0 ∧ j = 0 then (0 : ℝ) else 0) =
        (0 : Mat m m) := by ext i j; simp
    rw [← he]
    exact opNorm_single_entry 0 (le_refl 0)
  have hlam : lambdaMax (0 : Mat m m) = 0 := by
    simpa [hop] using lambdaMax_gram (0 : Mat m m)
  refine ⟨hpos, ?_, ?_⟩
  · rw [(conditionNumberFormula (assPin1_valid m) assSingularValueConvention_valid P').2.2.2.1,
      hpred, hres]
    simp [hlam]
  · intro A
    rw [(law_matrix_risk_regret P A).2, matrixRegret, hcanon, hS,
      matrixRisk_gram_factor, matrixRisk_gram_factor, hblocks]
    simp [Matrix.mul_smul, frob_eq_matrix_norm, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]

/-- Suppose [a is positive](hyp:ha), [P has second moment equal to S times
its transpose](hyp:hS), and [S has feature block a times the identity and zero
response block](hyp:hblocks). For [nonnegative radius eps](hyp:eps) with
[twice a at most eps](hyp:haeps), if [delta is positive](hyp:hd),
[delta is at most one](hyp:hd1), and [the rule selects population ERM
minimizers at radius eps](hyp:hsel), then [some law Q within Wasserstein
distance eps of P makes the rule's first coefficient equal to the reciprocal
of delta](goal). -/
-- @node: erm_isotropic_perturbation
lemma erm_isotropic_perturbation {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (a : ℝ) (ha : 0 < a)
    (S : Mat (p + m) p) (hS : secondMoment P = S * S.transpose)
    (hblocks : factorBlocks p m S = (a • 1, 0))
    (eps : ℝ≥0) (haeps : 2 * a ≤ eps)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (rule : Estimator p m) (hsel : IsPopulationSelection 0 eps rule) :
    ∃ Q ∈ lawBall P eps, (rule Q) 0 0 = delta⁻¹ := by
  let X : Mat p p := Matrix.diagonal (fun i => if i = 0 then a * delta else a)
  let Y : Mat m p := fun i j => if i = 0 ∧ j = 0 then a else 0
  let T : Mat (p + m) p := fun i j => Fin.addCases (fun k => X k j) (fun k => Y k j) i
  have hTblocks : factorBlocks p m T = (X, Y) := by
    apply Prod.ext <;> ext i j <;> simp [factorBlocks, T, Matrix.submatrix]
  have hdiffblocks : factorBlocks p m (T - S) = (X - a • 1, Y) := by
    have he : factorBlocks p m (T - S) =
        ((factorBlocks p m T).1 - (factorBlocks p m S).1,
         (factorBlocks p m T).2 - (factorBlocks p m S).2) := rfl
    rw [he, hTblocks, hblocks]
    simp
  have hXdiff : X - a • 1 =
      fun (i j : Fin p) => if i = 0 ∧ j = 0 then a * (delta - 1) else 0 := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hij : i = j <;>
      simp [X, Matrix.diagonal_apply, Matrix.one_apply, hi, hij] <;> grind
  have hnormsq : frob (T - S) ^ 2 = (a * (delta - 1)) ^ 2 + a ^ 2 := by
    rw [frob_factorBlocks_sq, hdiffblocks]
    rw [frob_sq, frob_sq]
    simp_rw [hXdiff, Y, ite_pow, zero_pow (by decide : 2 ≠ 0), ite_and]
    simp
  have hdist : frob (T - S) ≤ eps := by
    have hs : (delta - 1) ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
    have hn := frob_nonneg (T - S)
    rw [mul_pow] at hnormsq
    nlinarith [eps.coe_nonneg]
  obtain ⟨Q, hQ, hQT⟩ := rectangular_factor_comparison_law P S T hS eps hdist
  let B : Mat m p := fun i j => if i = 0 ∧ j = 0 then delta⁻¹ else 0
  have hB : B * (factorBlocks p m T).1 = (factorBlocks p m T).2 := by
    rw [hTblocks]
    ext i j
    simp only [X, Matrix.mul_diagonal]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [B, Y, hi, hj, ne_of_gt hd, mul_comm]
  have hinterp := erm_interpolates_factor Q T hQT B (rule Q) hB eps (hsel Q)
  rw [hTblocks] at hinterp
  have he := congrArg (fun M : Mat m p => M 0 0) hinterp
  simp only [X, Matrix.mul_diagonal, Y, ite_true, and_self, eq_self] at he
  refine ⟨Q, hQ, ?_⟩
  apply (mul_right_cancel₀ (ne_of_gt (mul_pos ha hd)))
  calc
    (rule Q) 0 0 * (a * delta) = a := he
    _ = delta⁻¹ * (a * delta) := by field_simp

-- @node: entry_sq_le_frob_sq
/-- [The square of any entry of A is at most its squared Frobenius norm](goal). -/
lemma entry_sq_le_frob_sq {p m : ℕ} (A : Mat m p) (i : Fin m) (j : Fin p) :
    (A i j) ^ 2 ≤ frob A ^ 2 := by
  rw [frob_sq]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l))) (Finset.mem_univ i))

-- @node: lem:lemma-34
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps)
with [eps positive](hyp:heps) and [condition-number cap kappa at least one](hyp:hkappa),
if [the rule selects population ERM minimizers at radius eps](hyp:hsel), then
[its worst-case regret over laws with condition number at most kappa is infinite](goal). -/
lemma lemma34 {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (eps : ℝ≥0) (heps : 0 < eps)
    (kappa : ℝ) (hkappa : 1 ≤ kappa) (rule : Estimator p m) (hsel : IsPopulationSelection 0 eps
      rule) :
    classRisk (wellConditionedSet p m kappa) eps rule = ⊤ := by
  let a : ℝ := (eps : ℝ) / 2
  have ha : 0 < a := half_pos (show 0 < (eps : ℝ) from heps)
  let S : Mat (p + m) p := fun i j =>
    Fin.addCases (fun k => (a • (1 : Mat p p)) k j) (fun _ => 0) i
  have hblocks : factorBlocks p m S = (a • 1, 0) := by
    apply Prod.ext <;> ext i j <;> simp [factorBlocks, S, Matrix.submatrix]
  obtain ⟨P, hP⟩ := psd_law_realization
    ⟨S * S.transpose, by simpa using Matrix.posSemidef_self_mul_conjTranspose S⟩
  obtain ⟨hpos, hcond, hregret⟩ := noiseless_isotropic_gram P S a ha hP hblocks
  have hclass : P ∈ wellConditionedSet p m kappa := by
    refine ⟨hpos, ?_⟩
    rw [hcond]
    exact_mod_cast (ENNReal.ofReal_le_ofReal hkappa)
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  let D : ℝ := a + Real.sqrt (r : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let delta : ℝ := a / D
  have hd : 0 < delta := div_pos ha hD
  have hd1 : delta ≤ 1 := by
    apply (div_le_one hD).mpr
    dsimp [D]
    linarith [Real.sqrt_nonneg (r : ℝ)]
  obtain ⟨Q, hQ, hentry⟩ := erm_isotropic_perturbation P a ha S hP hblocks eps
    (by dsimp [a]; linarith) delta hd hd1 rule hsel
  have heq : a * delta⁻¹ = D := by
    dsimp [delta]
    field_simp
  have hr : (r : ℝ) ≤ a ^ 2 * (delta⁻¹) ^ 2 := by
    rw [← mul_pow, heq]
    have hs := Real.sq_sqrt r.coe_nonneg
    have hn := Real.sqrt_nonneg (r : ℝ)
    dsimp [D]
    nlinarith
  have htarget : a ^ 2 * (delta⁻¹) ^ 2 ≤ regret (rule Q) P := by
    rw [hregret]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    rw [← hentry]
    exact entry_sq_le_frob_sq (rule Q) 0 0
  calc
    (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
    _ ≤ ENNReal.ofReal (regret (rule Q) P) := ENNReal.ofReal_le_ofReal (hr.trans htarget)
    _ ≤ classRisk (wellConditionedSet p m kappa) eps rule :=
      le_iSup_of_le P (le_iSup_of_le hclass
        (le_iSup_of_le Q (le_iSup_of_le hQ (le_max_right _ _))))

end Papers.WassersteinRegretS2S3
