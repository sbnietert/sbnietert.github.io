module
public import Papers.WassersteinRegretS2S3.Helpers.MinimaxLower
public import Papers.WassersteinRegretS2S3.Helpers.DROScalarA
public import Papers.WassersteinRegretS2S3.Helpers.DROConstruction
public import Papers.WassersteinRegretS2S3.T2
public import Papers.WassersteinRegretS2S3.Helpers.LowerAAssembly

/-!
# Population Wasserstein regret: Helpers/LowerA

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: droLowerA_target_source
/-- If [both feature and response dimensions are at least two](hyp:hq),
[the real condition-number parameter and coefficient scale](hyp:kappa,b)
[satisfy twice the squared scale equal to the condition-number parameter minus one](hyp:hb),
and [a contraction factor](hyp:c) [is positive](hyp:hc) and [at most one](hyp:hc1),
[there exist a centered Gaussian target law and a source law obtained by contracting
its first feature coordinate: the target has identity feature second moment, a rectangular
diagonal regression coefficient with the given scale, diagonal residual second moments
equal to the squared scale on matched coordinates other than the first and zero elsewhere,
and condition number equal to the given parameter; the source lies within Wasserstein
distance one of the target and has the same response second moment](goal). -/
lemma droLowerA_target_source {p m : ℕ} [NeZero p] [NeZero m]
    (hq : 2 ≤ min p m) (kappa b c : ℝ) (hb : 2 * b ^ 2 = kappa - 1)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    let A : Mat m p := fun i j => if i.val = j.val then b else 0
    let E : Mat m m := Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)
    ∃ P tildeP : JointLaws p m,
      secondMomentX P = 1 ∧ canonicalCoefficient (secondMoment P) = A ∧
      matrixResidual (secondMoment P) = E ∧
      lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P) ∧
      conditionNumber P = ENNReal.ofReal kappa ∧
      tildeP = contractFeatureLaw 0 c P ∧ tildeP ∈ lawBall P 1 ∧
      secondMomentY tildeP = secondMomentY P := by
  dsimp only
  let A : Mat m p := fun i j => if i.val = j.val then b else 0
  let E : Mat m m := Matrix.diagonal
    (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)
  have hE : E.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> positivity
  obtain ⟨P, hPX, hPA, hPE, hGaussian⟩ := regression_identity_law A ⟨E, hE⟩
  let tildeP := contractFeatureLaw (0 : Fin p) c P
  have hgram : A * A.transpose + E = Matrix.diagonal
      (fun i : Fin m => if i = 0 then b ^ 2 else
        if i.val < min p m then 2 * b ^ 2 else 0) := by
    rw [show A * A.transpose = _ from rectangular_identity_gram b]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, E]
      by_cases hi : i = 0
      · subst i
        simp [show 0 < p from NeZero.pos p]
      · have he : i.val < min p m ↔ i.val < p := by omega
        simp only [hi, if_false, he]
        split_ifs <;> ring
    · simp [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, E, hij]
  let j1 : Fin m := ⟨1, by omega⟩
  have hj1 : j1 ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    norm_num [j1] at hv
  have hjq : j1.val < min p m := by dsimp [j1]; omega
  have hmax : lambdaMax (A * A.transpose + E) = 2 * b ^ 2 := by
    rw [hgram]
    have hd := lambdaMax_diagonal_of_largest
      (fun i : Fin m => if i = 0 then b ^ 2 else
        if i.val < min p m then 2 * b ^ 2 else 0) j1 (by
          intro i
          simp only [hj1, if_false, hjq, if_true]
          split_ifs <;> nlinarith [sq_nonneg b])
    simpa only [hj1, if_false, hjq, if_true] using hd
  let P' : NondegenerateLaws p m := ⟨⟨P, by rw [hPX]; exact Matrix.PosDef.one⟩⟩
  have hpred : optimalPredictor P' = A := (optimalPredictor_eq_canonical P').trans hPA
  have hres : residualSecondMoment P' = E := (residual_law_matrix P').1.trans hPE
  have hcondition : conditionNumber P = ENNReal.ofReal kappa := by
    have hf :=
      (conditionNumberFormula (assPin1_valid m) assSingularValueConvention_valid P').2.2.2.1
    change conditionNumber P = _ at hf
    rw [hf, hpred, hres]
    change ENNReal.ofReal (1 + lambdaMax (A * A.transpose +
      (lambdaMin (secondMomentX P))⁻¹ • E)) = _
    rw [hPX, lambdaMin_identity, inv_one, one_smul, hmax]
    congr 1
    linarith
  exact ⟨P, tildeP, hPX, hPA, hPE, hGaussian, hcondition, rfl,
    contractFeatureLaw_mem_lawBall 0 c hc.le hc1 P hPX,
    contractFeatureLaw_response_moment 0 c P⟩

-- @node: lem:dro-lb-a
/-- [There is a universal positive constant such that, in every positive feature and
response dimension satisfying the Euclidean norm and singular-value conventions,
every population rule selecting a worst-case prediction-risk minimizer at unit Wasserstein radius
has worst-case robust regret, over laws with any condition-number bound at least one,
at least as large as that constant times the square root of the smaller dimension
times the excess of the condition-number bound over one](goal). -/
lemma droLbA :
    ∃ c : ℝ, 0 < c ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ rule : Estimator p m, IsPopulationSelection 1 1 rule →
      ENNReal.ofReal (c * Real.sqrt (min p m : ℕ) * (kappa - 1)) ≤
        classRisk (wellConditionedSet p m kappa) 1 rule := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro p m _ _ hpin hsv kappa hkappa rule hsel
  by_cases hk : kappa = 1
  · subst kappa
    simp
  by_cases hq : min p m < 65
  · have hminimax := minimaxLb (p := p) (m := m) hpin hsv 1 (by norm_num) kappa hkappa
    have hbound : ENNReal.ofReal kappa ≤ classRisk (wellConditionedSet p m kappa) 1 rule := by
      calc
        ENNReal.ofReal kappa ≤ classMinimax (wellConditionedSet p m kappa) 1 := by
          simpa using hminimax
        _ ≤ classRisk (wellConditionedSet p m kappa) 1 rule := iInf_le _ rule
    apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
    have hq64 : ((min p m : ℕ) : ℝ) ≤ 64 := by exact_mod_cast (show min p m ≤ 64 by omega)
    have hroot : Real.sqrt (min p m : ℕ) ≤ 8 := by
      have hs := Real.sq_sqrt (Nat.cast_nonneg (min p m))
      nlinarith [Real.sqrt_nonneg (min p m : ℕ)]
    have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ kappa - 1 by linarith)
    nlinarith
  have hkgt : 1 < kappa := lt_of_le_of_ne hkappa (Ne.symm hk)
  have hq65 : 65 ≤ min p m := by omega
  obtain ⟨alpha, beta, c, hc, hchalf, hmin, hall, hreg⟩ :=
    droLowerA_scalar_regret (min p m) hq65 kappa hkgt
  let b := Real.sqrt ((kappa - 1) / 2)
  have hb : 2 * b ^ 2 = kappa - 1 := by
    have hb2 := Real.sq_sqrt (show 0 ≤ (kappa - 1) / 2 by linarith)
    dsimp [b]
    linarith
  obtain ⟨P, tildeP, hPX, hPA, hPE, hGaussian, hcondition, hcontract, hsource, hresponse⟩ :=
    droLowerA_target_source (p := p) (m := m) (by omega) kappa b c hb hc (by linarith)
  have htarget : P ∈ wellConditionedSet p m kappa :=
    ⟨by rw [hPX]; exact Matrix.PosDef.one, hcondition.le⟩
  have hobjective (u v : ℝ) :
      populationObjective 1 tildeP 1 (droLowerACoefficient u v) =
        droLowerAObjective (((min p m : ℕ) : ℝ) - 1) b c u v := by
    apply droLowerA_matrix_objective (by omega : 2 ≤ min p m)
    intro i
    rw [hcontract]
    exact droLowerA_contracted_residual P b c u v hPX hPA hPE i
  have hrestricted (u v : ℝ)
      (hminMatrix : droLowerACoefficient u v ∈ populationMinimizers 1 tildeP 1) :
      u = alpha := by
    apply hall (u, v)
    intro w _
    change droLowerAObjective (((min p m : ℕ) : ℝ) - 1) b c u v ≤
      droLowerAObjective (((min p m : ℕ) : ℝ) - 1) b c w.1 w.2
    rw [← hobjective, ← hobjective]
    exact hminMatrix (Set.mem_univ _)
  have hrestrictedRegret (u v : ℝ)
      (hminMatrix : droLowerACoefficient u v ∈ populationMinimizers 1 tildeP 1) :
      (1 / 32 : ℝ) * Real.sqrt (min p m : ℕ) * (kappa - 1) ≤
        regret (droLowerACoefficient u v) P := by
    rw [droLowerA_target_regret P b u v hPX hPA, hrestricted u v hminMatrix]
    have hqreal : (1 : ℝ) ≤ (min p m : ℕ) := by
      exact_mod_cast (show 1 ≤ min p m by omega)
    exact hreg.trans (le_add_of_nonneg_right
      (mul_nonneg (by linarith) (sq_nonneg _)))
  let D := coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c
  let U := momentSymmetryGroup (secondMoment P) D
  have hU : assDroSymmetryCompactGroup U := momentSymmetryGroup_compact _ _
  have hinv : assDroSymmetryInvariantLaws U P tildeP := by
    rw [hcontract]
    exact momentSymmetryGroup_gaussian_invariant P D hGaussian
  have hsym := droSymmetry hpin U hU P tildeP hinv 1 1 (rule tildeP)
    ⟨by norm_num, by norm_num, hsel tildeP⟩
  obtain ⟨u, v, hbar⟩ := droLowerA_momentSymmetryGroup_coefficient
    (by omega : 2 ≤ min p m) P b c hPX hPA hPE _ hsym.2.1
  have hregret : (1 / 32 : ℝ) * Real.sqrt (min p m : ℕ) * (kappa - 1) ≤
      regret (rule tildeP) P := by
    apply le_trans _ hsym.2.2.1
    rw [hbar]
    apply hrestrictedRegret u v
    rw [← hbar]
    exact hsym.1
  calc
    ENNReal.ofReal ((1 / 32 : ℝ) * Real.sqrt (min p m : ℕ) * (kappa - 1)) ≤
        ENNReal.ofReal (regret (rule tildeP) P) := ENNReal.ofReal_le_ofReal hregret
    _ ≤ max (ENNReal.ofReal (regret (rule P) tildeP))
        (ENNReal.ofReal (regret (rule tildeP) P)) := le_max_right _ _
    _ ≤ robustRegret rule P 1 := le_iSup₂_of_le tildeP hsource le_rfl
    _ ≤ classRisk (wellConditionedSet p m kappa) 1 rule :=
      le_iSup₂_of_le P htarget le_rfl

end Papers.WassersteinRegretS2S3
