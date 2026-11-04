module
public import Papers.WassersteinRegretS2S3.Helpers.DROLower
public import Papers.WassersteinRegretS2S3.Helpers.ERMDivergence
public import Papers.WassersteinRegretS2S3.Helpers.RankAdaptive

/-!
# Population Wasserstein regret: T3

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: localRankRate_le_classRate
/-- For a joint law P with positive definite feature second moment and positive feature and
response dimensions, if [kappa is at least one](hyp:hkappa) and
[the condition number of P is at most kappa](hyp:hP), then
[the local effective-rank rate at P is at most the class rate for those dimensions and kappa](goal). -/
lemma localRankRate_le_classRate {p m : ℕ} [NeZero p] [NeZero m]
    (P : NondegenerateLaws p m) (kappa : ℝ) (hkappa : 1 ≤ kappa)
    (hP : conditionNumber P.carrier.val ≤ ENNReal.ofReal kappa) :
    localRankRate P ≤ classRate p m kappa := by
  let k := (conditionNumber P.carrier.val).toReal
  let r := effectiveRank (residualSecondMoment P)
  have hk : k ≤ kappa := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hP
    simpa only [ENNReal.toReal_ofReal (le_trans zero_le_one hkappa)] using h
  have hk1 : 1 ≤ k := by
    have h := (conditionNumberFormula (assPin1_valid m)
      assSingularValueConvention_valid P).2.2.2.2.1
    have hreal := (ENNReal.ofReal_le_iff_le_toReal (conditionNumber_ne_top P)).mp h
    have hsq := sq_nonneg (opNorm (optimalPredictor P))
    have hmax := le_max_left (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val))
    change 1 ≤ (conditionNumber P.carrier.val).toReal
    linarith
  have hr := effectiveRank_bounds
    (⟨residualSecondMoment P, (residual_law_matrix P).2⟩ : PSD m)
  have hr0 : 0 ≤ r := hr.1
  have hrm : r ≤ (m : ℝ) := hr.2.1
  have hmin : min (p : ℝ) r ≤ (min p m : ℕ) := by
    rw [Nat.cast_min]
    exact min_le_min le_rfl hrm
  change Real.sqrt (min (p : ℝ) r) * (k - 1) + Real.sqrt (r * (k - 1)) + k ≤ _
  unfold classRate
  apply add_le_add _ hk
  apply add_le_add
  · exact mul_le_mul (Real.sqrt_le_sqrt hmin) (by linarith)
      (by linarith) (Real.sqrt_nonneg _)
  · exact Real.sqrt_le_sqrt (mul_le_mul hrm (by linarith)
      (by linarith) (Nat.cast_nonneg _))

-- @node: classRate_tall_comparison
/-- With positive response dimension m, if [kappa is at least two](hyp:hkappa) and
[the response dimension m is at most the feature dimension p](hyp:hmp), then
[the class rate lies between one half and three times the product of the square root of m
and kappa](goal). -/
lemma classRate_tall_comparison {p m : ℕ} [NeZero m]
    (kappa : ℝ) (hkappa : 2 ≤ kappa) (hmp : m ≤ p) :
    (1 / 2 : ℝ) * Real.sqrt m * kappa ≤ classRate p m kappa ∧
      classRate p m kappa ≤ 3 * (Real.sqrt m * kappa) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  have hroot : 1 ≤ Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm
  have hsecond : Real.sqrt ((m : ℝ) * (kappa - 1)) ≤ Real.sqrt m * kappa := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hk : kappa - 1 ≤ kappa ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
  rw [classRate, min_eq_right hmp]
  constructor
  · have hfirst : (1 / 2 : ℝ) * Real.sqrt m * kappa ≤ Real.sqrt m * (kappa - 1) := by
      nlinarith [Real.sqrt_nonneg (m : ℝ)]
    exact hfirst.trans (by linarith [Real.sqrt_nonneg ((m : ℝ) * (kappa - 1))])
  · have hfirst : Real.sqrt m * (kappa - 1) ≤ Real.sqrt m * kappa := by
      nlinarith [Real.sqrt_nonneg (m : ℝ)]
    have hk : kappa ≤ Real.sqrt m * kappa := by nlinarith
    linarith

-- @node: thm:pop-limit-risk-bds
/-- [There are positive universal constants c and C such that, in any positive feature and
response dimensions, assuming the Euclidean squared-norm identity and the convention of
nonincreasing nonnegative singular values with the minimum at the smaller dimension,
for every kappa at least one, every positive Wasserstein radius epsilon, and every choice
of population minimizers for ordinary risk (ERM), worst-case risk (DRO), worst-case regret
(MRO), and risk penalized by epsilon squared times the squared operator norm (SNR), the
following bounds hold over laws with positive definite feature second moment and condition
number at most kappa: the class minimax robust regret is between c and C times kappa times
epsilon squared; the class robust regrets of MRO and SNR are each at most C times kappa
times epsilon squared; the class robust regret of ERM is infinite; and the class robust
regret of DRO is between c and C times the class rate times epsilon squared. Moreover,
when kappa is at least two and the response dimension m is at most the feature dimension,
the class robust regret of DRO is between c and C times the square root of m times kappa
times epsilon squared](goal). -/
theorem popLimitRiskBds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ eps : ℝ≥0, 0 < eps → ∀ erm dro mro snr : Estimator p m,
      IsPopulationSelection 0 eps erm → IsPopulationSelection 1 eps dro →
      IsPopulationSelection 2 eps mro → IsPopulationSelection 3 eps snr →
      let G := wellConditionedSet p m kappa -- @realizes \cG(class fixed by)
      ENNReal.ofReal (c * kappa * (eps : ℝ) ^ 2) ≤ classMinimax G eps ∧
      classMinimax G eps ≤ ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) ∧
      classRisk G eps mro ≤ ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) ∧
      classRisk G eps snr ≤ ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) ∧
      classRisk G eps erm = ⊤ ∧
      ENNReal.ofReal (c * classRate p m kappa * (eps : ℝ) ^ 2) ≤ classRisk G eps dro ∧
      classRisk G eps dro ≤ ENNReal.ofReal (C * classRate p m kappa * (eps : ℝ) ^ 2) ∧
      (2 ≤ kappa → m ≤ p →
        ENNReal.ofReal (c * Real.sqrt m * kappa * (eps : ℝ) ^ 2) ≤ classRisk G eps dro ∧
        classRisk G eps dro ≤ ENNReal.ofReal (C * Real.sqrt m * kappa * (eps : ℝ) ^ 2)) := by
  obtain ⟨S, hS, hstability⟩ := stabilityImplications
  obtain ⟨D, hD, hrank⟩ := droRankAdaptive
  obtain ⟨d, hd, hlower⟩ := lemma37
  let c := min 1 (d / 2)
  let C := 3 * (S + D)
  have hc : 0 < c := lt_min zero_lt_one (half_pos hd)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcd2 : c ≤ d / 2 := min_le_right _ _
  have hcd : c ≤ d := hcd2.trans (by linarith)
  have hSC : S ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hC, ?_⟩
  intro p m _ _ hpin hsv kappa hkappa eps heps erm dro mro snr herm hdro hmro hsnr
  dsimp only
  have hk : 0 ≤ kappa := le_trans zero_le_one hkappa
  have he : 0 ≤ (eps : ℝ) := eps.property
  have hrate0 : 0 ≤ classRate p m kappa := by
    unfold classRate
    positivity
  have hcast (T : ℝ) (hT : 0 ≤ T) :
      ENNReal.ofReal T * ENNReal.ofReal kappa * (eps : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (T * kappa * (eps : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hT hk), ENNReal.ofReal_mul hT,
      ENNReal.ofReal_pow he, ENNReal.ofReal_coe_nnreal]
  have hstable : classRisk (wellConditionedSet p m kappa) eps mro ≤
      ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) ∧
      classRisk (wellConditionedSet p m kappa) eps snr ≤
      ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) := by
    have hlocal (P : JointLaws p m) (hP : P ∈ wellConditionedSet p m kappa) :
        robustRegret mro P eps ≤ ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) ∧
        robustRegret snr P eps ≤ ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) := by
      let P' : NondegenerateLaws p m := ⟨⟨P, hP.1⟩⟩
      have hb := hstability p m hpin hsv P' eps heps erm dro mro snr herm hdro hmro hsnr
      have hbound : ENNReal.ofReal S * conditionNumber P * (eps : ℝ≥0∞) ^ 2 ≤
          ENNReal.ofReal (C * kappa * (eps : ℝ) ^ 2) := by
        rw [← hcast C hC.le]
        exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hSC) hP.2) le_rfl
      exact ⟨hb.1.trans hbound, hb.2.1.trans hbound⟩
    exact ⟨iSup₂_le (fun P hP => (hlocal P hP).1),
      iSup₂_le (fun P hP => (hlocal P hP).2)⟩
  have hdroUpper : classRisk (wellConditionedSet p m kappa) eps dro ≤
      ENNReal.ofReal (D * classRate p m kappa * (eps : ℝ) ^ 2) := by
    apply iSup₂_le
    intro P hP
    let P' : NondegenerateLaws p m := ⟨⟨P, hP.1⟩⟩
    have hb := hrank p m hpin hsv P' eps heps dro hdro
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (localRankRate_le_classRate P' kappa hkappa hP.2) hD.le)
      (sq_nonneg _)
  have hdroLower := hlower p m hpin hsv kappa hkappa eps heps dro hdro
  refine ⟨?_, (iInf_le _ mro).trans hstable.1, hstable.1, hstable.2,
    lemma34 hpin hsv eps heps kappa hkappa erm herm, ?_, ?_, ?_⟩
  · apply (ENNReal.ofReal_le_ofReal ?_).trans
      (minimaxLb hpin hsv eps heps kappa hkappa)
    exact mul_le_mul_of_nonneg_right (by nlinarith : c * kappa ≤ kappa) (sq_nonneg _)
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hdroLower
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcd hrate0) (sq_nonneg _)
  · apply hdroUpper.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC hrate0) (sq_nonneg _)
  · intro hk2 hmp
    have htall := classRate_tall_comparison kappa hk2 hmp
    constructor
    · apply (ENNReal.ofReal_le_ofReal ?_).trans hdroLower
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        c * Real.sqrt m * kappa = c * (Real.sqrt m * kappa) := by ring
        _ ≤ (d / 2) * (Real.sqrt m * kappa) :=
          mul_le_mul_of_nonneg_right hcd2 (by positivity)
        _ = d * ((1 / 2 : ℝ) * Real.sqrt m * kappa) := by ring
        _ ≤ d * classRate p m kappa := mul_le_mul_of_nonneg_left htall.1 hd.le
    · apply hdroUpper.trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        D * classRate p m kappa ≤ D * (3 * (Real.sqrt m * kappa)) :=
          mul_le_mul_of_nonneg_left htall.2 hD.le
        _ ≤ C * Real.sqrt m * kappa := by
          have hconst : 3 * D ≤ C := by dsimp [C]; linarith
          nlinarith [mul_le_mul_of_nonneg_right hconst
            (show 0 ≤ Real.sqrt m * kappa by positivity)]
-- @realizes \kappa(real class bound at least one, below absolute constants)

end Papers.WassersteinRegretS2S3
