module
public import Papers.WassersteinRegretS2S3.Helpers.PerturbedCondition
public import Papers.WassersteinRegretS2S3.Helpers.DROMinimax

/-!
# Population Wasserstein regret: Helpers/EstimatorBounds

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: population_erm_eq_optimal
/-- For [nonnegative radius eps](hyp:eps), if [A is a population ERM minimizer for the nondegenerate law P at radius
eps](hyp:hA), then [A equals P's optimal linear predictor](goal). -/
lemma population_erm_eq_optimal {p m : ℕ} (P : NondegenerateLaws p m)
    (eps : ℝ≥0) (A : Mat m p) (hA : A ∈ populationMinimizers 0 P.carrier.val eps) :
    A = optimalPredictor P := by
  apply (optimalPredictor_unique_minimizer P).2 A
  intro B _
  change risk A P.carrier.val ≤ risk B P.carrier.val
  rw [(population_erm_iff_risk_eq_canonical P.carrier.val eps A).mp hA]
  exact canonical_risk_minimal P.carrier.val B

-- @node: law_conditionNumber_small_radius
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius r](hyp:r), if [r is at most half the square
root of the smallest feature second-moment eigenvalue of P](hyp:hr) and
[Q is within Wasserstein distance r of P](hyp:hQ), then [Q's condition number
is at most nineteen times P's condition number](goal). -/
lemma law_conditionNumber_small_radius {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (r : ℝ≥0)
    (hr : (r : ℝ) ≤ Real.sqrt (lambdaMin (secondMomentX P.carrier.val)) / 2)
    (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val r) :
    conditionNumber Q ≤ 19 * conditionNumber P.carrier.val := by
  let S : NondegenerateSecondMoments p m := ⟨⟨momentPSD P.carrier.val, P.carrier.property⟩⟩
  have hd : assPerturbedConditionNumberRadius S (momentPSD Q) := by
    change buresDistance (secondMoment Q) (secondMoment P.carrier.val) ≤ _
    have hw : wassersteinDistance Q P.carrier.val ≤ r := by
      rw [wasserstein_symm]
      exact hQ
    exact (bures_le_wasserstein Q P.carrier.val).trans (hw.trans hr)
  have hb := perturbedConditionNumber hpin hsv S (momentPSD Q) hd
  let T : NondegenerateLaws p m := ⟨⟨Q, hb.1⟩⟩
  rw [conditionNumber_matrix P]
  exact (conditionNumber_matrix T).trans_le hb.2

-- @node: lem:stability-implications-erm
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps)
with [eps positive](hyp:heps), if [the rule selects population ERM minimizers
at radius eps](hyp:hsel), then [its robust regret around P is at most four
times eps squared times the largest condition number in the radius-eps law
ball; when eps squared is at most one quarter of P's smallest feature
second-moment eigenvalue, it is also at most seventy-six times P's condition
number times eps squared](goal). -/
lemma stabilityImplicationsErm {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : JointLaws p m)
    (eps : ℝ≥0) (heps : 0 < eps) (rule : Estimator p m) (hsel : IsPopulationSelection 0 eps rule) :
    robustRegret rule P eps ≤ 4 * (eps : ℝ≥0∞) ^ 2 * (⨆ Q ∈ lawBall P eps, conditionNumber Q) ∧
    (assStabilityImplicationsErmSmallRadius P eps →
      robustRegret rule P eps ≤ 76 * conditionNumber P * (eps : ℝ≥0∞) ^ 2) := by
  classical
  have hself : P ∈ lawBall P eps := by simp [lawBall, wasserstein_self]
  have hmain : robustRegret rule P eps ≤
      4 * (eps : ℝ≥0∞) ^ 2 * (⨆ Q ∈ lawBall P eps, conditionNumber Q) := by
    by_cases hdeg : ∀ Q ∈ lawBall P eps, (secondMomentX Q).PosDef
    · let P' : NondegenerateLaws p m := ⟨⟨P, hdeg P hself⟩⟩
      have hp : rule P = optimalPredictor P' := population_erm_eq_optimal P' eps _ (hsel P)
      apply iSup₂_le
      intro Q hQ
      let Q' : NondegenerateLaws p m := ⟨⟨Q, hdeg Q hQ⟩⟩
      have hq : rule Q = optimalPredictor Q' := population_erm_eq_optimal Q' eps _ (hsel Q)
      have hd : ENNReal.ofReal (wassersteinDistance P Q) ^ 2 ≤ (eps : ℝ≥0∞) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact (ENNReal.ofReal_le_ofReal hQ).trans_eq (by simp)
      have hd' : ENNReal.ofReal (wassersteinDistance Q P) ^ 2 ≤ (eps : ℝ≥0∞) ^ 2 := by
        simpa only [wasserstein_symm Q P] using hd
      apply max_le
      · rw [hp]
        apply (regretStability hpin hsv (optimalPredictor P') P' Q).2.trans
        calc
          _ ≤ 4 * conditionNumber P * (eps : ℝ≥0∞) ^ 2 := mul_le_mul' le_rfl hd
          _ = 4 * (eps : ℝ≥0∞) ^ 2 * conditionNumber P := by ac_rfl
          _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂_of_le P hself le_rfl)
      · rw [hq]
        apply (regretStability hpin hsv (optimalPredictor Q') Q' P).2.trans
        calc
          _ ≤ 4 * conditionNumber Q * (eps : ℝ≥0∞) ^ 2 := mul_le_mul' le_rfl hd'
          _ = 4 * (eps : ℝ≥0∞) ^ 2 * conditionNumber Q := by ac_rfl
          _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂_of_le Q hQ le_rfl)
    · push Not at hdeg
      obtain ⟨Q, hQ, hsing⟩ := hdeg
      have ht : (⨆ Q ∈ lawBall P eps, conditionNumber Q) = ⊤ := by
        apply top_unique
        exact le_iSup₂_of_le Q hQ (by simp [conditionNumber, hsing])
      rw [ht, ENNReal.mul_top (by positivity)]
      exact le_top
  refine ⟨hmain, ?_⟩
  intro hr
  have he : (0 : ℝ) < eps := by exact_mod_cast heps
  have hl : 0 < lambdaMin (secondMomentX P) := by
    change (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 4 at hr
    nlinarith [sq_pos_of_pos he]
  let P' : NondegenerateLaws p m := ⟨⟨P, posDef_of_lambdaMin_pos _
    (secondMoment_posSemidef P |>.submatrix (Fin.castAdd m)).isHermitian hl⟩⟩
  have hr' : (eps : ℝ) ≤ Real.sqrt (lambdaMin (secondMomentX P)) / 2 := by
    have hs := Real.sq_sqrt hl.le
    have hn := Real.sqrt_nonneg (lambdaMin (secondMomentX P))
    change (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 4 at hr
    nlinarith
  apply hmain.trans
  calc
    _ ≤ 4 * (eps : ℝ≥0∞) ^ 2 * (19 * conditionNumber P) := by
      apply mul_le_mul' le_rfl
      exact iSup₂_le fun Q hQ => law_conditionNumber_small_radius hpin hsv P' eps hr' Q hQ
    _ = 76 * conditionNumber P * (eps : ℝ≥0∞) ^ 2 := by ring

-- @node: population_dro_least_favorable
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps), if [S is within Wasserstein distance
eps of the nondegenerate law P](hyp:hS) and [A is a population DRO minimizer
at S with radius eps](hyp:hA), then [there is a law T within Wasserstein
distance eps of S for which A globally minimizes prediction risk](goal). -/
lemma population_dro_least_favorable {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (S : JointLaws p m) (eps : ℝ≥0)
    (hS : S ∈ lawBall P.carrier.val eps) (A : Mat m p)
    (hA : A ∈ populationMinimizers 1 S eps) :
    ∃ T ∈ lawBall S eps, IsMinOn (fun B => risk B T) Set.univ A := by
  obtain ⟨T, hT, heq, _⟩ := droMinimax hpin hsv eps P S hS
  have hmin : (⨆ Q ∈ lawBall S eps, ENNReal.ofReal (risk A Q)) =
      ⨅ B : Mat m p, ⨆ Q ∈ lawBall S eps, ENNReal.ofReal (risk B Q) := by
    apply le_antisymm
    · apply le_iInf
      intro B
      exact hA (Set.mem_univ B)
    · exact iInf_le _ A
  refine ⟨T, hT, ?_⟩
  intro B _
  apply (ENNReal.ofReal_le_ofReal_iff (risk_nonneg T B)).mp
  calc
    ENNReal.ofReal (risk A T) ≤ ⨆ Q ∈ lawBall S eps,
        ENNReal.ofReal (risk A Q) := le_iSup₂_of_le T hT le_rfl
    _ = ⨅ B : Mat m p, ENNReal.ofReal (risk B T) := hmin.trans heq
    _ ≤ ENNReal.ofReal (risk B T) := iInf_le _ B

-- @node: population_dro_pair_stability
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps), suppose [every law within twice eps
of P has positive definite feature second moment](hyp:hdeg), [S is within
eps of P](hyp:hS), and [T is within eps of S](hyp:hT), in Wasserstein distance.
If [A is a population DRO minimizer at S with radius eps](hyp:hA), then
[its regret at T is at most sixteen times eps squared times the largest
condition number in the radius-twice-eps law ball around P](goal). -/
lemma population_dro_pair_stability {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (eps : ℝ≥0)
    (hdeg : ∀ Q ∈ lawBall P.carrier.val (2 * eps), (secondMomentX Q).PosDef)
    (S T : JointLaws p m) (hS : S ∈ lawBall P.carrier.val eps)
    (hT : T ∈ lawBall S eps) (A : Mat m p)
    (hA : A ∈ populationMinimizers 1 S eps) :
    ENNReal.ofReal (regret A T) ≤ 16 * (eps : ℝ≥0∞) ^ 2 *
      (⨆ Q ∈ lawBall P.carrier.val (2 * eps), conditionNumber Q) := by
  obtain ⟨U, hU, hmin⟩ := population_dro_least_favorable hpin hsv P S eps hS A hA
  have hUP : U ∈ lawBall P.carrier.val (2 * eps) := by
    have ht := wasserstein_triangle P.carrier.val S U
    change wassersteinDistance P.carrier.val U ≤ _
    change wassersteinDistance P.carrier.val S ≤ _ at hS
    change wassersteinDistance S U ≤ _ at hU
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  let U' : NondegenerateLaws p m := ⟨⟨U, hdeg U hUP⟩⟩
  have hAU : A = optimalPredictor U' := (optimalPredictor_unique_minimizer U').2 A hmin
  have hd : wassersteinDistance U T ≤ (2 * eps : ℝ≥0) := by
    have ht := wasserstein_triangle U S T
    rw [wasserstein_symm U S] at ht
    change wassersteinDistance S U ≤ _ at hU
    change wassersteinDistance S T ≤ _ at hT
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  have hd' : ENNReal.ofReal (wassersteinDistance U T) ^ 2 ≤
      (2 * (eps : ℝ≥0∞)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa using ENNReal.ofReal_le_ofReal hd
  rw [hAU]
  apply (regretStability hpin hsv (optimalPredictor U') U' T).2.trans
  calc
    _ ≤ 4 * conditionNumber U * (2 * (eps : ℝ≥0∞)) ^ 2 := mul_le_mul' le_rfl hd'
    _ = 16 * (eps : ℝ≥0∞) ^ 2 * conditionNumber U := by ring
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂_of_le U hUP le_rfl)

-- @node: lem:stability-implications-dro
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps)
with [eps positive](hyp:heps), if [the rule selects population DRO minimizers
at radius eps](hyp:hsel), then [its robust regret around P is at most sixteen
times eps squared times the largest condition number within twice eps of P;
when eps squared is at most one sixteenth of P's smallest feature second-moment
eigenvalue, it is also at most 304 times P's condition number times eps squared](goal). -/
lemma stabilityImplicationsDro {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : JointLaws p m)
    (eps : ℝ≥0) (heps : 0 < eps) (rule : Estimator p m) (hsel : IsPopulationSelection 1 eps rule) :
    robustRegret rule P eps ≤ 16 * (eps : ℝ≥0∞) ^ 2 * (⨆ Q ∈ lawBall P (2 * eps),
      conditionNumber Q) ∧
    (assStabilityImplicationsDroSmallRadius P eps →
      robustRegret rule P eps ≤ 304 * conditionNumber P * (eps : ℝ≥0∞) ^ 2) := by
  classical
  have hself : P ∈ lawBall P eps := by simp [lawBall, wasserstein_self]
  have hself2 : P ∈ lawBall P (2 * eps) := by simp [lawBall, wasserstein_self]
  have hmain : robustRegret rule P eps ≤ 16 * (eps : ℝ≥0∞) ^ 2 *
      (⨆ Q ∈ lawBall P (2 * eps), conditionNumber Q) := by
    by_cases hdeg : ∀ Q ∈ lawBall P (2 * eps), (secondMomentX Q).PosDef
    · let P' : NondegenerateLaws p m := ⟨⟨P, hdeg P hself2⟩⟩
      apply iSup₂_le
      intro Q hQ
      apply max_le
      · exact population_dro_pair_stability hpin hsv P' eps hdeg P Q hself hQ _ (hsel P)
      · have hQP : P ∈ lawBall Q eps := by
          change wassersteinDistance Q P ≤ eps
          rw [wasserstein_symm]
          exact hQ
        exact population_dro_pair_stability hpin hsv P' eps hdeg Q P hQ hQP _ (hsel Q)
    · push Not at hdeg
      obtain ⟨Q, hQ, hsing⟩ := hdeg
      have ht : (⨆ Q ∈ lawBall P (2 * eps), conditionNumber Q) = ⊤ := by
        apply top_unique
        exact le_iSup₂_of_le Q hQ (by simp [conditionNumber, hsing])
      rw [ht, ENNReal.mul_top (by positivity)]
      exact le_top
  refine ⟨hmain, ?_⟩
  intro hr
  have he : (0 : ℝ) < eps := by exact_mod_cast heps
  have hl : 0 < lambdaMin (secondMomentX P) := by
    change (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 16 at hr
    nlinarith [sq_pos_of_pos he]
  let P' : NondegenerateLaws p m := ⟨⟨P, posDef_of_lambdaMin_pos _
    (secondMoment_posSemidef P |>.submatrix (Fin.castAdd m)).isHermitian hl⟩⟩
  have hr' : (2 * eps : ℝ≥0) ≤ Real.sqrt (lambdaMin (secondMomentX P)) / 2 := by
    have hs := Real.sq_sqrt hl.le
    have hn := Real.sqrt_nonneg (lambdaMin (secondMomentX P))
    change (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 16 at hr
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith
  apply hmain.trans
  calc
    _ ≤ 16 * (eps : ℝ≥0∞) ^ 2 * (19 * conditionNumber P) := by
      apply mul_le_mul' le_rfl
      exact iSup₂_le fun Q hQ => law_conditionNumber_small_radius hpin hsv P' (2 * eps) hr' Q hQ
    _ = 304 * conditionNumber P * (eps : ℝ≥0∞) ^ 2 := by ring

-- @node: reference_predictor_norm_le_condition
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), [the squared operator norm of the
optimal predictor for the nondegenerate law P is at most P's condition number](goal). -/
lemma reference_predictor_norm_le_condition {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m) :
    opNorm (optimalPredictor P) ^ 2 ≤ (conditionNumber P.carrier.val).toReal := by
  have hf := conditionNumberFormula hpin hsv P
  have hl := (ENNReal.ofReal_le_iff_le_toReal hf.1).mp hf.2.2.2.2.1
  have hm := le_max_left (opNorm (optimalPredictor P) ^ 2)
    (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val))
  linarith

-- @node: reference_regret_on_ball
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius r](hyp:r), if [Q is within Wasserstein distance
r of the nondegenerate law P](hyp:hQ), then [P's optimal predictor has regret
at Q at most four times P's condition number times r squared](goal). -/
lemma reference_regret_on_ball {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m)
    (r : ℝ≥0) (Q : JointLaws p m) (hQ : Q ∈ lawBall P.carrier.val r) :
    regret (optimalPredictor P) Q ≤ 4 * (conditionNumber P.carrier.val).toReal * (r : ℝ) ^ 2 := by
  have hb := (regretStability hpin hsv (optimalPredictor P) P Q).2
  have hk := ENNReal.toReal_nonneg (a := conditionNumber P.carrier.val)
  have heq : 4 * conditionNumber P.carrier.val *
      ENNReal.ofReal (wassersteinDistance P.carrier.val Q) ^ 2 =
      ENNReal.ofReal (4 * (conditionNumber P.carrier.val).toReal *
        wassersteinDistance P.carrier.val Q ^ 2) := by
    simp only [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hk),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_toReal (conditionNumber_ne_top P),
      ENNReal.ofReal_pow (wasserstein_nonneg _ _), ENNReal.ofReal_ofNat]
  rw [heq] at hb
  exact ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (wasserstein_nonneg _ _) hQ 2)
      (by positivity))

-- @node: population_mro_pair_stability
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps), if [S is within Wasserstein distance
eps of the nondegenerate law P](hyp:hS), [T is within eps of S](hyp:hT), and
[A is a population minimax-regret minimizer at S with radius eps](hyp:hA),
then [A's regret at T is at most sixteen times P's condition number times eps squared](goal). -/
lemma population_mro_pair_stability {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (eps : ℝ≥0)
    (S T : JointLaws p m) (hS : S ∈ lawBall P.carrier.val eps)
    (hT : T ∈ lawBall S eps) (A : Mat m p)
    (hA : A ∈ populationMinimizers 2 S eps) :
    ENNReal.ofReal (regret A T) ≤ 16 * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 := by
  have ho := hA (Set.mem_univ (optimalPredictor P))
  change populationObjective 2 S eps A ≤ populationObjective 2 S eps (optimalPredictor P) at ho
  simp only [populationObjective, show (2 : Fin 4) ≠ 0 by decide,
    show (2 : Fin 4) ≠ 1 by decide, if_false, ite_true] at ho
  apply (le_iSup₂_of_le T hT le_rfl).trans (ho.trans ?_)
  apply iSup₂_le
  intro U hU
  have hd : wassersteinDistance P.carrier.val U ≤ (2 * eps : ℝ≥0) := by
    have ht := wasserstein_triangle P.carrier.val S U
    change wassersteinDistance P.carrier.val S ≤ _ at hS
    change wassersteinDistance S U ≤ _ at hU
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  have hd' : ENNReal.ofReal (wassersteinDistance P.carrier.val U) ^ 2 ≤
      (2 * (eps : ℝ≥0∞)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa using ENNReal.ofReal_le_ofReal hd
  apply (regretStability hpin hsv (optimalPredictor P) P U).2.trans
  calc
    _ ≤ 4 * conditionNumber P.carrier.val * (2 * (eps : ℝ≥0∞)) ^ 2 := mul_le_mul' le_rfl hd'
    _ = _ := by ring

-- @node: population_snr_objective_bound
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps), if [S is within Wasserstein distance
eps of the nondegenerate law P](hyp:hS) and [A minimizes population risk plus
eps squared times squared operator norm at S](hyp:hA), then [A's regret at S
plus that norm penalty is at most five times P's condition number times eps squared](goal). -/
lemma population_snr_objective_bound {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (eps : ℝ≥0)
    (S : JointLaws p m) (hS : S ∈ lawBall P.carrier.val eps)
    (A : Mat m p) (hA : A ∈ populationMinimizers 3 S eps) :
    regret A S + (eps : ℝ) ^ 2 * opNorm A ^ 2 ≤
      5 * (conditionNumber P.carrier.val).toReal * (eps : ℝ) ^ 2 := by
  have ho := hA (Set.mem_univ (optimalPredictor P))
  change populationObjective 3 S eps A ≤ populationObjective 3 S eps (optimalPredictor P) at ho
  simp only [populationObjective, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, if_false] at ho
  have hr : risk A S + (eps : ℝ) ^ 2 * opNorm A ^ 2 ≤
      risk (optimalPredictor P) S + (eps : ℝ) ^ 2 * opNorm (optimalPredictor P) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg (risk_nonneg _ _) (by positivity))).mp ho
  have hb := reference_regret_on_ball hpin hsv P eps S hS
  have hn := mul_le_mul_of_nonneg_left (reference_predictor_norm_le_condition hpin hsv P)
    (sq_nonneg (eps : ℝ))
  unfold regret at *
  nlinarith

-- @node: population_snr_stability
/-- Under [the pinning assumption for the response dimension](hyp:hpin) and
[the singular-value convention](hyp:hsv), for [nonnegative radius eps](hyp:eps), if [the rule selects minimizers of
population risk plus eps squared times squared operator norm at every law](hyp:hsel),
then [its robust regret around the nondegenerate law P at radius eps is at most
thirty-six times P's condition number times eps squared](goal). -/
lemma population_snr_stability {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention)
    (P : NondegenerateLaws p m) (eps : ℝ≥0)
    (rule : Estimator p m) (hsel : IsPopulationSelection 3 eps rule) :
    robustRegret rule P.carrier.val eps ≤
      36 * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 := by
  let k := (conditionNumber P.carrier.val).toReal
  let x := Real.sqrt k * (eps : ℝ)
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  have hx : 0 ≤ x := mul_nonneg (Real.sqrt_nonneg _) eps.property
  have hx2 : x ^ 2 = k * (eps : ℝ) ^ 2 := by
    dsimp only [x]
    rw [mul_pow, Real.sq_sqrt hk]
  have hbound (S T : JointLaws p m) (hS : S ∈ lawBall P.carrier.val eps)
      (ht : |Real.sqrt (regret (rule S) S) - Real.sqrt (regret (rule S) T)| ≤
        (2 * Real.sqrt k + opNorm (rule S)) * eps) :
      ENNReal.ofReal (regret (rule S) T) ≤
        36 * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 := by
    have ho := population_snr_objective_bound hpin hsv P eps S hS _ (hsel S)
    have ha := Real.sqrt_nonneg (regret (rule S) S)
    have hb : 0 ≤ opNorm (rule S) * (eps : ℝ) := mul_nonneg (norm_nonneg _) eps.property
    have hs := Real.sq_sqrt (regret_nonneg S (rule S))
    -- Cauchy--Schwarz for the regret and penalty components.
    have hcs : Real.sqrt (regret (rule S) S) + opNorm (rule S) * (eps : ℝ) ≤ 4 * x := by
      have hdiff := sq_nonneg (Real.sqrt (regret (rule S) S) - opNorm (rule S) * (eps : ℝ))
      change regret (rule S) S + (eps : ℝ) ^ 2 * opNorm (rule S) ^ 2 ≤
        5 * k * (eps : ℝ) ^ 2 at ho
      nlinarith [sq_nonneg (Real.sqrt (regret (rule S) S) + opNorm (rule S) *
        (eps : ℝ) + 4 * x)]
    have hroot : Real.sqrt (regret (rule S) T) ≤ 6 * x := by
      have ht' := (abs_le.mp ht).1
      dsimp only [x] at hcs ⊢
      nlinarith
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    rw [Real.sq_sqrt (regret_nonneg T (rule S)), mul_pow, hx2] at hsq
    apply (ENNReal.ofReal_le_ofReal hsq).trans_eq
    norm_num only [show (6 : ℝ) ^ 2 = 36 by norm_num]
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36),
      ENNReal.ofReal_mul hk, ENNReal.ofReal_toReal (conditionNumber_ne_top P),
      ENNReal.ofReal_ofNat, k]
    change 36 * (conditionNumber P.carrier.val * ENNReal.ofReal ((eps : ℝ) ^ 2)) = _
    rw [ENNReal.ofReal_pow (p := (eps : ℝ)) eps.property 2, ENNReal.ofReal_coe_nnreal]
    ring
  apply iSup₂_le
  intro Q hQ
  have hself : P.carrier.val ∈ lawBall P.carrier.val eps := by simp [lawBall, wasserstein_self]
  have hdist (A : Mat m p) :
      |Real.sqrt (regret A P.carrier.val) - Real.sqrt (regret A Q)| ≤
        (2 * Real.sqrt k + opNorm A) * eps := by
    apply (regretStability hpin hsv A P Q).1.trans
    exact mul_le_mul_of_nonneg_left hQ (by positivity [norm_nonneg (matrixCLM A)])
  apply max_le
  · exact hbound P.carrier.val Q hself (hdist _)
  · apply hbound Q P.carrier.val hQ
    rw [abs_sub_comm]
    exact hdist _

-- @node: lem:stability-implications
/-- [There is a universal positive constant C such that, in positive feature
and response dimensions under the pinning and singular-value assumptions,
every nondegenerate law P and positive radius eps admit the following bounds
for any population ERM, DRO, minimax-regret, and squared-operator-norm-regularized
selections: the latter two have robust regret at most C times P's condition
number times eps squared, while ERM and DRO have bounds using C times eps
squared times the largest condition number within eps and twice eps of P,
respectively; when eps squared is at most one sixteenth of P's smallest feature
second-moment eigenvalue, both of these last bounds are at most nineteen C
times P's condition number times eps squared](goal). -/
lemma stabilityImplications :
    ∃ C : ℝ, 0 < C ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ (P : NondegenerateLaws p m)
      (eps : ℝ≥0), 0 < eps → ∀ erm dro mro snr : Estimator p m,
      IsPopulationSelection 0 eps erm → IsPopulationSelection 1 eps dro →
      IsPopulationSelection 2 eps mro → IsPopulationSelection 3 eps snr →
      robustRegret mro P.carrier.val eps ≤ ENNReal.ofReal C * conditionNumber P.carrier.val *
        (eps : ℝ≥0∞) ^ 2 ∧
      robustRegret snr P.carrier.val eps ≤ ENNReal.ofReal C * conditionNumber P.carrier.val *
        (eps : ℝ≥0∞) ^ 2 ∧
      robustRegret erm P.carrier.val eps ≤ ENNReal.ofReal C * (eps : ℝ≥0∞) ^ 2 *
        (⨆ Q ∈ lawBall P.carrier.val eps, conditionNumber Q) ∧
      robustRegret dro P.carrier.val eps ≤ ENNReal.ofReal C * (eps : ℝ≥0∞) ^ 2 *
        (⨆ Q ∈ lawBall P.carrier.val (2 * eps), conditionNumber Q) ∧
      (assStabilityImplicationsSmallRadius P.carrier.val eps →
        ENNReal.ofReal C * (eps : ℝ≥0∞) ^ 2 * (⨆ Q ∈ lawBall P.carrier.val eps, conditionNumber Q) ≤
          ENNReal.ofReal (19 * C) * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 ∧
        ENNReal.ofReal C * (eps : ℝ≥0∞) ^ 2 * (⨆ Q ∈ lawBall P.carrier.val (2 * eps),
          conditionNumber Q) ≤
          ENNReal.ofReal (19 * C) * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2) := by
  refine ⟨36, by norm_num, ?_⟩
  intro p m _ _ hpin hsv P eps heps erm dro mro snr herm hdro hmro hsnr
  have he : 0 ≤ (eps : ℝ) := eps.property
  have hself : P.carrier.val ∈ lawBall P.carrier.val eps := by simp [lawBall, wasserstein_self]
  have hmroBound : robustRegret mro P.carrier.val eps ≤
      16 * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 := by
    apply iSup₂_le
    intro Q hQ
    apply max_le
    · exact population_mro_pair_stability hpin hsv P eps P.carrier.val Q hself hQ _ (hmro _)
    · have hrev : P.carrier.val ∈ lawBall Q eps := by
        change wassersteinDistance Q P.carrier.val ≤ eps
        rw [wasserstein_symm]
        exact hQ
      exact population_mro_pair_stability hpin hsv P eps Q P.carrier.val hQ hrev _ (hmro _)
  have hsnrBound := population_snr_stability hpin hsv P eps snr hsnr
  have hermBound := (stabilityImplicationsErm hpin hsv P.carrier.val eps heps erm herm).1
  have hdroBound := (stabilityImplicationsDro hpin hsv P.carrier.val eps heps dro hdro).1
  norm_num only [ENNReal.ofReal_ofNat]
  refine ⟨hmroBound.trans ?_, hsnrBound, hermBound.trans ?_, hdroBound.trans ?_, ?_⟩
  · exact mul_le_mul' (mul_le_mul' (by norm_num : (16 : ℝ≥0∞) ≤ 36) le_rfl) le_rfl
  · exact mul_le_mul' (mul_le_mul' (by norm_num : (4 : ℝ≥0∞) ≤ 36) le_rfl) le_rfl
  · exact mul_le_mul' (mul_le_mul' (by norm_num : (16 : ℝ≥0∞) ≤ 36) le_rfl) le_rfl
  · intro hr
    have hl := lambdaMin_pos_of_posDef (secondMomentX P.carrier.val) P.carrier.property
    have hs := Real.sq_sqrt hl.le
    have hn := Real.sqrt_nonneg (lambdaMin (secondMomentX P.carrier.val))
    have hr2 : (2 * eps : ℝ≥0) ≤ Real.sqrt (lambdaMin (secondMomentX P.carrier.val)) / 2 := by
      change (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P.carrier.val) / 16 at hr
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      nlinarith [he]
    have hc2 : ∀ Q ∈ lawBall P.carrier.val (2 * eps),
        conditionNumber Q ≤ 19 * conditionNumber P.carrier.val :=
      fun Q hQ => law_conditionNumber_small_radius hpin hsv P (2 * eps) hr2 Q hQ
    have hc1 : ∀ Q ∈ lawBall P.carrier.val eps,
        conditionNumber Q ≤ 19 * conditionNumber P.carrier.val := by
      intro Q hQ
      apply hc2 Q
      change wassersteinDistance P.carrier.val Q ≤ (2 * eps : ℝ≥0)
      change wassersteinDistance P.carrier.val Q ≤ eps at hQ
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [he]
    constructor
    · calc
        _ ≤ 36 * (eps : ℝ≥0∞) ^ 2 * (19 * conditionNumber P.carrier.val) :=
          mul_le_mul' le_rfl (iSup₂_le hc1)
        _ = _ := by ring
    · calc
        _ ≤ 36 * (eps : ℝ≥0∞) ^ 2 * (19 * conditionNumber P.carrier.val) :=
          mul_le_mul' le_rfl (iSup₂_le hc2)
        _ = _ := by ring

end Papers.WassersteinRegretS2S3
