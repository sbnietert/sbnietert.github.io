module
public import Papers.WassersteinRegretS2S3.Helpers.Scaling

/-!
# Scaling class regret and arbitrary DRO selections

Positive dilation preserves the full well-conditioned class. Pulling back any
DRO selection therefore transports unit-radius lower bounds to every radius.
-/

public section

namespace Papers.WassersteinRegretS2S3

open scoped NNReal ENNReal

-- @node: wellConditionedSet_dilateLaw_iff
/-- If [the dilation factor is positive](hyp:ha), then [dilating a joint law preserves
and reflects membership in the class of laws whose condition number is bounded by
the given threshold](goal). -/
lemma wellConditionedSet_dilateLaw_iff {p m : ℕ} [NeZero p] [NeZero m]
    (a : ℝ) (ha : 0 < a) (kappa : ℝ) (P : JointLaws p m) :
    dilateLaw a P ∈ wellConditionedSet p m kappa ↔
      P ∈ wellConditionedSet p m kappa := by
  change ((secondMomentX (dilateLaw a P)).PosDef ∧ _) ↔ _
  rw [secondMomentX_dilate_posDef_iff a ha,
    conditionNumber_dilateLaw (assPin1_valid m) assSingularValueConvention_valid a ha]
  rfl

-- @node: classRisk_dilateLaw
/-- For [a nonnegative ambiguity radius eps](hyp:eps), if [the dilation factor is positive](hyp:ha), then [the class risk of an estimator
at the dilated ambiguity radius equals the squared dilation factor times the class
risk at the original radius of the estimator that first dilates its input law,
over the same well-conditioned class](goal). -/
lemma classRisk_dilateLaw {p m : ℕ} [NeZero p] [NeZero m]
    (a : ℝ) (ha : 0 < a) (kappa : ℝ) (eps : ℝ≥0) (rule : Estimator p m) :
    classRisk (wellConditionedSet p m kappa) (a.toNNReal * eps) rule =
      ENNReal.ofReal (a ^ 2) *
        classRisk (wellConditionedSet p m kappa) eps (fun Q => rule (dilateLaw a Q)) := by
  change (⨆ P ∈ wellConditionedSet p m kappa,
    robustRegret rule P (a.toNNReal * eps)) = _
  simp only [classRisk, classRegrets, ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun P => iSup_le fun hP => ?_
    let Q := dilateLaw a⁻¹ P
    have hQ : Q ∈ wellConditionedSet p m kappa :=
      (wellConditionedSet_dilateLaw_iff a⁻¹ (inv_pos.mpr ha) kappa P).mpr hP
    have hPQ : dilateLaw a Q = P := by
      dsimp [Q]
      rw [dilateLaw_comp, mul_inv_cancel₀ ha.ne', dilateLaw_one]
    rw [← hPQ, robustRegret_dilateLaw a ha]
    exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  · refine iSup_le fun P => iSup_le fun hP => ?_
    rw [← robustRegret_dilateLaw a ha]
    exact le_iSup_of_le (dilateLaw a P)
      (le_iSup_of_le ((wellConditionedSet_dilateLaw_iff a ha kappa P).mpr hP) le_rfl)

-- @node: population_dro_selection_dilateLaw
/-- For [a nonnegative ambiguity radius eps](hyp:eps), if [the dilation factor is positive](hyp:ha) and [an estimator selects a population
DRO solution minimizing worst-case risk at the dilated ambiguity radius for every input
law](hyp:hsel), then [applying that estimator after dilating the input law selects a
population DRO solution minimizing worst-case risk at the original radius](goal). -/
lemma population_dro_selection_dilateLaw {p m : ℕ}
    (a : ℝ) (ha : 0 < a) (eps : ℝ≥0) (rule : Estimator p m)
    (hsel : IsPopulationSelection 1 (a.toNNReal * eps) rule) :
    IsPopulationSelection 1 eps (fun P => rule (dilateLaw a P)) := by
  intro P
  rw [← population_dro_dilateLaw a ha P eps]
  exact hsel (dilateLaw a P)

-- @node: dro_class_lower_bound_rescale
/-- If [every population DRO selection minimizing worst-case risk at unit radius has class
risk at least c times the specified rate for every positive feature and response
dimension and condition threshold at least one, under the pinning and singular-value
assumptions](hyp:hunit), then [every such selection at any positive radius has class
risk at least c times that rate times the squared radius, under the same dimension,
threshold, and structural assumptions](goal). -/
lemma dro_class_lower_bound_rescale
    (c : ℝ) (rate : ℕ → ℕ → ℝ → ℝ)
    (hunit : ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ rule : Estimator p m, IsPopulationSelection 1 1 rule →
        ENNReal.ofReal (c * rate p m kappa) ≤
          classRisk (wellConditionedSet p m kappa) 1 rule) :
    ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ eps : ℝ≥0, 0 < eps → ∀ rule : Estimator p m,
      IsPopulationSelection 1 eps rule →
        ENNReal.ofReal (c * rate p m kappa * (eps : ℝ) ^ 2) ≤
          classRisk (wellConditionedSet p m kappa) eps rule := by
  intro p m _ _ hpin hsv kappa hkappa eps heps rule hsel
  have ha : 0 < (eps : ℝ) := heps
  have hr : (eps : ℝ).toNNReal * 1 = eps := by simp
  have hsel' : IsPopulationSelection 1 ((eps : ℝ).toNNReal * 1) rule := by
    rwa [hr]
  have hbound := hunit p m hpin hsv kappa hkappa
    (fun Q => rule (dilateLaw (eps : ℝ) Q))
    (population_dro_selection_dilateLaw (eps : ℝ) ha 1 rule hsel')
  have hscaled := mul_le_mul_right hbound (ENNReal.ofReal ((eps : ℝ) ^ 2))
  rw [← classRisk_dilateLaw (eps : ℝ) ha kappa 1 rule, hr] at hscaled
  rw [mul_comm (c * rate p m kappa), ENNReal.ofReal_mul (sq_nonneg _)]
  exact hscaled

end Papers.WassersteinRegretS2S3
