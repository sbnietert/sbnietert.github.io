module
public import Papers.WassersteinRegretS2S3.Helpers.LowerB
public import Papers.WassersteinRegretS2S3.Helpers.ClassScaling

/-!
# Population Wasserstein regret: Helpers/DROLower

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
The combination and scaling proof uses `droLbA` and `droLbB`; their remaining
proof obligations are visible in LowerA and LowerB.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: lem:lemma-37
/-- [There is a universal positive constant such that, in all positive feature
and response dimensions, under the Euclidean squared-norm identity and the
convention that singular values are nonnegative and decreasing with the smallest
at the last index, every population Wasserstein robust selection rule with unit
robustness factor has worst-case regret on the well-conditioned class at least
that constant times the squared positive ambiguity radius times the sum of the
square root of the smaller dimension multiplied by the excess of the condition
parameter over one, the square root of the product of the response dimension and
that excess, and the condition parameter, for every condition parameter at least one](goal). -/
lemma lemma37 :
    ∃ c : ℝ, 0 < c ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ (kappa : ℝ), 1 ≤ kappa →
      ∀ eps : ℝ≥0, 0 < eps → ∀ rule : Estimator p m, IsPopulationSelection 1 eps rule →
      ENNReal.ofReal (c * classRate p m kappa * (eps : ℝ) ^ 2) ≤
        classRisk (wellConditionedSet p m kappa) eps rule := by
  suffices hunit : ∃ c : ℝ, 0 < c ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ kappa : ℝ, 1 ≤ kappa →
      ∀ rule : Estimator p m, IsPopulationSelection 1 1 rule →
        ENNReal.ofReal (c * classRate p m kappa) ≤
          classRisk (wellConditionedSet p m kappa) 1 rule by
    obtain ⟨c, hc, hbound⟩ := hunit
    exact ⟨c, hc, dro_class_lower_bound_rescale c classRate hbound⟩
  obtain ⟨cA, hcA, hA⟩ := droLbA
  obtain ⟨cB, hcB, hB⟩ := droLbB
  let t : ℝ := min (min cA cB) 1
  have ht : 0 < t := lt_min (lt_min hcA hcB) zero_lt_one
  have htA : t ≤ cA := (min_le_left _ _).trans (min_le_left _ _)
  have htB : t ≤ cB := (min_le_left _ _).trans (min_le_right _ _)
  have ht1 : t ≤ 1 := min_le_right _ _
  refine ⟨t / 3, by positivity, ?_⟩
  intro p m _ _ hpin hsv kappa hkappa rule hsel
  let x := Real.sqrt (min p m : ℕ) * (kappa - 1)
  let y := Real.sqrt ((m : ℝ) * (kappa - 1))
  have hx : 0 ≤ x := mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hkappa)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hk : 0 ≤ kappa := le_trans zero_le_one hkappa
  have hAx : ENNReal.ofReal (t * x) ≤
      classRisk (wellConditionedSet p m kappa) 1 rule := by
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right htA hx)).trans
    simpa only [x, mul_assoc] using hA p m hpin hsv kappa hkappa rule hsel
  have hBy : ENNReal.ofReal (t * y) ≤
      classRisk (wellConditionedSet p m kappa) 1 rule :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right htB hy)).trans
      (hB p m hpin hsv kappa hkappa rule hsel)
  have hCk : ENNReal.ofReal (t * kappa) ≤
      classRisk (wellConditionedSet p m kappa) 1 rule := by
    calc
      _ ≤ ENNReal.ofReal kappa := ENNReal.ofReal_le_ofReal (by nlinarith [ht1])
      _ ≤ classMinimax (wellConditionedSet p m kappa) 1 := by
        simpa using minimaxLb (p := p) (m := m) hpin hsv 1 (by norm_num) kappa hkappa
      _ ≤ classRisk (wellConditionedSet p m kappa) 1 rule := iInf_le _ rule
  have hmaxX : t * x ≤ max (t * x) (max (t * y) (t * kappa)) := le_max_left _ _
  have hmaxY : t * y ≤ max (t * x) (max (t * y) (t * kappa)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmaxK : t * kappa ≤ max (t * x) (max (t * y) (t * kappa)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  calc
    ENNReal.ofReal (t / 3 * classRate p m kappa) ≤
        ENNReal.ofReal (max (t * x) (max (t * y) (t * kappa))) := by
      apply ENNReal.ofReal_le_ofReal
      change t / 3 * (x + y + kappa) ≤ _
      nlinarith
    _ = max (ENNReal.ofReal (t * x))
        (max (ENNReal.ofReal (t * y)) (ENNReal.ofReal (t * kappa))) := by
      rw [ENNReal.ofReal_max, ENNReal.ofReal_max]
    _ ≤ classRisk (wellConditionedSet p m kappa) 1 rule := max_le hAx (max_le hBy hCk)

end Papers.WassersteinRegretS2S3
