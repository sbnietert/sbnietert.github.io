module
public import Papers.WassersteinRegretS2S3.Helpers.FactorSupremum
public import Papers.WassersteinRegretS2S3.Helpers.BuresGeometry
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Population Wasserstein regret: Helpers/AlternativeCondition

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: alternativeValue_normalized_tendsto
/-- For nondegenerate second moments, [the alternative value divided by the squared
radius converges, as the positive radius tends to zero, to the supremum of derivative
sensitivity over perturbations with Frobenius norm at most one](goal). -/
lemma alternativeValue_normalized_tendsto {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : NondegenerateSecondMoments p m) :
    Filter.Tendsto
      (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * alternativeValue Sigma.carrier.val eps)
      positiveRadii
      (nhds (⨆ D, ⨆ (_ : frob D ≤ 1),
        ENNReal.ofReal (derivativeSensitivity Sigma.carrier.val D))) := by
  let c := ⨆ D, ⨆ (_ : frob D ≤ 1),
    ENNReal.ofReal (derivativeSensitivity Sigma.carrier.val D)
  have hc : c ≠ ⊤ := derivativeSensitivity_sup_ne_top Sigma.carrier.val
  have hrad : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  have hreal : Filter.Tendsto
      (fun eps : ℝ≥0 => (alternativeValue Sigma.carrier.val eps).toReal / (eps : ℝ) ^ 2)
      positiveRadii (nhds c.toReal) := by
    apply Metric.tendsto_nhds.mpr
    intro e he
    obtain ⟨δ, hδ, hb⟩ := alternativeValue_uniform_taylor {Sigma} isCompact_singleton (half_pos he)
    have hsmall := hrad.eventually (eventually_lt_nhds hδ)
    filter_upwards [hpos, hsmall] with eps heps hepsδ
    have hr : 0 < (eps : ℝ) := by exact_mod_cast heps
    have hr2 : 0 < (eps : ℝ) ^ 2 := sq_pos_of_pos hr
    have hb' := (hb eps heps hepsδ Sigma (Set.mem_singleton Sigma)).2
    rw [Real.dist_eq]
    have heq : (alternativeValue Sigma.carrier.val eps).toReal / (eps : ℝ) ^ 2 - c.toReal =
        ((alternativeValue Sigma.carrier.val eps).toReal - c.toReal * (eps : ℝ) ^ 2) /
          (eps : ℝ) ^ 2 := by field_simp
    rw [heq, abs_div, abs_of_pos hr2]
    exact ((div_le_iff₀ hr2).mpr hb').trans_lt (half_lt_self he)
  have hconv := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [ENNReal.ofReal_toReal hc] at hconv
  apply hconv.congr'
  obtain ⟨δ, hδ, hb⟩ := alternativeValue_uniform_taylor {Sigma} isCompact_singleton (by norm_num : (0 : ℝ) < 1)
  have hsmall := hrad.eventually (eventually_lt_nhds hδ)
  filter_upwards [hpos, hsmall] with eps heps hepsδ
  have hr : 0 < (eps : ℝ) := by exact_mod_cast heps
  have hfinite := (hb eps heps hepsδ Sigma (Set.mem_singleton Sigma)).1
  simp only [Function.comp_apply]
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hr), ENNReal.ofReal_toReal hfinite]
  simp only [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow,
    div_eq_mul_inv, ENNReal.inv_pow, mul_comm]

-- @node: lem:alt-condition-number-formula
/-- Assuming [the squared Euclidean norm of every response vector equals the sum
of its squared coordinates](hyp:hpin),
[the alternative condition number equals the supremum of derivative sensitivity over
the Frobenius unit ball; moreover, uniformly on every compact set of nondegenerate
second moments, the alternative value and condition number are finite for all
sufficiently small positive radii, and the error in approximating the value by the
condition number times the squared radius is at most any prescribed positive
multiple of the squared radius](goal). -/
lemma altConditionNumberFormula {p m : ℕ} [NeZero p] [NeZero m] (hpin : assPin1 m) :
    (∀ Sigma : NondegenerateSecondMoments p m,
      alternativeConditionNumber Sigma =
        ⨆ (Delta : Mat (p + m) (p + m)) (_ : frob Delta ≤ 1),
          ENNReal.ofReal (derivativeSensitivity Sigma.carrier.val Delta)) ∧
    (∀ K : Set (NondegenerateSecondMoments p m), IsCompact K →
      ∀ eta : ℝ, 0 < eta → ∀ᶠ eps : ℝ≥0 in positiveRadii,
        ∀ Sigma ∈ K,
          alternativeValue Sigma.carrier.val eps ≠ ⊤ ∧ alternativeConditionNumber Sigma ≠ ⊤ ∧
          |(alternativeValue Sigma.carrier.val eps).toReal -
              (alternativeConditionNumber Sigma).toReal * (eps : ℝ) ^ 2| ≤ eta * (eps : ℝ) ^ 2)
                := by
  have hformula : ∀ Sigma : NondegenerateSecondMoments p m,
      alternativeConditionNumber Sigma =
        ⨆ (D : Mat (p + m) (p + m)) (_ : frob D ≤ 1),
          ENNReal.ofReal (derivativeSensitivity Sigma.carrier.val D) := by
    intro Sigma
    exact (alternativeValue_normalized_tendsto Sigma).limsup_eq
  refine ⟨hformula, ?_⟩
  intro K hK eta heta
  obtain ⟨δ, hδ, hb⟩ := alternativeValue_uniform_taylor K hK heta
  have hrad : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  filter_upwards [hpos, hrad.eventually (eventually_lt_nhds hδ)] with eps heps hepsδ
  intro Sigma hS
  rw [hformula Sigma]
  exact ⟨(hb eps heps hepsδ Sigma hS).1, derivativeSensitivity_sup_ne_top Sigma.carrier.val,
    (hb eps heps hepsδ Sigma hS).2⟩

end Papers.WassersteinRegretS2S3
