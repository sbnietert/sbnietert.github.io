module
public import Papers.WassersteinRegretS2S3.Helpers.EstimatorBounds
public import Papers.WassersteinRegretS2S3.Helpers.Regularizer

/-!
# Population Wasserstein regret: Helpers/RankAdaptive

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: rank_adaptive_trace_bounds
/-- For a matrix A with p columns and a positive semidefinite matrix E, [the trace
of A times its transpose times E is bounded both by the squared operator norm of
A times the trace of E and by p times the largest eigenvalue of E times the
squared operator norm of A](goal). -/
lemma rank_adaptive_trace_bounds {p m : ℕ} [NeZero m]
    (A : Mat m p) (E : PSD m) :
    Matrix.trace (A * A.transpose * E.val) ≤ opNorm A ^ 2 * Matrix.trace E.val ∧
    Matrix.trace (A * A.transpose * E.val) ≤
      (p : ℝ) * lambdaMax E.val * opNorm A ^ 2 := by
  let S := CFC.sqrt E.val
  have hS : E.val = S * S.transpose := psd_sqrt_factor E
  have ht : frob (A.transpose * S) ^ 2 = Matrix.trace (A * A.transpose * E.val) := by
    rw [frob_sq_trace_rows, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = Matrix.trace (A.transpose * (S * S.transpose) * A) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_cycle, ← hS]
  have htrace : frob S ^ 2 = Matrix.trace E.val := by
    rw [frob_sq_trace_rows, ← hS]
  have hnorm : opNorm S ^ 2 = lambdaMax E.val := by rw [hS, lambdaMax_gram]
  have hp : frob A ^ 2 ≤ (p : ℝ) * opNorm A ^ 2 := by
    have hr : (Matrix.rank A : ℝ) ≤ p := by exact_mod_cast Matrix.rank_le_width A
    have hb := pow_le_pow_left₀ (frob_nonneg A) (frob_le_sqrt_rank_opNorm A) 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _))
  constructor
  · have hb := pow_le_pow_left₀ (frob_nonneg _) (frob_mul_left_le A.transpose S) 2
    simpa only [ht, mul_pow, opNorm_transpose, htrace] using hb
  · have hb := pow_le_pow_left₀ (frob_nonneg _) (frob_mul_right_le A.transpose S) 2
    rw [ht, mul_pow, frob_transpose, hnorm] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right hp (by rw [← hnorm]; positivity)).trans_eq
      (by ring))

-- @node: rank_adaptive_regularizer_bound
/-- Assuming [Euclidean squared norms equal the sum of squared coordinates in
the response space](hyp:hpin) and [singular values are nonnegative and ordered
from largest to smallest, with the minimum singular value in the last
position](hyp:hsv), [the DRO regularizer scale for a nondegenerate law is at most
the square root of the smallest feature second-moment eigenvalue times the sum
of two terms: the square root of the product of residual effective rank and
condition number minus one, and condition number minus one times the square root
of the smaller of feature dimension and residual effective rank](goal). -/
lemma rank_adaptive_regularizer_bound {p m : ℕ} [NeZero p] [NeZero m]
    (hpin : assPin1 m) (hsv : assSingularValueConvention) (P : NondegenerateLaws p m) :
    droRegularizerScale P ≤ Real.sqrt (lambdaMin (secondMomentX P.carrier.val)) *
      (Real.sqrt (effectiveRank (residualSecondMoment P) *
        ((conditionNumber P.carrier.val).toReal - 1)) +
      ((conditionNumber P.carrier.val).toReal - 1) *
        Real.sqrt (min (p : ℝ) (effectiveRank (residualSecondMoment P)))) := by
  let A := optimalPredictor P
  let E : PSD m := ⟨residualSecondMoment P, (residual_law_matrix P).2⟩
  let l := lambdaMin (secondMomentX P.carrier.val)
  let mu := lambdaMax E.val
  let r := effectiveRank E.val
  let s := (conditionNumber P.carrier.val).toReal - 1
  let q := min (p : ℝ) r
  have hl : 0 < l := lambdaMin_pos_of_posDef _ P.carrier.property
  have hnorm : opNorm E.val = mu := by
    have hS := psd_sqrt_factor E
    change opNorm E.val = lambdaMax E.val
    rw [hS, lambdaMax_gram]
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt E.val).transpose
    change opNorm ((CFC.sqrt E.val).transpose.conjTranspose * (CFC.sqrt E.val).transpose) =
      opNorm (CFC.sqrt E.val).transpose * opNorm (CFC.sqrt E.val).transpose at h
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      opNorm_transpose, pow_two] using h
  have hmu : 0 ≤ mu := hnorm ▸ norm_nonneg (matrixCLM E.val)
  have hr : 0 ≤ r := (effectiveRank_bounds E).1
  have hq : 0 ≤ q := le_min (Nat.cast_nonneg _) hr
  have htrace : Matrix.trace E.val = r * mu := by
    simpa only [← hnorm] using (effectiveRank_bounds E).2.2
  have hf := conditionNumberFormula hpin hsv P
  have hc := (ENNReal.ofReal_le_iff_le_toReal hf.1).mp hf.2.2.2.2.1
  have ha : opNorm A ^ 2 ≤ s := by
    have hm := le_max_left (opNorm A ^ 2) (mu / l)
    change 1 + max (opNorm A ^ 2) (mu / l) ≤ (conditionNumber P.carrier.val).toReal at hc
    dsimp only [s]
    linarith
  have hs : 0 ≤ s := (sq_nonneg _).trans ha
  have hmul : mu ≤ s * l := by
    have hm := le_max_right (opNorm A ^ 2) (mu / l)
    change 1 + max (opNorm A ^ 2) (mu / l) ≤ (conditionNumber P.carrier.val).toReal at hc
    dsimp only [s]
    exact (div_le_iff₀ hl).mp (by linarith)
  have ht := rank_adaptive_trace_bounds A E
  have htq : Matrix.trace (A * A.transpose * E.val) ≤ q * mu * s := by
    have ht1 : Matrix.trace (A * A.transpose * E.val) ≤ r * mu * s := by
      rw [htrace] at ht
      exact ht.1.trans ((mul_le_mul_of_nonneg_right ha (mul_nonneg hr hmu)).trans_eq
        (by ring))
    have ht2 : Matrix.trace (A * A.transpose * E.val) ≤ (p : ℝ) * mu * s :=
      ht.2.trans (mul_le_mul_of_nonneg_left ha (mul_nonneg (Nat.cast_nonneg _) hmu))
    rcases le_total (p : ℝ) r with hp | hp
    · simpa only [q, min_eq_left hp] using ht2
    · simpa only [q, min_eq_right hp] using ht1
  have hb : Matrix.trace (((1 : Mat m m) + A * A.transpose) * E.val) ≤
      l * (r * s + s ^ 2 * q) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, htrace]
    calc
      _ ≤ r * mu + q * mu * s := add_le_add le_rfl htq
      _ = mu * (r + s * q) := by ring
      _ ≤ (s * l) * (r + s * q) := mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = _ := by ring
  change Real.sqrt (Matrix.trace (((1 : Mat m m) + A * A.transpose) * E.val)) ≤
    Real.sqrt l * (Real.sqrt (r * s) + s * Real.sqrt q)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, hb.trans ?_⟩
  have hcross : 0 ≤ 2 * Real.sqrt (r * s) * s * Real.sqrt q := by positivity
  have heq : (Real.sqrt (r * s) + s * Real.sqrt q) ^ 2 =
      r * s + s ^ 2 * q + 2 * Real.sqrt (r * s) * s * Real.sqrt q := by
    nlinarith [Real.sq_sqrt (mul_nonneg hr hs), Real.sq_sqrt hq]
  rw [mul_pow, Real.sq_sqrt hl.le, heq]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcross) hl.le

-- @node: lem:dro-rank-adaptive
/-- [There is a universal positive constant C such that, in any positive feature
and response dimensions, under the Euclidean squared-norm identity and the
convention of nonnegative decreasing singular values with the minimum last,
every population DRO minimizer rule at any positive Wasserstein radius has
robust regret at any nondegenerate law bounded by C times that law's local
rank rate times the squared radius](goal).

The local rank rate is the condition number plus the square root of the product
of residual effective rank and condition number minus one, plus condition number
minus one times the square root of the smaller of feature dimension and residual
effective rank. -/
lemma droRankAdaptive :
    ∃ C : ℝ, 0 < C ∧ ∀ (p m : ℕ) [NeZero p] [NeZero m],
      assPin1 m → assSingularValueConvention → ∀ (P : NondegenerateLaws p m)
      (eps : ℝ≥0), 0 < eps → ∀ rule : Estimator p m, IsPopulationSelection 1 eps rule →
      robustRegret rule P.carrier.val eps ≤ ENNReal.ofReal (C * localRankRate P * (eps : ℝ) ^
        2) := by
  refine ⟨304, by norm_num, ?_⟩
  intro p m _ _ hpin hsv P eps heps rule hsel
  let k := (conditionNumber P.carrier.val).toReal
  let s := k - 1
  let r := effectiveRank (residualSecondMoment P)
  let t := Real.sqrt (min (p : ℝ) r) * s + Real.sqrt (r * s)
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  have hc := (ENNReal.ofReal_le_iff_le_toReal (conditionNumber_ne_top P)).mp
    (conditionNumberFormula hpin hsv P).2.2.2.2.1
  have hs : 0 ≤ s := by
    have hm := le_max_left (opNorm (optimalPredictor P) ^ 2)
      (lambdaMax (residualSecondMoment P) / lambdaMin (secondMomentX P.carrier.val))
    dsimp only [s, k]
    linarith [sq_nonneg (opNorm (optimalPredictor P))]
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hrate : localRankRate P = t + k := rfl
  have he : 0 ≤ (eps : ℝ) := eps.property
  have hcast (c : ℝ) (hc : 0 ≤ c) :
      ENNReal.ofReal (c * k * (eps : ℝ) ^ 2) =
        ENNReal.ofReal c * conditionNumber P.carrier.val * (eps : ℝ≥0∞) ^ 2 := by
    rw [ENNReal.ofReal_mul (mul_nonneg hc hk), ENNReal.ofReal_mul hc,
      ENNReal.ofReal_toReal (conditionNumber_ne_top P), ENNReal.ofReal_pow he,
      ENNReal.ofReal_coe_nnreal]
  by_cases hradius : (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P.carrier.val) / 16
  · have hb := (stabilityImplicationsDro hpin hsv P.carrier.val eps heps rule hsel).2 hradius
    apply hb.trans
    rw [← show ENNReal.ofReal (304 : ℝ) = 304 by norm_num, ← hcast 304 (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [hrate]
    nlinarith [mul_nonneg ht (sq_nonneg (eps : ℝ))]
  · have hl : 0 < lambdaMin (secondMomentX P.carrier.val) :=
      lambdaMin_pos_of_posDef _ P.carrier.property
    have hroot : Real.sqrt (lambdaMin (secondMomentX P.carrier.val)) ≤ 4 * (eps : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith⟩
    have hg : droRegularizerScale P ≤ 4 * (eps : ℝ) * t := by
      have hb := rank_adaptive_regularizer_bound hpin hsv P
      change droRegularizerScale P ≤ Real.sqrt (lambdaMin (secondMomentX P.carrier.val)) *
        (Real.sqrt (r * s) + s * Real.sqrt (min (p : ℝ) r)) at hb
      have ht' : Real.sqrt (r * s) + s * Real.sqrt (min (p : ℝ) r) = t := by
        dsimp only [t]; ring
      rw [ht'] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hroot ht)
    have hb : robustRegret rule P.carrier.val eps ≤
        ENNReal.ofReal (4 * droRegularizerScale P * eps + 5 * k * (eps : ℝ) ^ 2) := by
      have hb := droRegularizer hpin hsv P eps rule hsel
      have hg0 : 0 ≤ droRegularizerScale P := Real.sqrt_nonneg _
      rw [ENNReal.ofReal_add (by positivity) (by positivity), hcast 5 (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      exact hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    rw [hrate]
    have hlin := mul_le_mul_of_nonneg_right hg he
    nlinarith [mul_nonneg ht (sq_nonneg (eps : ℝ)), mul_nonneg hk (sq_nonneg (eps : ℝ))]

end Papers.WassersteinRegretS2S3
