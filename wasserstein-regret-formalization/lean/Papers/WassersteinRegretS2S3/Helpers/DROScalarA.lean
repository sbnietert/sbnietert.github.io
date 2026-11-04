module
public import Papers.WassersteinRegretS2S3.Helpers.Scalar
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Scalar certificate for the first DRO lower bound

The bulk objective attains a minimum. Every bulk minimizer gives the same
first-coordinate certificate needed for the regret bound. The dual infimum at
the candidate is justified by a right limit at the excluded multiplier.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open scoped ENNReal NNReal

-- @node: droLowerAHeight
/-- For [a real bulk weight](hyp:n), [a target coefficient](hyp:b), and [a bulk
coefficient](hyp:beta), the [bulk height](goal) is the square root of one plus the
squared bulk coefficient, plus the square root of the bulk weight times the
square root of the sum of the squared bulk coefficient error and the squared target. -/
noncomputable def droLowerAHeight (n b beta : ℝ) : ℝ :=
  Real.sqrt (1 + beta ^ 2) + Real.sqrt n * Real.sqrt ((beta - b) ^ 2 + b ^ 2)

-- @node: droLowerADual
/-- For [a bulk weight](hyp:n), [a target coefficient](hyp:b), [a feature scaling
factor](hyp:c), [a first-coordinate coefficient](hyp:alpha), [a bulk
coefficient](hyp:beta), and [a dual multiplier](hyp:eta), the [scalar dual
value](goal) is the multiplier times one plus two fractions: the squared scaled
first-coordinate error divided by the multiplier minus one minus the squared
first-coordinate coefficient, and the bulk weight times the sum of the squared
bulk error and squared target divided by the multiplier minus one minus the
squared bulk coefficient. -/
noncomputable def droLowerADual (n b c alpha beta eta : ℝ) : ℝ :=
  eta * (1 + (alpha * c - b) ^ 2 / (eta - 1 - alpha ^ 2) +
    n * ((beta - b) ^ 2 + b ^ 2) / (eta - 1 - beta ^ 2))

-- @node: droLowerAObjective
/-- For [a bulk weight](hyp:n), [a target coefficient](hyp:b), [a feature scaling
factor](hyp:c), [a first-coordinate coefficient](hyp:alpha), and [a bulk
coefficient](hyp:beta), the [scalar robust objective](goal) is the infimum of the
nonnegative extended-real versions of the scalar dual values over multipliers
strictly greater than one plus the larger squared coefficient. -/
noncomputable def droLowerAObjective (n b c alpha beta : ℝ) : ℝ≥0∞ :=
  ⨅ (eta : ℝ) (_ : 1 + max (alpha ^ 2) (beta ^ 2) < eta),
    ENNReal.ofReal (droLowerADual n b c alpha beta eta)

-- @node: droLowerAHeight_continuous
/-- [The bulk height is continuous as a function of the bulk coefficient](goal). -/
@[fun_prop] lemma droLowerAHeight_continuous (n b : ℝ) :
    Continuous (droLowerAHeight n b) := by
  unfold droLowerAHeight
  fun_prop

-- @node: droLowerAHeight_nonneg
/-- [The bulk height is nonnegative for all real bulk weights, targets, and bulk coefficients](goal). -/
lemma droLowerAHeight_nonneg (n b beta : ℝ) : 0 ≤ droLowerAHeight n b beta := by
  unfold droLowerAHeight
  positivity

-- @node: droLowerAHeight_exists_minimizer
/-- [For every real bulk weight and target coefficient, the bulk height attains
a global minimum over all real bulk coefficients](goal). -/
lemma droLowerAHeight_exists_minimizer (n b : ℝ) :
    ∃ beta : ℝ, ∀ gamma : ℝ, droLowerAHeight n b beta ≤ droLowerAHeight n b gamma := by
  apply (droLowerAHeight_continuous n b).exists_forall_le_of_isBounded 0
  rw [isBounded_iff_forall_norm_le]
  refine ⟨droLowerAHeight n b 0, ?_⟩
  intro beta hbeta
  have hroot : |beta| ≤ Real.sqrt (1 + beta ^ 2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + beta ^ 2 by positivity)
    nlinarith [Real.sqrt_nonneg (1 + beta ^ 2), sq_abs beta]
  exact hroot.trans ((le_add_of_nonneg_right (by positivity)).trans hbeta)

-- @node: droLowerAHeight_hasDerivAt
/-- If [the target coefficient is positive](hyp:hb), then [the derivative of the
bulk height at the bulk coefficient equals that coefficient divided by the square
root of one plus its square, plus the square root of the bulk weight times the
bulk coefficient error divided by the square root of the sum of the squared bulk
error and squared target](goal). -/
lemma droLowerAHeight_hasDerivAt (n b beta : ℝ) (hb : 0 < b) :
    HasDerivAt (droLowerAHeight n b)
      (beta / Real.sqrt (1 + beta ^ 2) +
        Real.sqrt n * ((beta - b) / Real.sqrt ((beta - b) ^ 2 + b ^ 2))) beta := by
  have hu : 0 < 1 + beta ^ 2 := by positivity
  have hv : 0 < (beta - b) ^ 2 + b ^ 2 := by positivity
  convert (((hasDerivAt_const beta (1 : ℝ)).add ((hasDerivAt_id beta).pow 2)).sqrt
    hu.ne').add
    (HasDerivAt.const_mul (Real.sqrt n)
      (((((hasDerivAt_id beta).sub_const b).pow 2).add_const (b ^ 2)).sqrt
        hv.ne')) using 1 <;>
    first | rfl | (simp only [Pi.add_apply, Pi.pow_apply, id_eq, mul_one, zero_add]; ring)

-- @node: droLowerAHeight_minimizer_gt_half
/-- If [the bulk weight is at least 64](hyp:hn), [the target coefficient is
positive](hyp:hb), and [the bulk coefficient globally minimizes the bulk
height](hyp:hmin), then [the bulk coefficient is strictly greater than half the
target coefficient](goal). -/
lemma droLowerAHeight_minimizer_gt_half (n b beta : ℝ) (hn : 64 ≤ n) (hb : 0 < b)
    (hmin : ∀ gamma : ℝ, droLowerAHeight n b beta ≤ droLowerAHeight n b gamma) :
    b / 2 < beta := by
  have hlocal : IsLocalMin (droLowerAHeight n b) beta :=
    Filter.Eventually.of_forall hmin
  have hderiv := hlocal.hasDerivAt_eq_zero (droLowerAHeight_hasDerivAt n b beta hb)
  by_contra hnot
  have hbeta : beta ≤ b / 2 := le_of_not_gt hnot
  let u := Real.sqrt (1 + beta ^ 2)
  let v := Real.sqrt ((beta - b) ^ 2 + b ^ 2)
  have hu : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u ^ 2 = 1 + beta ^ 2 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (beta - b) ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hr2 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hquot : beta / u ≤ 1 := by
    apply (div_le_iff₀ hu).mpr
    nlinarith
  have hratio : Real.sqrt n * (b - beta) / v ≤ 1 := by
    change beta / u + Real.sqrt n * ((beta - b) / v) = 0 at hderiv
    calc
      Real.sqrt n * (b - beta) / v = beta / u := by
        calc
          _ = -(Real.sqrt n * ((beta - b) / v)) := by ring
          _ = beta / u := by linarith
      _ ≤ 1 := hquot
  have hbound : Real.sqrt n * (b - beta) ≤ v := by
    simpa using (div_le_iff₀ hv).mp hratio
  have hgap : 0 < b - beta := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt n * (b - beta)) hbound
  have hpoly : n * (b - beta) ^ 2 ≤ (beta - b) ^ 2 + b ^ 2 := by
    calc
      _ = (Real.sqrt n * (b - beta)) ^ 2 := by rw [mul_pow, hr2]
      _ ≤ v ^ 2 := by nlinarith [hsq]
      _ = _ := hv2
  have hlarge : 64 * (b - beta) ^ 2 ≤ n * (b - beta) ^ 2 :=
    mul_le_mul_of_nonneg_right hn (sq_nonneg _)
  nlinarith [sq_nonneg (b - 2 * beta)]

-- @node: droLowerAMultiplier
/-- For [a bulk weight](hyp:n), [a target coefficient](hyp:b), and [a bulk
coefficient](hyp:beta), the [candidate dual multiplier](goal) is one plus the
squared bulk coefficient plus the square root of the product of one plus that
square and the bulk weight times the sum of the squared bulk error and squared target. -/
noncomputable def droLowerAMultiplier (n b beta : ℝ) : ℝ :=
  1 + beta ^ 2 + Real.sqrt ((1 + beta ^ 2) * (n * ((beta - b) ^ 2 + b ^ 2)))

-- @node: droLowerAAlpha
/-- For [a bulk weight](hyp:n), [a target coefficient](hyp:b), and [a bulk
coefficient](hyp:beta), the [candidate first-coordinate coefficient](goal) is the
square root of the candidate dual multiplier minus one. -/
noncomputable def droLowerAAlpha (n b beta : ℝ) : ℝ :=
  Real.sqrt (droLowerAMultiplier n b beta - 1)

-- @node: droLowerAAlpha_properties
/-- If [the bulk weight is positive](hyp:hn) and [the target coefficient is
positive](hyp:hb), then [the candidate first-coordinate coefficient is positive,
its square equals the candidate dual multiplier minus one, and its square
strictly exceeds the squared bulk coefficient](goal). -/
lemma droLowerAAlpha_properties (n b beta : ℝ) (hn : 0 < n) (hb : 0 < b) :
    0 < droLowerAAlpha n b beta ∧
    (droLowerAAlpha n b beta) ^ 2 = droLowerAMultiplier n b beta - 1 ∧
    beta ^ 2 < (droLowerAAlpha n b beta) ^ 2 := by
  have hr : 0 < Real.sqrt ((1 + beta ^ 2) * (n * ((beta - b) ^ 2 + b ^ 2))) :=
    Real.sqrt_pos.mpr (by positivity)
  have he : 0 < droLowerAMultiplier n b beta - 1 := by
    unfold droLowerAMultiplier
    nlinarith [sq_nonneg beta]
  refine ⟨Real.sqrt_pos.mpr he, Real.sq_sqrt he.le, ?_⟩
  rw [droLowerAAlpha, Real.sq_sqrt he.le]
  unfold droLowerAMultiplier
  linarith

-- @node: droLowerADual_lower
/-- If [the bulk weight is nonnegative](hyp:hn) and [the dual multiplier strictly
exceeds one plus the larger squared coefficient](hyp:heta), then [the scalar dual
value is at least the squared bulk height plus the squared error of the scaled
first-coordinate coefficient relative to the target](goal). -/
lemma droLowerADual_lower (n b c alpha beta eta : ℝ) (hn : 0 ≤ n)
    (heta : 1 + max (alpha ^ 2) (beta ^ 2) < eta) :
    (droLowerAHeight n b beta) ^ 2 + (alpha * c - b) ^ 2 ≤
      droLowerADual n b c alpha beta eta := by
  have hd : 0 < eta - 1 - alpha ^ 2 := by
    have := le_max_left (alpha ^ 2) (beta ^ 2)
    linarith
  have he : 0 < eta - 1 - beta ^ 2 := by
    have := le_max_right (alpha ^ 2) (beta ^ 2)
    linarith
  have hbulk := scalar_variational_lower (1 + beta ^ 2)
    (n * ((beta - b) ^ 2 + b ^ 2)) (eta - 1 - beta ^ 2)
    (by positivity) (by positivity) he
  rw [Real.sqrt_mul hn] at hbulk
  have hadd : 1 + beta ^ 2 + (eta - 1 - beta ^ 2) = eta := by ring
  rw [hadd] at hbulk
  have hratio : 1 ≤ eta / (eta - 1 - alpha ^ 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg alpha]
  calc
    (droLowerAHeight n b beta) ^ 2 + (alpha * c - b) ^ 2 ≤
        eta * (1 + n * ((beta - b) ^ 2 + b ^ 2) / (eta - 1 - beta ^ 2)) +
          eta / (eta - 1 - alpha ^ 2) * (alpha * c - b) ^ 2 :=
      add_le_add hbulk (by nlinarith [sq_nonneg (alpha * c - b)])
    _ = droLowerADual n b c alpha beta eta := by unfold droLowerADual; ring

-- @node: droLowerAObjective_lower
/-- If [the bulk weight is nonnegative](hyp:hn), then [the scalar robust objective
is at least the nonnegative extended-real value of the squared bulk height plus
the squared error of the scaled first-coordinate coefficient relative to the target](goal). -/
lemma droLowerAObjective_lower (n b c alpha beta : ℝ) (hn : 0 ≤ n) :
    ENNReal.ofReal ((droLowerAHeight n b beta) ^ 2 + (alpha * c - b) ^ 2) ≤
      droLowerAObjective n b c alpha beta := by
  exact le_iInf fun eta => le_iInf fun heta =>
    ENNReal.ofReal_le_ofReal (droLowerADual_lower n b c alpha beta eta hn heta)

-- @node: droLowerAObjective_candidate
/-- If [the bulk weight is positive](hyp:hn) and [the target coefficient is
positive](hyp:hb), then [choosing the candidate first-coordinate coefficient and
setting the feature scaling factor to the target divided by that candidate makes
the scalar robust objective equal the squared bulk height, viewed as a nonnegative
extended-real number](goal). -/
lemma droLowerAObjective_candidate (n b beta : ℝ) (hn : 0 < n) (hb : 0 < b) :
    droLowerAObjective n b (b / droLowerAAlpha n b beta) (droLowerAAlpha n b beta) beta =
      ENNReal.ofReal ((droLowerAHeight n b beta) ^ 2) := by
  let alpha := droLowerAAlpha n b beta
  let etaStar := droLowerAMultiplier n b beta
  obtain ⟨halpha, halpha2, hbeta⟩ := droLowerAAlpha_properties n b beta hn hb
  change 0 < alpha at halpha
  change alpha ^ 2 = etaStar - 1 at halpha2
  change beta ^ 2 < alpha ^ 2 at hbeta
  have hres : alpha * (b / alpha) - b = 0 := by field_simp; ring
  have hvalue : etaStar * (1 + n * ((beta - b) ^ 2 + b ^ 2) /
      (etaStar - 1 - beta ^ 2)) = (droLowerAHeight n b beta) ^ 2 := by
    have hh := scalar_variational_attainment (1 + beta ^ 2)
      (n * ((beta - b) ^ 2 + b ^ 2)) (by positivity) (by positivity) (by positivity)
    have hd : etaStar - 1 - beta ^ 2 =
        Real.sqrt ((1 + beta ^ 2) * (n * ((beta - b) ^ 2 + b ^ 2))) := by
      dsimp [etaStar, droLowerAMultiplier]; ring
    rw [hd]
    simpa only [etaStar, droLowerAMultiplier, droLowerAHeight, Real.sqrt_mul hn.le] using hh
  let f : ℝ → ℝ≥0∞ := fun eta => ENNReal.ofReal
    (eta * (1 + n * ((beta - b) ^ 2 + b ^ 2) / (eta - 1 - beta ^ 2)))
  have hden : 0 < etaStar - 1 - beta ^ 2 := by linarith
  have hcont : ContinuousAt f etaStar := by
    dsimp [f]
    apply ENNReal.continuous_ofReal.continuousAt.comp
    fun_prop (disch := linarith)
  have hmem : etaStar ∈ closure (Set.Ioi etaStar) := by
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hbound : ∀ eta ∈ Set.Ioi etaStar,
      droLowerAObjective n b (b / alpha) alpha beta ≤ f eta := by
    intro eta heta
    have hfeas : 1 + max (alpha ^ 2) (beta ^ 2) < eta := by
      rw [max_eq_left hbeta.le]
      change etaStar < eta at heta
      linarith
    refine (iInf_le_of_le eta (iInf_le_of_le hfeas le_rfl)).trans_eq ?_
    simp [droLowerADual, hres, f]
  have hmaps : Set.MapsTo f (Set.Ioi etaStar)
      (Set.Ici (droLowerAObjective n b (b / alpha) alpha beta)) := hbound
  have hlimit := hcont.continuousWithinAt.mem_closure hmem hmaps
  rw [closure_Ici] at hlimit
  change droLowerAObjective n b (b / alpha) alpha beta ≤ f etaStar at hlimit
  have hlow := droLowerAObjective_lower n b (b / alpha) alpha beta hn.le
  simp only [hres, zero_pow (by decide : 2 ≠ 0), add_zero] at hlow
  exact le_antisymm (by simpa only [f, hvalue] using hlimit) hlow

-- @node: droLowerAObjective_minimizer_first_coordinate
/-- If [the bulk weight is positive](hyp:hn), [the target coefficient is
positive](hyp:hb), [the reference bulk coefficient globally minimizes the bulk
height](hyp:hbulk), and [a coefficient pair has scalar robust objective no larger
than the candidate pair when the feature scaling factor is the target divided by
the reference candidate first-coordinate coefficient](hyp:hmin), then [that pair's
first-coordinate coefficient equals the reference candidate first-coordinate coefficient](goal). -/
lemma droLowerAObjective_minimizer_first_coordinate (n b betaStar alpha beta : ℝ)
    (hn : 0 < n) (hb : 0 < b)
    (hbulk : ∀ gamma : ℝ, droLowerAHeight n b betaStar ≤ droLowerAHeight n b gamma)
    (hmin : droLowerAObjective n b (b / droLowerAAlpha n b betaStar) alpha beta ≤
      droLowerAObjective n b (b / droLowerAAlpha n b betaStar)
        (droLowerAAlpha n b betaStar) betaStar) :
    alpha = droLowerAAlpha n b betaStar := by
  let alphaStar := droLowerAAlpha n b betaStar
  have hstar : 0 < alphaStar := (droLowerAAlpha_properties n b betaStar hn hb).1
  have hc : 0 < b / alphaStar := div_pos hb hstar
  rw [droLowerAObjective_candidate n b betaStar hn hb] at hmin
  have hlower := droLowerAObjective_lower n b (b / alphaStar) alpha beta hn.le
  have hr := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (droLowerAHeight n b betaStar))).mp
    (hlower.trans hmin)
  have hsquare : (droLowerAHeight n b betaStar) ^ 2 ≤ (droLowerAHeight n b beta) ^ 2 :=
    pow_le_pow_left₀ (droLowerAHeight_nonneg n b betaStar) (hbulk beta) 2
  have hzero : alpha * (b / alphaStar) - b = 0 := by
    nlinarith [sq_nonneg (alpha * (b / alphaStar) - b)]
  apply (mul_left_inj' hc.ne').mp
  calc
    alpha * (b / alphaStar) = b := sub_eq_zero.mp hzero
    _ = alphaStar * (b / alphaStar) := by field_simp

-- @node: droLowerA_parameters
/-- If [the bulk weight is at least 64](hyp:hn), [the target coefficient is
positive](hyp:hb), and [the bulk coefficient globally minimizes the bulk
height](hyp:hmin), then [the candidate first-coordinate coefficient is positive,
its square is at least half the squared target times the square root of the bulk
weight, and it is at least twice the target; the target divided by it lies between
zero exclusively and one half inclusively, and its squared deviation from the
target is at least one eighth of the squared target times the square root of the
bulk weight](goal). -/
lemma droLowerA_parameters (n b beta : ℝ) (hn : 64 ≤ n) (hb : 0 < b)
    (hmin : ∀ gamma : ℝ, droLowerAHeight n b beta ≤ droLowerAHeight n b gamma) :
    let alpha := droLowerAAlpha n b beta
    0 < alpha ∧ (b ^ 2 / 2) * Real.sqrt n ≤ alpha ^ 2 ∧
      2 * b ≤ alpha ∧ 0 < b / alpha ∧ b / alpha ≤ 1 / 2 ∧
      (b ^ 2 / 8) * Real.sqrt n ≤ (alpha - b) ^ 2 := by
  dsimp
  have hn0 : 0 < n := by linarith
  have hbeta := droLowerAHeight_minimizer_gt_half n b beta hn hb hmin
  obtain ⟨ha, ha2, hba⟩ := droLowerAAlpha_properties n b beta hn0 hb
  have hu : b / 2 ≤ Real.sqrt (1 + beta ^ 2) := by
    have hu2 := Real.sq_sqrt (show 0 ≤ 1 + beta ^ 2 by positivity)
    nlinarith [Real.sqrt_nonneg (1 + beta ^ 2)]
  have hv : b ≤ Real.sqrt ((beta - b) ^ 2 + b ^ 2) := by
    have hv2 := Real.sq_sqrt (show 0 ≤ (beta - b) ^ 2 + b ^ 2 by positivity)
    nlinarith [Real.sqrt_nonneg ((beta - b) ^ 2 + b ^ 2), sq_nonneg (beta - b)]
  have hprod : b ^ 2 / 2 * Real.sqrt n ≤
      Real.sqrt ((1 + beta ^ 2) * (n * ((beta - b) ^ 2 + b ^ 2))) := by
    rw [Real.sqrt_mul (show 0 ≤ 1 + beta ^ 2 by positivity), Real.sqrt_mul hn0.le]
    calc
      _ = (b / 2) * (Real.sqrt n * b) := by ring
      _ ≤ Real.sqrt (1 + beta ^ 2) *
          (Real.sqrt n * Real.sqrt ((beta - b) ^ 2 + b ^ 2)) := by
        gcongr
  have halower : b ^ 2 / 2 * Real.sqrt n ≤ (droLowerAAlpha n b beta) ^ 2 := by
    rw [ha2]
    unfold droLowerAMultiplier
    nlinarith [sq_nonneg beta]
  have hnroot : 8 ≤ Real.sqrt n := by
    have hr2 := Real.sq_sqrt hn0.le
    nlinarith [Real.sqrt_nonneg n]
  have htwo : 2 * b ≤ droLowerAAlpha n b beta := by
    have hh := mul_le_mul_of_nonneg_left hnroot (by positivity : 0 ≤ b ^ 2 / 2)
    nlinarith
  refine ⟨ha, halower, htwo, div_pos hb ha, ?_, ?_⟩
  · apply (div_le_iff₀ ha).mpr
    linarith
  · have hquarter : (droLowerAAlpha n b beta) ^ 2 / 4 ≤
        (droLowerAAlpha n b beta - b) ^ 2 := by
      nlinarith [sq_nonneg (droLowerAAlpha n b beta / 2 - b)]
    linarith

-- @node: droLowerA_scalar_certificate
/-- If [the bulk weight is at least 64](hyp:hn) and [the target coefficient is
positive](hyp:hb), then [there exist a first-coordinate coefficient, a bulk
coefficient, and a feature scaling factor strictly above zero and at most one
half such that the coefficient pair globally minimizes the scalar robust
objective, every global minimizer has the same first-coordinate coefficient,
and its squared deviation from the target is at least one eighth of the squared
target times the square root of the bulk weight](goal). -/
lemma droLowerA_scalar_certificate (n b : ℝ) (hn : 64 ≤ n) (hb : 0 < b) :
    ∃ alpha beta c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      IsMinOn (fun v : ℝ × ℝ => droLowerAObjective n b c v.1 v.2) Set.univ (alpha, beta) ∧
      (∀ v : ℝ × ℝ,
        IsMinOn (fun w : ℝ × ℝ => droLowerAObjective n b c w.1 w.2) Set.univ v →
          v.1 = alpha) ∧
      (b ^ 2 / 8) * Real.sqrt n ≤ (alpha - b) ^ 2 := by
  obtain ⟨beta, hbulk⟩ := droLowerAHeight_exists_minimizer n b
  obtain ⟨ha, halower, htwo, hc, hchalf, hreg⟩ := droLowerA_parameters n b beta hn hb hbulk
  have hn0 : 0 < n := by linarith
  refine ⟨droLowerAAlpha n b beta, beta, b / droLowerAAlpha n b beta, hc, hchalf, ?_, ?_, hreg⟩
  · intro v _
    change droLowerAObjective n b (b / droLowerAAlpha n b beta)
      (droLowerAAlpha n b beta) beta ≤ droLowerAObjective n b (b / droLowerAAlpha n b beta) v.1 v.2
    rw [droLowerAObjective_candidate n b beta hn0 hb]
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      (droLowerAObjective_lower n b (b / droLowerAAlpha n b beta) v.1 v.2 hn0.le)
    have hs := pow_le_pow_left₀ (droLowerAHeight_nonneg n b beta) (hbulk v.2) 2
    exact hs.trans (le_add_of_nonneg_right (sq_nonneg _))
  · intro v hv
    have hcompare := hv (Set.mem_univ (droLowerAAlpha n b beta, beta))
    change droLowerAObjective n b (b / droLowerAAlpha n b beta) v.1 v.2 ≤
      droLowerAObjective n b (b / droLowerAAlpha n b beta)
        (droLowerAAlpha n b beta) beta at hcompare
    exact droLowerAObjective_minimizer_first_coordinate n b beta v.1 v.2 hn0 hb hbulk
      hcompare

-- @node: droLowerA_scalar_regret
/-- If [the dimension is at least 65](hyp:hq) and [the condition parameter exceeds
one](hyp:hkappa), then [with target equal to the square root of half the excess of
the condition parameter over one, there exist a feature scaling factor strictly above zero
and at most one half and a globally minimizing coefficient pair for the scalar
robust objective with bulk weight equal to dimension minus one; every global
minimizer has the same first-coordinate coefficient, whose squared deviation
from the target is at least one thirty-second times the square root of dimension
times the excess of the condition parameter over one](goal). -/
lemma droLowerA_scalar_regret (q : ℕ) (hq : 65 ≤ q) (kappa : ℝ) (hkappa : 1 < kappa) :
    let b := Real.sqrt ((kappa - 1) / 2)
    ∃ alpha beta c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      IsMinOn (fun v : ℝ × ℝ => droLowerAObjective ((q : ℝ) - 1) b c v.1 v.2)
        Set.univ (alpha, beta) ∧
      (∀ v : ℝ × ℝ,
        IsMinOn (fun w : ℝ × ℝ => droLowerAObjective ((q : ℝ) - 1) b c w.1 w.2)
          Set.univ v → v.1 = alpha) ∧
      (1 / 32 : ℝ) * Real.sqrt q * (kappa - 1) ≤ (alpha - b) ^ 2 := by
  dsimp
  have hqr : (65 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 0 < Real.sqrt ((kappa - 1) / 2) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨alpha, beta, c, hc, hchalf, hmin, hall, hreg⟩ :=
    droLowerA_scalar_certificate ((q : ℝ) - 1) (Real.sqrt ((kappa - 1) / 2))
      (by linarith) hb
  refine ⟨alpha, beta, c, hc, hchalf, hmin, hall, ?_⟩
  have hb2 := Real.sq_sqrt (show 0 ≤ (kappa - 1) / 2 by linarith)
  have hroot : Real.sqrt q ≤ 2 * Real.sqrt ((q : ℝ) - 1) := by
    have hq2 := Real.sq_sqrt (Nat.cast_nonneg q)
    have hn2 := Real.sq_sqrt (show 0 ≤ (q : ℝ) - 1 by linarith)
    nlinarith [Real.sqrt_nonneg (q : ℝ), Real.sqrt_nonneg ((q : ℝ) - 1)]
  have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ kappa - 1 by linarith)
  rw [hb2] at hreg
  nlinarith

end Papers.WassersteinRegretS2S3
