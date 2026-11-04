module
public import Papers.WassersteinRegretS2S3.Helpers.Scalar
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Scalar certificate for the second DRO lower bound

The dual objective has a pole at the candidate multiplier. Its value at the
candidate coefficient is obtained as a right limit, rather than by inserting
an infeasible multiplier. The uniqueness statement applies to every minimizer.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open scoped ENNReal NNReal

-- @node: droLowerBDual
/-- For [noise level N](hyp:N), [signal a](hyp:a), [loading c](hyp:c),
[coefficient alpha](hyp:alpha), and [multiplier eta](hyp:eta), the [scalar dual
value](goal) is eta times the sum of one, the squared residual alpha times c
minus a divided by eta minus one minus alpha squared, and N divided by eta minus one. -/
noncomputable def droLowerBDual (N a c alpha eta : ℝ) : ℝ :=
  eta * (1 + (alpha * c - a) ^ 2 / (eta - 1 - alpha ^ 2) + N / (eta - 1))

-- @node: droLowerBObjective
/-- For [noise level N](hyp:N), [signal a](hyp:a), [loading c](hyp:c), and
[coefficient alpha](hyp:alpha), the [scalar DRO objective](goal) is the infimum
of the nonnegative dual values over multipliers strictly above one plus alpha squared. -/
noncomputable def droLowerBObjective (N a c alpha : ℝ) : ℝ≥0∞ :=
  ⨅ (eta : ℝ) (_ : 1 + alpha ^ 2 < eta), ENNReal.ofReal (droLowerBDual N a c alpha eta)

-- @node: droLowerBDual_lower
/-- If [N is positive](hyp:hN) and [eta exceeds one plus alpha squared](hyp:heta),
[the dual value is at least the square of one plus the square root of N, plus
the squared residual alpha times c minus a](goal). -/
lemma droLowerBDual_lower (N a c alpha eta : ℝ) (hN : 0 < N)
    (heta : 1 + alpha ^ 2 < eta) :
    (1 + Real.sqrt N) ^ 2 + (alpha * c - a) ^ 2 ≤
      droLowerBDual N a c alpha eta := by
  have hd : 0 < eta - 1 - alpha ^ 2 := by linarith
  have he : 0 < eta - 1 := by nlinarith [sq_nonneg alpha]
  have hbulk := scalar_variational_lower 1 N (eta - 1) zero_le_one hN.le he
  simp only [Real.sqrt_one, add_sub_cancel] at hbulk
  have hratio : 1 ≤ eta / (eta - 1 - alpha ^ 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg alpha]
  calc
    (1 + Real.sqrt N) ^ 2 + (alpha * c - a) ^ 2 ≤
        eta * (1 + N / (eta - 1)) +
          eta / (eta - 1 - alpha ^ 2) * (alpha * c - a) ^ 2 :=
      add_le_add hbulk (by nlinarith [sq_nonneg (alpha * c - a)])
    _ = droLowerBDual N a c alpha eta := by unfold droLowerBDual; ring

-- @node: droLowerBObjective_lower
/-- If [N is positive](hyp:hN), [the scalar DRO objective is at least the square
of one plus the square root of N, plus the squared residual alpha times c minus a](goal). -/
lemma droLowerBObjective_lower (N a c alpha : ℝ) (hN : 0 < N) :
    ENNReal.ofReal ((1 + Real.sqrt N) ^ 2 + (alpha * c - a) ^ 2) ≤
      droLowerBObjective N a c alpha := by
  exact le_iInf fun eta => le_iInf fun heta =>
    ENNReal.ofReal_le_ofReal (droLowerBDual_lower N a c alpha eta hN heta)

-- @node: droLowerBObjective_candidate
/-- If [N is positive](hyp:hN), [the scalar DRO objective at coefficient equal
to the fourth root of N and loading equal to a divided by that root is exactly
the square of one plus the square root of N](goal). -/
lemma droLowerBObjective_candidate (N a : ℝ) (hN : 0 < N) :
    droLowerBObjective N a (a / Real.sqrt (Real.sqrt N)) (Real.sqrt (Real.sqrt N)) =
      ENNReal.ofReal ((1 + Real.sqrt N) ^ 2) := by
  let alpha := Real.sqrt (Real.sqrt N)
  let etaStar := 1 + Real.sqrt N
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have halpha : 0 < alpha := Real.sqrt_pos.mpr hroot
  have halpha2 : alpha ^ 2 = Real.sqrt N := Real.sq_sqrt hroot.le
  have hres : alpha * (a / alpha) - a = 0 := by field_simp; ring
  have hvalue : etaStar * (1 + N / (etaStar - 1)) = (1 + Real.sqrt N) ^ 2 := by
    have hh := scalar_variational_attainment 1 N zero_le_one hN.le (by simpa using hN)
    simpa [etaStar] using hh
  let f : ℝ → ℝ≥0∞ := fun eta => ENNReal.ofReal (eta * (1 + N / (eta - 1)))
  have hcont : ContinuousAt f etaStar := by
    dsimp [f]
    apply ENNReal.continuous_ofReal.continuousAt.comp
    fun_prop (disch := dsimp [etaStar]; linarith)
  have hmem : etaStar ∈ closure (Set.Ioi etaStar) := by
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hbound : ∀ eta ∈ Set.Ioi etaStar,
      droLowerBObjective N a (a / alpha) alpha ≤ f eta := by
    intro eta heta
    have hfeas : 1 + alpha ^ 2 < eta := by
      simpa only [Set.mem_Ioi, etaStar, halpha2] using heta
    refine (iInf_le_of_le eta (iInf_le_of_le hfeas le_rfl)).trans_eq ?_
    simp [droLowerBDual, hres, f]
  have hmaps : Set.MapsTo f (Set.Ioi etaStar)
      (Set.Ici (droLowerBObjective N a (a / alpha) alpha)) := hbound
  have hlimit := hcont.continuousWithinAt.mem_closure hmem hmaps
  rw [closure_Ici] at hlimit
  change droLowerBObjective N a (a / alpha) alpha ≤ f etaStar at hlimit
  have hlow := droLowerBObjective_lower N a (a / alpha) alpha hN
  simp only [hres, zero_pow (by decide : 2 ≠ 0), add_zero] at hlow
  exact le_antisymm (by simpa only [f, hvalue] using hlimit) hlow

-- @node: droLowerBObjective_unique_minimizer
/-- If [N is positive](hyp:hN), [a is positive](hyp:ha), and [alpha minimizes
the scalar DRO objective over all coefficients when the loading is a divided
by the fourth root of N](hyp:hmin), then [alpha equals the fourth root of N](goal). -/
lemma droLowerBObjective_unique_minimizer (N a : ℝ) (hN : 0 < N) (ha : 0 < a)
    (alpha : ℝ)
    (hmin : ∀ beta : ℝ,
      droLowerBObjective N a (a / Real.sqrt (Real.sqrt N)) alpha ≤
        droLowerBObjective N a (a / Real.sqrt (Real.sqrt N)) beta) :
    alpha = Real.sqrt (Real.sqrt N) := by
  let alphaStar := Real.sqrt (Real.sqrt N)
  have hstar : 0 < alphaStar := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hN)
  have hc : 0 < a / alphaStar := div_pos ha hstar
  have hupper := hmin alphaStar
  rw [droLowerBObjective_candidate N a hN] at hupper
  have hlower := droLowerBObjective_lower N a (a / alphaStar) alpha hN
  have hr := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (1 + Real.sqrt N))).mp
    (hlower.trans hupper)
  have hzero : alpha * (a / alphaStar) - a = 0 := by
    nlinarith [sq_nonneg (alpha * (a / alphaStar) - a)]
  apply (mul_left_inj' hc.ne').mp
  calc
    alpha * (a / alphaStar) = a := sub_eq_zero.mp hzero
    _ = alphaStar * (a / alphaStar) := by field_simp

-- @node: droLowerBObjective_isMinOn_iff
/-- If [N is positive](hyp:hN) and [a is positive](hyp:ha), [alpha globally
minimizes the scalar DRO objective with loading a divided by the fourth root
of N if and only if alpha equals that root](goal). -/
lemma droLowerBObjective_isMinOn_iff (N a : ℝ) (hN : 0 < N) (ha : 0 < a)
    (alpha : ℝ) :
    IsMinOn (droLowerBObjective N a (a / Real.sqrt (Real.sqrt N))) Set.univ alpha ↔
      alpha = Real.sqrt (Real.sqrt N) := by
  constructor
  · intro hmin
    exact droLowerBObjective_unique_minimizer N a hN ha alpha
      (fun beta => hmin (Set.mem_univ beta))
  · rintro rfl beta _
    rw [droLowerBObjective_candidate N a hN]
    exact (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))).trans
      (droLowerBObjective_lower N a (a / Real.sqrt (Real.sqrt N)) beta hN)

-- @node: droLowerB_parameters
/-- If [s is positive](hyp:hs) and [N is positive](hyp:hN), [setting alpha-star
to the fourth root of N and a to half the smaller of the square root of s and
alpha-star gives positive a with square at most s, a positive ratio a to
alpha-star at most one half, and squared separation at least one quarter of
the square root of N](goal). -/
lemma droLowerB_parameters (s N : ℝ) (hs : 0 < s) (hN : 0 < N) :
    let alphaStar := Real.sqrt (Real.sqrt N)
    let a := (1 / 2 : ℝ) * min (Real.sqrt s) alphaStar
    0 < a ∧ a ^ 2 ≤ s ∧ 0 < a / alphaStar ∧ a / alphaStar ≤ 1 / 2 ∧
      (1 / 4 : ℝ) * Real.sqrt N ≤ (alphaStar - a) ^ 2 := by
  dsimp
  let alphaStar := Real.sqrt (Real.sqrt N)
  have hstar : 0 < alphaStar := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hN)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hmin : 0 < min (Real.sqrt s) alphaStar := lt_min hsqrt hstar
  have hleS := min_le_left (Real.sqrt s) alphaStar
  have hleA := min_le_right (Real.sqrt s) alphaStar
  have hstar2 : alphaStar ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg N)
  have hsqrt2 : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have ha : 0 < (1 / 2 : ℝ) * min (Real.sqrt s) alphaStar := by positivity
  refine ⟨ha, ?_, div_pos ha hstar, ?_, ?_⟩
  · nlinarith [sq_nonneg (Real.sqrt s - min (Real.sqrt s) alphaStar)]
  · apply (div_le_iff₀ hstar).mpr
    linarith
  · nlinarith [sq_nonneg (alphaStar / 2 - (1 / 2 : ℝ) * min (Real.sqrt s) alphaStar)]

-- @node: droLowerB_scalar_regret
/-- If [m is at least two](hyp:hm) and [s is positive](hyp:hs), [setting N to
m minus one times s, alpha-star to the fourth root of N, and a to half the
smaller of the square root of s and alpha-star gives positive a with square
at most s, a positive ratio a to alpha-star at most one half, and squared
separation at least one eighth of the square root of m times s](goal). -/
lemma droLowerB_scalar_regret (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (hs : 0 < s) :
    let N := ((m : ℝ) - 1) * s
    let alphaStar := Real.sqrt (Real.sqrt N)
    let a := (1 / 2 : ℝ) * min (Real.sqrt s) alphaStar
    0 < a ∧ a ^ 2 ≤ s ∧ 0 < a / alphaStar ∧ a / alphaStar ≤ 1 / 2 ∧
      (1 / 8 : ℝ) * Real.sqrt ((m : ℝ) * s) ≤ (alphaStar - a) ^ 2 := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : 0 < ((m : ℝ) - 1) * s := mul_pos (by linarith) hs
  obtain ⟨ha, ha2, hc, hc2, hreg⟩ := droLowerB_parameters s (((m : ℝ) - 1) * s) hs hN
  refine ⟨ha, ha2, hc, hc2, ?_⟩
  have hms : 0 ≤ (m : ℝ) * s := mul_nonneg (Nat.cast_nonneg m) hs.le
  have hcompare : Real.sqrt ((m : ℝ) * s) ≤ 2 * Real.sqrt (((m : ℝ) - 1) * s) := by
    have hleft := Real.sq_sqrt hms
    have hright := Real.sq_sqrt hN.le
    have hmN : (m : ℝ) * s ≤ 4 * (((m : ℝ) - 1) * s) := by
      nlinarith
    nlinarith [Real.sqrt_nonneg ((m : ℝ) * s), Real.sqrt_nonneg (((m : ℝ) - 1) * s)]
  exact (by linarith : (1 / 8 : ℝ) * Real.sqrt ((m : ℝ) * s) ≤
    (1 / 4 : ℝ) * Real.sqrt (((m : ℝ) - 1) * s)).trans hreg

end Papers.WassersteinRegretS2S3
