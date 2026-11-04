module
public import Papers.WassersteinRegretS2S3.Helpers.FactorRegression
public import Papers.WassersteinRegretS2S3.Helpers.BuresGeometry

/-!
# Supremum estimates for factor perturbations

Uniform quadratic remainders survive maximization over a Frobenius ball.
The Bures ball is also expressed exactly using factor perturbations.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: derivativeSensitivity_radius_sup_error_bound
/-- For [a real-valued function f of factor perturbations](hyp:f), if
[r is positive](hyp:hr), [e is nonnegative](hyp:he), [f is nonnegative on the
Frobenius ball of radius r](hyp:hn), and [f differs from the derivative
sensitivity at Sigma by at most e throughout that ball](hyp:herr), then
[the supremum of f on the ball is finite and differs by at most e from r
squared times the supremum of derivative sensitivity on the unit ball](goal). -/
lemma derivativeSensitivity_radius_sup_error_bound {p m : ℕ} (Sigma : PSD (p + m))
    (f : Mat (p + m) (p + m) → ℝ) {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hn : ∀ D, frob D ≤ r → 0 ≤ f D)
    (herr : ∀ D, frob D ≤ r → |f D - derivativeSensitivity Sigma D| ≤ e) :
    (⨆ D, ⨆ (_ : frob D ≤ r), ENNReal.ofReal (f D)) ≠ ⊤ ∧
    |(⨆ D, ⨆ (_ : frob D ≤ r), ENNReal.ofReal (f D)).toReal -
      (⨆ D, ⨆ (_ : frob D ≤ 1),
        ENNReal.ofReal (derivativeSensitivity Sigma D)).toReal * r ^ 2| ≤ e := by
  obtain ⟨D, hD, hmax⟩ := derivativeSensitivity_attains_max Sigma
  have hnon : 0 ≤ derivativeSensitivity Sigma D := by
    unfold derivativeSensitivity
    positivity
  have hunit : (⨆ E, ⨆ (_ : frob E ≤ 1),
      ENNReal.ofReal (derivativeSensitivity Sigma E)) =
      ENNReal.ofReal (derivativeSensitivity Sigma D) := by
    apply le_antisymm
    · exact iSup_le fun E => iSup_le fun hE => ENNReal.ofReal_le_ofReal (hmax E hE)
    · exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hscaled : frob (r • D) ≤ r := by
    simpa [frob_eq_matrix_norm, norm_smul, abs_of_pos hr] using
      mul_le_mul_of_nonneg_left hD hr.le
  have hrad := derivativeSensitivity_radius_scaling Sigma r hr
  rw [hunit, ← ENNReal.ofReal_mul (sq_nonneg r)] at hrad
  have hu : (⨆ E, ⨆ (_ : frob E ≤ r), ENNReal.ofReal (f E)) ≤
      ENNReal.ofReal (r ^ 2 * derivativeSensitivity Sigma D + e) := by
    refine iSup_le fun E => iSup_le fun hE => ENNReal.ofReal_le_ofReal ?_
    have hb := (abs_le.mp (herr E hE)).2
    have hlead : derivativeSensitivity Sigma E ≤ r ^ 2 * derivativeSensitivity Sigma D := by
      have hl : ENNReal.ofReal (derivativeSensitivity Sigma E) ≤
          ENNReal.ofReal (r ^ 2 * derivativeSensitivity Sigma D) :=
        (le_iSup_of_le E (le_iSup_of_le hE le_rfl) :
          ENNReal.ofReal (derivativeSensitivity Sigma E) ≤
            ⨆ E, ⨆ (_ : frob E ≤ r), ENNReal.ofReal (derivativeSensitivity Sigma E)).trans_eq hrad
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hl
    linarith
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  refine ⟨hfinite, ?_⟩
  rw [hunit, ENNReal.toReal_ofReal hnon]
  have hupper := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at hupper
  have hlower := ENNReal.toReal_mono hfinite
    (le_iSup_of_le (r • D) (le_iSup_of_le hscaled le_rfl) :
      ENNReal.ofReal (f (r • D)) ≤ ⨆ E, ⨆ (_ : frob E ≤ r), ENNReal.ofReal (f E))
  rw [ENNReal.toReal_ofReal (hn _ hscaled)] at hlower
  have hb := (abs_le.mp (herr (r • D) hscaled)).1
  rw [derivativeSensitivity_smul] at hb
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

-- @node: factor_loss_sup_uniform_taylor
/-- If [K is compact](hyp:hK) and [eta is positive](hyp:heta), [there is a
positive radius threshold such that, uniformly over second moments in K and
positive radii below that threshold, the supremum of squared prediction loss
over factor perturbations in the radius-r Frobenius ball is finite and differs
by at most eta times r squared from r squared times the supremum of derivative
sensitivity on the unit ball](goal). -/
lemma factor_loss_sup_uniform_taylor {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → ∀ S ∈ K,
      let V := ⨆ D : Mat (p + m) (p + m), ⨆ (_ : frob D ≤ r),
        ENNReal.ofReal (frob ((parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
          parameterMap (symOfPSD S.carrier.val)) *
          CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2)
      V ≠ ⊤ ∧ |V.toReal -
        (⨆ D, ⨆ (_ : frob D ≤ 1),
          ENNReal.ofReal (derivativeSensitivity S.carrier.val D)).toReal * r ^ 2| ≤
            eta * r ^ 2 := by
  obtain ⟨δ, hδ, hpoint⟩ := factor_squared_loss_uniform_taylor K hK heta
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ S hS
  apply derivativeSensitivity_radius_sup_error_bound S.carrier.val _ hr (by positivity)
  · intro D hD
    positivity
  · intro D hD
    exact (hpoint S hS D (hD.trans_lt hrδ)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (frob_nonneg D) hD 2) heta.le)

-- @node: alternativeValue_factor_sup
/-- For [nonnegative radius eps](hyp:eps), [the alternative value at Sigma
equals the supremum, over square-root factor perturbations of Frobenius norm
at most eps, of the regret at Sigma of the perturbed moment's canonical predictor](goal). -/
lemma alternativeValue_factor_sup {p m : ℕ} (Sigma : PSD (p + m)) (eps : ℝ≥0) :
    alternativeValue Sigma eps =
      ⨆ D : Mat (p + m) (p + m), ⨆ (_ : frob D ≤ eps),
        ENNReal.ofReal (matrixRegret
          (canonicalCoefficient (factorPerturbedMoment Sigma D).val) Sigma.val) := by
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => ?_
    obtain ⟨D, hD, heq⟩ := (buresProcrustes T Sigma).2.2.1 eps |>.mp hT
    have hfactor : T = factorPerturbedMoment Sigma D := Subtype.ext heq
    rw [hfactor]
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  · refine iSup_le fun D => iSup_le fun hD => ?_
    apply le_iSup_of_le (factorPerturbedMoment Sigma D)
    apply le_iSup_of_le
      ((buresProcrustes (factorPerturbedMoment Sigma D) Sigma).2.2.1 eps |>.mpr ⟨D, hD, rfl⟩)
    exact le_rfl

-- @node: alternativeValue_uniform_taylor
/-- If [K is compact](hyp:hK) and [eta is positive](hyp:heta), [there is a
positive radius threshold such that, uniformly over second moments in K and
positive eps below that threshold, the alternative value is finite and differs
by at most eta times eps squared from eps squared times the supremum of
derivative sensitivity on the unit Frobenius ball](goal). -/
lemma alternativeValue_uniform_taylor {p m : ℕ} [NeZero p] [NeZero m]
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ eps : ℝ≥0, 0 < eps → (eps : ℝ) < δ → ∀ S ∈ K,
      alternativeValue S.carrier.val eps ≠ ⊤ ∧
      |(alternativeValue S.carrier.val eps).toReal -
        (⨆ D, ⨆ (_ : frob D ≤ 1),
          ENNReal.ofReal (derivativeSensitivity S.carrier.val D)).toReal * (eps : ℝ) ^ 2| ≤
            eta * (eps : ℝ) ^ 2 := by
  obtain ⟨δ₁, hδ₁, hloss⟩ := factor_loss_sup_uniform_taylor K hK heta
  obtain ⟨δ₂, hδ₂, hpos⟩ := factor_moments_uniform_posDef K hK
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro eps heps hepsδ S hS
  have h₁ : (eps : ℝ) < δ₁ := hepsδ.trans_le (min_le_left _ _)
  have h₂ : (eps : ℝ) < δ₂ := hepsδ.trans_le (min_le_right _ _)
  have heq : alternativeValue S.carrier.val eps =
      ⨆ D : Mat (p + m) (p + m), ⨆ (_ : frob D ≤ eps),
        ENNReal.ofReal (frob ((parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
          parameterMap (symOfPSD S.carrier.val)) *
          CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2) := by
    rw [alternativeValue_factor_sup]
    apply iSup_congr
    intro D
    apply iSup_congr
    intro hD
    rw [matrixRegret_feature_sqrt,
      canonicalCoefficient_eq_parameterMap _ (hpos S hS D (hD.trans_lt h₂)),
      canonicalCoefficient_eq_parameterMap _ S.carrier.property]
  rw [heq]
  exact hloss eps (by exact_mod_cast heps) h₁ S hS

end Papers.WassersteinRegretS2S3
