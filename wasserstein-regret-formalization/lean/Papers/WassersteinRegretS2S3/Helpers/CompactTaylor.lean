module
public import Papers.WassersteinRegretS2S3.Helpers.FactorTaylor
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniform Taylor estimates on compact sets of nondegenerate moments

The continuously differentiable parameter map has a first order remainder
uniform in the base moment, including moments with singular response blocks.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

set_option maxHeartbeats 800000 in
-- @node: parameterMap_uniform_taylor
/-- If [a set of symmetric joint moment matrices is compact](hyp:hK) and [each matrix
has a positive definite feature block](hyp:hpos), then for [any positive error
tolerance](hyp:he), [all sufficiently small symmetric perturbations have a first-order
Taylor remainder for the regression coefficient map bounded by that tolerance times
their Frobenius norm, uniformly over the set](goal). -/
lemma parameterMap_uniform_taylor {p m : ℕ}
    (K : Set (Sym (p + m))) (hK : IsCompact K)
    (hpos : ∀ S ∈ K, (blockX p m S.val).PosDef)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ H : Sym (p + m) in nhds 0, ∀ S ∈ K,
      frob (parameterMap (S + H) - parameterMap S -
        fderiv ℝ (@parameterMap p m) S H) ≤ e * frob H.val := by
  letI : TopologicalSpace (Mat m p) :=
    (inferInstance : NormedAddCommGroup (Mat m p)).toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Sym (p + m)) :=
    (inferInstance : NormedAddCommGroup (Sym (p + m))).toUniformSpace.toTopologicalSpace
  letI : Module ℝ (Mat m p) := (inferInstance : NormedSpace ℝ (Mat m p)).toModule
  letI : Module ℝ (Sym (p + m)) :=
    (inferInstance : NormedSpace ℝ (Sym (p + m))).toModule
  letI : SeminormedAddCommGroup (Sym (p + m) →L[ℝ] Mat m p) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  apply hK.eventually_forall_of_forall_eventually
  intro S hS
  have hc := parameterMap_contDiffAt (p := p) (m := m) S (hpos S hS)
  have hstrict := (hc.hasStrictFDerivAt (by norm_num)).isLittleO.bound (half_pos he)
  have ht : Filter.Tendsto
      (fun z : Sym (p + m) × Sym (p + m) => (z.2 + z.1, z.2))
      (nhds (0, S)) (nhds (S, S)) := by
    have h : Continuous (fun z : Sym (p + m) × Sym (p + m) =>
        (z.2 + z.1, z.2)) := by fun_prop
    simpa using (h.continuousAt (x := (0, S))).tendsto
  have hrem := ht.eventually hstrict
  have hd := (hc.continuousAt_fderiv (by norm_num)).tendsto.eventually
    (Metric.ball_mem_nhds (fderiv ℝ (@parameterMap p m) S) (half_pos he))
  have hd' := (show Filter.Tendsto (fun z : Sym (p + m) × Sym (p + m) => z.2)
      (nhds (0, S)) (nhds S) from continuous_snd.continuousAt).eventually hd
  filter_upwards [hrem, hd'] with z hz hdS
  simp only [add_sub_cancel_left] at hz
  have hdiff : ‖fderiv ℝ (@parameterMap p m) z.2 -
      fderiv ℝ (@parameterMap p m) S‖ ≤ e / 2 := by
    rw [dist_eq_norm] at hdS
    exact hdS.le
  have hde := (fderiv ℝ (@parameterMap p m) z.2 -
    fderiv ℝ (@parameterMap p m) S).le_opNorm z.1
  have heq : parameterMap (z.2 + z.1) - parameterMap z.2 -
      fderiv ℝ (@parameterMap p m) z.2 z.1 =
      (parameterMap (z.2 + z.1) - parameterMap z.2 -
        fderiv ℝ (@parameterMap p m) S z.1) -
      (fderiv ℝ (@parameterMap p m) z.2 z.1 -
        fderiv ℝ (@parameterMap p m) S z.1) := by abel
  rw [frob_eq_matrix_norm]
  calc
    _ = ‖(parameterMap (z.2 + z.1) - parameterMap z.2 -
        fderiv ℝ (@parameterMap p m) S z.1) -
      (fderiv ℝ (@parameterMap p m) z.2 z.1 -
        fderiv ℝ (@parameterMap p m) S z.1)‖ := congrArg (fun A : Mat m p => ‖A‖) heq
    _ ≤ ‖parameterMap (z.2 + z.1) - parameterMap z.2 -
        fderiv ℝ (@parameterMap p m) S z.1‖ +
        ‖fderiv ℝ (@parameterMap p m) z.2 z.1 -
          fderiv ℝ (@parameterMap p m) S z.1‖ := norm_sub_le _ _
    _ ≤ (e / 2) * ‖z.1‖ + (e / 2) * ‖z.1‖ :=
      add_le_add hz (hde.trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)))
    _ = e * frob z.1.val := by rw [frob_eq_matrix_norm]; change _ = e * ‖z.1‖; ring

-- @node: parameterMap_compact_derivative_bound
/-- If [a set of symmetric joint moment matrices is compact](hyp:hK) and [every feature
block is positive definite](hyp:hpos), then [there is a nonnegative constant bounding
the Frobenius norm of the regression coefficient derivative applied to any symmetric
perturbation by that constant times the perturbation's Frobenius norm, uniformly over
the set](goal). -/
lemma parameterMap_compact_derivative_bound {p m : ℕ}
    (K : Set (Sym (p + m))) (hK : IsCompact K)
    (hpos : ∀ S ∈ K, (blockX p m S.val).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S ∈ K, ∀ H : Sym (p + m),
      frob (fderiv ℝ (@parameterMap p m) S H) ≤ C * frob H.val := by
  letI : TopologicalSpace (Mat m p) :=
    (inferInstance : NormedAddCommGroup (Mat m p)).toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (Sym (p + m)) :=
    (inferInstance : NormedAddCommGroup (Sym (p + m))).toUniformSpace.toTopologicalSpace
  letI : Module ℝ (Mat m p) := (inferInstance : NormedSpace ℝ (Mat m p)).toModule
  letI : Module ℝ (Sym (p + m)) :=
    (inferInstance : NormedSpace ℝ (Sym (p + m))).toModule
  letI : SeminormedAddCommGroup (Sym (p + m) →L[ℝ] Mat m p) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hc : ContinuousOn (fun S => ‖fderiv ℝ (@parameterMap p m) S‖) K := by
    intro S hS
    exact ((parameterMap_contDiffAt S (hpos S hS)).continuousAt_fderiv
      (by norm_num)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro S hS H
  calc
    _ = ‖fderiv ℝ (@parameterMap p m) S H‖ := frob_eq_matrix_norm _
    _ ≤ ‖fderiv ℝ (@parameterMap p m) S‖ * ‖H‖ :=
      (fderiv ℝ (@parameterMap p m) S).le_opNorm H
    _ ≤ max 0 C * ‖H‖ := mul_le_mul_of_nonneg_right
      ((hC (Set.mem_image_of_mem _ hS)).trans (le_max_right _ _)) (norm_nonneg _)
    _ = _ := by rw [frob_eq_matrix_norm]; rfl

-- @node: nondegenerateMoment_sym_continuous
/-- [Viewing a nondegenerate joint second moment as a symmetric matrix is a continuous
operation](goal). -/
@[fun_prop] lemma nondegenerateMoment_sym_continuous {p m : ℕ} :
    Continuous (fun S : NondegenerateSecondMoments p m => symOfPSD S.carrier.val) := by
  have hc : Continuous (fun S : NondegenerateSecondMoments p m => S.carrier) :=
    continuous_induced_dom
  exact (((continuous_subtype_val.comp continuous_subtype_val).comp hc).subtype_mk _)

set_option maxHeartbeats 800000 in
-- @node: parameterMap_uniform_taylor_moments
/-- For [a compact set of nondegenerate joint second moments](hyp:hK) and [a positive
error tolerance](hyp:he), [there is a positive perturbation radius such that the
regression coefficient map's first-order Taylor remainder is at most the tolerance
times the perturbation's Frobenius norm for every base moment in the set and every
symmetric perturbation smaller than that radius](goal). -/
lemma parameterMap_uniform_taylor_moments {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ K, ∀ H : Sym (p + m), frob H.val < δ →
      frob (parameterMap (symOfPSD S.carrier.val + H) -
        parameterMap (symOfPSD S.carrier.val) -
        fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val) H) ≤ e * frob H.val := by
  let f := fun S : NondegenerateSecondMoments p m => symOfPSD S.carrier.val
  have hk := hK.image nondegenerateMoment_sym_continuous
  have hp : ∀ S ∈ f '' K, (blockX p m S.val).PosDef := by
    rintro _ ⟨S, _, rfl⟩
    exact S.carrier.property
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp
    (parameterMap_uniform_taylor (f '' K) hk hp he)
  refine ⟨δ, hδ, ?_⟩
  intro S hS H hH
  apply hb (y := H) _ (f S) (Set.mem_image_of_mem f hS)
  simpa [dist_zero_right, frob_eq_matrix_norm] using hH

-- @node: compact_moment_sqrt_bound
/-- For [a compact set of nondegenerate joint second moments](hyp:hK), [there is a
nonnegative uniform upper bound on the Frobenius norms of their positive semidefinite
square roots](goal). -/
lemma compact_moment_sqrt_bound {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ S ∈ K, frob (CFC.sqrt S.carrier.val.val) ≤ R := by
  have hc : Continuous (fun S : NondegenerateSecondMoments p m =>
      Matrix.trace S.carrier.val.val) := by
    have hv := continuous_subtype_val.comp
      (nondegenerateMoment_sym_continuous (p := p) (m := m))
    have ht : Continuous (fun A : Mat (p + m) (p + m) => Matrix.trace A) := by
      unfold Matrix.trace
      fun_prop
    exact ht.comp hv
  obtain ⟨R, hR⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max 1 R, (by positivity), ?_⟩
  intro S hS
  have hs : frob (CFC.sqrt S.carrier.val.val) ^ 2 = Matrix.trace S.carrier.val.val := by
    rw [frob_sq_trace_rows, ← psd_sqrt_factor S.carrier.val]
  have ht : Matrix.trace S.carrier.val.val ≤ max 1 R :=
    (hR (Set.mem_image_of_mem _ hS)).trans (le_max_right _ _)
  have hbig : 1 ≤ max 1 R := le_max_left _ _
  nlinarith [sq_nonneg (max 1 R - 1)]

set_option maxHeartbeats 800000 in
-- @node: factor_parameterMap_uniform_taylor
/-- For [a compact set of nondegenerate joint second moments](hyp:hK) and [a positive
error tolerance](hyp:he), [there is a positive radius such that perturbing any moment's
square-root factor by a matrix smaller than that radius changes the regression
coefficient by its derivative along the induced first-order moment change, with a
Frobenius remainder at most the tolerance times the factor perturbation's Frobenius
norm, uniformly over the set](goal). -/
lemma factor_parameterMap_uniform_taylor {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ K, ∀ D : Mat (p + m) (p + m), frob D < δ →
      frob (parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
        parameterMap (symOfPSD S.carrier.val) -
        fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
          (factorTangent S.carrier.val D)) ≤ e * frob D := by
  let f := fun S : NondegenerateSecondMoments p m => symOfPSD S.carrier.val
  have hk := hK.image nondegenerateMoment_sym_continuous
  have hp : ∀ S ∈ f '' K, (blockX p m S.val).PosDef := by
    rintro _ ⟨S, _, rfl⟩
    exact S.carrier.property
  obtain ⟨C, hC, hder⟩ := parameterMap_compact_derivative_bound (f '' K) hk hp
  obtain ⟨R, hR, hroot⟩ := compact_moment_sqrt_bound K hK
  let L := 2 * R + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hCp : 0 < C + 1 := by positivity
  obtain ⟨r, hr, htaylor⟩ := parameterMap_uniform_taylor_moments K hK (e := e / (2 * L))
    (div_pos he (mul_pos (by norm_num) hL))
  refine ⟨min 1 (min (r / L) (e / (2 * (C + 1)))),
    lt_min (by norm_num) (lt_min (div_pos hr hL) (by positivity)), ?_⟩
  intro S hS D hD
  have hd := frob_nonneg D
  have hd1 : frob D ≤ 1 := (hD.trans_le (min_le_left _ _)).le
  have hdr : frob D < r / L :=
    hD.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdC : frob D ≤ e / (2 * (C + 1)) :=
    (hD.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  let H := symOfPSD (factorPerturbedMoment S.carrier.val D) - symOfPSD S.carrier.val
  have hH : frob H.val ≤ L * frob D := by
    have hb := factor_covariance_displacement_bound S.carrier.val D
    change frob ((CFC.sqrt S.carrier.val.val + D) *
      (CFC.sqrt S.carrier.val.val + D).transpose - S.carrier.val.val) ≤ _
    calc
      _ ≤ 2 * frob (CFC.sqrt S.carrier.val.val) * frob D + frob D ^ 2 := hb
      _ ≤ 2 * R * frob D + frob D ^ 2 := by
        gcongr <;> first
          | fun_prop
          | assumption
          | positivity
          | exact frob_nonneg _
          | exact hroot S hS
      _ ≤ L * frob D := by dsimp [L]; nlinarith
  have hHr : frob H.val < r :=
    hH.trans_lt ((lt_div_iff₀' hL).mp hdr)
  have ht := htaylor S hS H hHr
  have hsum : symOfPSD S.carrier.val + H =
      symOfPSD (factorPerturbedMoment S.carrier.val D) := by dsimp [H]; abel
  rw [hsum] at ht
  have hlin := factor_taylor_error_transfer S.carrier.val D hC
    (hder (f S) (Set.mem_image_of_mem _ hS)) ht
  have hsmall : C * frob D ≤ e / 2 := by
    have hb := (le_div_iff₀ (mul_pos (by norm_num) hCp)).mp hdC
    nlinarith
  calc
    _ ≤ e / (2 * L) * frob H.val + C * frob D ^ 2 := hlin
    _ ≤ e / (2 * L) * (L * frob D) + (e / 2) * frob D := by
      exact add_le_add (mul_le_mul_of_nonneg_left hH (by positivity))
        (by nlinarith [mul_le_mul_of_nonneg_right hsmall hd])
    _ = e * frob D := by field_simp; ring

-- @node: compact_feature_sqrt_bound
/-- For [a compact set of nondegenerate joint second moments](hyp:hK), [there is a
nonnegative uniform upper bound on the Frobenius norms of the positive semidefinite
square roots of their feature blocks](goal). -/
lemma compact_feature_sqrt_bound {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ S ∈ K, frob (CFC.sqrt (blockX p m S.carrier.val.val)) ≤ W := by
  have hv := continuous_subtype_val.comp
    (nondegenerateMoment_sym_continuous (p := p) (m := m))
  have hc : Continuous (fun S : NondegenerateSecondMoments p m =>
      Matrix.trace (blockX p m S.carrier.val.val)) := by
    change Continuous (fun S : NondegenerateSecondMoments p m =>
      Matrix.trace (blockX p m (symOfPSD S.carrier.val).val))
    unfold Matrix.trace blockX rawBlocks
    fun_prop
  obtain ⟨W, hW⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max 1 W, (by positivity), ?_⟩
  intro S hS
  have hs : frob (CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2 =
      Matrix.trace (blockX p m S.carrier.val.val) := by
    rw [frob_sq_trace_rows]
    exact congrArg Matrix.trace
      (psd_sqrt_factor ⟨blockX p m S.carrier.val.val, S.carrier.property.posSemidef⟩).symm
  have ht : Matrix.trace (blockX p m S.carrier.val.val) ≤ max 1 W :=
    (hW (Set.mem_image_of_mem _ hS)).trans (le_max_right _ _)
  have hbig : 1 ≤ max 1 W := le_max_left _ _
  nlinarith [sq_nonneg (max 1 W - 1)]

set_option maxHeartbeats 800000 in
-- @node: factor_squared_loss_uniform_taylor
/-- For [a compact set of nondegenerate joint second moments](hyp:hK) and [a positive
error tolerance](hyp:heta), [there is a positive factor-perturbation radius such that
the squared Frobenius norm of the resulting coefficient change weighted by the
original feature square root differs from derivative sensitivity by at most the
tolerance times the squared Frobenius norm of the factor perturbation, uniformly
over the set](goal). -/
lemma factor_squared_loss_uniform_taylor {p m : ℕ}
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ K, ∀ D : Mat (p + m) (p + m), frob D < δ →
      |frob ((parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
          parameterMap (symOfPSD S.carrier.val)) *
          CFC.sqrt (blockX p m S.carrier.val.val)) ^ 2 -
        derivativeSensitivity S.carrier.val D| ≤ eta * frob D ^ 2 := by
  let f := fun S : NondegenerateSecondMoments p m => symOfPSD S.carrier.val
  have hk := hK.image nondegenerateMoment_sym_continuous
  have hp : ∀ S ∈ f '' K, (blockX p m S.val).PosDef := by
    rintro _ ⟨S, _, rfl⟩
    exact S.carrier.property
  obtain ⟨C, hC, hder⟩ := parameterMap_compact_derivative_bound (f '' K) hk hp
  obtain ⟨R, hR, hroot⟩ := compact_moment_sqrt_bound K hK
  obtain ⟨W, hW, hweight⟩ := compact_feature_sqrt_bound K hK
  let B := C * (2 * R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let t := min 1 (eta / ((2 * B + 1) * (W ^ 2 + 1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have hteta : t * ((2 * B + 1) * (W ^ 2 + 1)) ≤ eta :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨δ, hδ, hfactor⟩ := factor_parameterMap_uniform_taylor K hK ht
  refine ⟨δ, hδ, ?_⟩
  intro S hS D hD
  let A := fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)
    (factorTangent S.carrier.val D)
  let E := parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
    parameterMap (symOfPSD S.carrier.val) - A
  let V := CFC.sqrt (blockX p m S.carrier.val.val)
  have hA : frob A ≤ B * frob D := by
    calc
      _ ≤ C * frob (factorTangent S.carrier.val D).val :=
        hder (f S) (Set.mem_image_of_mem _ hS) _
      _ ≤ C * (2 * frob (CFC.sqrt S.carrier.val.val) * frob D) :=
        mul_le_mul_of_nonneg_left (factorTangent_norm_bound _ _) hC
      _ ≤ C * (2 * R * frob D) := by
        gcongr <;> first
          | fun_prop
          | assumption
          | positivity
          | exact frob_nonneg _
          | exact hroot S hS
      _ = _ := by dsimp [B]; ring
  have hE : frob E ≤ t * frob D := hfactor S hS D hD
  have heq : parameterMap (symOfPSD (factorPerturbedMoment S.carrier.val D)) -
      parameterMap (symOfPSD S.carrier.val) = A + E := by dsimp [E]; abel
  have hloss := factor_scaled_squared_loss_remainder_bound A E V hB ht.le
    (frob_nonneg D) hA hE
  have hcoef : (2 * B * t + t ^ 2) * frob V ^ 2 ≤ eta := by
    calc
      _ ≤ ((2 * B + 1) * t) * (W ^ 2 + 1) := by
        apply mul_le_mul
        · nlinarith [mul_le_mul_of_nonneg_left ht1 ht.le]
        · exact (pow_le_pow_left₀ (frob_nonneg V) (hweight S hS) 2).trans
            (le_add_of_nonneg_right (by norm_num))
        · positivity
        · positivity
      _ = t * ((2 * B + 1) * (W ^ 2 + 1)) := by ring
      _ ≤ eta := hteta
  have hbound := hloss.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  change |frob ((_ - _) * V) ^ 2 - frob (A * V) ^ 2| ≤ _
  rw [heq]
  exact hbound

end Papers.WassersteinRegretS2S3
