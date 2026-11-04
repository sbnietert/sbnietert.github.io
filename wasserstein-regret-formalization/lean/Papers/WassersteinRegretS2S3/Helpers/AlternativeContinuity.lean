module
public import Papers.WassersteinRegretS2S3.Helpers.AlternativeCondition
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of the alternative condition number

The compact Frobenius unit ball represents the sensitivity coefficient as a
continuous maximum, including at singular joint and residual moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: psd_sqrt_continuous
/-- [The positive semidefinite matrix square root varies continuously with its
positive semidefinite matrix argument, including at singular matrices](goal). -/
@[fun_prop] lemma psd_sqrt_continuous {n : ℕ} :
    Continuous (fun S : PSD n => CFC.sqrt S.val) := by
  open scoped Matrix.Norms.L2Operator in
    exact CFC.continuousOn_sqrt.comp_continuous continuous_subtype_val
      (fun S => S.property.nonneg)

-- @node: nondegenerateMoment_psd_continuous
/-- [The joint second-moment matrix varies continuously with the nondegenerate
second-moment object that represents it](goal). -/
@[fun_prop] lemma nondegenerateMoment_psd_continuous {p m : ℕ} :
    Continuous (fun S : NondegenerateSecondMoments p m => S.carrier.val) := by
  exact continuous_subtype_val.comp continuous_induced_dom

-- @node: parameterMap_fderiv_continuous_moments
/-- [The derivative of the regression parameter map varies continuously with
nondegenerate joint second moments](goal). -/
@[fun_prop] lemma parameterMap_fderiv_continuous_moments {p m : ℕ} :
    Continuous (fun S : NondegenerateSecondMoments p m =>
      fderiv ℝ (@parameterMap p m) (symOfPSD S.carrier.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  have hdiff := parameterMap_contDiffAt (symOfPSD S.carrier.val) S.carrier.property
  have hd := hdiff.continuousAt_fderiv (by norm_num)
  exact hd.comp (f := fun T : NondegenerateSecondMoments p m => symOfPSD T.carrier.val)
    nondegenerateMoment_sym_continuous.continuousAt

-- @node: derivativeSensitivity_joint_continuous
/-- [Derivative sensitivity is jointly continuous in nondegenerate second moments
and the matrix perturbation direction](goal). -/
@[fun_prop] lemma derivativeSensitivity_joint_continuous {p m : ℕ} :
    Continuous (fun z : NondegenerateSecondMoments p m × Mat (p + m) (p + m) =>
      derivativeSensitivity z.1.carrier.val z.2) := by
  have hs : Continuous (fun S : NondegenerateSecondMoments p m =>
      CFC.sqrt S.carrier.val.val) := by
    exact psd_sqrt_continuous.comp nondegenerateMoment_psd_continuous
  have hx : Continuous (fun S : NondegenerateSecondMoments p m =>
      (⟨blockX p m S.carrier.val.val, S.carrier.property.posSemidef⟩ : PSD p)) := by
    apply Continuous.subtype_mk
    unfold blockX rawBlocks
    fun_prop
  have hw := psd_sqrt_continuous.comp hx
  have ht : Continuous (fun z : NondegenerateSecondMoments p m × Mat (p + m) (p + m) =>
      factorTangent z.1.carrier.val z.2) := by
    unfold factorTangent
    apply Continuous.subtype_mk
    exact ((hs.comp continuous_fst).matrix_mul continuous_snd.matrix_transpose).add
      (continuous_snd.matrix_mul (hs.comp continuous_fst))
  unfold derivativeSensitivity
  simp only [frob_eq_matrix_norm]
  exact (((rectangularMulCLM m p p).continuous.comp
    ((parameterMap_fderiv_continuous_moments.comp continuous_fst).clm_apply ht)).clm_apply
      (hw.comp continuous_fst)).norm.pow 2

-- @node: alternativeConditionNumber_continuous
/-- [The alternative condition number is continuous on the space of nondegenerate
second moments](goal). -/
@[fun_prop] lemma alternativeConditionNumber_continuous {p m : ℕ} [NeZero p] [NeZero m] :
    Continuous (@alternativeConditionNumber p m) := by
  let K := Metric.closedBall (0 : Mat (p + m) (p + m)) 1
  have hc : Continuous (fun S : NondegenerateSecondMoments p m =>
      sSup ((fun D => ENNReal.ofReal (derivativeSensitivity S.carrier.val D)) '' K)) :=
    (isCompact_closedBall _ _).continuous_sSup
      (ENNReal.continuous_ofReal.comp derivativeSensitivity_joint_continuous)
  convert hc using 1
  funext S
  rw [(altConditionNumberFormula (pin1_proved m)).1 S]
  simp only [sSup_image, K, Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm]

-- @node: factorPerturbedMoment_continuous
/-- For a fixed positive semidefinite matrix, [the second moment obtained by adding
a perturbation to its square-root factor and multiplying by the transpose is
continuous in the perturbation](goal). -/
@[fun_prop] lemma factorPerturbedMoment_continuous {n : ℕ} (S : PSD n) :
    Continuous (factorPerturbedMoment S) := by
  unfold factorPerturbedMoment
  fun_prop

-- @node: nondegenerateMoment_continuous_lift
/-- If [a family of positive semidefinite joint moments is continuous](hyp:hf) and
[its feature block is positive definite at every index](hyp:hp), then [viewing the
family as nondegenerate second moments preserves continuity](goal). -/
@[fun_prop] lemma nondegenerateMoment_continuous_lift {α : Type*} [TopologicalSpace α]
    {p m : ℕ} (f : α → PSD (p + m)) (hf : Continuous f)
    (hp : ∀ x, (blockX p m (f x).val).PosDef) :
    Continuous (fun x => (⟨⟨f x, hp x⟩⟩ : NondegenerateSecondMoments p m)) := by
  exact continuous_induced_rng.mpr (hf.subtype_mk _)

-- @node: nondegenerateMoment_factor_chart
/-- Around any nondegenerate second moments, [there is a positive-radius closed
Frobenius ball of factor perturbations and a continuous map from that ball to
nondegenerate second moments, whose joint moment matrix is exactly the perturbed
square-root factor times its transpose](goal). -/
lemma nondegenerateMoment_factor_chart {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Metric.closedBall (0 : Mat (p + m) (p + m)) r →
      NondegenerateSecondMoments p m, Continuous F ∧
      (∀ D, (F D).carrier.val = factorPerturbedMoment S.carrier.val D.val) := by
  obtain ⟨δ, hδ, hp⟩ := factor_moments_uniform_posDef {S} isCompact_singleton
  have hpos (D : Metric.closedBall (0 : Mat (p + m) (p + m)) (δ / 2)) :
      (blockX p m (factorPerturbedMoment S.carrier.val D.val).val).PosDef := by
    apply hp S (Set.mem_singleton S) D.val
    have hn : frob D.val ≤ δ / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using D.property
    linarith
  refine ⟨δ / 2, half_pos hδ,
    fun D => ⟨⟨factorPerturbedMoment S.carrier.val D.val, hpos D⟩⟩, ?_, fun _ => rfl⟩
  exact nondegenerateMoment_continuous_lift _
    ((factorPerturbedMoment_continuous S.carrier.val).comp continuous_subtype_val) _

-- @node: bures_moments_compact_localization
/-- For any nondegenerate second moments, [there are a positive radius and a compact
set of nondegenerate second moments containing representatives of every matrix in
each Bures ball about those moments with radius no larger than that radius](goal). -/
lemma bures_moments_compact_localization {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : Set (NondegenerateSecondMoments p m), IsCompact K ∧
      ∀ eps : ℝ≥0, (eps : ℝ) ≤ r → ∀ T ∈ matrixBall S.carrier.val eps,
        ∃ U ∈ K, U.carrier.val = T := by
  obtain ⟨r, hr, F, hF, hfactor⟩ := nondegenerateMoment_factor_chart S
  let : CompactSpace (Metric.closedBall (0 : Mat (p + m) (p + m)) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  refine ⟨r, hr, Set.range F, isCompact_range hF, ?_⟩
  intro eps heps T hT
  obtain ⟨D, hD, heq⟩ := (buresProcrustes T S.carrier.val).2.2.1 eps |>.mp hT
  have hd : D ∈ Metric.closedBall (0 : Mat (p + m) (p + m)) r := by
    simpa only [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using hD.trans heps
  refine ⟨F ⟨D, hd⟩, Set.mem_range_self _, ?_⟩
  rw [hfactor]
  exact Subtype.ext heq.symm

-- @node: bures_moments_eventually_mem
/-- If [a set is a neighborhood of given nondegenerate second moments](hyp:hU), then
[there is a positive radius such that every matrix in any strictly smaller Bures
ball about those moments has a nondegenerate representative in that neighborhood](goal). -/
lemma bures_moments_eventually_mem {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) (U : Set (NondegenerateSecondMoments p m))
    (hU : U ∈ nhds S) :
    ∃ r : ℝ, 0 < r ∧ ∀ eps : ℝ≥0, (eps : ℝ) < r →
      ∀ T ∈ matrixBall S.carrier.val eps, ∃ V ∈ U, V.carrier.val = T := by
  obtain ⟨r, hr, F, hF, hfactor⟩ := nondegenerateMoment_factor_chart S
  let D0 : Metric.closedBall (0 : Mat (p + m) (p + m)) r :=
    ⟨0, by simpa using hr.le⟩
  have hzero : F D0 = S := by
    have hv := hfactor D0
    have heq : factorPerturbedMoment S.carrier.val D0.val = S.carrier.val := by
      apply Subtype.ext
      simpa only [D0, factorPerturbedMoment, add_zero] using (psd_sqrt_factor S.carrier.val).symm
    have hc : (F D0).carrier = S.carrier := Subtype.ext (hv.trans heq)
    exact congrArg NondegenerateSecondMoments.mk hc
  have hev : ∀ᶠ D in nhds D0, F D ∈ U := by
    rw [← hzero] at hU
    exact hF.continuousAt.eventually hU
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro eps heps T hT
  obtain ⟨D, hD, heq⟩ := (buresProcrustes T S.carrier.val).2.2.1 eps |>.mp hT
  have hd : D ∈ Metric.closedBall (0 : Mat (p + m) (p + m)) r := by
    simpa only [Metric.mem_closedBall, dist_zero_right, ← frob_eq_matrix_norm] using
      hD.trans (heps.trans_le (min_le_left _ _)).le
  refine ⟨F ⟨D, hd⟩, hb ?_, ?_⟩
  · change dist D 0 < δ
    simpa only [dist_zero_right, ← frob_eq_matrix_norm] using
      hD.trans_lt (heps.trans_le (min_le_right _ _))
  · rw [hfactor]
    exact Subtype.ext heq.symm

-- @node: alternativeConditionNumber_ne_top
/-- [The alternative condition number of any nondegenerate second moments is
finite](goal). -/
lemma alternativeConditionNumber_ne_top {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) : alternativeConditionNumber S ≠ ⊤ := by
  rw [(altConditionNumberFormula (pin1_proved m)).1 S]
  exact derivativeSensitivity_sup_ne_top S.carrier.val

-- @node: alternativeConditionNumber_toReal_continuous
/-- [The real-valued alternative condition number varies continuously over
nondegenerate second moments](goal). -/
@[fun_prop] lemma alternativeConditionNumber_toReal_continuous
    {p m : ℕ} [NeZero p] [NeZero m] :
    Continuous (fun S : NondegenerateSecondMoments p m =>
      (alternativeConditionNumber S).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  exact (ENNReal.continuousAt_toReal (alternativeConditionNumber_ne_top S)).comp
    alternativeConditionNumber_continuous.continuousAt

-- @node: nearby_alternativeValue_eventual_upper
/-- For nondegenerate second moments and [a positive tolerance](hyp:he), [at all
sufficiently small positive radii, the supremum of the alternative value over the
Bures ball of that radius is at most the squared radius times the sum of the
central alternative condition number and the tolerance](goal). -/
lemma nearby_alternativeValue_eventual_upper {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) {e : ℝ} (he : 0 < e) :
    ∀ᶠ eps : ℝ≥0 in positiveRadii,
      (⨆ T ∈ matrixBall S.carrier.val eps, alternativeValue T eps) ≤
        ENNReal.ofReal (((alternativeConditionNumber S).toReal + e) * (eps : ℝ) ^ 2) := by
  obtain ⟨r, hr, K, hK, hcover⟩ := bures_moments_compact_localization S
  have hcoeff : {V : NondegenerateSecondMoments p m |
      (alternativeConditionNumber V).toReal < (alternativeConditionNumber S).toReal + e / 2}
      ∈ nhds S :=
    alternativeConditionNumber_toReal_continuous.continuousAt.eventually
      (eventually_lt_nhds (by linarith : (alternativeConditionNumber S).toReal <
        (alternativeConditionNumber S).toReal + e / 2))
  obtain ⟨s, hs, hnear⟩ := bures_moments_eventually_mem S _ hcoeff
  have htaylor := (altConditionNumberFormula (pin1_proved m)).2 K hK (e / 2) (half_pos he)
  have hrad : Filter.Tendsto (fun eps : ℝ≥0 => (eps : ℝ)) positiveRadii (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [htaylor, hrad.eventually (eventually_lt_nhds hr),
    hrad.eventually (eventually_lt_nhds hs)] with eps ht hepsr hepss
  refine iSup_le fun T => iSup_le fun hT => ?_
  obtain ⟨V, hVK, hVT⟩ := hcover eps hepsr.le T hT
  obtain ⟨W, hW, hWT⟩ := hnear eps hepss T hT
  have hWV : W = V := congrArg NondegenerateSecondMoments.mk
    (Subtype.ext (hWT.trans hVT.symm))
  subst W
  have hb := ht V hVK
  rw [← hVT]
  rw [← ENNReal.ofReal_toReal hb.1]
  apply ENNReal.ofReal_le_ofReal
  have herr := (abs_le.mp hb.2.2).2
  have hc : (alternativeConditionNumber V).toReal ≤
      (alternativeConditionNumber S).toReal + e / 2 := hW.le
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg (eps : ℝ))
  nlinarith

-- @node: nearby_alternative_limsup_le
/-- For nondegenerate second moments, [the upper limit, as the positive radius tends
to zero, of the supremum of alternative values over the Bures ball divided by the
squared radius is at most the alternative condition number at the center](goal). -/
lemma nearby_alternative_limsup_le {p m : ℕ} [NeZero p] [NeZero m]
    (S : NondegenerateSecondMoments p m) :
    Filter.limsup (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 *
      ⨆ T ∈ matrixBall S.carrier.val eps, alternativeValue T eps) positiveRadii ≤
        alternativeConditionNumber S := by
  apply ENNReal.le_of_forall_pos_le_add
  intro e he _
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  have hb := nearby_alternativeValue_eventual_upper S he'
  have hpos : ∀ᶠ eps : ℝ≥0 in positiveRadii, 0 < eps := self_mem_nhdsWithin
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hb, hpos] with eps hb heps
  have hz : (eps : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt heps
  have hscale : (eps : ℝ≥0∞)⁻¹ ^ 2 * ENNReal.ofReal
      (((alternativeConditionNumber S).toReal + (e : ℝ)) * (eps : ℝ) ^ 2) =
        alternativeConditionNumber S + e := by
    rw [ENNReal.ofReal_mul (p := (alternativeConditionNumber S).toReal + (e : ℝ))
      (q := (eps : ℝ) ^ 2) (by positivity)]
    simp only [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
    rw [mul_comm, mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hz ENNReal.coe_ne_top,
      one_pow, mul_one, ENNReal.ofReal_add (p := (alternativeConditionNumber S).toReal)
        (q := (e : ℝ)) ENNReal.toReal_nonneg e.property,
      ENNReal.ofReal_toReal (alternativeConditionNumber_ne_top S), ENNReal.ofReal_coe_nnreal]
  exact (mul_le_mul' le_rfl hb).trans_eq hscale

end Papers.WassersteinRegretS2S3
