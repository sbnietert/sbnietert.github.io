module
public import Papers.WassersteinRegretS2S3.Helpers.CompactTaylor
public import Papers.WassersteinRegretS2S3.Helpers.RegressionProjection

/-!
# Regression identities near nondegenerate factor moments

Small factor balls remain in the parameter domain, uniformly on compact sets.
Their squared prediction loss agrees with the original matrix regret.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: canonicalCoefficient_eq_parameterMap
/-- If [the feature block of Sigma is positive definite](hyp:hS), then
[the canonical regression coefficient of Sigma equals the regression parameter
map evaluated at the same symmetric second-moment matrix](goal). -/
lemma canonicalCoefficient_eq_parameterMap {p m : ℕ} (Sigma : PSD (p + m))
    (hS : (blockX p m Sigma.val).PosDef) :
    canonicalCoefficient Sigma.val = parameterMap (symOfPSD Sigma) := by
  unfold canonicalCoefficient parameterMap
  simp only [symOfPSD]
  congr 1
  apply isMoorePenroseInverse_unique (moorePenroseInverse_spec _)
  have hi := (Matrix.isUnit_iff_isUnit_det (blockX p m Sigma.val)).mp hS.isUnit
  have hl := Matrix.mul_nonsing_inv _ hi
  have hr := Matrix.nonsing_inv_mul _ hi
  exact ⟨by rw [hl, Matrix.one_mul], by rw [hr, Matrix.one_mul],
    by rw [hl, Matrix.transpose_one], by rw [hr, Matrix.transpose_one]⟩

-- @node: matrixRegret_feature_sqrt
/-- [The regret of A at Sigma equals the squared Frobenius norm of the
coefficient error relative to the canonical predictor, multiplied on the right
by the positive semidefinite square root of Sigma's feature block](goal). -/
lemma matrixRegret_feature_sqrt {p m : ℕ} [NeZero p] [NeZero m]
    (Sigma : PSD (p + m)) (A : Mat m p) :
    matrixRegret A Sigma.val =
      frob ((A - canonicalCoefficient Sigma.val) * CFC.sqrt (blockX p m Sigma.val)) ^ 2 := by
  have hf := psd_sqrt_factor Sigma
  have hp := regretProjectionFormula (pin1_proved m) assSingularValueConvention_valid
    Sigma (CFC.sqrt Sigma.val) hf
  have hreg := (hp.2.2.2.2.2.2 A).2.2
  rw [hreg, frob_sq_trace_rows, frob_sq_trace_rows]
  have hX := (factor_gram_blocks (CFC.sqrt Sigma.val)).1
  rw [← hf] at hX
  have hroot := psd_sqrt_factor
    (⟨blockX p m Sigma.val, Sigma.property.submatrix (Fin.castAdd m)⟩ : PSD p)
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((factorBlocks p m (CFC.sqrt Sigma.val)).1), ← hX,
    ← Matrix.mul_assoc (CFC.sqrt (blockX p m Sigma.val)), ← hroot]

set_option maxHeartbeats 800000 in
-- @node: factor_moments_uniform_posDef
/-- If [K is compact](hyp:hK), [there is a positive radius such that every
second-moment matrix in K retains a positive definite feature block after
any perturbation of its square-root factor with Frobenius norm below that radius](goal). -/
lemma factor_moments_uniform_posDef {p m : ℕ} [NeZero p] [NeZero m]
    (K : Set (NondegenerateSecondMoments p m)) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ K, ∀ D : Mat (p + m) (p + m), frob D < δ →
      (blockX p m (factorPerturbedMoment S.carrier.val D).val).PosDef := by
  let f := fun S : NondegenerateSecondMoments p m => symOfPSD S.carrier.val
  have hk := hK.image nondegenerateMoment_sym_continuous
  have hp : ∀ S ∈ f '' K, (blockX p m S.val).PosDef := by
    rintro _ ⟨S, _, rfl⟩
    exact S.carrier.property
  have hev : ∀ᶠ H : Sym (p + m) in nhds 0, ∀ S ∈ f '' K,
      (blockX p m (S + H).val).PosDef := by
    apply hk.eventually_forall_of_forall_eventually
    intro S hS
    have ht : Filter.Tendsto (fun z : Sym (p + m) × Sym (p + m) => z.2 + z.1)
        (nhds (0, S)) (nhds S) := by
      have hc : Continuous (fun z : Sym (p + m) × Sym (p + m) => z.2 + z.1) := by fun_prop
      simpa using (hc.continuousAt (x := (0, S))).tendsto
    exact ht.eventually ((parameterMapDerivative (p := p) (m := m)).1.mem_nhds (hp S hS))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨R, hR, hroot⟩ := compact_moment_sqrt_bound K hK
  let L := 2 * R + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨min 1 (r / L), lt_min (by norm_num) (div_pos hr hL), ?_⟩
  intro S hS D hD
  have hd := frob_nonneg D
  have hd1 : frob D ≤ 1 := (hD.trans_le (min_le_left _ _)).le
  have hdr : frob D < r / L := hD.trans_le (min_le_right _ _)
  let H := symOfPSD (factorPerturbedMoment S.carrier.val D) - symOfPSD S.carrier.val
  have hH : frob H.val ≤ L * frob D := by
    change frob ((CFC.sqrt S.carrier.val.val + D) *
      (CFC.sqrt S.carrier.val.val + D).transpose - S.carrier.val.val) ≤ _
    calc
      _ ≤ 2 * frob (CFC.sqrt S.carrier.val.val) * frob D + frob D ^ 2 :=
        factor_covariance_displacement_bound _ _
      _ ≤ 2 * R * frob D + frob D ^ 2 := by
        gcongr <;> first | fun_prop | assumption | positivity | exact hroot S hS
      _ ≤ L * frob D := by dsimp [L]; nlinarith
  have hHr : frob H.val < r := hH.trans_lt ((lt_div_iff₀' hL).mp hdr)
  have ht := hball (y := H) (by simpa [dist_zero_right, frob_eq_matrix_norm] using hHr)
    (f S) (Set.mem_image_of_mem f hS)
  have heq : f S + H = symOfPSD (factorPerturbedMoment S.carrier.val D) := by
    dsimp [f, H]; abel
  rw [heq] at ht
  exact ht

end Papers.WassersteinRegretS2S3
