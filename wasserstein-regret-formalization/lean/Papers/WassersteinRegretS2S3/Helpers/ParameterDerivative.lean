module
public import Papers.WassersteinRegretS2S3.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Population Wasserstein regret: Helpers/ParameterDerivative

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: symSubmatrixCLM
/-- Given [a selection of row indices](hyp:rows) and [a selection of column indices](hyp:cols),
the [submatrix extraction operator](goal) is the continuous linear map sending a symmetric
matrix to the rectangular matrix at those rows and columns. -/
noncomputable def symSubmatrixCLM {n a b : ℕ} (rows : Fin a → Fin n)
    (cols : Fin b → Fin n) : Sym n →L[ℝ] Mat a b :=
  { toFun := fun S => S.val.submatrix rows cols
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := by fun_prop }

-- @node: rectangularMulCLM
/-- For [an output row count a](hyp:a), [a shared inner dimension b](hyp:b), and
[an output column count c](hyp:c), the [rectangular multiplication operator](goal)
is the continuous bilinear map multiplying an a-by-b matrix by a b-by-c matrix. -/
noncomputable def rectangularMulCLM (a b c : ℕ) :
    Mat a b →L[ℝ] Mat b c →L[ℝ] Mat a c :=
  (mulLinearMap ℝ).mkContinuous₂ 1 (by
    intro A B
    simpa using Matrix.frobenius_norm_mul A B)

-- @node: sym_posDef_isOpen
/-- For [a matrix dimension n](hyp:n), [the positive definite matrices form an open
subset of the real symmetric matrices](goal). -/
lemma sym_posDef_isOpen (n : ℕ) : IsOpen {S : Sym n | S.val.PosDef} := by
  let q : Sym n × (Fin n → ℝ) → ℝ := fun z => z.2 ⬝ᵥ (z.1.val *ᵥ z.2)
  have hq : Continuous q := by fun_prop
  apply isOpen_iff_forall_mem_open.mpr
  intro S hS
  have hpos : ({S} : Set (Sym n)) ×ˢ Metric.sphere (0 : Fin n → ℝ) 1 ⊆
      {z | 0 < q z} := by
    rintro ⟨T, x⟩ ⟨rfl : T = S, hx⟩
    have hx' : x ≠ 0 := by
      intro h
      simp [h] at hx
    simpa [q] using hS.dotProduct_mulVec_pos hx'
  obtain ⟨u, v, hu, hv, hSu, hsv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere _ _)
      (isOpen_lt continuous_const hq) hpos
  refine ⟨u, ?_, hu, hSu (Set.mem_singleton S)⟩
  intro T hT
  apply Matrix.PosDef.of_dotProduct_mulVec_pos T.property.isHermitian
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have hp : 0 < q (T, ‖x‖⁻¹ • x) := huv ⟨hT, hsv hunit⟩
  change 0 < (‖x‖⁻¹ • x) ⬝ᵥ (T.val *ᵥ (‖x‖⁻¹ • x)) at hp
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hp
  have hp' : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (T.val *ᵥ x)) := by
    simpa only [mul_assoc] using hp
  simpa using (pos_of_mul_pos_right hp' (by positivity : 0 ≤ ‖x‖⁻¹ * ‖x‖⁻¹))

-- @node: parameterMap_contDiffAt
/-- At [a symmetric joint moment matrix S](hyp:S) whose [feature block is positive
definite](hyp:hS), [the map from moments to the regression coefficient is continuously
differentiable](goal). -/
@[fun_prop] lemma parameterMap_contDiffAt {p m : ℕ} (S : Sym (p + m))
    (hS : (blockX p m S.val).PosDef) : ContDiffAt ℝ 1 (@parameterMap p m) S := by
  let X : Sym (p + m) →L[ℝ] Mat p p := symSubmatrixCLM (Fin.castAdd m) (Fin.castAdd m)
  let Y : Sym (p + m) →L[ℝ] Mat m p := symSubmatrixCLM (Fin.natAdd p) (Fin.castAdd m)
  have hi := (contDiffAt_ringInverse ℝ (n := 1) hS.isUnit.unit).comp S X.contDiff.contDiffAt
  have hi' : ContDiffAt ℝ 1 (fun S => (X S)⁻¹) S := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse, IsUnit.unit_spec] using! hi
  exact (rectangularMulCLM m p p).isBoundedBilinearMap.contDiff.contDiffAt.comp S
    (Y.contDiff.contDiffAt.prodMk hi')

-- @node: parameterMap_fderiv_apply
/-- At [a symmetric joint moment matrix S](hyp:S) with [positive definite feature
block](hyp:hS), and for [a symmetric direction H](hyp:H), [the derivative of the
regression coefficient equals the response-feature block of H minus the coefficient
at S times the feature block of H, all multiplied on the right by the inverse feature
block of S](goal). -/
lemma parameterMap_fderiv_apply {p m : ℕ} (S : Sym (p + m))
    (hS : (blockX p m S.val).PosDef) (H : Sym (p + m)) :
    fderiv ℝ (@parameterMap p m) S H =
      (blockYX p m H.val - parameterMap S * blockX p m H.val) *
        (blockX p m S.val)⁻¹ := by
  let X : Sym (p + m) →L[ℝ] Mat p p := symSubmatrixCLM (Fin.castAdd m) (Fin.castAdd m)
  let Y : Sym (p + m) →L[ℝ] Mat m p := symSubmatrixCLM (Fin.natAdd p) (Fin.castAdd m)
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) hS.isUnit.unit).comp S (X.hasFDerivAt)
  have hi' : HasFDerivAt (fun S => (X S)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ (Mat p p)
        (↑hS.isUnit.unit⁻¹) (↑hS.isUnit.unit⁻¹)).comp X) S := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse, IsUnit.unit_spec] using! hi
  have hd := (rectangularMulCLM m p p).hasFDerivAt_of_bilinear Y.hasFDerivAt hi'
  have he := congrArg (fun f : Sym (p + m) →L[ℝ] Mat m p => f H) hd.fderiv
  change fderiv ℝ (@parameterMap p m) S H = _ at he
  rw [he]
  change blockYX p m S.val *
      (-((↑(hS.isUnit.unit⁻¹) : Mat p p) * blockX p m H.val * (↑(hS.isUnit.unit⁻¹) : Mat p p))) +
      blockYX p m H.val * (blockX p m S.val)⁻¹ = _
  rw [Matrix.sub_mul]
  simp only [Matrix.coe_units_inv, IsUnit.unit_spec, parameterMap,
    Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg, add_comm]


-- @node: lem:parameter-map-derivative
/-- [The symmetric matrices with positive definite feature block form an open set,
and the regression coefficient map is continuously differentiable there; at every
point it has a Fréchet derivative that sends any symmetric direction to its
response-feature block minus the current coefficient times its feature block,
multiplied on the right by the inverse feature block at that point](goal). -/
lemma parameterMapDerivative {p m : ℕ} [NeZero p] [NeZero m] :
    IsOpen {Sigma : Sym (p + m) | (blockX p m Sigma.val).PosDef} ∧
    ContDiffOn ℝ 1 (@parameterMap p m) {Sigma | (blockX p m Sigma.val).PosDef} ∧
    (∀ Sigma : ParameterDomain p m,
      HasFDerivAt (@parameterMap p m) (fderiv ℝ (@parameterMap p m) Sigma.carrier.val)
        Sigma.carrier.val ∧
      ∀ H : Sym (p + m),
        fderiv ℝ (@parameterMap p m) Sigma.carrier.val H =
          (blockYX p m H.val - parameterMap Sigma.carrier.val * blockX p m H.val) *
            (blockX p m Sigma.carrier.val.val)⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · let X : Sym (p + m) → Sym p := fun S =>
      ⟨blockX p m S.val, (S.property.isHermitian.submatrix (Fin.castAdd m)).isSelfAdjoint⟩
    have hc : Continuous X := by fun_prop
    exact (sym_posDef_isOpen p).preimage hc
  · intro S hS
    exact (parameterMap_contDiffAt S hS).contDiffWithinAt
  · intro S
    exact ⟨(parameterMap_contDiffAt S.carrier.val S.carrier.property).differentiableAt
      (by norm_num) |>.hasFDerivAt,
      parameterMap_fderiv_apply S.carrier.val S.carrier.property⟩
-- @realizes Dg(Fréchet derivative on the ambient symmetric vector space)
-- @realizes \bH(arbitrary symmetric direction, including indefinite directions)

-- @node: psd_selfAdjoint
/-- For [a positive semidefinite real matrix Sigma](hyp:Sigma),
[Sigma is self-adjoint, equivalently symmetric](goal). -/
lemma psd_selfAdjoint {n : ℕ} (Sigma : PSD n) : IsSelfAdjoint Sigma.val := by
  exact Sigma.property.isHermitian.isSelfAdjoint
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma), its [symmetric-matrix
representation](goal) is the same matrix regarded as a real symmetric matrix. -/
noncomputable def symOfPSD {n : ℕ} (Sigma : PSD n) : Sym n := ⟨Sigma.val, psd_selfAdjoint Sigma⟩
-- @node: factorTangent_selfAdjoint
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a square factor
perturbation Delta](hyp:Delta), [the square root of Sigma times the transpose of
Delta plus Delta times the square root of Sigma is symmetric](goal). -/
lemma factorTangent_selfAdjoint {n : ℕ} (Sigma : PSD n) (Delta : Mat n n) :
    IsSelfAdjoint (CFC.sqrt Sigma.val * Delta.transpose + Delta * CFC.sqrt Sigma.val) := by
  have hs : IsSelfAdjoint (CFC.sqrt Sigma.val) :=
    (CFC.sqrt_nonneg Sigma.val).isSelfAdjoint
  rw [IsSelfAdjoint, star_add, star_mul, star_mul, hs.star_eq]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose]
  exact add_comm _ _
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a square factor
perturbation Delta](hyp:Delta), the [induced symmetric moment direction](goal) is
the square root of Sigma times the transpose of Delta plus Delta times the square
root of Sigma. -/
noncomputable def factorTangent {n : ℕ} (Sigma : PSD n) (Delta : Mat n n) : Sym n :=
  ⟨CFC.sqrt Sigma.val * Delta.transpose + Delta * CFC.sqrt Sigma.val, factorTangent_selfAdjoint
    Sigma Delta⟩
/-- For [a positive semidefinite joint moment matrix Sigma](hyp:Sigma) and
[a square factor perturbation Delta](hyp:Delta), the [derivative sensitivity](goal)
is the squared Frobenius norm of the derivative of the regression coefficient in
the induced symmetric moment direction, multiplied on the right by the square
root of the feature block of Sigma. -/
noncomputable def derivativeSensitivity {p m : ℕ} (Sigma : PSD (p + m)) (Delta : Mat (p + m) (p
   + m)) : ℝ :=
  frob (fderiv ℝ (@parameterMap p m) (symOfPSD Sigma) (factorTangent Sigma Delta) *
    CFC.sqrt (blockX p m Sigma.val)) ^ 2

end Papers.WassersteinRegretS2S3
