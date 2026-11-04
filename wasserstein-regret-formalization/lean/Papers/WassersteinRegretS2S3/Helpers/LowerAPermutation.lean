module
public import Papers.WassersteinRegretS2S3.Helpers.LowerASymmetry
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Bulk-coordinate permutations for the first DRO lower bound

Together with simultaneous reflections, simultaneous bulk-coordinate swaps force
the invariant coefficient matrix to have the two parameters used by the scalar proof.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

-- @node: droPermutationOrth
/-- For [a permutation of n coordinates](hyp:σ), the [associated orthogonal
transformation](goal) is its permutation matrix. -/
noncomputable def droPermutationOrth {n : ℕ} (σ : Equiv.Perm (Fin n)) : Orth n :=
  ⟨σ.permMatrix ℝ, by
    apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

-- @node: droPermutationOrth_coefficient
/-- [Applying the transposed response permutation on the left of a coefficient
matrix and the feature permutation on the right selects the original entry at
the inverse-permuted response and feature indices](goal). -/
lemma droPermutationOrth_coefficient {p m : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin m))
    (A : Mat m p) (i : Fin m) (j : Fin p) :
    ((droPermutationOrth τ).val.transpose * A * (droPermutationOrth σ).val) i j =
      A (τ.symm i) (σ.symm j) := by
  simp only [droPermutationOrth, Matrix.transpose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, Function.id_def]
  rfl

-- @node: droLowerABulkSwap
/-- For [p features](hyp:p), [m responses](hyp:m), and [two matched coordinate
indices k and l](hyp:k,l), the [simultaneous coordinate swap](goal) exchanges
k and l in both the feature and response blocks. -/
noncomputable def droLowerABulkSwap (p m : ℕ) (k l : Fin (min p m)) : BlockOrth p m :=
  (droPermutationOrth (Equiv.swap (k.castLE (min_le_left p m)) (l.castLE (min_le_left p m))),
   droPermutationOrth (Equiv.swap (k.castLE (min_le_right p m)) (l.castLE (min_le_right p m))))

-- @node: droLowerABulkSwap_coefficient
/-- [Simultaneously swapping matched coordinates k and l in the feature and
response blocks transforms each coefficient into the original coefficient at
the correspondingly swapped row and column](goal). -/
lemma droLowerABulkSwap_coefficient {p m : ℕ} (k l : Fin (min p m))
    (A : Mat m p) (i : Fin m) (j : Fin p) :
    ((droLowerABulkSwap p m k l).2.val.transpose * A *
      (droLowerABulkSwap p m k l).1.val) i j =
      A (Equiv.swap (k.castLE (min_le_right p m)) (l.castLE (min_le_right p m)) i)
        (Equiv.swap (k.castLE (min_le_left p m)) (l.castLE (min_le_left p m)) j) := by
  unfold droLowerABulkSwap
  rw [droPermutationOrth_coefficient]
  rfl

-- @node: droLowerA_coefficient_of_reflections_swaps
/-- If [there are at least two matched feature–response coordinates](hyp:hq),
[a coefficient matrix is unchanged by every simultaneous coordinate
reflection](hyp:hreflect), and [it is unchanged by every simultaneous swap of
two nonfirst matched coordinates](hyp:hswap), [it is a rectangular diagonal
matrix with one coefficient alpha in the first coordinate and one common
coefficient beta in all other matched coordinates](goal). -/
lemma droLowerA_coefficient_of_reflections_swaps {p m : ℕ} [NeZero p] [NeZero m]
    (hq : 2 ≤ min p m) (A : Mat m p)
    (hreflect : ∀ k : ℕ, (droCoordinateReflection m k).val.transpose * A *
      (droCoordinateReflection p k).val = A)
    (hswap : ∀ k l : Fin (min p m), k.val ≠ 0 → l.val ≠ 0 →
      (droLowerABulkSwap p m k l).2.val.transpose * A *
        (droLowerABulkSwap p m k l).1.val = A) :
    ∃ alpha beta : ℝ, A = droLowerACoefficient alpha beta := by
  have hoff := (droLowerA_reflection_invariant_iff A).mp hreflect
  let oneq : Fin (min p m) := ⟨1, by omega⟩
  let onep := oneq.castLE (min_le_left p m)
  let onem := oneq.castLE (min_le_right p m)
  refine ⟨A 0 0, A onem onep, ?_⟩
  ext i j
  by_cases hij : i.val = j.val
  · by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      have hj0 : j = 0 := Fin.ext (hij.symm.trans hi)
      simp [droLowerACoefficient, hi0, hj0]
    · let k : Fin (min p m) := ⟨i.val, by omega⟩
      have him : k.castLE (min_le_right p m) = i := Fin.ext rfl
      have hjp : k.castLE (min_le_left p m) = j := Fin.ext hij
      have h := congrArg (fun B : Mat m p => B i j)
        (hswap k oneq hi (by simp [oneq]))
      rw [droLowerABulkSwap_coefficient, ← him, ← hjp,
        Equiv.swap_apply_left, Equiv.swap_apply_left] at h
      have hj : j.val ≠ 0 := by omega
      rw [him, hjp] at h
      simpa [droLowerACoefficient, hij, hi, hj, onem, onep] using h.symm
  · simp [droLowerACoefficient, hij, hoff i j hij]

-- @node: droBlockPermutation
/-- Given [a feature permutation](hyp:σ) and [a response permutation](hyp:τ),
the [permutation of the concatenated feature and response coordinates](goal)
[applies each permutation within its own block](step:1), [inverts each block
using the corresponding inverse permutation](step:2), and satisfies
[inverse-after-forward cancellation](step:3) and
[forward-after-inverse cancellation](step:4). -/
def droBlockPermutation {p m : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (p + m)) where
  toFun := Fin.addCases (fun i => Fin.castAdd m (σ i)) (fun i => Fin.natAdd p (τ i))
  invFun := Fin.addCases (fun i => Fin.castAdd m (σ.symm i))
    (fun i => Fin.natAdd p (τ.symm i))
  left_inv i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  right_inv i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

-- @node: blockActionMatrix_permutation
/-- [The joint block action matrix of a feature permutation and a response
permutation is the permutation matrix of their combined within-block
permutation](goal). -/
lemma blockActionMatrix_permutation {p m : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin m)) :
    blockActionMatrix (droPermutationOrth σ, droPermutationOrth τ) =
      (droBlockPermutation σ τ).permMatrix ℝ := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals
    simp [blockActionMatrix, droPermutationOrth, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, droBlockPermutation]
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

-- @node: droPermutation_conjugate
/-- [Conjugating a square matrix by a permutation matrix gives, at row i and
column j, the original entry at the permuted indices i and j](goal). -/
lemma droPermutation_conjugate {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Mat n n) (i j : Fin n) :
    (σ.permMatrix ℝ * S * (σ.permMatrix ℝ).transpose) i j = S (σ i) (σ j) := by
  simp only [Matrix.transpose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, Function.id_def]
  rfl

-- @node: droCommonSwap_val
/-- If [q is at most n](hyp:hqn), [swapping two indices k and l from the first
q coordinates of an n-coordinate vector sends k to l, sends l to k, and leaves
every other index unchanged](goal). -/
lemma droCommonSwap_val {q n : ℕ} (hqn : q ≤ n) (k l : Fin q) (i : Fin n) :
    (Equiv.swap (k.castLE hqn) (l.castLE hqn) i).val =
      if i.val = k.val then l.val else if i.val = l.val then k.val else i.val := by
  by_cases hik : i = k.castLE hqn
  · subst i
    simp
  · have hvk : i.val ≠ k.val := fun h => hik (Fin.ext h)
    by_cases hil : i = l.castLE hqn
    · subst i
      simp [eq_comm]
    · have hvl : i.val ≠ l.val := fun h => hil (Fin.ext h)
      simp [Equiv.swap_apply_of_ne_of_ne hik hil, hvk, hvl]

-- @node: droLowerA_bulkSwap_moment_invariant
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), and [the residual second-moment matrix is diagonal with
zero in the first coordinate, b squared in the other matched coordinates, and
zero elsewhere](hyp:hPE), then for [a matched coordinate k other than the
first](hyp:hk) and [a matched coordinate l other than the first](hyp:hl),
[the joint second-moment matrix is unchanged by simultaneously swapping k and
l in the feature and response blocks](goal). -/
lemma droLowerA_bulkSwap_moment_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (k l : Fin (min p m)) (hk : k.val ≠ 0) (hl : l.val ≠ 0) :
    let C := blockActionMatrix (droLowerABulkSwap p m k l)
    C * secondMoment P * C.transpose = secondMoment P := by
  let σ := Equiv.swap (k.castLE (min_le_left p m)) (l.castLE (min_le_left p m))
  let τ := Equiv.swap (k.castLE (min_le_right p m)) (l.castLE (min_le_right p m))
  have hYX := (identity_feature_cross_moment P hPX).trans hPA
  have hY := droLowerA_response_moment P b hPX hPA hPE
  have hxx (i j : Fin p) :
      secondMoment P (Fin.castAdd m i) (Fin.castAdd m j) = if i = j then 1 else 0 :=
    congrArg (fun M : Mat p p => M i j) hPX
  have hyx (i : Fin m) (j : Fin p) :
      secondMoment P (Fin.natAdd p i) (Fin.castAdd m j) =
        if i.val = j.val then b else 0 :=
    congrArg (fun M : Mat m p => M i j) hYX
  have hxy (i : Fin p) (j : Fin m) :
      secondMoment P (Fin.castAdd m i) (Fin.natAdd p j) =
        if j.val = i.val then b else 0 := by
    rw [← hyx j i]
    exact congrArg (fun M : Mat (p + m) (p + m) => M (Fin.natAdd p j) (Fin.castAdd m i))
      (secondMoment_posSemidef P).isHermitian.eq
  have hyy (i j : Fin m) :
      secondMoment P (Fin.natAdd p i) (Fin.natAdd p j) =
        if i = j then
          (if i.val < p then b ^ 2 else 0) +
            (if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0)
        else 0 :=
    congrArg (fun M : Mat m m => M i j) hY
  have hmatch (i : Fin m) (j : Fin p) : (τ i).val = (σ j).val ↔ i.val = j.val := by
    simp only [τ, σ, droCommonSwap_val]
    split_ifs <;> omega
  have hzero (i : Fin m) : τ i = 0 ↔ i = 0 := by
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [τ, droCommonSwap_val, Fin.val_zero]
    split_ifs <;> omega
  have hrange (i : Fin m) (r : ℕ) (hkr : k.val < r) (hlr : l.val < r) :
      (τ i).val < r ↔ i.val < r := by
    simp only [τ, droCommonSwap_val]
    split_ifs <;> omega
  change blockActionMatrix (droPermutationOrth σ, droPermutationOrth τ) * secondMoment P *
    (blockActionMatrix (droPermutationOrth σ, droPermutationOrth τ)).transpose = _
  rw [blockActionMatrix_permutation]
  ext i j
  rw [droPermutation_conjugate]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [droBlockPermutation, Equiv.coe_fn_mk, Fin.addCases_left, hxx, σ.injective.eq_iff]
  · simp only [droBlockPermutation, Equiv.coe_fn_mk, Fin.addCases_left, Fin.addCases_right,
      hxy, hmatch]
  · simp only [droBlockPermutation, Equiv.coe_fn_mk, Fin.addCases_left, Fin.addCases_right,
      hyx, hmatch]
  · simp only [droBlockPermutation, Equiv.coe_fn_mk, Fin.addCases_right,
      hyy, τ.injective.eq_iff, hzero,
      hrange i p (lt_of_lt_of_le k.isLt (min_le_left p m))
        (lt_of_lt_of_le l.isLt (min_le_left p m)), hrange i (min p m) k.isLt l.isLt]

-- @node: droPermutation_commute_diagonal
/-- If [the diagonal weights are unchanged by a coordinate permutation](hyp:hd),
[the permutation matrix commutes with the matrix of those diagonal
weights](goal). -/
lemma droPermutation_commute_diagonal {n : ℕ} (σ : Equiv.Perm (Fin n))
    (d : Fin n → ℝ) (hd : ∀ i, d (σ i) = d i) :
    σ.permMatrix ℝ * Matrix.diagonal d = Matrix.diagonal d * σ.permMatrix ℝ := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  by_cases hji : j = σ i
  · subst j
    simp [hd]
  · simp [Ne.symm hji]

-- @node: droLowerA_bulkSwap_commute_scaling
/-- For [a matched coordinate k other than the first](hyp:hk) and
[a matched coordinate l other than the first](hyp:hl), [simultaneously swapping
k and l in the feature and response blocks commutes with scaling the first
feature by c](goal). -/
lemma droLowerA_bulkSwap_commute_scaling {p m : ℕ} [NeZero p] [NeZero m]
    (k l : Fin (min p m)) (hk : k.val ≠ 0) (hl : l.val ≠ 0) (c : ℝ) :
    blockActionMatrix (droLowerABulkSwap p m k l) *
        coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c =
      coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c *
        blockActionMatrix (droLowerABulkSwap p m k l) := by
  let σ := Equiv.swap (k.castLE (min_le_left p m)) (l.castLE (min_le_left p m))
  let τ := Equiv.swap (k.castLE (min_le_right p m)) (l.castLE (min_le_right p m))
  change blockActionMatrix (droPermutationOrth σ, droPermutationOrth τ) * _ =
    _ * blockActionMatrix (droPermutationOrth σ, droPermutationOrth τ)
  rw [blockActionMatrix_permutation]
  unfold coordinateScalingMatrix
  apply droPermutation_commute_diagonal
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have hzero : σ i = 0 ↔ i = 0 := by
      rw [Fin.ext_iff, Fin.ext_iff]
      simp only [σ, droCommonSwap_val, Fin.val_zero]
      split_ifs <;> omega
    simp [droBlockPermutation, hzero]
  · have hz (j : Fin m) : Fin.natAdd p j ≠ Fin.castAdd m (0 : Fin p) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero] at hv
      have hp := NeZero.pos p
      omega
    simp [droBlockPermutation, hz]

-- @node: droLowerA_bulkSwap_gaussian_invariant
/-- If [the feature second-moment matrix is the identity](hyp:hPX),
[the canonical regression coefficient is b on matched coordinates and zero
elsewhere](hyp:hPA), [the residual second-moment matrix is diagonal with zero
in the first coordinate, b squared in the other matched coordinates, and zero
elsewhere](hyp:hPE), and [the joint law is centered Gaussian with its specified
second-moment matrix](hyp:hGaussian), then for [a matched coordinate k other
than the first](hyp:hk) and [a matched coordinate l other than the first](hyp:hl),
[simultaneously swapping k and l preserves both the original law and the law
obtained by scaling the first feature by c](goal). -/
lemma droLowerA_bulkSwap_gaussian_invariant {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (hGaussian : lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P))
    (k l : Fin (min p m)) (hk : k.val ≠ 0) (hl : l.val ≠ 0) :
    Measure.map (matrixCLM (blockActionMatrix (droLowerABulkSwap p m k l)))
      (lawMeasure P) = lawMeasure P ∧
      Measure.map (matrixCLM (blockActionMatrix (droLowerABulkSwap p m k l)))
        (lawMeasure (contractFeatureLaw 0 c P)) = lawMeasure (contractFeatureLaw 0 c P) := by
  have htarget := gaussianLaw_invariant_of_secondMoment P hGaussian _
    (droLowerA_bulkSwap_moment_invariant P b hPX hPA hPE k l hk hl)
  refine ⟨htarget, ?_⟩
  exact lawMapCLM_invariant_of_commute P _ _
    (droLowerA_bulkSwap_commute_scaling k l hk hl c) htarget

end Papers.WassersteinRegretS2S3
