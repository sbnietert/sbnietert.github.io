module
public import Papers.WassersteinRegretS2S3.Helpers.GaussianSymmetry
public import Papers.WassersteinRegretS2S3.Helpers.Symmetry

/-!
# Compact block-orthogonal moment stabilizers

The simultaneous centralizer of a second moment and a deterministic contraction
is a compact symmetry group for the Gaussian target and its contracted source.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

-- @node: blockActionMatrix_one
/-- [The identity pair of feature and response rotations acts as the identity matrix on
the joint feature-response space](goal). -/
lemma blockActionMatrix_one (p m : ℕ) :
    blockActionMatrix (1 : BlockOrth p m) = 1 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp [blockActionMatrix, Matrix.one_apply, Fin.ext_iff]
  all_goals omega

-- @node: blockActionMatrix_mul
/-- [The joint matrix for the product of two pairs of block rotations is the product
of their joint matrices, in the same order](goal). -/
lemma blockActionMatrix_mul {p m : ℕ} (u v : BlockOrth p m) :
    blockActionMatrix (u * v) = blockActionMatrix u * blockActionMatrix v := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp [blockActionMatrix, Matrix.mul_apply, Fin.sum_univ_add]

-- @node: blockActionMatrix_inv
/-- [The joint matrix for the inverse of a pair of block rotations is the transpose
of its joint matrix](goal). -/
lemma blockActionMatrix_inv {p m : ℕ} (u : BlockOrth p m) :
    blockActionMatrix u⁻¹ = (blockActionMatrix u).transpose := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp [blockActionMatrix, Matrix.transpose_apply, Matrix.UnitaryGroup.inv_val,
    Matrix.star_apply]

-- @node: blockActionMatrix_mul_transpose
/-- [Multiplying the joint matrix of a pair of block rotations by its transpose gives
the identity matrix](goal). -/
lemma blockActionMatrix_mul_transpose {p m : ℕ} (u : BlockOrth p m) :
    blockActionMatrix u * (blockActionMatrix u).transpose = 1 := by
  rw [← blockActionMatrix_inv, ← blockActionMatrix_mul, mul_inv_cancel,
    blockActionMatrix_one]

-- @node: blockActionMatrix_continuous
/-- [The joint block-diagonal action matrix varies continuously with the feature and
response rotations](goal). -/
@[fun_prop] lemma blockActionMatrix_continuous (p m : ℕ) :
    Continuous (blockActionMatrix : BlockOrth p m → Mat (p + m) (p + m)) := by
  have hx : Continuous (fun u : BlockOrth p m => (u.1.val : Mat p p)) :=
    (continuous_subtype_val : Continuous (fun u : Orth p => (u.val : Mat p p))).comp
      continuous_fst
  have hy : Continuous (fun u : BlockOrth p m => (u.2.val : Mat m m)) :=
    (continuous_subtype_val : Continuous (fun u : Orth m => (u.val : Mat m m))).comp
      continuous_snd
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp only [blockActionMatrix, Fin.addCases_left, Fin.addCases_right]
  · exact (continuous_apply j).comp ((continuous_apply i).comp hx)
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply j).comp ((continuous_apply i).comp hy)

-- @node: droOrthogonalGroup_compact
/-- [The set of real orthogonal matrices in any fixed finite dimension is compact](goal). -/
lemma droOrthogonalGroup_compact (n : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin n) ℝ : Set (Mat n n)) := by
  have hbound (A : Mat n n) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
      (i j : Fin n) : -1 ≤ A i j ∧ A i j ≤ 1 := by
    have hrow := congrArg (fun M : Mat n n => M i i)
      ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hA)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hrow
    have hentry := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
      sq_nonneg (A i k)) (Finset.mem_univ j)
    simp only [pow_two] at hentry
    constructor <;> nlinarith
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : Fin n => (-1 : ℝ))
    (fun _ _ : Fin n => (1 : ℝ)))).of_isClosed_subset
      (isClosed_unitary (R := Mat n n))
  intro A hA
  exact ⟨fun i j => (hbound A hA i j).1, fun i j => (hbound A hA i j).2⟩

-- @node: momentSymmetryGroup
/-- For [a joint second-moment matrix](hyp:S) and [a linear transformation matrix](hyp:D),
the [moment symmetry group](goal) consists of pairs of feature and response rotations
whose joint action commutes with both matrices. -/
noncomputable def momentSymmetryGroup {p m : ℕ}
    (S D : Mat (p + m) (p + m)) : Subgroup (BlockOrth p m) where
  carrier := {u | blockActionMatrix u * S = S * blockActionMatrix u ∧
    blockActionMatrix u * D = D * blockActionMatrix u}
  one_mem' := by simp [blockActionMatrix_one]
  mul_mem' := by
    intro u v hu hv
    constructor
    · rw [blockActionMatrix_mul, Matrix.mul_assoc, hv.1, ← Matrix.mul_assoc, hu.1,
        Matrix.mul_assoc]
    · rw [blockActionMatrix_mul, Matrix.mul_assoc, hv.2, ← Matrix.mul_assoc, hu.2,
        Matrix.mul_assoc]
  inv_mem' := by
    intro u hu
    let U : (Mat (p + m) (p + m))ˣ :=
      ⟨blockActionMatrix u, blockActionMatrix u⁻¹,
        by rw [← blockActionMatrix_mul, mul_inv_cancel, blockActionMatrix_one],
        by rw [← blockActionMatrix_mul, inv_mul_cancel, blockActionMatrix_one]⟩
    exact ⟨(Commute.units_inv_left (u := U) hu.1).eq,
      (Commute.units_inv_left (u := U) hu.2).eq⟩

-- @node: momentSymmetryGroup_compact
/-- [The group of block rotations commuting with both a joint second-moment matrix
and a linear transformation matrix is compact](goal). -/
lemma momentSymmetryGroup_compact {p m : ℕ} (S D : Mat (p + m) (p + m)) :
    assDroSymmetryCompactGroup (momentSymmetryGroup (p := p) (m := m) S D) := by
  let : CompactSpace (Orth p) := isCompact_iff_compactSpace.mp (droOrthogonalGroup_compact p)
  let : CompactSpace (Orth m) := isCompact_iff_compactSpace.mp (droOrthogonalGroup_compact m)
  have hS : IsClosed {u : BlockOrth p m | blockActionMatrix u * S = S * blockActionMatrix u} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hD : IsClosed {u : BlockOrth p m | blockActionMatrix u * D = D * blockActionMatrix u} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact (hS.inter hD).isCompact

-- @node: momentSymmetryGroup_gaussian_invariant
/-- If [the joint law is a centered Gaussian with its given second moment](hyp:hGaussian),
then [every block rotation commuting with that second moment and the linear transformation
preserves both the joint law and its image under that transformation](goal). -/
lemma momentSymmetryGroup_gaussian_invariant {p m : ℕ}
    (P : JointLaws p m) (D : Mat (p + m) (p + m))
    (hGaussian : lawMeasure P = ProbabilityTheory.multivariateGaussian 0 (secondMoment P)) :
    assDroSymmetryInvariantLaws
      (momentSymmetryGroup (secondMoment P) D) P (lawMapCLM (matrixCLM D) P) := by
  intro u
  have hmoment : blockActionMatrix u.val * secondMoment P *
      (blockActionMatrix u.val).transpose = secondMoment P := by
    rw [u.property.1, Matrix.mul_assoc, blockActionMatrix_mul_transpose, Matrix.mul_one]
  have htarget := gaussianLaw_invariant_of_secondMoment P hGaussian _ hmoment
  exact ⟨htarget, lawMapCLM_invariant_of_commute P _ _ u.property.2 htarget⟩

-- @node: momentSymmetryGroup_mem_of_conjugate
/-- If [a block rotation preserves the second-moment matrix under orthogonal
conjugation](hyp:hS) and [commutes with the linear transformation matrix](hyp:hD), then
[it belongs to their moment symmetry group](goal). -/
lemma momentSymmetryGroup_mem_of_conjugate {p m : ℕ}
    (S D : Mat (p + m) (p + m)) (u : BlockOrth p m)
    (hS : blockActionMatrix u * S * (blockActionMatrix u).transpose = S)
    (hD : blockActionMatrix u * D = D * blockActionMatrix u) :
    u ∈ momentSymmetryGroup S D := by
  refine ⟨?_, hD⟩
  have hinv : (blockActionMatrix u).transpose * blockActionMatrix u = 1 := by
    rw [← blockActionMatrix_inv, ← blockActionMatrix_mul, inv_mul_cancel,
      blockActionMatrix_one]
  have h := congrArg (fun M => M * blockActionMatrix u) hS
  simpa only [Matrix.mul_assoc, hinv, Matrix.mul_one] using h

end Papers.WassersteinRegretS2S3
