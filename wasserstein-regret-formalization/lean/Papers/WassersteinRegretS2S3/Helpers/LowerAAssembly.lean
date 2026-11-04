module
public import Papers.WassersteinRegretS2S3.Helpers.LowerAPermutation
public import Papers.WassersteinRegretS2S3.Helpers.CompactMomentSymmetry

/-!
# Symmetry transfer for every minimizer in the first DRO lower bound

The compact moment stabilizer contains the reflections and bulk swaps. Its
invariant coefficients therefore belong to the scalar certificate's family.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

-- @node: droLowerA_reflection_mem_momentSymmetryGroup
/-- For [a joint law](hyp:P), [a regression scale and a first-feature scaling factor](hyp:b,c),
assume [the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has the given scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
and [the residual second moment is diagonal, with the squared regression scale on matched
coordinates other than the first and zero elsewhere](hyp:hPE).
Then [simultaneously reflecting the feature and response coordinates at any given index](hyp:k)
[belongs to the moment symmetry group that preserves the joint second moment and commutes
with scaling the first feature by the given factor](goal). -/
lemma droLowerA_reflection_mem_momentSymmetryGroup {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (k : ℕ) :
    droLowerAReflection p m k ∈ momentSymmetryGroup (secondMoment P)
      (coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c) := by
  have hD := blockActionMatrix_diagonal (droLowerAReflection p m k)
    (fun i => if i.val = k then -1 else 1)
    (fun i => if i.val = k then -1 else 1) rfl rfl
  apply momentSymmetryGroup_mem_of_conjugate
  · rw [hD]
    apply droLowerA_diagonal_moment_invariant P b hPX hPA hPE
    · intro i; split_ifs <;> norm_num
    · intro i; split_ifs <;> norm_num
    · intro i j hij; rw [hij]
  · rw [hD]
    simp only [coordinateScalingMatrix, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

-- @node: droLowerA_bulkSwap_mem_momentSymmetryGroup
/-- For [a joint law](hyp:P), [a regression scale and a first-feature scaling factor](hyp:b,c),
assume [the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has the given scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
and [the residual second moment is diagonal, with the squared regression scale on matched
coordinates other than the first and zero elsewhere](hyp:hPE).
For [two matched coordinate indices](hyp:k,l) with [the first index nonzero](hyp:hk)
and [the second index nonzero](hyp:hl), [simultaneously swapping those feature and response
coordinates belongs to the moment symmetry group that preserves the joint second moment
and commutes with scaling the first feature by the given factor](goal). -/
lemma droLowerA_bulkSwap_mem_momentSymmetryGroup {p m : ℕ} [NeZero p] [NeZero m]
    (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (k l : Fin (min p m)) (hk : k.val ≠ 0) (hl : l.val ≠ 0) :
    droLowerABulkSwap p m k l ∈ momentSymmetryGroup (secondMoment P)
      (coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c) := by
  exact momentSymmetryGroup_mem_of_conjugate _ _ _
    (droLowerA_bulkSwap_moment_invariant P b hPX hPA hPE k l hk hl)
    (droLowerA_bulkSwap_commute_scaling k l hk hl c)

-- @node: droLowerA_momentSymmetryGroup_coefficient
/-- Suppose [both feature and response dimensions are at least two](hyp:hq).
For [a joint law](hyp:P), [a regression scale and a first-feature scaling factor](hyp:b,c),
assume [the feature second moment is the identity](hyp:hPX),
[the canonical regression coefficient has the given scale on its rectangular diagonal and zero elsewhere](hyp:hPA),
and [the residual second moment is diagonal, with the squared regression scale on matched
coordinates other than the first and zero elsewhere](hyp:hPE).
If [a prediction coefficient matrix](hyp:A) [is invariant under the moment symmetry group
that also commutes with scaling the first feature](hyp:hA), [it has a two-parameter rectangular
diagonal form: one value on the first matched coordinate, a common value on all remaining
matched coordinates, and zero elsewhere](goal). -/
lemma droLowerA_momentSymmetryGroup_coefficient {p m : ℕ} [NeZero p] [NeZero m]
    (hq : 2 ≤ min p m) (P : JointLaws p m) (b c : ℝ) (hPX : secondMomentX P = 1)
    (hPA : canonicalCoefficient (secondMoment P) =
      fun i j => if i.val = j.val then b else 0)
    (hPE : matrixResidual (secondMoment P) = Matrix.diagonal
      (fun i => if i = 0 then 0 else if i.val < min p m then b ^ 2 else 0))
    (A : Mat m p)
    (hA : invariantCoefficient (momentSymmetryGroup (secondMoment P)
      (coordinateScalingMatrix (p + m) (Fin.castAdd m (0 : Fin p)) c)) A) :
    ∃ alpha beta : ℝ, A = droLowerACoefficient alpha beta := by
  apply droLowerA_coefficient_of_reflections_swaps hq A
  · intro k
    exact hA ⟨droLowerAReflection p m k,
      droLowerA_reflection_mem_momentSymmetryGroup P b c hPX hPA hPE k⟩
  · intro k l hk hl
    exact hA ⟨droLowerABulkSwap p m k l,
      droLowerA_bulkSwap_mem_momentSymmetryGroup P b c hPX hPA hPE k l hk hl⟩

end Papers.WassersteinRegretS2S3
