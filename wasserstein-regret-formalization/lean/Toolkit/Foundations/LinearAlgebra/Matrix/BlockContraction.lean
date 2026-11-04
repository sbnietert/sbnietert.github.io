module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.LinearAlgebra.ContractionExtension

/-!
# Positive block matrices and contraction factorizations

A complex block matrix with positive semidefinite diagonal blocks A and B is
positive semidefinite exactly when its upper-right block is sqrt(A) K sqrt(B)
for a matrix K with Euclidean operator norm at most one. The characterization
includes singular diagonal blocks and an empty index set.

The main theorem is `posSemidef_fromBlocks_iff_exists_contraction`. Supporting
results provide common Gram factors, the identity-diagonal characterization,
and rectangular contraction factorizations through a positive square root.
Rectangular matrix norms use the Euclidean operator norm scope; square-matrix
norm bounds in the block characterization explicitly use `toEuclideanCLM`.

Reference: Rajendra Bhatia, *Positive Definite Matrices*, Proposition 1.3.2,
printed p. 13 (2007; cited edition 2009), DOI 10.1515/9781400827787.
-/

public section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Toolkit.Foundations.LinearAlgebra.Matrix

section BlockPositivity

variable {n : Type*} [Fintype n]

/-- If [the block matrix with block rows (A, X) and (X conjugate transpose, B)
is positive semidefinite](hyp:hblock), [there are two rectangular complex matrices
with twice as many rows as columns whose column Gram matrices are A and B,
respectively, and whose cross Gram matrix is X](goal). -/
theorem exists_joint_gram_of_posSemidef_fromBlocks {A B X : Matrix n n ℂ}
    (hblock : (fromBlocks A X Xᴴ B).PosSemidef) :
    ∃ P Q : Matrix (n ⊕ n) n ℂ,
      Pᴴ * P = A ∧ Qᴴ * Q = B ∧ Pᴴ * Q = X := by
  classical
  let S := CFC.sqrt (fromBlocks A X Xᴴ B)
  have hS : Sᴴ * S = fromBlocks A X Xᴴ B := by
    rw [(CFC.sqrt_nonneg (fromBlocks A X Xᴴ B)).posSemidef.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ hblock.nonneg
  refine ⟨S.submatrix id Sum.inl, S.submatrix id Sum.inr, ?_, ?_, ?_⟩
  · ext i j
    change (Sᴴ * S) (Sum.inl i) (Sum.inl j) = A i j
    rw [hS]
    rfl
  · ext i j
    change (Sᴴ * S) (Sum.inr i) (Sum.inr j) = B i j
    rw [hS]
    rfl
  · ext i j
    change (Sᴴ * S) (Sum.inl i) (Sum.inr j) = X i j
    rw [hS]
    rfl

variable [DecidableEq n]

/-- [A complex square matrix has Euclidean operator norm at most one if and only
if the identity minus its column Gram matrix is positive semidefinite](goal). -/
theorem norm_le_one_iff_posSemidef_sub_conjTranspose_mul (K : Matrix n n ℂ) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) K‖ ≤ 1 ↔ (1 - Kᴴ * K).PosSemidef := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, ← sq_le_one_iff₀ (norm_nonneg K),
    sq, ← CStarRing.norm_star_mul_self,
    CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg K)]
  exact Matrix.le_iff

/-- [The complex block matrix with identity diagonal blocks and off-diagonal
blocks K and its conjugate transpose is positive semidefinite if and only if
K has Euclidean operator norm at most one](goal). -/
theorem posSemidef_fromBlocks_one_iff_norm_le_one (K : Matrix n n ℂ) :
    (fromBlocks (1 : Matrix n n ℂ) K Kᴴ 1).PosSemidef ↔
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) K‖ ≤ 1 := by
  let : Invertible (1 : Matrix n n ℂ) := invertibleOne
  rw [norm_le_one_iff_posSemidef_sub_conjTranspose_mul]
  simpa using (Matrix.PosDef.fromBlocks₁₁ K (1 : Matrix n n ℂ) Matrix.PosDef.one)

end BlockPositivity

section Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- If [a complex square matrix A is positive semidefinite](hyp:hA) and
[a rectangular complex matrix P has column Gram matrix A](hyp:hGram),
[P can be written as U times the positive semidefinite square root of A,
where U is a rectangular matrix with Euclidean operator norm at most one](goal). -/
theorem exists_contraction_mul_sqrt_of_gram_eq {A : Matrix n n ℂ}
    {P : Matrix m n ℂ} (hA : A.PosSemidef) (hGram : Pᴴ * P = A) :
    ∃ U : Matrix m n ℂ, ‖U‖ ≤ 1 ∧ P = U * CFC.sqrt A := by
  classical
  have hsqrt : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hinner (x y : EuclideanSpace ℂ n) :
      inner ℂ (toEuclideanLin P x) (toEuclideanLin P y) =
        inner ℂ (toEuclideanLin (CFC.sqrt A) x) (toEuclideanLin (CFC.sqrt A) y) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply]
    change (P *ᵥ WithLp.ofLp y) ⬝ᵥ star (P *ᵥ WithLp.ofLp x) =
      (CFC.sqrt A *ᵥ WithLp.ofLp y) ⬝ᵥ star (CFC.sqrt A *ᵥ WithLp.ofLp x)
    rw [dotProduct_comm (P *ᵥ WithLp.ofLp y),
      dotProduct_comm (CFC.sqrt A *ᵥ WithLp.ofLp y)]
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hGram, hsqrt]
  have hnorm (x : EuclideanSpace ℂ n) :
      ‖toEuclideanLin P x‖ = ‖toEuclideanLin (CFC.sqrt A) x‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      hinner]
  obtain ⟨k, hk, hcomp⟩ := exists_contraction_comp_of_norm_le
    (toEuclideanLin P).toContinuousLinearMap
    (toEuclideanLin (CFC.sqrt A)).toContinuousLinearMap (fun x => (hnorm x).le)
  let U : Matrix m n ℂ := toEuclideanLin.symm k.toLinearMap
  have hU : toEuclideanLin U = k.toLinearMap :=
    toEuclideanLin.apply_symm_apply k.toLinearMap
  have hkmap : k.toLinearMap.toContinuousLinearMap = k := by
    apply ContinuousLinearMap.coe_injective
    exact LinearMap.coe_toContinuousLinearMap k.toLinearMap
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.l2_opNorm_def]
    change ‖(toEuclideanLin U).toContinuousLinearMap‖ ≤ 1
    simpa only [hU, hkmap] using hk
  · apply toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m => f x)
      hcomp
    change toEuclideanLin P x = k (toEuclideanLin (CFC.sqrt A) x) at hx
    rw [show toEuclideanLin (U * CFC.sqrt A) x =
        toEuclideanLin U (toEuclideanLin (CFC.sqrt A) x) by
      simp only [toLpLin_apply, Matrix.mulVec_mulVec]]
    simpa only [hU, ContinuousLinearMap.coe_coe] using hx

end Rectangular

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If [A is positive semidefinite](hyp:hA), [B is positive semidefinite](hyp:hB),
and [the complex block matrix with block rows (A, X) and (X conjugate transpose, B)
is positive semidefinite](hyp:hblock), [X is the positive semidefinite square root
of A times a matrix with Euclidean operator norm at most one times the positive
semidefinite square root of B](goal). -/
theorem exists_contraction_of_posSemidef_fromBlocks {A B X : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hblock : (fromBlocks A X Xᴴ B).PosSemidef) :
    ∃ K : Matrix n n ℂ, ‖toEuclideanCLM (n := n) (𝕜 := ℂ) K‖ ≤ 1 ∧
      X = CFC.sqrt A * K * CFC.sqrt B := by
  classical
  obtain ⟨P, Q, hP, hQ, hX⟩ := exists_joint_gram_of_posSemidef_fromBlocks hblock
  obtain ⟨U, hU, rfl⟩ := exists_contraction_mul_sqrt_of_gram_eq hA hP
  obtain ⟨V, hV, rfl⟩ := exists_contraction_mul_sqrt_of_gram_eq hB hQ
  refine ⟨Uᴴ * V, ?_, ?_⟩
  · rw [Matrix.l2_opNorm_toEuclideanCLM]
    calc
      ‖Uᴴ * V‖ ≤ ‖Uᴴ‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul
        (by simpa only [Matrix.l2_opNorm_conjTranspose] using hU) hV
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · simpa only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
      Matrix.mul_assoc] using hX.symm

/-- If [A is positive semidefinite](hyp:hA), [B is positive semidefinite](hyp:hB),
and [K has Euclidean operator norm at most one](hyp:hK), [the complex block matrix
with diagonal blocks A and B, upper-right block equal to the positive semidefinite
square root of A times K times the positive semidefinite square root of B, and
lower-left block equal to its conjugate transpose is positive semidefinite](goal). -/
theorem posSemidef_fromBlocks_sqrt_mul_contraction {A B K : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hK : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) K‖ ≤ 1) :
    (fromBlocks A (CFC.sqrt A * K * CFC.sqrt B)
      (CFC.sqrt A * K * CFC.sqrt B)ᴴ B).PosSemidef := by
  have h := ((posSemidef_fromBlocks_one_iff_norm_le_one K).mpr hK).mul_mul_conjTranspose_same
    (fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B))
  simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_one, Matrix.one_mul, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg,
    Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- Let A, B and X be complex square matrices [with A positive semidefinite](hyp:hA)
and [B positive semidefinite](hyp:hB). Then [the block matrix with block rows
(A, X) and (X conjugate transpose, B) is positive semidefinite if and only if
there exists a complex square matrix K with Euclidean operator norm at most
one such that X is the positive semidefinite square root of A times K times
the positive semidefinite square root of B](goal).

This includes singular diagonal blocks. Both square roots are positive
semidefinite, and the operator norm is taken on complex Euclidean space.
Bhatia, *Positive Definite Matrices*, Proposition 1.3.2, p. 13. -/
theorem posSemidef_fromBlocks_iff_exists_contraction {A B X : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A X Xᴴ B).PosSemidef ↔
      ∃ K : Matrix n n ℂ, ‖toEuclideanCLM (n := n) (𝕜 := ℂ) K‖ ≤ 1 ∧
        X = CFC.sqrt A * K * CFC.sqrt B := by
  constructor
  · exact exists_contraction_of_posSemidef_fromBlocks hA hB
  · rintro ⟨K, hK, rfl⟩
    exact posSemidef_fromBlocks_sqrt_mul_contraction hA hB hK

end Toolkit.Foundations.LinearAlgebra.Matrix
