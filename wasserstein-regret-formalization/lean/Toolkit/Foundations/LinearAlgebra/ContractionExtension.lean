module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Contractive factorization through a finite-dimensional range

For two linear maps between finite-dimensional complex Euclidean spaces,
pointwise domination of image lengths gives a factorization through a map
with operator norm at most one. The intermediate map need not be injective
or surjective. The proof extends a map on its range by orthogonal projection.

This result supports square-root factorizations with singular matrix factors.
-/

public section

namespace Toolkit.Foundations.LinearAlgebra

variable {p m n : Type*} [Finite p] [Fintype m] [Fintype n]

/-- If [the first of two linear maps between finite-dimensional complex Euclidean
spaces sends every input to a vector no longer than the second does](hyp:hdom),
[the first map is the composition of the second with a linear map whose operator
norm is at most one](goal). -/
theorem exists_contraction_comp_of_norm_le
    (f : EuclideanSpace ℂ p →L[ℂ] EuclideanSpace ℂ m)
    (g : EuclideanSpace ℂ p →L[ℂ] EuclideanSpace ℂ n)
    (hdom : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    ∃ k : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m,
      ‖k‖ ≤ 1 ∧ f = k.comp g := by
  classical
  have hker : g.toLinearMap.ker ≤ f.toLinearMap.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    change f x = 0
    apply norm_eq_zero.mp
    have hg : g x = 0 := LinearMap.mem_ker.mp hx
    exact le_antisymm (by simpa only [hg, norm_zero] using hdom x) (norm_nonneg _)
  let d : g.toLinearMap.range →ₗ[ℂ] EuclideanSpace ℂ m :=
    (g.toLinearMap.ker.liftQ f.toLinearMap hker).comp
      g.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hd (x : EuclideanSpace ℂ p) :
      d ⟨g x, LinearMap.mem_range_self g.toLinearMap x⟩ = f x := by
    change (g.toLinearMap.ker.liftQ f.toLinearMap hker)
      (g.toLinearMap.quotKerEquivRange.symm
        ⟨g.toLinearMap x, LinearMap.mem_range_self g.toLinearMap x⟩) = f x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hbound : ∀ y, ‖d y‖ ≤ 1 * ‖y‖ := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    have hy : y = ⟨g x, LinearMap.mem_range_self g.toLinearMap x⟩ :=
      Subtype.ext hx.symm
    rw [hy, hd]
    simpa using hdom x
  let D := d.mkContinuous 1 hbound
  refine ⟨D.comp g.toLinearMap.range.orthogonalProjectionOnto, ?_, ?_⟩
  · calc
      ‖D.comp g.toLinearMap.range.orthogonalProjectionOnto‖ ≤
          ‖D‖ * ‖g.toLinearMap.range.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (d.mkContinuous_norm_le zero_le_one hbound)
        g.toLinearMap.range.orthogonalProjectionOnto_norm_le
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · apply ContinuousLinearMap.ext
    intro x
    change f x = D (g.toLinearMap.range.orthogonalProjectionOnto (g x))
    rw [show g x = (⟨g x, LinearMap.mem_range_self g.toLinearMap x⟩ :
      g.toLinearMap.range).val from rfl,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact (hd x).symm

end Toolkit.Foundations.LinearAlgebra
