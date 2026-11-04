module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Bures--Wasserstein distance as an attained Procrustes minimum

For complex positive semidefinite matrices, the Bures--Wasserstein trace expression
is both the minimum Frobenius distance between square factors and the minimum
unitary alignment error between their positive square roots. Both minima are attained,
including for singular matrices and for an empty index set.

This module supplies the explicit Frobenius norm and its trace identities, unitary
equivalence of factors with equal Gram matrices, a unitary polar factor, the trace
bound for unitary alignment, and the general attained Procrustes minimum. The main
result is `bures_eq_min_frobenius`; all declarations use general matrix vocabulary.

Reference: R. Bhatia, T. Jain, Y. Lim, *On the Bures--Wasserstein distance between positive
definite matrices*, Expositiones Mathematicae 37 (2019), 165--191, Theorem 1, equation (3).
DOI: https://doi.org/10.1016/j.exmath.2018.01.002; arXiv:1712.01504.
The source explicitly defines its cone to consist of positive semidefinite matrices.
-/

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Toolkit.Foundations.LinearAlgebra.Matrix

section Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- For [a complex matrix](hyp:M) with [finitely many row labels](hyp:m) and
[finitely many column labels](hyp:n), its [Frobenius norm](goal) is the square root of
the sum of the squared absolute values of all its entries. -/
noncomputable def frobeniusNorm (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

/-- [Every finite complex matrix has a nonnegative Frobenius norm](goal). -/
theorem frobeniusNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ frobeniusNorm M :=
  Real.sqrt_nonneg _

/-- [The square of a complex matrix's Frobenius norm equals the sum of the squared absolute
values of its entries](goal). -/
theorem frobeniusNorm_sq (M : Matrix m n ℂ) :
    frobeniusNorm M ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- [The square of a complex matrix's Frobenius norm equals the real part of the trace of
its column Gram matrix](goal). -/
theorem frobeniusNorm_sq_eq_trace (M : Matrix m n ℂ) :
    frobeniusNorm M ^ 2 = (Mᴴ * M).trace.re := by
  -- Expand trace and matrix multiplication; the diagonal summands are conjugate z times z.
  -- Swap the two finite sums and use Complex.normSq_eq_norm_sq.
  rw [frobeniusNorm_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_mul', Complex.re_sum, ← Complex.ofReal_pow,
    Complex.ofReal_re]
  exact Finset.sum_comm

/-- [The squared Frobenius distance between two complex matrices equals the sum of their
squared Frobenius norms minus twice the real part of the trace of the first matrix's
conjugate transpose times the second](goal). -/
theorem frobeniusNorm_sub_sq (M N : Matrix m n ℂ) :
    frobeniusNorm (M - N) ^ 2 =
      frobeniusNorm M ^ 2 + frobeniusNorm N ^ 2 - 2 * (Mᴴ * N).trace.re := by
  -- Expand the Gram matrix of M - N. The cross terms are complex conjugates after trace.
  have hcross : (Nᴴ * M).trace.re = (Mᴴ * N).trace.re := by
    rw [← Matrix.conjTranspose_conjTranspose M,
      ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]
    simp
  simp only [frobeniusNorm_sq_eq_trace, Matrix.conjTranspose_sub, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hcross]
  ring

variable [DecidableEq n]

/-- If [a complex square matrix is unitary](hyp:hU), [multiplying any compatible complex
matrix on the right by it preserves the Frobenius norm](goal). -/
theorem frobeniusNorm_mul_unitary (M : Matrix m n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : frobeniusNorm (M * U) = frobeniusNorm M := by
  -- Compare squares using frobeniusNorm_sq_eq_trace, trace cyclicity, and U * Uᴴ = I.
  -- Nonnegativity removes the square.
  apply (sq_eq_sq₀ (frobeniusNorm_nonneg _) (frobeniusNorm_nonneg _)).mp
  rw [frobeniusNorm_sq_eq_trace, frobeniusNorm_sq_eq_trace,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_cycle',
    ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose U,
    Matrix.mul_assoc M U (star U), Matrix.mem_unitaryGroup_iff.mp hU,
    Matrix.mul_one, Matrix.trace_mul_comm M]

end Frobenius

section UnitaryFactors

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If [two complex square matrices have equal column Gram matrices](hyp:hGram),
[there is a linear map preserving lengths and inner products from the first matrix's
column space into the ambient space that sends its output for each input vector to the
second matrix's output for that same vector](goal). -/
theorem exists_range_isometry_of_gram_eq {M N : Matrix n n ℂ}
    (hGram : Mᴴ * M = Nᴴ * N) :
    ∃ L : LinearMap.range (toEuclideanLin M) →ₗᵢ[ℂ] EuclideanSpace ℂ n,
      ∀ x, L ((toEuclideanLin M).rangeRestrict x) = toEuclideanLin N x := by
  -- For all x,y, the Gram identity implies <Mx,My> = <Nx,Ny>.
  -- In particular ker M = ker N. Descend N to range M with LinearMap.liftQ /
  -- quotKerEquivRange (or construct the range map by choosing preimages), then equip
  -- it with LinearMap.isometryOfInner. No inverse of M is available or needed.
  classical
  have hinner (A : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
      inner ℂ (toEuclideanLin A x) (toEuclideanLin A y) =
        star (WithLp.ofLp x) ⬝ᵥ ((Aᴴ * A) *ᵥ WithLp.ofLp y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (A *ᵥ WithLp.ofLp y) ⬝ᵥ star (A *ᵥ WithLp.ofLp x) = _
    rw [dotProduct_comm, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
      ← dotProduct_mulVec]
  have hMN (x y : EuclideanSpace ℂ n) :
      inner ℂ (toEuclideanLin M x) (toEuclideanLin M y) =
        inner ℂ (toEuclideanLin N x) (toEuclideanLin N y) := by
    rw [hinner, hinner, hGram]
  have hker : LinearMap.ker (toEuclideanLin M) ≤ LinearMap.ker (toEuclideanLin N) := by
    intro x hx
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← hMN, LinearMap.mem_ker.mp hx, inner_zero_left]
  let f := ((LinearMap.ker (toEuclideanLin M)).liftQ (toEuclideanLin N) hker).comp
    (toEuclideanLin M).quotKerEquivRange.symm.toLinearMap
  have hf (x : EuclideanSpace ℂ n) :
      f ((toEuclideanLin M).rangeRestrict x) = toEuclideanLin N x := by
    change (LinearMap.ker (toEuclideanLin M)).liftQ (toEuclideanLin N) hker
      ((toEuclideanLin M).quotKerEquivRange.symm ⟨toEuclideanLin M x, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨f.isometryOfInner ?_, hf⟩
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
  change inner ℂ (f ((toEuclideanLin M).rangeRestrict x))
    (f ((toEuclideanLin M).rangeRestrict y)) = _
  rw [hf, hf, ← hMN]
  rfl

/-- If [two complex square matrices have equal column Gram matrices](hyp:hGram),
[a unitary matrix multiplying the second on the left gives the first](goal). -/
theorem exists_unitary_left_of_gram_eq {M N : Matrix n n ℂ}
    (hGram : Mᴴ * M = Nᴴ * N) :
    ∃ U : Matrix n n ℂ, U ∈ unitaryGroup n ℂ ∧ M = U * N := by
  -- Apply exists_range_isometry_of_gram_eq with M,N exchanged, then use
  -- LinearIsometry.extend and LinearIsometry.extend_apply (Mathlib's PiL2 module).
  -- Represent the extended isometry in EuclideanSpace.basisFun. Preservation of
  -- inner products gives Uᴴ * U = I, hence Matrix.mem_unitaryGroup_iff'.
  classical
  obtain ⟨L, hL⟩ := exists_range_isometry_of_gram_eq hGram.symm
  let e := L.extend.toLinearIsometryEquiv rfl
  let b := (EuclideanSpace.basisFun n ℂ).toBasis
  let U := e.toLinearEquiv.toLinearMap.toMatrix b b
  refine ⟨U, ?_, ?_⟩
  · exact e.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun n ℂ)
      (EuclideanSpace.basisFun n ℂ)
  · apply (Matrix.toLin b b).injective
    rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix]
    apply LinearMap.ext
    intro x
    change toEuclideanLin M x = L.extend (toEuclideanLin N x)
    rw [← hL x, ← LinearIsometry.extend_apply]
    rfl

/-- [Every complex square matrix can be written as a unitary matrix times the positive
semidefinite square root of its column Gram matrix](goal), even when it is singular. -/
theorem exists_unitary_polar (X : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, U ∈ unitaryGroup n ℂ ∧ X = U * CFC.sqrt (Xᴴ * X) := by
  have hG := posSemidef_conjTranspose_mul_self X
  have hP : (CFC.sqrt (Xᴴ * X)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  apply exists_unitary_left_of_gram_eq
  rw [hP.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hG.nonneg]

/-- If [a complex square matrix is positive semidefinite](hyp:hA), [another square matrix
times its own conjugate transpose equals it exactly when that other matrix is its positive
semidefinite square root multiplied on the right by a unitary matrix](goal). -/
theorem factor_eq_sqrt_mul_unitary_iff {A M : Matrix n n ℂ} (hA : A.PosSemidef) :
    M * Mᴴ = A ↔
      ∃ U : Matrix n n ℂ, U ∈ unitaryGroup n ℂ ∧ M = CFC.sqrt A * U := by
  constructor
  · intro hM
    have hP : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
    have hGram : (Mᴴ)ᴴ * Mᴴ = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
      rw [conjTranspose_conjTranspose, hP.isHermitian.eq,
        CFC.sqrt_mul_sqrt_self _ hA.nonneg, hM]
    obtain ⟨U, hU, h⟩ := exists_unitary_left_of_gram_eq hGram
    refine ⟨Uᴴ, ?_, ?_⟩
    · exact Unitary.star_mem hU
    · simpa only [conjTranspose_conjTranspose, conjTranspose_mul, hP.isHermitian.eq]
        using congrArg Matrix.conjTranspose h
  · rintro ⟨U, hU, rfl⟩
    have hUU : U * Uᴴ = 1 := hU.2
    have hP : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
    rw [conjTranspose_mul, mul_assoc, ← mul_assoc U, hUU, one_mul,
      hP.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hA.nonneg]

end UnitaryFactors

section TraceOptimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If [a complex square matrix is positive semidefinite](hyp:hP) and [another is unitary](hyp:hU),
[the real part of the trace of the unitary matrix times the positive semidefinite matrix
is at most the real part of the latter matrix's trace](goal). -/
theorem re_trace_unitary_mul_le {P U : Matrix n n ℂ}
    (hP : P.PosSemidef) (hU : U ∈ unitaryGroup n ℂ) :
    (U * P).trace.re ≤ P.trace.re := by
  -- Positivity of (I-U) * P * (I-U)ᴴ gives a nonnegative real trace.
  -- Expand the trace and cycle the U * P * Uᴴ term; it has trace P.
  -- The remaining two cross traces have equal real parts since Pᴴ = P.
  -- Thus the nonnegative trace is 2 * (Re tr P - Re tr (U * P)).
  -- hP.mul_mul_conjTranspose_same and hP.trace_nonneg supply the positivity facts.
  have hnonneg := (hP.mul_mul_conjTranspose_same (1 - U)).trace_nonneg
  have hreal := (RCLike.nonneg_iff.mp hnonneg).1
  change 0 ≤ ((1 - U) * P * (1 - U)ᴴ).trace.re at hreal
  have hunit : Uᴴ * U = 1 := hU.1
  have hcycle : (U * P * Uᴴ).trace = P.trace := by
    rw [trace_mul_cycle, hunit, one_mul]
  have hcross : (P * Uᴴ).trace.re = (U * P).trace.re := by
    have heq : P * Uᴴ = (U * P)ᴴ := by
      rw [conjTranspose_mul, hP.isHermitian.eq]
    rw [heq, trace_conjTranspose]
    rfl
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, one_mul,
    mul_one, trace_sub, Complex.sub_re] at hreal
  rw [hcycle, hcross] at hreal
  linarith

end TraceOptimization

section Procrustes

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If [the matrix aligning two complex square matrices is unitary](hyp:hU), [the squared
Frobenius alignment error equals the real traces of their two column Gram matrices minus
twice the real trace of the aligning matrix's conjugate transpose times the second
matrix's conjugate transpose times the first](goal). -/
theorem frobeniusNorm_sub_mul_unitary_sq (M N : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) :
    frobeniusNorm (M - N * U) ^ 2 =
      (Mᴴ * M).trace.re + (Nᴴ * N).trace.re - 2 * (Uᴴ * (Nᴴ * M)).trace.re := by
  have hcross : (Mᴴ * (N * U)).trace.re = (Uᴴ * (Nᴴ * M)).trace.re := by
    have heq : Uᴴ * (Nᴴ * M) = (Mᴴ * (N * U))ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
    rw [heq, trace_conjTranspose]
    rfl
  rw [frobeniusNorm_sub_sq, frobeniusNorm_mul_unitary N hU,
    frobeniusNorm_sq_eq_trace, frobeniusNorm_sq_eq_trace, hcross]

/-- [The minimum Frobenius error when aligning two complex square matrices by a unitary
right multiple of the second is attained and equals the square root of their two real
column Gram traces minus twice the real trace of the positive square root of the column
Gram matrix of the second matrix's conjugate transpose times the first](goal). -/
theorem procrustes_isLeast (M N : Matrix n n ℂ) :
    IsLeast {r : ℝ | ∃ U : Matrix n n ℂ,
      U ∈ unitaryGroup n ℂ ∧ frobeniusNorm (M - N * U) = r}
      (Real.sqrt ((Mᴴ * M).trace.re + (Nᴴ * N).trace.re -
        2 * (CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M))).trace.re)) := by
  -- Obtain Nᴴ*M = V*P from exists_unitary_polar. At U=V the cross trace is tr P.
  -- At arbitrary U, Uᴴ*V is unitary; re_trace_unitary_mul_le gives the upper
  -- bound on the cross trace. Use frobeniusNorm_sub_mul_unitary_sq to compare
  -- squared costs, and nonnegativity to pass to norms. First identify the
  -- radicand with the squared cost at V; this also proves its nonnegativity.
  -- More concretely, let X=Nᴴ*M and P=CFC.sqrt (Xᴴ*X). If X=V*P,
  -- hV.1 gives Vᴴ*V=1, so rewriting mul_assoc backwards collapses
  -- Vᴴ*(V*P) to P. This identifies the radicand with
  -- frobeniusNorm (M-N*V)^2; Real.sqrt_sq_eq_abs and abs_of_nonneg
  -- prove membership. For a candidate U, use Unitary.mul_mem
  -- (Unitary.star_mem hU) hV to apply re_trace_unitary_mul_le to Uᴴ*V.
  -- Rewrite both squared costs with frobeniusNorm_sub_mul_unitary_sq,
  -- derive the square inequality by linarith, and use nonnegative norms
  -- (sq_le_sq₀ or nlinarith) to obtain the lower-bound component of IsLeast.
  obtain ⟨V, hV, hpolar⟩ := exists_unitary_polar (Nᴴ * M)
  have hVV : Vᴴ * V = 1 := hV.1
  have hcross : Vᴴ * (Nᴴ * M) = CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M)) := by
    conv_lhs => rw [hpolar, ← mul_assoc, hVV, one_mul]
  have hcost := frobeniusNorm_sub_mul_unitary_sq M N hV
  rw [hcross] at hcost
  rw [← hcost, Real.sqrt_sq (frobeniusNorm_nonneg _)]
  refine ⟨⟨V, hV, rfl⟩, ?_⟩
  rintro r ⟨U, hU, rfl⟩
  have hbound := re_trace_unitary_mul_le
    (P := CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M)))
    (CFC.sqrt_nonneg _).posSemidef ((unitaryGroup n ℂ).mul_mem (Unitary.star_mem hU) hV)
  change (Uᴴ * V * CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M))).trace.re ≤
    (CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M))).trace.re at hbound
  have hcrossU : Uᴴ * (Nᴴ * M) =
      (Uᴴ * V) * CFC.sqrt ((Nᴴ * M)ᴴ * (Nᴴ * M)) := by
    conv_lhs => rw [hpolar, ← mul_assoc]
  have hcostU := frobeniusNorm_sub_mul_unitary_sq M N hU
  rw [hcrossU] at hcostU
  have hsq : frobeniusNorm (M - N * V) ^ 2 ≤ frobeniusNorm (M - N * U) ^ 2 := by
    linarith
  nlinarith [frobeniusNorm_nonneg (M - N * V), frobeniusNorm_nonneg (M - N * U)]

end Procrustes

section BuresDistance

variable {n : Type*} [Fintype n]

open Classical in
/-- For [a first complex square matrix](hyp:A) and [a second complex square matrix](hyp:B)
with [a common finite set of row and column labels](hyp:n), the [Bures--Wasserstein trace
expression](goal) is the square root of the sum of their real traces minus twice the real
trace of the positive square root of the second matrix sandwiched between positive square
roots of the first. On positive semidefinite matrices this is their distance. -/
noncomputable def buresDistance (A B : Matrix n n ℂ) : ℝ :=
  Real.sqrt (A.trace.re + B.trace.re -
    2 * (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).trace.re)

open Classical in
/-- If [the second of two complex square matrices is positive semidefinite](hyp:hB),
[the column Gram matrix of its positive square root times the first matrix's positive
square root equals the second matrix sandwiched between positive square roots of the
first](goal). -/
theorem sqrt_product_gram {A B : Matrix n n ℂ}
    (hB : B.PosSemidef) :
    (CFC.sqrt B * CFC.sqrt A)ᴴ * (CFC.sqrt B * CFC.sqrt A) =
      CFC.sqrt A * B * CFC.sqrt A := by
  have hSA : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hSB : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  rw [conjTranspose_mul, hSA.isHermitian.eq, hSB.isHermitian.eq,
    mul_assoc, ← mul_assoc (CFC.sqrt B), CFC.sqrt_mul_sqrt_self _ hB.nonneg,
    ← mul_assoc]

variable [DecidableEq n]

/-- Let A and B be complex square matrices [with A positive semidefinite](hyp:hA) and
[B positive semidefinite](hyp:hB). [Their Bures--Wasserstein distance equals both the minimum
Frobenius distance between square factors of A and B and the minimum Frobenius distance
between the square root of A and a unitary right multiple of the square root of B; both
minima are attained](goal).

Each least-value assertion includes membership in the corresponding set of achieved
errors, so the theorem asserts actual minima rather than just equality of infima.
Membership in the unitary group means that both products with the conjugate transpose
are the identity. Real parts of traces make the expression real-valued; positivity makes
the traces in the distance formula real. -/
theorem bures_eq_min_frobenius {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IsLeast {r : ℝ | ∃ M N : Matrix n n ℂ,
      M * Mᴴ = A ∧ N * Nᴴ = B ∧ frobeniusNorm (M - N) = r} (buresDistance A B) ∧
    IsLeast {r : ℝ | ∃ U : Matrix n n ℂ,
      U ∈ unitaryGroup n ℂ ∧
        frobeniusNorm (CFC.sqrt A - CFC.sqrt B * U) = r} (buresDistance A B) := by
  -- Apply procrustes_isLeast to sqrt A, sqrt B. Hermitian symmetry,
  -- CFC.sqrt_mul_sqrt_self, and sqrt_product_gram identify its value with buresDistance.
  -- Its optimizer gives factors sqrt A and sqrt B * U, proving attainment for factors.
  -- For arbitrary factors, factor_eq_sqrt_mul_unitary_iff gives M=sqrt A*V,
  -- N=sqrt B*W. Multiply M-N on the right by Vᴴ and use
  -- frobeniusNorm_mul_unitary; the resulting unitary is W*Vᴴ.
  -- For the specialization, first name the Hermitian identities for both
  -- square roots. Then simplify the two self Gram traces with
  -- CFC.sqrt_mul_sqrt_self _ hA.nonneg (and hB.nonneg), and simplify
  -- the cross Gram with sqrt_product_gram hB. This yields the second
  -- IsLeast assertion directly, without a separate square-root inequality.
  -- Its membership witness U also gives N*Nᴴ=B via the reverse direction
  -- of factor_eq_sqrt_mul_unitary_iff hB. For the lower bound, apply the
  -- second IsLeast's lower-bound component to W*Vᴴ; rewrite the candidate
  -- norm using sub_mul, mul_assoc, V*Vᴴ=1, and frobeniusNorm_mul_unitary.
  have hSA := ((CFC.sqrt_nonneg A).posSemidef).isHermitian.eq
  have hSB := ((CFC.sqrt_nonneg B).posSemidef).isHermitian.eq
  have hmin := procrustes_isLeast (CFC.sqrt A) (CFC.sqrt B)
  simp only [hSA, hSB, CFC.sqrt_mul_sqrt_self A hA.nonneg,
    CFC.sqrt_mul_sqrt_self B hB.nonneg, sqrt_product_gram hB] at hmin
  change IsLeast _ (buresDistance A B) at hmin
  refine ⟨⟨?_, ?_⟩, hmin⟩
  · obtain ⟨U, hU, hcost⟩ := hmin.1
    refine ⟨CFC.sqrt A, CFC.sqrt B * U, ?_, ?_, hcost⟩
    · rw [hSA, CFC.sqrt_mul_sqrt_self A hA.nonneg]
    · exact (factor_eq_sqrt_mul_unitary_iff hB).mpr ⟨U, hU, rfl⟩
  · rintro r ⟨M, N, hM, hN, rfl⟩
    obtain ⟨V, hV, rfl⟩ := (factor_eq_sqrt_mul_unitary_iff hA).mp hM
    obtain ⟨W, hW, rfl⟩ := (factor_eq_sqrt_mul_unitary_iff hB).mp hN
    have hVV : V * Vᴴ = 1 := hV.2
    have hunit : W * Vᴴ ∈ unitaryGroup n ℂ :=
      (unitaryGroup n ℂ).mul_mem hW (Unitary.star_mem hV)
    have hbound := hmin.2 ⟨W * Vᴴ, hunit, rfl⟩
    have heq :
        (CFC.sqrt A * V - CFC.sqrt B * W) * Vᴴ =
          CFC.sqrt A - CFC.sqrt B * (W * Vᴴ) := by
      rw [sub_mul, mul_assoc, hVV, mul_one, mul_assoc]
    rw [← heq, frobeniusNorm_mul_unitary _ (U := Vᴴ) (Unitary.star_mem hV)] at hbound
    exact hbound

end BuresDistance

end Toolkit.Foundations.LinearAlgebra.Matrix
