module
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Papers.WassersteinRegretS2S3.Helpers.MatrixDefs

/-!
# Population Wasserstein regret: Helpers/Scalar

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @env: S4
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

-- @node: scalar_variational_lower
/-- If [A is nonnegative](hyp:hA), [B is nonnegative](hyp:hB), and
[delta is positive](hyp:hδ), [the square of the sum of the square roots of A and B
is at most the product of A plus delta and one plus B divided by delta](goal). -/
lemma scalar_variational_lower (A B δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 < δ) :
    (Real.sqrt A + Real.sqrt B) ^ 2 ≤ (A + δ) * (1 + B / δ) := by
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  have hs := sq_nonneg (δ - Real.sqrt A * Real.sqrt B)
  apply (mul_le_mul_iff_right₀ hδ).mp
  have he : (A + δ) * (1 + B / δ) * δ = (A + δ) * (δ + B) := by
    field_simp
  rw [mul_comm δ ((A + δ) * (1 + B / δ)), he]
  nlinarith [congrArg (fun t => t * δ) ha,
    congrArg (fun t => t * δ) hb,
    congrArg (fun t => t * (Real.sqrt B) ^ 2) ha,
    congrArg (fun t => A * t) hb]

-- @node: scalar_variational_attainment
/-- If [A is nonnegative](hyp:hA), [B is nonnegative](hyp:hB), and
[their product is positive](hyp:hAB), [choosing delta as the square root of their
product makes the product of A plus delta and one plus B divided by delta equal
to the square of the sum of their square roots](goal). -/
lemma scalar_variational_attainment (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : 0 < A * B) :
    (A + Real.sqrt (A * B)) * (1 + B / Real.sqrt (A * B)) =
      (Real.sqrt A + Real.sqrt B) ^ 2 := by
  have hp := Real.sqrt_pos.2 hAB
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  have hab := Real.sq_sqrt (le_of_lt hAB)
  rw [Real.sqrt_mul hA] at *
  have hsa : Real.sqrt A ≠ 0 := left_ne_zero_of_mul (ne_of_gt hp)
  have hsb : Real.sqrt B ≠ 0 := right_ne_zero_of_mul (ne_of_gt hp)
  field_simp [hsa, hsb]
  nlinarith [congrArg (fun t => t * Real.sqrt A * Real.sqrt B) ha,
    congrArg (fun t => t * Real.sqrt A * Real.sqrt B) hb,
    congrArg (fun t => t * (Real.sqrt B) ^ 2) ha,
    congrArg (fun t => A * t) hb]


-- @node: lem:elementary-scalar-ineqs
/-- [For any nonempty finite list of nonnegative numbers, the squared sum is at most
the list length times the sum of squares; for nonnegative A and B, the infimum over
positive delta of the product of A plus delta and one plus B divided by delta is
the square of the sum of their square roots, attained at the positive square root
of their product when that product is positive; and for any two points in a real
normed vector space, the infimum over centers of the larger squared distance to
the two points is one quarter of their squared distance](goal). -/
lemma elementaryScalarIneqs :
    (∀ (k : ℕ) [NeZero k] (a : Fin k → ℝ), (∀ i, 0 ≤ a i) →
      (∑ i, a i) ^ 2 ≤ (k : ℝ) * ∑ i, (a i) ^ 2) ∧
    (∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      sInf {v : ℝ | ∃ delta : ℝ, 0 < delta ∧ (A + delta) * (1 + B / delta) = v} =
        (Real.sqrt A + Real.sqrt B) ^ 2 ∧
      (0 < A * B → 0 < Real.sqrt (A * B) ∧
        (A + Real.sqrt (A * B)) * (1 + B / Real.sqrt (A * B)) = (Real.sqrt A + Real.sqrt B) ^ 2)) ∧
    (∀ x0 x1 : V, (⨅ x : V, max (‖x - x0‖ ^ 2) (‖x - x1‖ ^ 2)) = (1 / 4 : ℝ) * ‖x0 - x1‖ ^ 2)
     := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _ a _
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a))
  · intro A B hA hB
    let S : Set ℝ := {v | ∃ δ : ℝ, 0 < δ ∧ (A + δ) * (1 + B / δ) = v}
    have hne : S.Nonempty := ⟨(A + 1) * (1 + B / 1), 1, by norm_num, rfl⟩
    have hlo : ∀ v ∈ S, (Real.sqrt A + Real.sqrt B) ^ 2 ≤ v := by
      rintro v ⟨δ, hδ, rfl⟩
      exact scalar_variational_lower A B δ hA hB hδ
    have hbd : BddBelow S := ⟨_, hlo⟩
    refine ⟨le_antisymm ?_ (le_csInf hne hlo), ?_⟩
    · by_cases hp : 0 < A * B
      · have he := scalar_variational_attainment A B hA hB hp
        exact csInf_le hbd ⟨Real.sqrt (A * B), Real.sqrt_pos.2 hp, he⟩
      · have hz : A = 0 ∨ B = 0 :=
          mul_eq_zero.mp (le_antisymm (le_of_not_gt hp) (mul_nonneg hA hB))
        apply le_of_forall_pos_le_add
        intro ε hε
        rcases hz with rfl | rfl
        · have he : (0 + ε) * (1 + B / ε) = B + ε := by field_simp; ring
          have hh := csInf_le hbd (show B + ε ∈ S from ⟨ε, hε, he⟩)
          simpa [S, Real.sq_sqrt hB] using hh
        · have hh := csInf_le hbd (show A + ε ∈ S from ⟨ε, hε, by simp⟩)
          simpa [S, Real.sq_sqrt hA] using hh
    · intro hp
      exact ⟨Real.sqrt_pos.2 hp, scalar_variational_attainment A B hA hB hp⟩
  · intro x0 x1
    have hlo (x : V) : (1 / 4 : ℝ) * ‖x0 - x1‖ ^ 2 ≤
        max (‖x - x0‖ ^ 2) (‖x - x1‖ ^ 2) := by
      have ht : ‖x0 - x1‖ ≤ ‖x - x0‖ + ‖x - x1‖ := by
        simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub x0 x x1
      have h0 := le_max_left (‖x - x0‖ ^ 2) (‖x - x1‖ ^ 2)
      have h1 := le_max_right (‖x - x0‖ ^ 2) (‖x - x1‖ ^ 2)
      nlinarith [sq_nonneg (‖x - x0‖ - ‖x - x1‖),
        mul_self_le_mul_self (norm_nonneg _) ht]
    have hbd : BddBelow (Set.range (fun x : V => max (‖x - x0‖ ^ 2) (‖x - x1‖ ^ 2))) :=
      ⟨_, by rintro _ ⟨x, rfl⟩; exact hlo x⟩
    apply le_antisymm _ (le_ciInf hlo)
    let mid : V := (1 / 2 : ℝ) • (x0 + x1)
    have h0 : mid - x0 = (1 / 2 : ℝ) • (x1 - x0) := by dsimp [mid]; module
    have h1 : mid - x1 = (1 / 2 : ℝ) • (x0 - x1) := by dsimp [mid]; module
    have hh := ciInf_le hbd mid
    norm_num [h0, h1, norm_smul, norm_sub_rev, Real.norm_eq_abs] at hh
    simp only [norm_sub_rev] at ⊢
    nlinarith [hh]

-- @realizes A(nonnegative scalar)
-- @realizes B(nonnegative scalar)
-- @realizes \delta(positive infimum variable)
-- @realizes x(arbitrary normed space point) @realizes x_0(first point) @realizes x_1(second point)

end Papers.WassersteinRegretS2S3
