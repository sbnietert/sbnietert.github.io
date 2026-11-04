module
public import Papers.WassersteinRegretS2S3.Helpers.Symmetry

/-!
# Sign symmetries for the second DRO lower bound

Independent reflections of the feature and response tails already give exactly
its one-parameter invariant coefficient family.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Matrix
open scoped Matrix.Norms.Frobenius

-- @node: droTailReflection
/-- In [dimension n](hyp:n), the [tail reflection](goal) is the orthogonal transformation
that fixes the first coordinate and reverses the sign of every remaining coordinate. -/
noncomputable def droTailReflection (n : ℕ) [NeZero n] : Orth n :=
  ⟨Matrix.diagonal (fun i : Fin n => if i = 0 then (1 : ℝ) else -1), by
    apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
    ext i j
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    by_cases hi : i = 0 <;> simp [hi, Matrix.diagonal_apply, Matrix.one_apply]⟩

-- @node: droTailReflection_square
/-- [Applying the tail reflection twice gives the identity transformation](goal). -/
lemma droTailReflection_square (n : ℕ) [NeZero n] :
    droTailReflection n * droTailReflection n = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Mat n n)
  ext i j
  simp only [Matrix.diagonal_mul_diagonal]
  by_cases hi : i = 0 <;> simp [hi, Matrix.diagonal_apply, Matrix.one_apply]

-- @node: droTailReflection_inv
/-- [The inverse of the tail reflection is the tail reflection itself](goal). -/
lemma droTailReflection_inv (n : ℕ) [NeZero n] :
    (droTailReflection n)⁻¹ = droTailReflection n := by
  exact inv_eq_of_mul_eq_one_right (droTailReflection_square n)

-- @node: droTailSignSubgroup
/-- In [dimension n](hyp:n), the [tail-sign subgroup](goal) consists of the identity
and the reflection that fixes the first coordinate and reverses all remaining coordinates. -/
noncomputable def droTailSignSubgroup (n : ℕ) [NeZero n] : Subgroup (Orth n) where
  carrier := {u | u = 1 ∨ u = droTailReflection n}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (droTailReflection_square n)
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl (inv_one)
    · exact Or.inr (droTailReflection_inv n)

-- @node: droTailSignSubgroup_compact
/-- [The subgroup consisting of the identity and the tail reflection is compact](goal). -/
lemma droTailSignSubgroup_compact (n : ℕ) [NeZero n] :
    IsCompact (droTailSignSubgroup n : Set (Orth n)) := by
  have h : (droTailSignSubgroup n : Set (Orth n)) = {1, droTailReflection n} := by
    ext u
    simp [droTailSignSubgroup]
  rw [h]
  exact (Set.toFinite _).isCompact

-- @node: droLowerBSymmetryGroup
/-- For [p feature coordinates](hyp:p) and [m response coordinates](hyp:m), the
[symmetry group for the second distributionally robust lower bound](goal) is the
product of the feature and response tail-sign subgroups, allowing their reflections
to be chosen independently. -/
noncomputable def droLowerBSymmetryGroup (p m : ℕ) [NeZero p] [NeZero m] :
    Subgroup (BlockOrth p m) := (droTailSignSubgroup p).prod (droTailSignSubgroup m)

-- @node: droLowerBSymmetryGroup_compact
/-- [The group of independent feature-tail and response-tail reflections is compact](goal). -/
lemma droLowerBSymmetryGroup_compact (p m : ℕ) [NeZero p] [NeZero m] :
    assDroSymmetryCompactGroup (droLowerBSymmetryGroup p m) := by
  exact (droTailSignSubgroup_compact p).prod (droTailSignSubgroup_compact m)

-- @node: droTailReflection_right
/-- [Right multiplication by the feature-tail reflection preserves entries in the first
column and negates entries in every other column](goal). -/
lemma droTailReflection_right {p m : ℕ} [NeZero p] (A : Mat m p) (i : Fin m) (j : Fin p) :
    (A * (droTailReflection p).val) i j = A i j * (if j = 0 then 1 else -1) := by
  simp [droTailReflection, Matrix.mul_diagonal]

-- @node: droTailReflection_left
/-- [Left multiplication by the transpose of the response-tail reflection preserves
entries in the first row and negates entries in every other row](goal). -/
lemma droTailReflection_left {p m : ℕ} [NeZero m] (A : Mat m p) (i : Fin m) (j : Fin p) :
    ((droTailReflection m).val.transpose * A) i j =
      (if i = 0 then 1 else -1) * A i j := by
  simp [droTailReflection, Matrix.diagonal_mul]

-- @node: droLowerBSymmetryGroup_invariant_iff
/-- [A coefficient matrix is invariant under independent feature-tail and response-tail
reflections if and only if all its entries vanish except possibly the first
response–feature entry, which may be any real number](goal). -/
lemma droLowerBSymmetryGroup_invariant_iff {p m : ℕ} [NeZero p] [NeZero m]
    (A : Mat m p) :
    invariantCoefficient (droLowerBSymmetryGroup p m) A ↔
      ∃ alpha : ℝ, A = fun i j => if i = 0 ∧ j = 0 then alpha else 0 := by
  constructor
  · intro hA
    have hx := hA ⟨(droTailReflection p, 1), Or.inr rfl, Or.inl rfl⟩
    have hy := hA ⟨(1, droTailReflection m), Or.inl rfl, Or.inr rfl⟩
    change (1 : Mat m m).transpose * A * (droTailReflection p).val = A at hx
    change (droTailReflection m).val.transpose * A * (1 : Mat p p) = A at hy
    simp only [Matrix.transpose_one, Matrix.one_mul] at hx
    simp only [Matrix.mul_one] at hy
    refine ⟨A 0 0, ?_⟩
    ext i j
    have hxi := congrArg (fun B : Mat m p => B i j) hx
    have hyi := congrArg (fun B : Mat m p => B i j) hy
    rw [droTailReflection_right] at hxi
    rw [droTailReflection_left] at hyi
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · simp [hi, hj]
    · simp only [hi, hj, if_false] at hxi
      simp only [hi, hj, and_false, if_false]
      linarith
    · simp only [hi, if_false] at hyi
      simp only [hi, false_and, if_false]
      linarith
    · simp only [hi, if_false] at hyi
      simp only [hi, false_and, if_false]
      linarith
  · rintro ⟨alpha, hA⟩ u
    rcases u.property with ⟨hx, hy⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals
      change u.val.2.val.transpose * A * u.val.1.val = A
      rw [hx, hy]
      try simp only [Matrix.UnitaryGroup.one_val, Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one]
    · ext i j
      rw [droTailReflection_left]
      rw [hA]
      by_cases hi : i = 0 <;> simp [hi]
    · ext i j
      rw [droTailReflection_right]
      rw [hA]
      by_cases hj : j = 0 <;> simp [hj]
    · ext i j
      rw [droTailReflection_right, droTailReflection_left]
      rw [hA]
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

end Papers.WassersteinRegretS2S3
