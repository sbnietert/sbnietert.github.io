module
public import Papers.WassersteinRegretS2S3.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Sion

/-!
# Population Wasserstein regret: Helpers/MinimaxConvex

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: finiteDimensional_convex_affine_minimax
/-- In finite-dimensional real normed spaces, suppose [K is compact](hyp:hK),
[convex](hyp:hconv), and [nonempty](hyp:hne), and the real-valued objective is
[jointly continuous](hyp:hcont), [convex in the first variable for each second
variable in K](hyp:hc), and [affine in the second variable on K](hyp:ha).
Then [there is a point y in K for which the infimum over the first variable of the
worst objective over K equals the infimum with the second variable fixed at y,
with both values interpreted in the extended real numbers](goal). -/
lemma finiteDimensional_convex_affine_minimax {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Set F) (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : E → F → ℝ) (hcont : Continuous (Function.uncurry f))
    (hc : ∀ y ∈ K, ConvexOn ℝ Set.univ (fun x => f x y))
    (ha : ∀ x : E, ∀ y ∈ K, ∀ z ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x (a • y + b • z) = a * f x y + b * f x z) :
    ∃ y ∈ K, (⨅ x : E, ⨆ (z : F) (_ : z ∈ K), (f x z : EReal)) = ⨅ x : E, (f x y : EReal) := by
  have hcontx (x : E) : Continuous (fun y => (f x y : EReal)) := by
    exact continuous_coe_real_ereal.comp (hcont.comp (continuous_const.prodMk continuous_id))
  have hconty (y : F) : Continuous (fun x => (f x y : EReal)) := by
    exact continuous_coe_real_ereal.comp (hcont.comp (continuous_id.prodMk continuous_const))
  have hconc (x : E) : ConcaveOn ℝ K (f x) := by
    refine ⟨hconv, ?_⟩
    intro y hy z hz a b ha' hb hab
    exact le_of_eq (ha x y hy z hz a b ha' hb hab).symm
  have hquasiK (x : E) : QuasiconcaveOn ℝ K (fun y => (f x y : EReal)) := by
    simpa only [Function.comp_def] using
      QuasiconcaveOn.monotone_comp (g := fun t : ℝ => (t : EReal))
      (fun _ _ h => EReal.coe_le_coe_iff.mpr h) (hconc x).quasiconcaveOn
  have hquasiE (y : F) (hy : y ∈ K) :
      QuasiconvexOn ℝ Set.univ (fun x => (f x y : EReal)) := by
    simpa only [Function.comp_def] using
      QuasiconvexOn.monotone_comp (g := fun t : ℝ => (t : EReal))
      (fun _ _ h => EReal.coe_le_coe_iff.mpr h) (hc y hy).quasiconvexOn
  have heq : (⨅ x : E, ⨆ z ∈ K, (f x z : EReal)) =
      ⨆ z ∈ K, ⨅ x : E, (f x z : EReal) := by
    -- Put the compact moment variable first by reversing the value order.
    have hd := Sion.minimax' (β := OrderDual EReal)
      (X := K) (Y := Set.univ) (f := fun y x => OrderDual.toDual (f x y : EReal))
      hne hconv hK
      (fun x _ => (hcontx x).continuousOn.upperSemicontinuousOn)
      (fun x _ => (hquasiK x).dual)
      convex_univ
      (fun y hy => (hconty y).continuousOn.lowerSemicontinuousOn)
      (fun y hy => (hquasiE y hy).dual)
    simpa only [ofDual_iSup, ofDual_iInf, OrderDual.ofDual_toDual,
      iSup_univ, iInf_univ] using congrArg OrderDual.ofDual hd.symm
  have husc : UpperSemicontinuousOn (fun y => ⨅ x : E, (f x y : EReal)) K := by
    intro y hy
    exact upperSemicontinuousWithinAt_iInf fun x =>
      ((hcontx x).continuousWithinAt).upperSemicontinuousWithinAt
  obtain ⟨y, hy, hmax⟩ := husc.exists_isMaxOn hne hK
  refine ⟨y, hy, heq.trans ?_⟩
  apply le_antisymm
  · exact iSup₂_le fun z hz => hmax hz
  · exact le_iSup₂_of_le y hy le_rfl

-- @node: finiteDimensional_convex_affine_minimax_ennreal
/-- In finite-dimensional real normed spaces, suppose [K is compact](hyp:hK),
[convex](hyp:hconv), and [nonempty](hyp:hne), and the real-valued objective is
[jointly continuous](hyp:hcont), [convex in the first variable for each second
variable in K](hyp:hc), and [affine in the second variable on K](hyp:ha).
Then [there is a point y in K for which the infimum over the first variable of the
worst nonnegative part of the objective over K equals the infimum of that
nonnegative part with the second variable fixed at y, allowing infinite values](goal). -/
lemma finiteDimensional_convex_affine_minimax_ennreal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Set F) (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : E → F → ℝ) (hcont : Continuous (Function.uncurry f))
    (hc : ∀ y ∈ K, ConvexOn ℝ Set.univ (fun x => f x y))
    (ha : ∀ x : E, ∀ y ∈ K, ∀ z ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x (a • y + b • z) = a * f x y + b * f x z) :
    ∃ y ∈ K, (⨅ x : E, ⨆ (z : F) (_ : z ∈ K), ENNReal.ofReal (f x z)) =
      ⨅ x : E, ENNReal.ofReal (f x y) := by
  have hcontx (x : E) : Continuous (fun y => ENNReal.ofReal (f x y)) := by
    exact ENNReal.continuous_ofReal.comp (hcont.comp (continuous_const.prodMk continuous_id))
  have hconty (y : F) : Continuous (fun x => ENNReal.ofReal (f x y)) := by
    exact ENNReal.continuous_ofReal.comp (hcont.comp (continuous_id.prodMk continuous_const))
  have hconc (x : E) : ConcaveOn ℝ K (f x) := by
    refine ⟨hconv, ?_⟩
    intro y hy z hz a b ha' hb hab
    exact le_of_eq (ha x y hy z hz a b ha' hb hab).symm
  have hquasiK (x : E) : QuasiconcaveOn ℝ K (fun y => ENNReal.ofReal (f x y)) := by
    simpa only [Function.comp_def] using
      QuasiconcaveOn.monotone_comp (g := fun t : ℝ => ENNReal.ofReal t)
      (fun _ _ h => ENNReal.ofReal_le_ofReal h) (hconc x).quasiconcaveOn
  have hquasiE (y : F) (hy : y ∈ K) :
      QuasiconvexOn ℝ Set.univ (fun x => ENNReal.ofReal (f x y)) := by
    simpa only [Function.comp_def] using
      QuasiconvexOn.monotone_comp (g := fun t : ℝ => ENNReal.ofReal t)
      (fun _ _ h => ENNReal.ofReal_le_ofReal h) (hc y hy).quasiconvexOn
  have heq : (⨅ x : E, ⨆ z ∈ K, ENNReal.ofReal (f x z)) =
      ⨆ z ∈ K, ⨅ x : E, ENNReal.ofReal (f x z) := by
    -- Put the compact moment variable first by reversing the value order.
    have hd := Sion.minimax' (β := OrderDual ℝ≥0∞)
      (X := K) (Y := Set.univ) (f := fun y x => OrderDual.toDual (ENNReal.ofReal (f x y)))
      hne hconv hK
      (fun x _ => (hcontx x).continuousOn.upperSemicontinuousOn)
      (fun x _ => (hquasiK x).dual)
      convex_univ
      (fun y hy => (hconty y).continuousOn.lowerSemicontinuousOn)
      (fun y hy => (hquasiE y hy).dual)
    simpa only [ofDual_iSup, ofDual_iInf, OrderDual.ofDual_toDual,
      iSup_univ, iInf_univ] using congrArg OrderDual.ofDual hd.symm
  have husc : UpperSemicontinuousOn (fun y => ⨅ x : E, ENNReal.ofReal (f x y)) K := by
    intro y hy
    exact upperSemicontinuousWithinAt_iInf fun x =>
      ((hcontx x).continuousWithinAt).upperSemicontinuousWithinAt
  obtain ⟨y, hy, hmax⟩ := husc.exists_isMaxOn hne hK
  refine ⟨y, hy, heq.trans ?_⟩
  apply le_antisymm
  · exact iSup₂_le fun z hz => hmax hz
  · exact le_iSup₂_of_le y hy le_rfl

end Papers.WassersteinRegretS2S3
