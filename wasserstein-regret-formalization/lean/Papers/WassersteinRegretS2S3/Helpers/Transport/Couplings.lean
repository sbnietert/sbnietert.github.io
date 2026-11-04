module
public import Papers.WassersteinRegretS2S3.Basic
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Population Wasserstein regret: Helpers/Transport/Couplings

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @node: couplings_nonempty
/-- For [two observation laws with finite second moments](hyp:P,Q),
[there exists a joint distribution with these laws as its marginals](goal). -/
lemma couplings_nonempty {p m : ℕ} (P Q : JointLaws p m) : Nonempty (Couplings P Q) := by
  let pi : ProbabilityMeasure (Observation p m × Observation p m) :=
    ⟨(lawMeasure P).prod (lawMeasure Q), inferInstance⟩
  refine ⟨⟨pi, ?_, ?_⟩⟩ <;> simp [pi]

-- @node: coupling_squared_cost_integrable
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [the squared Euclidean distance between the
paired observations is integrable under the coupling](goal). -/
lemma coupling_squared_cost_integrable {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    Integrable (fun z : Observation p m × Observation p m => ‖z.1 - z.2‖ ^ 2)
      (pi.val : Measure (Observation p m × Observation p m)) := by
  have hfst : MemLp (fun z : Observation p m × Observation p m => z.1) 2
      (pi.val : Measure (Observation p m × Observation p m)) := by
    have h := P.carrier.property
    change MemLp id 2 (lawMeasure P) at h
    rw [← pi.property.1] at h
    exact h.comp_of_map (by fun_prop)
  have hsnd : MemLp (fun z : Observation p m × Observation p m => z.2) 2
      (pi.val : Measure (Observation p m × Observation p m)) := by
    have h := Q.carrier.property
    change MemLp id 2 (lawMeasure Q) at h
    rw [← pi.property.2] at h
    exact h.comp_of_map (by fun_prop)
  exact (hfst.sub hsnd).norm.integrable_sq

-- @node: couplingCost_nonneg
/-- For [a probability distribution on pairs of observations](hyp:pi),
[the root mean squared distance between the paired observations is nonnegative](goal). -/
lemma couplingCost_nonneg {p m : ℕ}
    (pi : ProbabilityMeasure (Observation p m × Observation p m)) :
    0 ≤ couplingCost pi := Real.sqrt_nonneg _

-- @node: couplingCost_bddBelow
/-- For [two observation laws with finite second moments](hyp:P,Q),
[the set of root mean squared transport costs over all their couplings is bounded below](goal). -/
lemma couplingCost_bddBelow {p m : ℕ} (P Q : JointLaws p m) :
    BddBelow {c : ℝ | ∃ pi : Couplings P Q, couplingCost pi.val = c} := by
  refine ⟨0, ?_⟩
  rintro c ⟨pi, rfl⟩
  exact couplingCost_nonneg pi.val

-- @node: wasserstein_le_couplingCost
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling of these laws](hyp:pi), [their quadratic Wasserstein distance is at
most the coupling's root mean squared transport cost](goal). -/
lemma wasserstein_le_couplingCost {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    wassersteinDistance P Q ≤ couplingCost pi.val :=
  csInf_le (couplingCost_bddBelow P Q) ⟨pi, rfl⟩

-- @node: wasserstein_nonneg
/-- For [two observation laws with finite second moments](hyp:P,Q),
[their quadratic Wasserstein distance is nonnegative](goal). -/
lemma wasserstein_nonneg {p m : ℕ} (P Q : JointLaws p m) : 0 ≤ wassersteinDistance P Q := by
  obtain ⟨pi⟩ := couplings_nonempty P Q
  unfold wassersteinDistance
  refine le_csInf ?_ ?_
  · exact ⟨couplingCost pi.val, pi, rfl⟩
  · rintro c ⟨gamma, rfl⟩
    exact couplingCost_nonneg gamma.val

-- @node: wasserstein_self
/-- For [an observation law with finite second moments](hyp:P),
[its quadratic Wasserstein distance from itself is zero](goal). -/
lemma wasserstein_self {p m : ℕ} (P : JointLaws p m) : wassersteinDistance P P = 0 := by
  let pi := P.carrier.val.map (f := fun z : Observation p m => (z, z)) (by fun_prop)
  have hpi : pi ∈ {pi : ProbabilityMeasure (Observation p m × Observation p m) |
      Measure.map Prod.fst (pi : Measure (Observation p m × Observation p m)) = lawMeasure P ∧
      Measure.map Prod.snd (pi : Measure (Observation p m × Observation p m)) = lawMeasure P} := by
    constructor <;>
      (simp only [pi, ProbabilityMeasure.toMeasure_map]
       rw [Measure.map_map (by fun_prop) (by fun_prop)]
       exact Measure.map_id)
  have hc : couplingCost pi = 0 := by
    unfold couplingCost
    rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
    simp
  apply le_antisymm _ (wasserstein_nonneg P P)
  calc
    wassersteinDistance P P ≤ couplingCost pi := wasserstein_le_couplingCost P P ⟨pi, hpi⟩
    _ = 0 := hc

-- @node: coupling_swap
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a coupling from the first law to the second](hyp:pi), [there exists a coupling
in the reverse direction with the same root mean squared transport cost](goal). -/
lemma coupling_swap {p m : ℕ} (P Q : JointLaws p m) (pi : Couplings P Q) :
    ∃ gamma : Couplings Q P, couplingCost gamma.val = couplingCost pi.val := by
  let gamma := pi.val.map (f := Prod.swap) (by fun_prop)
  have hgamma : Measure.map Prod.fst (gamma : Measure (Observation p m × Observation p m)) =
      lawMeasure Q ∧
      Measure.map Prod.snd (gamma : Measure (Observation p m × Observation p m)) =
        lawMeasure P := by
    constructor
    · simp only [gamma, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      exact pi.property.2
    · simp only [gamma, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      exact pi.property.1
  refine ⟨⟨gamma, hgamma⟩, ?_⟩
  unfold couplingCost
  change Real.sqrt (∫ z : Observation p m × Observation p m, ‖z.1 - z.2‖ ^ 2
    ∂(gamma : Measure (Observation p m × Observation p m))) = _
  rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
  simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

-- @node: wasserstein_symm
/-- For [two observation laws with finite second moments](hyp:P,Q),
[their quadratic Wasserstein distance is unchanged when the laws are exchanged](goal). -/
lemma wasserstein_symm {p m : ℕ} (P Q : JointLaws p m) :
    wassersteinDistance P Q = wassersteinDistance Q P := by
  unfold wassersteinDistance
  congr 1
  ext c
  constructor
  · rintro ⟨pi, rfl⟩
    obtain ⟨gamma, hgamma⟩ := coupling_swap P Q pi
    exact ⟨gamma, hgamma⟩
  · rintro ⟨pi, rfl⟩
    obtain ⟨gamma, hgamma⟩ := coupling_swap Q P pi
    exact ⟨gamma, hgamma⟩

-- @node: wasserstein_approx_coupling
/-- For [two observation laws with finite second moments](hyp:P,Q) and
[a real tolerance](hyp:delta) that [is strictly positive](hyp:hd),
[there exists a coupling whose root mean squared transport cost is less than
their quadratic Wasserstein distance plus that tolerance](goal). -/
lemma wasserstein_approx_coupling {p m : ℕ} (P Q : JointLaws p m) (delta : ℝ) (hd : 0 < delta) :
    ∃ pi : Couplings P Q, couplingCost pi.val < wassersteinDistance P Q + delta := by
  obtain ⟨pi⟩ := couplings_nonempty P Q
  obtain ⟨c, ⟨gamma, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (s := {c : ℝ | ∃ pi : Couplings P Q, couplingCost pi.val = c})
    ⟨couplingCost pi.val, pi, rfl⟩ (lt_add_of_pos_right _ hd)
  exact ⟨gamma, hc⟩

-- @node: couplings_gluing
/-- For [three observation laws with finite second moments](hyp:P,Q,T),
[a coupling of the first and second laws](hyp:pi), and [a coupling of the second
and third laws](hyp:rho), [there exists a joint distribution of three observations
whose first two and last two observations have the respective given couplings](goal).

Disintegrating the second coupling over its first marginal provides the joint
distribution on the Euclidean observation space. -/
lemma couplings_gluing {p m : ℕ} (P Q T : JointLaws p m)
    (pi : Couplings P Q) (rho : Couplings Q T) :
    ∃ xi : ProbabilityMeasure ((Observation p m × Observation p m) × Observation p m),
      Measure.map Prod.fst
        (xi : Measure ((Observation p m × Observation p m) × Observation p m)) =
          (pi.val : Measure (Observation p m × Observation p m)) ∧
      Measure.map (fun z : (Observation p m × Observation p m) × Observation p m =>
        (z.1.2, z.2))
        (xi : Measure ((Observation p m × Observation p m) × Observation p m)) =
          (rho.val : Measure (Observation p m × Observation p m)) := by
  let k := (rho.val : Measure (Observation p m × Observation p m)).condKernel
  let mu : Measure ((Observation p m × Observation p m) × Observation p m) :=
    (pi.val : Measure (Observation p m × Observation p m)).compProd (k.prodMkLeft (Observation p m))
  refine ⟨⟨mu, inferInstance⟩, ?_, ?_⟩
  · exact Measure.fst_compProd _ _
  · ext s hs
    rw [Measure.map_apply (by fun_prop) hs]
    change mu ((fun z => (z.1.2, z.2)) ⁻¹' s) = _
    rw [Measure.compProd_apply (hs.preimage (by fun_prop))]
    change (∫⁻ z, k z.2 {w | (z.2, w) ∈ s}
      ∂(pi.val : Measure (Observation p m × Observation p m))) = _
    have hmeas : Measurable (fun z => k z {w | (z, w) ∈ s}) :=
      ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs
    rw [← lintegral_map hmeas measurable_snd, pi.property.2]
    have hdis := (rho.val : Measure (Observation p m × Observation p m)).disintegrate k
    rw [show (rho.val : Measure (Observation p m × Observation p m)).fst = lawMeasure Q
      from rho.property.1] at hdis
    rw [← hdis, Measure.compProd_apply hs]
    rfl

-- @node: root_mean_square_eq_lpNorm
/-- If [a function into a normed additive group is strongly measurable almost
everywhere under a measure](hyp:hf), [the square root of the integral of its
squared norm equals its L2 norm](goal). -/
lemma root_mean_square_eq_lpNorm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {mu : Measure Ω} {f : Ω → E}
    (hf : AEStronglyMeasurable f mu) :
    Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂mu) = lpNorm f 2 mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  norm_num

-- @node: coupling_gluing_cost_le
/-- For [three observation laws with finite second moments](hyp:P,Q,T),
[a coupling of the first and second laws](hyp:pi), and [a coupling of the second
and third laws](hyp:rho), [there exists a coupling of the first and third laws
whose root mean squared transport cost is at most the sum of the two given costs](goal). -/
lemma coupling_gluing_cost_le {p m : ℕ} (P Q T : JointLaws p m)
    (pi : Couplings P Q) (rho : Couplings Q T) :
    ∃ gamma : Couplings P T,
      couplingCost gamma.val ≤ couplingCost pi.val + couplingCost rho.val := by
  obtain ⟨xi, hxy, hyz⟩ := couplings_gluing P Q T pi rho
  let mu : Measure ((Observation p m × Observation p m) × Observation p m) := xi
  have hx : Measure.map (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.1.1) mu = lawMeasure P := by
    change Measure.map (Prod.fst ∘ Prod.fst) mu = _
    rw [← Measure.map_map measurable_fst measurable_fst, hxy]
    exact pi.property.1
  have hy : Measure.map (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.1.2) mu = lawMeasure Q := by
    change Measure.map (Prod.snd ∘ Prod.fst) mu = _
    rw [← Measure.map_map measurable_snd measurable_fst, hxy]
    exact pi.property.2
  have hz : Measure.map (Prod.snd : (Observation p m × Observation p m) × Observation p m →
      Observation p m) mu = lawMeasure T := by
    have h := congrArg (Measure.map Prod.snd) hyz
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
    exact h.trans rho.property.2
  have hX : MemLp (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.1.1) 2 mu := by
    have h := P.carrier.property
    change MemLp id 2 (lawMeasure P) at h
    rw [← hx] at h
    exact h.comp_of_map (by fun_prop)
  have hY : MemLp (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.1.2) 2 mu := by
    have h := Q.carrier.property
    change MemLp id 2 (lawMeasure Q) at h
    rw [← hy] at h
    exact h.comp_of_map (by fun_prop)
  have hZ : MemLp (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.2) 2 mu := by
    have h := T.carrier.property
    change MemLp id 2 (lawMeasure T) at h
    rw [← hz] at h
    exact h.comp_of_map (by fun_prop)
  let g := xi.map (f := fun z => (z.1.1, z.2)) (by fun_prop)
  have hg : Measure.map Prod.fst (g : Measure (Observation p m × Observation p m)) =
      lawMeasure P ∧
      Measure.map Prod.snd (g : Measure (Observation p m × Observation p m)) =
        lawMeasure T := by
    constructor <;>
      simp only [g, ProbabilityMeasure.toMeasure_map] <;>
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    · exact hx
    · exact hz
  refine ⟨⟨g, hg⟩, ?_⟩
  have hleft : lpNorm (fun z => z.1.1 - z.1.2) 2 mu = couplingCost pi.val := by
    rw [← root_mean_square_eq_lpNorm (mu := mu) (f := fun z => z.1.1 - z.1.2)
      (hX.sub hY).aestronglyMeasurable]
    unfold couplingCost
    rw [← hxy, integral_map (by fun_prop) (by fun_prop)]
  have hright : lpNorm (fun z => z.1.2 - z.2) 2 mu = couplingCost rho.val := by
    rw [← root_mean_square_eq_lpNorm (mu := mu) (f := fun z => z.1.2 - z.2)
      (hY.sub hZ).aestronglyMeasurable]
    unfold couplingCost
    rw [← hyz, integral_map (by fun_prop) (by fun_prop)]
  have hend : couplingCost g = lpNorm (fun z => z.1.1 - z.2) 2 mu := by
    unfold couplingCost
    rw [ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
    exact root_mean_square_eq_lpNorm (hX.sub hZ).aestronglyMeasurable
  rw [hend, ← hleft, ← hright]
  have hsum : (fun z : (Observation p m × Observation p m) × Observation p m =>
      z.1.1 - z.2) = (fun z => z.1.1 - z.1.2) + (fun z => z.1.2 - z.2) := by
    ext z
    simp
  rw [hsum]
  exact lpNorm_add_le (hX.sub hY) (by norm_num)

-- @node: wasserstein_triangle
/-- For [three observation laws with finite second moments](hyp:P,Q,T),
[the quadratic Wasserstein distance from the first to the third is at most
the distance from the first to the second plus the distance from the second
to the third](goal). -/
lemma wasserstein_triangle {p m : ℕ} (P Q T : JointLaws p m) :
    wassersteinDistance P T ≤ wassersteinDistance P Q + wassersteinDistance Q T := by
  apply le_of_forall_pos_le_add
  intro delta hd
  obtain ⟨pi, hpi⟩ := wasserstein_approx_coupling P Q (delta / 2) (by positivity)
  obtain ⟨rho, hrho⟩ := wasserstein_approx_coupling Q T (delta / 2) (by positivity)
  obtain ⟨gamma, hgamma⟩ := coupling_gluing_cost_le P Q T pi rho
  have hbound := (wasserstein_le_couplingCost P T gamma).trans hgamma
  linarith

end Papers.WassersteinRegretS2S3
