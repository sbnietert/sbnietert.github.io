module
public import Papers.WassersteinRegretS2S3.Helpers.LawDefs
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Order.SaddlePoint
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Population Wasserstein regret: Basic

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open MeasureTheory
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

attribute [local instance] Classical.propDecidable
-- @env: S3
variable {p m : ℕ} [NeZero p] [NeZero m]

/-- With [feature dimension p](hyp:p) and [response dimension m](hyp:m), an
[estimator](goal) assigns a coefficient matrix to each joint law with finite second moments. -/
abbrev Estimator (p m : ℕ) := JointLaws p m → Mat m p
-- @realizes \hat{\bA}(arbitrary law to coefficient rule)
/-- For [a joint law P](hyp:P) and [a nonnegative radius](hyp:eps), the
[Wasserstein ball](goal) consists of all joint laws at Wasserstein distance at most that radius from P. -/
abbrev lawBall {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) : Set (JointLaws p m) :=
  {Q | wassersteinDistance P Q ≤ eps}
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a nonnegative radius](hyp:eps),
the [Bures ball](goal) consists of positive semidefinite matrices at Bures distance at most that radius from Sigma. -/
abbrev matrixBall {n : ℕ} (Sigma : PSD n) (eps : ℝ≥0) : Set (PSD n) :=
  {T | buresDistance T.val Sigma.val ≤ eps}

-- @node: def:robust-regret
/-- For [an estimator rule](hyp:rule), [a reference law P](hyp:P), and [a radius](hyp:eps),
the [robust regret](goal) is the supremum over laws Q in the Wasserstein ball of the larger of
the regret under Q of the rule fitted to P and the regret under P of the rule fitted to Q. -/
noncomputable def robustRegret {p m : ℕ} (rule : Estimator p m)
    (P : JointLaws p m) (eps : ℝ≥0) : ℝ≥0∞ :=
  ⨆ Q ∈ lawBall P eps,
    max (ENNReal.ofReal (regret (rule P) Q)) (ENNReal.ofReal (regret (rule Q) P))
-- @realizes R_\eps(supremum of both source and target regret orientations)

-- @node: def:local-minimax
/-- For [a reference law P](hyp:P) and [a radius](hyp:eps), the [local minimax regret](goal)
is the infimum of robust regret over all law-to-coefficient estimator rules. -/
noncomputable def localMinimax {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) : ℝ≥0∞ :=
  ⨅ rule : Estimator p m, robustRegret rule P eps
-- @realizes R_\eps^\star(infimum over all law level estimators)

/-- Given [an objective index from zero to three](hyp:o), [a reference law P](hyp:P),
[a radius](hyp:eps), and [a coefficient matrix A](hyp:A), the [population objective](goal)
is [risk under P for index zero](step:1), [worst risk over the Wasserstein ball for index one](step:2),
[worst regret over that ball for index two](step:3), or
[risk under P plus the squared radius times the squared operator norm of A for index three](step:4). -/
noncomputable def populationObjective {p m : ℕ} (o : Fin 4) (P : JointLaws p m)
    (eps : ℝ≥0) (A : Mat m p) : ℝ≥0∞ :=
  if o = 0 then ENNReal.ofReal (risk A P)
  else if o = 1 then ⨆ Q ∈ lawBall P eps, ENNReal.ofReal (risk A Q)
  else if o = 2 then ⨆ Q ∈ lawBall P eps, ENNReal.ofReal (regret A Q)
  else ENNReal.ofReal (risk A P + (eps : ℝ) ^ 2 * opNorm A ^ 2)

/-- For [an objective index](hyp:o), [a reference law](hyp:P), and [a radius](hyp:eps),
the [population minimizer set](goal) contains every coefficient matrix that globally minimizes the corresponding population objective. -/
noncomputable def populationMinimizers {p m : ℕ} (o : Fin 4) (P : JointLaws p m) (eps : ℝ≥0) :=
  {A : Mat m p | IsMinOn (populationObjective o P eps) Set.univ A}

/-- For [an objective index](hyp:o) and [a radius](hyp:eps), [an estimator rule](hyp:rule)
is [a population selection](goal) if it returns a global minimizer of that objective at every joint law. -/
noncomputable def IsPopulationSelection {p m : ℕ} (o : Fin 4) (eps : ℝ≥0) (rule : Estimator p
  m) : Prop :=
  ∀ P, rule P ∈ populationMinimizers o P eps

/-- For [a radius](hyp:eps), the [population estimator collection](goal) consists of four
law-to-coefficient rules, each globally minimizing its respective objective at every law:
ordinary risk, worst risk in the Wasserstein ball, worst regret in that ball, and risk regularized
by the squared radius times the squared operator norm.

Their values at a fixed law `P` are obtained by evaluation at `P`.
Every admissible selection is included; no particular minimizer is chosen. -/
-- @node: def:population-estimators
noncomputable def populationEstimators {p m : ℕ} (eps : ℝ≥0) : Type :=
  { ERM : Estimator p m // -- @realizes \ERM(arbitrary all-law risk argmin rule)
    IsPopulationSelection 0 eps ERM } ×
  { DRO : Estimator p m // -- @realizes \DRO_\eps(arbitrary all-law worst-risk argmin rule)
    IsPopulationSelection 1 eps DRO } ×
  { MRO : Estimator p m // -- @realizes \MRO_\eps(arbitrary all-law worst-regret argmin rule)
    IsPopulationSelection 2 eps MRO } ×
  { SNR : Estimator p m // -- @realizes \SNR_\eps(arbitrary all-law regularized-risk argmin rule)
    IsPopulationSelection 3 eps SNR }

-- @node: def:class-regrets
/-- For [a class of joint laws](hyp:G), [a radius](hyp:eps), and [an estimator rule](hyp:rule),
the [class regret pair](goal) records the supremum of the rule's robust regret over the class
and the infimum of that supremum over all estimator rules. -/
noncomputable def classRegrets {p m : ℕ} (G : Set (JointLaws p m)) (eps : ℝ≥0)
    (rule : Estimator p m) : (ℝ≥0∞) × (ℝ≥0∞) :=
  (⨆ P ∈ G, robustRegret rule P eps,
   ⨅ a : Estimator p m, ⨆ P ∈ G, robustRegret a P eps)
-- @realizes \cG(arbitrary class of finite second moment laws)
/-- For [a class of joint laws](hyp:G), [a radius](hyp:eps), and [an estimator rule](hyp:rule),
the [class risk](goal) is the supremum of the rule's robust regret over laws in that class. -/
noncomputable def classRisk {p m : ℕ} (G : Set (JointLaws p m)) (eps : ℝ≥0) (rule : Estimator p
  m) :=
  (classRegrets G eps rule).1
/-- For [a class of joint laws](hyp:G) and [a radius](hyp:eps), the [class minimax value](goal)
is the infimum over estimator rules of their worst robust regret across the class. -/
noncomputable def classMinimax {p m : ℕ} (G : Set (JointLaws p m)) (eps : ℝ≥0) : ℝ≥0∞ :=
  ⨅ rule : Estimator p m, classRisk G eps rule

/-- The [positive-radius limiting filter](goal) describes nonnegative radii approaching zero through strictly positive values. -/
abbrev positiveRadii := nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)
-- @realizes \eps(nonnegative radii tending to zero through positive radii)

-- @node: def:condition-number
/-- For [a joint law P](hyp:P), the [condition number](goal) is
[the limit superior of local minimax regret divided by squared radius as positive radii tend to zero, when the feature second moment is positive definite](step:1),
and [infinity otherwise](step:2). -/
noncomputable def conditionNumber {p m : ℕ} (P : JointLaws p m) : ℝ≥0∞ :=
  if (secondMomentX P).PosDef then
    Filter.limsup (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * localMinimax P eps) positiveRadii
  else ⊤
-- @realizes \kappa_P(positive radius limsup; infinity outside the nondegenerate class)

-- @node: def:well-conditioned-family
/-- With [feature dimension p](hyp:p), [response dimension m](hyp:m), and
[a real condition-number bound](hyp:kappa), the [well-conditioned family type](goal)
packages [a law with positive definite feature second moment whose condition number is at most the nonnegative part of the bound](step:1). -/
structure WellConditionedFamily (p m : ℕ) (kappa : ℝ) where
  carrier : -- @realizes \cG(\kappa)(nondegenerate laws with)
    {P : NondegenerateLaws p m // conditionNumber P.carrier.val ≤ ENNReal.ofReal kappa}
/-- For [feature dimension p](hyp:p), [response dimension m](hyp:m), and
[a real condition-number bound](hyp:kappa), the [well-conditioned set](goal) consists of joint laws
with positive definite feature second moments and condition numbers at most the nonnegative part of the bound. -/
noncomputable def wellConditionedSet (p m : ℕ) (kappa : ℝ) : Set (JointLaws p m) :=
  {P | (secondMomentX P).PosDef ∧ conditionNumber P ≤ ENNReal.ofReal kappa}

/-- For [a positive semidefinite reference second-moment matrix](hyp:Sigma), [a radius](hyp:eps),
and [a coefficient matrix A](hyp:A), the [worst matrix regret](goal) is the supremum of A's regret
over positive semidefinite matrices in the reference matrix's Bures ball. -/
noncomputable def matrixWorstRegret {p m : ℕ} (Sigma : PSD (p + m)) (eps : ℝ≥0) (A : Mat m p) :
  ℝ≥0∞ :=
  ⨆ T ∈ matrixBall Sigma eps, ENNReal.ofReal (matrixRegret A T.val)
/-- For [a positive semidefinite reference second-moment matrix](hyp:Sigma) and [a radius](hyp:eps),
the [matrix minimax value](goal) is the infimum over coefficient matrices of their worst regret in the Bures ball. -/
noncomputable def matrixMinimaxValue {p m : ℕ} (Sigma : PSD (p + m)) (eps : ℝ≥0) : ℝ≥0∞ :=
  ⨅ A : Mat m p, matrixWorstRegret Sigma eps A
-- @realizes \kappa(matrix condition-number functional; in particular on C*)
/-- For [a positive semidefinite second-moment matrix](hyp:Sigma), the [matrix condition number](goal)
is the limit superior of the matrix minimax value divided by squared radius as positive radii tend to zero. -/
noncomputable def matrixCondition {p m : ℕ} (Sigma : PSD (p + m)) : ℝ≥0∞ :=
  Filter.limsup (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * matrixMinimaxValue Sigma eps) positiveRadii
-- @realizes \kappa(\bSigma)(positive radius minimax limsup)

-- @node: def:matrix-local-minimax
/-- For [a second-moment matrix with positive definite feature block](hyp:Sigma) and [a radius](hyp:eps),
the [matrix local minimax pair](goal) records the matrix minimax value at that radius and the matrix condition number. -/
noncomputable def matrixLocalMinimax {p m : ℕ} (Sigma : NondegenerateSecondMoments p m) (eps :
  ℝ≥0) :=
  (matrixMinimaxValue Sigma.carrier.val eps, matrixCondition Sigma.carrier.val)

/-- Given [an objective index from zero to three](hyp:o), [a positive semidefinite reference second-moment matrix](hyp:Sigma),
[a radius](hyp:eps), and [a coefficient matrix A](hyp:A), the [matrix objective](goal) is
[risk at the reference matrix for index zero](step:1), [worst risk over its Bures ball for index one](step:2),
[worst regret over that ball for index two](step:3), or
[reference risk plus the squared radius times the squared operator norm of A for index three](step:4). -/
noncomputable def matrixObjective {p m : ℕ} (o : Fin 4) (Sigma : PSD (p + m))
    (eps : ℝ≥0) (A : Mat m p) : ℝ≥0∞ :=
  if o = 0 then ENNReal.ofReal (matrixRisk A Sigma.val)
  else if o = 1 then ⨆ T ∈ matrixBall Sigma eps, ENNReal.ofReal (matrixRisk A T.val)
  else if o = 2 then matrixWorstRegret Sigma eps A
  else ENNReal.ofReal (matrixRisk A Sigma.val + (eps : ℝ) ^ 2 * opNorm A ^ 2)
/-- For [an objective index](hyp:o), [a positive semidefinite reference second-moment matrix](hyp:Sigma),
and [a radius](hyp:eps), the [matrix minimizer set](goal) consists of all coefficient matrices globally minimizing the corresponding matrix objective. -/
noncomputable def matrixMinimizers {p m : ℕ} (o : Fin 4) (Sigma : PSD (p + m)) (eps : ℝ≥0) :=
  {A : Mat m p | IsMinOn (matrixObjective o Sigma eps) Set.univ A}

/-- For [a positive semidefinite reference second-moment matrix](hyp:Sigma) and [a radius](hyp:eps),
the [matrix estimator collection](goal) consists of four coefficient matrices globally minimizing,
respectively, reference risk, worst risk in the Bures ball, worst regret in that ball, and
reference risk regularized by the squared radius times the squared operator norm.

Every inhabitant is an admissible selection; no particular minimizer is chosen. -/
-- @node: def:matrix-estimators
noncomputable def matrixEstimators {p m : ℕ} (Sigma : PSD (p + m)) (eps : ℝ≥0) : Type :=
  { ERM : Mat m p // ERM ∈ matrixMinimizers 0 Sigma eps } × -- @realizes \ERM(value and argmin)
  { DRO : Mat m p // DRO ∈ matrixMinimizers 1 Sigma eps } × -- @realizes \DRO_\eps(value and argmin)
  { MRO : Mat m p // MRO ∈ matrixMinimizers 2 Sigma eps } × -- @realizes \MRO_\eps(value and argmin)
  { SNR : Mat m p // SNR ∈ matrixMinimizers 3 Sigma eps } -- @realizes \SNR_\eps(value and argmin)

/-- For [a positive semidefinite reference second-moment matrix](hyp:Sigma) and [a radius](hyp:eps),
the [alternative value](goal) is the supremum, over its Bures ball, of the regret at the reference matrix
of the canonical coefficient fitted to each perturbed matrix. -/
noncomputable def alternativeValue {p m : ℕ} (Sigma : PSD (p + m)) (eps : ℝ≥0) : ℝ≥0∞ :=
  ⨆ T ∈ matrixBall Sigma eps, ENNReal.ofReal (matrixRegret (canonicalCoefficient T.val) Sigma.val)

-- @node: def:alternative-condition-number
/-- For [a second-moment matrix with positive definite feature block](hyp:Sigma),
the [alternative condition number](goal) is the limit superior of the alternative value divided by squared radius as positive radii tend to zero. -/
noncomputable def alternativeConditionNumber {p m : ℕ} (Sigma : NondegenerateSecondMoments p m)
  : ℝ≥0∞ :=
  Filter.limsup (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * alternativeValue Sigma.carrier.val eps)
    positiveRadii
-- @realizes \tilde{\kappa}(limsup over the full PSD Bures ball)

/-- For [a second-moment matrix with positive definite feature block](hyp:Sigma),
the [lower asymptotic coefficient](goal) is the limit inferior of the matrix minimax value divided by squared radius as positive radii tend to zero. -/
noncomputable def lowerAsymptoticCoefficient {p m : ℕ} (Sigma : NondegenerateSecondMoments p m)
  : ℝ≥0∞ :=
  Filter.liminf (fun eps : ℝ≥0 => (eps : ℝ≥0∞)⁻¹ ^ 2 * matrixMinimaxValue Sigma.carrier.val
    eps) positiveRadii
-- @realizes J_\bSigma(positive radius liminf of normalized minimax value)

-- @node: def:dro-regularizer-scale
/-- For [a law with positive definite feature second moment](hyp:P), the [DRO regularizer scale](goal)
is the square root of the trace of the residual second-moment matrix multiplied by the sum of the identity
and the optimal coefficient matrix times its transpose. -/
noncomputable def droRegularizerScale {p m : ℕ} (P : NondegenerateLaws p m) : ℝ :=
  Real.sqrt (Matrix.trace (((1 : Mat m m) + optimalPredictor P * (optimalPredictor P).transpose) *
    residualSecondMoment P))
-- @realizes \Gamma_P(square root of trace)

-- @node: ass:dro-strong-duality-diagonal
/-- For [a joint law](hyp:_P), [a radius](hyp:eps), [a coefficient matrix A](hyp:A), and
[real diagonal parameters a](hyp:a), the [diagonal strong-duality assumption](goal) requires
[a strictly positive radius](step:1) and [that A times its transpose be diagonal with entries equal to the squares of a](step:2). -/
def assDroStrongDualityDiagonal {p m : ℕ} (_P : JointLaws p m) (eps : ℝ≥0)
    (A : Mat m p) (a : Fin m → ℝ) : Prop :=
  0 < eps ∧ A * A.transpose = Matrix.diagonal (fun i => (a i) ^ 2)
-- @realizes a_i(real diagonal parameters with unrestricted signs)

-- @node: ass:perturbed-condition-number-radius
/-- For [a reference second-moment matrix with positive definite feature block](hyp:Sigma)
and [a positive semidefinite perturbed matrix](hyp:barSigma), the [perturbation-radius assumption](goal)
requires their Bures distance to be at most half the square root of the smallest eigenvalue of the reference feature block. -/
def assPerturbedConditionNumberRadius {p m : ℕ} (Sigma : NondegenerateSecondMoments p m)
    (barSigma : PSD (p + m)) : Prop :=
  buresDistance barSigma.val Sigma.carrier.val.val ≤ Real.sqrt (lambdaMin (blockX p m
    Sigma.carrier.val.val)) / 2
-- @realizes \bar{\bSigma}(arbitrary PSD perturbation satisfying the radius bound)

-- @node: ass:stability-implications-small-radius
/-- For [a joint law](hyp:P) and [a radius](hyp:eps), the [small-radius stability assumption](goal)
requires the squared radius to be at most one sixteenth of the smallest eigenvalue of the feature second-moment matrix. -/
def assStabilityImplicationsSmallRadius {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) : Prop :=
  (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 16
-- @node: ass:stability-implications-erm-small-radius
/-- For [a joint law](hyp:P) and [a radius](hyp:eps), the [ERM small-radius stability assumption](goal)
requires the squared radius to be at most one quarter of the smallest eigenvalue of the feature second-moment matrix. -/
def assStabilityImplicationsErmSmallRadius {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) : Prop :=
  (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 4
-- @node: ass:stability-implications-dro-small-radius
/-- For [a joint law](hyp:P) and [a radius](hyp:eps), the [DRO small-radius stability assumption](goal)
requires the squared radius to be at most one sixteenth of the smallest eigenvalue of the feature second-moment matrix. -/
def assStabilityImplicationsDroSmallRadius {p m : ℕ} (P : JointLaws p m) (eps : ℝ≥0) : Prop :=
  (eps : ℝ) ^ 2 ≤ lambdaMin (secondMomentX P) / 16

/-- With [feature dimension p](hyp:p) and [response dimension m](hyp:m), the [block orthogonal group](goal)
consists of pairs of orthogonal transformations acting separately on features and responses. -/
abbrev BlockOrth (p m : ℕ) := Orth p × Orth m
-- @realizes \bU_X(real feature orthogonal block) @realizes \bU_Y(real response orthogonal block)
/-- For [a pair of feature and response orthogonal transformations](hyp:u), the [block action matrix](goal)
places the feature transformation in the upper-left block and the response transformation in the lower-right block, with zero off-diagonal blocks. -/
def blockActionMatrix {p m : ℕ} (u : BlockOrth p m) : Mat (p + m) (p + m) :=
  fun i j => Fin.addCases (motive := fun _ => ℝ)
    (fun a => Fin.addCases (motive := fun _ => ℝ) (fun b => u.1.val a b) (fun _ => 0) j)
    (fun a => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun b => u.2.val a b) j) i

-- @node: ass:dro-symmetry-compact-group
/-- For [a subgroup of feature and response orthogonal transformations](hyp:U), the
[compact-group symmetry assumption](goal) requires the subgroup to be compact as a set of transformation pairs. -/
def assDroSymmetryCompactGroup {p m : ℕ} (U : Subgroup (BlockOrth p m)) : Prop :=
  IsCompact (U : Set (BlockOrth p m))
-- @realizes U(compact subgroup of block orthogonal transformations)

-- @node: ass:dro-symmetry-invariant-laws
/-- For [a subgroup of block orthogonal transformations](hyp:U), [a law P](hyp:P), and
[a law tilde P](hyp:tildeP), the [invariant-laws assumption](goal) requires every subgroup transformation
to [preserve P](step:1) and [preserve tilde P](step:2). -/
def assDroSymmetryInvariantLaws {p m : ℕ} (U : Subgroup (BlockOrth p m))
    (P tildeP : JointLaws p m) : Prop :=
  ∀ u : U,
    Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure P) = lawMeasure P ∧
    Measure.map (matrixCLM (blockActionMatrix u.val)) (lawMeasure tildeP) = lawMeasure tildeP
-- @realizes \tilde{P}(invariant source law with no distance constraint)

-- @node: ass:dro-symmetry-minimizer
/-- For [an objective index](hyp:o), [a reference law tilde P](hyp:tildeP), [a radius](hyp:eps),
and [a coefficient matrix](hyp:Ahat), the [symmetry minimizer assumption](goal) requires
[a nonzero objective index](step:1), [a strictly positive radius](step:2), and
[global minimization of the indexed population objective at tilde P by that coefficient matrix](step:3). -/
noncomputable def assDroSymmetryMinimizer {p m : ℕ} (o : Fin 4) (tildeP : JointLaws p m)
    (eps : ℝ≥0) (Ahat : Mat m p) : Prop :=
  o ≠ 0 ∧ 0 < eps ∧ Ahat ∈ populationMinimizers o tildeP eps

/-- For [a joint second-moment matrix](hyp:Sigma), the [spectral condition expression](goal)
is one plus the largest eigenvalue of the sum of the canonical coefficient matrix times its transpose
and the residual matrix scaled by the reciprocal of the smallest eigenvalue of the feature block. -/
noncomputable def conditionSpectral {p m : ℕ} (Sigma : Mat (p + m) (p + m)) : ℝ :=
  1 + lambdaMax (canonicalCoefficient Sigma * (canonicalCoefficient Sigma).transpose +
    (lambdaMin (blockX p m Sigma))⁻¹ • matrixResidual Sigma)
/-- For [a joint second-moment matrix](hyp:Sigma), the [lower condition expression](goal)
is one plus the larger of the squared operator norm of the canonical coefficient matrix and
the largest eigenvalue of the residual matrix divided by the smallest eigenvalue of the feature block. -/
noncomputable def conditionLower {p m : ℕ} (Sigma : Mat (p + m) (p + m)) : ℝ :=
  1 + max (opNorm (canonicalCoefficient Sigma) ^ 2)
    (lambdaMax (matrixResidual Sigma) / lambdaMin (blockX p m Sigma))
/-- For [a joint second-moment matrix](hyp:Sigma), the [upper condition expression](goal)
is one plus the squared operator norm of the canonical coefficient matrix plus
the largest eigenvalue of the residual matrix divided by the smallest eigenvalue of the feature block. -/
noncomputable def conditionUpper {p m : ℕ} (Sigma : Mat (p + m) (p + m)) : ℝ :=
  1 + opNorm (canonicalCoefficient Sigma) ^ 2 + lambdaMax (matrixResidual Sigma) / lambdaMin
    (blockX p m Sigma)

/-- For [feature dimension p](hyp:p), [response dimension m](hyp:m), and
[a real condition-number parameter kappa](hyp:kappa), the [class rate](goal) is the sum of
three terms: the product of the square root of the smaller dimension and the quantity kappa minus one,
the square root of the product of m and the quantity kappa minus one, and kappa. -/
noncomputable def classRate (p m : ℕ) (kappa : ℝ) : ℝ :=
  Real.sqrt (min p m : ℕ) * (kappa - 1) + Real.sqrt ((m : ℝ) * (kappa - 1)) + kappa
/-- For [a joint law P with positive definite feature second moment](hyp:P), the
[local rank rate](goal) uses [r equal to the effective rank of the residual second-moment matrix](step:1)
and [k equal to the condition number of P converted to a real number](step:2), and returns
[the product of the square root of the smaller of the feature dimension and r and the quantity k minus one,
plus the square root of the product of r and the quantity k minus one, plus k](step:3).

The conversion of the condition number to a real number sends infinity to zero. -/
noncomputable def localRankRate {p m : ℕ} (P : NondegenerateLaws p m) : ℝ :=
  let r := effectiveRank (residualSecondMoment P) -- @realizes r(real residual effective)
  let k := (conditionNumber P.carrier.val).toReal
  Real.sqrt (min (p : ℝ) r) * (k - 1) + Real.sqrt (r * (k - 1)) + k

end Papers.WassersteinRegretS2S3
