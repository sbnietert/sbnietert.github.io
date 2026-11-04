module
public import Causalean.Mathlib.Analysis.MatrixEuclidean
public import Causalean.Mathlib.Analysis.MoorePenrose
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Data.ENNReal.Basic

/-!
# Population Wasserstein regret: Helpers/MatrixDefs

Real Euclidean matrices and finite-second-moment laws, including singular second moments.
-/

@[expose] public section

namespace Papers.WassersteinRegretS2S3

open Causalean.Mathlib.Analysis Matrix
open scoped BigOperators MatrixOrder NNReal ENNReal Matrix.Norms.Frobenius

-- @env: S2
variable {p m : ℕ}
  [NeZero p] [NeZero
  m] -- @realizes p(positive feature dimension) @realizes m(positive response dimension)

/-- For [a feature dimension p](hyp:p) and [a response dimension m](hyp:m), the
[joint dimension](goal) is their sum. -/
abbrev JointDim (p m : ℕ) := p + m -- @realizes d(d=p+m)
/-- The [matrix type](goal) consists of real rectangular matrices indexed by finite
row and column sets. -/
abbrev Mat := RectMatrix -- @realizes \bM(real rectangular carrier)
/-- For [a dimension n](hyp:n), the [positive semidefinite cone](goal) consists of
real n-by-n positive semidefinite matrices. -/
abbrev PSD (n : ℕ) := {A : Mat n n // A.PosSemidef} -- @realizes \PSD^d(positive semidefinite cone)
/-- For [a dimension n](hyp:n), the [symmetric matrix space](goal) consists of real
symmetric n-by-n matrices. -/
abbrev Sym (n : ℕ) := selfAdjoint (Mat n n) -- @realizes \Sym^d(real symmetric vector)
/-- For [a dimension n](hyp:n), the [orthogonal group](goal) consists of real
orthogonal n-by-n matrices. -/
abbrev Orth (n : ℕ) := Matrix.orthogonalGroup (Fin n) ℝ -- @realizes \OO^d(real orthogonal group)

/-- For [a real rectangular matrix A](hyp:A), its [Frobenius norm](goal) is the
square root of the sum of the squares of all its entries. -/
noncomputable def frob {a b : ℕ} (A : Mat a b) : ℝ := Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)
/-- For [a real rectangular matrix A](hyp:A), its [operator norm](goal) is the
operator norm of the linear map it induces between Euclidean spaces. -/
noncomputable def opNorm {a b : ℕ} (A : Mat a b) : ℝ := ‖matrixCLM A‖
/-- For [a real rectangular matrix A](hyp:A), its [minimum singular value](goal)
is the singular value at the smaller matrix dimension minus one in zero-based
decreasing order, using index zero if either dimension is zero. -/
noncomputable def minSV {a b : ℕ} (A : Mat a b) : ℝ := singularValue A (min a b - 1)
/-- For [a real square matrix A](hyp:A), the [minimum Rayleigh value](goal) is the
infimum of the quadratic form of A over Euclidean unit vectors. -/
noncomputable def lambdaMin {n : ℕ} (A : Mat n n) : ℝ :=
  sInf {t : ℝ | ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = t}
/-- For [a real square matrix A](hyp:A), the [maximum Rayleigh value](goal) is the
supremum of the quadratic form of A over Euclidean unit vectors. -/
noncomputable def lambdaMax {n : ℕ} (A : Mat n n) : ℝ :=
  sSup {t : ℝ | ∃ x : Euc n, ‖x‖ = 1 ∧ inner ℝ x (matrixCLM A x) = t}

-- @node: def:regression-norms
/-- For [a row count a](hyp:a) and [a column count b](hyp:b), the
[regression norm pair](goal) comprises the Frobenius and Euclidean operator norms
on real a-by-b matrices. -/
noncomputable def regressionNorms (a b : ℕ) := (@frob a b, @opNorm a b)

-- @node: def:matrix-notation
/-- For [a dimension n](hyp:n), the [matrix notation bundle](goal) collects the
positive semidefinite cone, symmetric matrices, orthogonal group, zero and identity
matrices, matrix square root, pseudoinverse, extreme Rayleigh values, trace,
diagonal matrices, semidefinite and definite order comparisons, block diagonal
concatenation, and scalar comparisons up to positive multiplicative constants
in either or both directions. -/
noncomputable def matrixNotation (n : ℕ) :=
  (PSD n, Sym n, Orth n, (0 : Mat n n), (1 : Mat n n),
    (fun A : Mat n n => CFC.sqrt A),
    (fun a b : ℕ => @moorePenroseInverse a b), @lambdaMin n, @lambdaMax n,
    (fun M : Mat n n => Matrix.trace M),
    (fun a : Fin n → ℝ => Matrix.diagonal a),
    (fun A B : Sym n => (B.val - A.val).PosSemidef),
    (fun A B : Sym n => (B.val - A.val).PosDef),
    (fun (a b : ℕ) (A : Mat a a) (B : Mat b b) => Matrix.fromBlocks A 0 0 B),
    (fun a b : ℝ => ∃ C : ℝ, 0 < C ∧ a ≤ C * b),
    (fun a b : ℝ => ∃ C : ℝ, 0 < C ∧ b ≤ C * a),
    (fun a b : ℝ => (∃ C : ℝ, 0 < C ∧ a ≤ C * b) ∧
      (∃ C : ℝ, 0 < C ∧ b ≤ C * a)))
-- @realizes \bZero(zero matrix) @realizes \bI(identity matrix)

-- @node: def:predictor-space
/-- For [a feature dimension p](hyp:p) and [a response dimension m](hyp:m), the
[predictor space](goal) consists of all real m-by-p coefficient matrices. -/
structure PredictorSpace (p m : ℕ) where
  matrix : Mat m p -- @realizes \cA(all m by) @realizes \bA(real coefficient carrier)

-- @node: ass:basic-matrix-norms-projection
/-- For [a real square matrix Pi](hyp:Pi), the [orthogonal projection condition](goal)
requires that [Pi is symmetric](step:1) and [Pi squared equals Pi](step:2). -/
def assBasicMatrixNormsProjection {n : ℕ} (Pi : Mat n n) : Prop :=
  Pi.transpose = Pi ∧ Pi * Pi = Pi -- @realizes \bPi(orthogonal projection)

-- @node: ass:pseudoinverse-projection-facts-row-rank
/-- For [a real rectangular matrix M](hyp:M), the [full row rank condition](goal)
requires that its induced linear map is onto the Euclidean space whose dimension
is the number of rows of M. -/
def assPseudoinverseProjectionFactsRowRank {a b : ℕ} (M : Mat a b) : Prop :=
  Function.Surjective (Matrix.toEuclideanLin M)

-- @node: ass:pseudoinverse-projection-facts-positive
/-- For [a real square matrix B](hyp:B), the [positivity condition](goal) requires
that B is positive semidefinite. -/
def assPseudoinverseProjectionFactsPositive {n : ℕ} (B : Mat n n) : Prop := B.PosSemidef

-- @node: ass:rectangular-resolvent-identities-eta
/-- For [a real rectangular matrix M](hyp:M) and [a real threshold eta](hyp:eta),
the [resolvent gap condition](goal) requires that the squared Euclidean operator
norm of M is strictly less than eta. -/
def assRectangularResolventIdentitiesEta {a b : ℕ} (M : Mat a b) (eta : ℝ) : Prop :=
  opNorm M ^ 2 < eta -- @realizes \eta(resolvent spectral gap)

-- @node: ass:sin-thm-variant-row-rank
/-- For [a real rectangular reference matrix M0](hyp:M0), the
[full row rank condition for the perturbation bound](goal) requires that its
induced Euclidean linear map is surjective. -/
def assSinThmVariantRowRank {a b : ℕ} (M0 : Mat a b) : Prop :=
  Function.Surjective (Matrix.toEuclideanLin M0) -- @realizes \bM_0(full row rank)

-- @node: ass:singular-value-convention
/-- The [singular value convention](goal) requires that, for every real matrix
with positive row and column counts, [its singular values are nonincreasing](step:1),
[all its singular values are nonnegative](step:2), and [its minimum singular value
is the entry in position min(a, b) in that ordering](step:3), where a and b are its
row and column counts. -/
def assSingularValueConvention : Prop :=
  ∀ (a b : ℕ) [NeZero a] [NeZero b] (M : Mat a b),
    Antitone (singularValue M) ∧ (∀ j, 0 ≤ singularValue M j) ∧
      minSV M = singularValue M (min a b - 1)

-- @node: assSingularValueConvention_valid
/-- [Every real matrix with positive row and column counts has nonincreasing,
nonnegative singular values, and its minimum singular value is the entry in
position equal to the smaller dimension in that ordering](goal). -/
lemma assSingularValueConvention_valid : assSingularValueConvention := by
  intro a b _ _ M
  exact ⟨(Matrix.toEuclideanLin M).singularValues_antitone,
    (Matrix.toEuclideanLin M).singularValues_nonneg, rfl⟩

/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a joint square matrix Sigma](hyp:Sigma), the [four-block decomposition](goal)
returns its feature block, feature-response block, response-feature block, and
response block, in that order. -/
def rawBlocks (p m : ℕ) (Sigma : Mat (p + m) (p + m)) :=
  (Sigma.submatrix (Fin.castAdd m) (Fin.castAdd m), -- @realizes \bSigma_X(feature principal block)
   Sigma.submatrix (Fin.castAdd m) (Fin.natAdd p), -- @realizes \bSigma_{XY}(feature response cross)
   Sigma.submatrix (Fin.natAdd p) (Fin.castAdd m), -- @realizes \bSigma_{YX}(response feature cross)
   Sigma.submatrix (Fin.natAdd p) (Fin.natAdd p)) -- @realizes \bSigma_Y(response principal block)

-- @node: def:matrix-blocks
/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a symmetric joint matrix Sigma](hyp:Sigma), the [symmetric matrix block bundle](goal)
returns its feature, feature-response, response-feature, and response blocks. -/
def matrixBlocks (p m : ℕ) (Sigma : Sym (p + m)) := rawBlocks p m Sigma.val

/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a joint square matrix S](hyp:S), the [feature block](goal) is its leading p-by-p
principal block. -/
abbrev blockX (p m : ℕ) (S : Mat (p + m) (p + m)) := (rawBlocks p m S).1
/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a joint square matrix S](hyp:S), the [feature-response block](goal) consists of
the first p rows and last m columns of S. -/
abbrev blockXY (p m : ℕ) (S : Mat (p + m) (p + m)) := (rawBlocks p m S).2.1
/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a joint square matrix S](hyp:S), the [response-feature block](goal) consists of
the last m rows and first p columns of S. -/
abbrev blockYX (p m : ℕ) (S : Mat (p + m) (p + m)) := (rawBlocks p m S).2.2.1
/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a joint square matrix S](hyp:S), the [response block](goal) is its trailing m-by-m
principal block. -/
abbrev blockY (p m : ℕ) (S : Mat (p + m) (p + m)) := (rawBlocks p m S).2.2.2

-- @node: def:factor-blocks
/-- Given [a feature dimension p](hyp:p), [a response dimension m](hyp:m), and
[a matrix S with p + m rows](hyp:S), its [factor block pair](goal) consists of the
first p rows and the last m rows, retaining all columns. -/
def factorBlocks (p m : ℕ) {k : ℕ} (S : Mat (p + m) k) :=
  (S.submatrix (Fin.castAdd m) id, -- @realizes \bS_X(feature row block)
   S.submatrix (Fin.natAdd p) id) -- @realizes \bS_Y(response row block)

-- @node: def:quadratic-regression-matrix
/-- For [an m-by-p coefficient matrix A](hyp:A), the [regression residual matrix](goal)
is the horizontal concatenation of A and the negative m-by-m identity, mapping
joint features and responses to predicted responses minus observed responses. -/
def quadraticRegressionMatrix {p m : ℕ} (A : Mat m p) : Mat m (p + m) :=
  fun i j => (Fin.addCases (motive := fun _ => ℝ) (fun k => A i k) (fun k => - (1 : Mat m m) i k)) j
-- @realizes \bM_\bA(horizontal concatenation of A and minus identity)

/-- For [a joint square matrix Sigma](hyp:Sigma), the [canonical regression
coefficient](goal) is its response-feature block multiplied by the Moore–Penrose
pseudoinverse of its feature block. -/
noncomputable def canonicalCoefficient {p m : ℕ} (Sigma : Mat (p + m) (p + m)) : Mat m p :=
  blockYX p m Sigma * moorePenroseInverse (blockX p m Sigma)
-- @realizes \bA_\bSigma(cross block times feature pseudoinverse)
/-- For [a coefficient matrix A](hyp:A) and [a joint square matrix Sigma](hyp:Sigma),
the [quadratic regression risk](goal) is the trace of A-transpose times A times
the feature block, minus twice the trace of A times the feature-response block,
plus the trace of the response block. -/
noncomputable def matrixRisk {p m : ℕ} (A : Mat m p) (Sigma : Mat (p + m) (p + m)) : ℝ :=
  Matrix.trace (A.transpose * A * blockX p m Sigma) -
    2 * Matrix.trace (A * blockXY p m Sigma) + Matrix.trace (blockY p m Sigma)
/-- For [a coefficient matrix A](hyp:A) and [a joint square matrix Sigma](hyp:Sigma),
the [regression regret](goal) is the risk of A minus the risk of the canonical
coefficient, both evaluated at Sigma. -/
noncomputable def matrixRegret {p m : ℕ} (A : Mat m p) (Sigma : Mat (p + m) (p + m)) : ℝ :=
  matrixRisk A Sigma - matrixRisk (canonicalCoefficient Sigma) Sigma
/-- For [a joint square matrix Sigma](hyp:Sigma), the [canonical residual matrix](goal)
is Sigma multiplied on the left by the canonical regression residual map and on
the right by its transpose; for second moments, this is the uncentered residual
second moment matrix. -/
noncomputable def matrixResidual {p m : ℕ} (Sigma : Mat (p + m) (p + m)) : Mat m m :=
  quadraticRegressionMatrix (canonicalCoefficient Sigma) * Sigma *
    (quadraticRegressionMatrix (canonicalCoefficient Sigma)).transpose
-- @realizes \bSigma_E(uncentered canonical residual second moment)

-- @node: def:bures-regression
/-- For [a positive semidefinite joint second moment matrix Sigma](hyp:Sigma) and
[a coefficient matrix A](hyp:A), the [Bures regression bundle](goal) collects the
canonical coefficient, the risk of A, the regret of A, and the canonical residual
second moment matrix. -/
noncomputable def buresRegression {p m : ℕ} (Sigma : PSD (p + m)) (A : Mat m p) :=
  (canonicalCoefficient Sigma.val, matrixRisk A Sigma.val, matrixRegret A Sigma.val,
    matrixResidual Sigma.val)

-- @node: def:nondegenerate-second-moments
/-- For [a feature dimension p](hyp:p) and [a response dimension m](hyp:m), the
[space of nondegenerate second moments](goal) consists of positive semidefinite
joint matrices whose feature block is positive definite. -/
structure NondegenerateSecondMoments (p m : ℕ) where
  carrier : -- @realizes \cC^*(PSD with positive)
    {Sigma : PSD (p + m) // (blockX p m Sigma.val).PosDef}

/-- The [topology on nondegenerate second moments](goal) is induced by viewing
each such second moment as a positive semidefinite joint matrix with a positive
definite feature block, equipped with its inherited matrix topology. -/
instance {p m : ℕ} : TopologicalSpace (NondegenerateSecondMoments p m) :=
  TopologicalSpace.induced NondegenerateSecondMoments.carrier inferInstance

-- @node: def:parameter-domain
/-- For [a feature dimension p](hyp:p) and [a response dimension m](hyp:m), the
[parameter domain](goal) consists of symmetric joint matrices whose feature block
is positive definite. -/
structure ParameterDomain (p m : ℕ) where
  carrier : -- @realizes \bSigma(symmetric matrix with) -- @realizes \cC(open symmetric domain)
    {Sigma : Sym (p + m) // (blockX p m Sigma.val).PosDef}

-- @node: def:parameter-map
/-- For [a symmetric joint matrix Sigma](hyp:Sigma), the [regression parameter
map](goal) returns its response-feature block multiplied by the inverse of its
feature block. -/
noncomputable def parameterMap {p m : ℕ} (Sigma : Sym (p + m)) : Mat m p :=
  blockYX p m Sigma.val * (blockX p m Sigma.val)⁻¹
-- @realizes g(cross block times feature inverse on the open domain)

-- @node: def:bures-distance
/-- For [a real square matrix A](hyp:A) and [a real square matrix B of the same
size](hyp:B), the [Bures trace expression](goal) is the square root of the sum of
their traces minus twice the trace obtained by first sandwiching B between two
matrix square roots of A and then taking the matrix square root of that product. -/
noncomputable def buresDistance {n : ℕ} (A B : Mat n n) : ℝ :=
  Real.sqrt (Matrix.trace A + Matrix.trace B -
    2 * Matrix.trace (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)))
-- @realizes \sB(nonnegative square root of Bures trace formula)

-- @node: def:bures-ball
/-- For [a positive semidefinite center Sigma](hyp:Sigma) and [a nonnegative
radius eps](hyp:eps), the [closed Bures ball](goal) consists of all positive
semidefinite matrices whose Bures distance from Sigma is at most eps. -/
structure BuresBall {n : ℕ} (Sigma : PSD n) (eps : ℝ≥0) where
  carrier : -- @realizes \cB_\eps(\bSigma)(closed full PSD)
    {T : PSD n // buresDistance T.val Sigma.val ≤ eps}

-- @node: def:effective-rank
/-- For [a real square matrix M](hyp:M), its [effective rank](goal) is its trace
divided by its Euclidean operator norm, with value zero when the denominator is zero. -/
noncomputable def effectiveRank {n : ℕ} (M : Mat n n) : ℝ := Matrix.trace M / opNorm M
-- @realizes \reff(trace divided by real Euclidean operator norm; zero at zero)

-- @node: ass:regret-projection-formula-factor
/-- For [a positive semidefinite matrix Sigma](hyp:Sigma) and [a rectangular
factor matrix S](hyp:S), the [factorization condition](goal) requires that Sigma
equals S multiplied by its transpose. -/
def assRegretProjectionFormulaFactor {n r : ℕ} (Sigma : PSD n) (S : Mat n r) : Prop :=
  Sigma.val = S * S.transpose

/-- For [a real rectangular matrix M](hyp:M), the [orthogonal projector onto
its row space](goal) is the Moore–Penrose pseudoinverse of M multiplied by M. -/
noncomputable def rowProjector {a b : ℕ} (M : Mat a b) : Mat b b := moorePenroseInverse M * M
/-- For [a real rectangular matrix M](hyp:M), the [orthogonal projector onto
its column space](goal) is M multiplied by its Moore–Penrose pseudoinverse. -/
noncomputable def rangeProjector {a b : ℕ} (M : Mat a b) : Mat a a := M * moorePenroseInverse M

end Papers.WassersteinRegretS2S3
