import Succinct.LinearAlgebra
import Succinct.Vandermonde
import Succinct.Prob.Implication
import Succinct.Prob.Laws
import Succinct.Codes.Core
import Succinct.Codes.Hamming
import Succinct.Codes.Distance
import Succinct.Codes.EvalCode
import Succinct.Codes.Singleton
import Succinct.Codes.SingletonLemmas
import Succinct.Codes.Lagrange
import Succinct.Codes.ReedSolomon
import Succinct.Codes.Hadamard
import Succinct.Codes.SingletonKernel
import Succinct.Codes.KroneckerDistance
import Succinct.Codes.Aristotle.PolynomialZeroViaEvaluation
import Succinct.Checks.Sparsity
import Succinct.Checks.Zero
import Succinct.Checks.MatrixZero
import Succinct.Checks.SparsityZero
import Succinct.Checks.PolynomialZero
import Succinct.Checks.ReducedMatrixZero
import Succinct.Prob.Examples
import Succinct.Fri.SubspaceDistanceProved
import Succinct.Fri.Aristotle.BadAlphaSetFiniteGated
import Succinct.Fri.FRICompletenessDecomposition
import Succinct.Fri.FRIConstruction

/-!
# Succinct: Preliminaries for Linear Codes and Evaluation Maps

This umbrella module re-exports the main components:

* `Succinct.LinearAlgebra`       – basic Vec/Mat setup, nullspace, basis matrices
* `Succinct.Vandermonde`         – Vandermonde matrices and evaluation view
* `Succinct.Prob.Implication`    – calculus of probabilistic implication (§1.4)
* `Succinct.Codes.Core`          – linear codes and encoding
* `Succinct.Codes.Hamming`       – ℓ₀/Hamming weights on vectors and sets
* `Succinct.Codes.Distance`      – code distance via minimum nonzero weight
* `Succinct.Codes.EvalCode`      – evaluation codes as a concrete instance
-/
