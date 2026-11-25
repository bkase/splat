module

public import Succinct.LinearAlgebra
public import Succinct.Vandermonde
public import Succinct.Prob.Implication
public import Succinct.Prob.Laws
public import Succinct.Codes.Core
public import Succinct.Codes.Hamming
public import Succinct.Codes.Distance
public import Succinct.Codes.EvalCode
public import Succinct.Codes.Singleton
public import Succinct.Codes.SingletonLemmas
public import Succinct.Codes.Lagrange
public import Succinct.Codes.ReedSolomon
public import Succinct.Codes.Hadamard
public import Succinct.Codes.SingletonKernel
public import Succinct.Codes.KroneckerDistance
public import Succinct.Codes.Aristotle.PolynomialZeroViaEvaluation
public import Succinct.Checks.Sparsity
public import Succinct.Checks.Zero
public import Succinct.Checks.MatrixZero
public import Succinct.Checks.SparsityZero
public import Succinct.Checks.PolynomialZero
public import Succinct.Checks.ReducedMatrixZero
public import Succinct.Prob.Examples
public import Succinct.Fri.SubspaceDistanceProved
public import Succinct.Fri.Aristotle.BadAlphaSetFiniteGated
public import Succinct.Fri.FRICompletenessDecomposition
public import Succinct.Fri.FRIConstruction

public section

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
