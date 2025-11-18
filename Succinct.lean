import Succinct.LinearAlgebra
import Succinct.Vandermonde
import Succinct.Prob.Implication
import Succinct.Codes.Core
import Succinct.Codes.Hamming
import Succinct.Codes.Distance
import Succinct.Codes.EvalCode

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
