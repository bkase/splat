/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd6fe8fc-a7e6-4520-910a-c228f9c0c22a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem kronecker_product_distance {k m n m' : ℕ}
    (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n)
    (hGm' : G'.m = m') (hGn' : G'.n = k)
    {d : ℕ} {d' : ℕ}
    (h_dist : distance G ≥ d)
    (h_dist' : distance G' ≥ d') :
    distance (kroneckerCode G' G) ≥ d' * d

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Target: kronecker_product_distance in Succinct/Codes/KroneckerDistance.lean:158

This proves the main theorem: distance(G' ⊗ G) ≥ d' * d

Key insight: The theorem follows from showing that for any nonzero message z,
the encoded weight is at least d' * d. We decompose z into "slices" and use
the distance properties of the component codes.
-/

import Mathlib.Tactic


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

noncomputable section

open scoped BigOperators

namespace KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

/-- Type alias for vectors -/
abbrev Vec (F : Type*) (n : ℕ) := Fin n → F

/-- Type alias for matrices -/
abbrev Mat (F : Type*) (m n : ℕ) := Fin m → Fin n → F

/-- Linear code structure -/
structure LinearCode (F : Type*) [Field F] where
  (m n : ℕ)
  (G : Mat F m n)

/-- Encode a message -/
def encode (C : LinearCode F) (x : Vec F C.n) : Vec F C.m :=
  Matrix.mulVec C.G x

infixl:70 " ⇀ₑ " => encode

/-- Hamming weight -/
def weightVec {n : ℕ} (x : Vec F n) : ℕ :=
  Fintype.card { i : Fin n | x i ≠ 0 }

notation "∥" x "∥₀" => weightVec x

/-- Code distance as infimum -/
def distance (C : LinearCode F) : WithTop ℕ :=
  sInf { w : WithTop ℕ | ∃ x : Vec F C.n, x ≠ 0 ∧ w = ∥C ⇀ₑ x∥₀ }

/-- Kronecker product code -/
def kroneckerCode (G' G : LinearCode F) : LinearCode F where
  m := G'.m * G.m
  n := G'.n * G.n
  G := fun (p : Fin (G'.m * G.m)) (q : Fin (G'.n * G.n)) =>
    let i := p.val / G.m
    let j := p.val % G.m
    let a := q.val / G.n
    let b := q.val % G.n
    have hi : i < G'.m := Nat.div_lt_of_lt_mul (by nlinarith [Fin.is_lt p])
    have hj : j < G.m := by
      have hp := Fin.is_lt p
      have : G'.m * G.m > 0 := by nlinarith
      have : G.m > 0 := Nat.pos_of_mul_pos_left this
      exact Nat.mod_lt p.val this
    have ha : a < G'.n := Nat.div_lt_of_lt_mul (by nlinarith [Fin.is_lt q])
    have hb : b < G.n := by
      have hq := Fin.is_lt q
      have : G'.n * G.n > 0 := by nlinarith
      have : G.n > 0 := Nat.pos_of_mul_pos_left this
      exact Nat.mod_lt q.val this
    G'.G ⟨i, hi⟩ ⟨a, ha⟩ * G.G ⟨j, hj⟩ ⟨b, hb⟩

/- Main Theorem: Kronecker Product Distance

    If G has distance ≥ d and G' has distance ≥ d',
    then G' ⊗ G has distance ≥ d' * d.

    Proof idea: For any nonzero z in the message space, view z as a matrix Z.
    Find a nonzero row Z_a. Use G's distance on Z_a to get d positions.
    For each position, use G''s distance to get d' positions.
    Total support ≥ d' * d. -/
noncomputable section AristotleLemmas

/-
Converts a vector of length m*n to an m x n matrix.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def vecToMat {m n : ℕ} (v : Vec F (m * n)) : Mat F m n :=
  fun i j => v ⟨i.val * n + j.val, by
    nlinarith [ Fin.is_lt i, Fin.is_lt j ]⟩

/-
Definitions for the Hamming weight of a matrix (number of non-zero entries) and the number of non-zero columns.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def weightMat {m n : ℕ} (M : Mat F m n) : ℕ :=
  Fintype.card { p : Fin m × Fin n | M p.1 p.2 ≠ 0 }

def nonZeroCols {m n : ℕ} (M : Mat F m n) : ℕ :=
  Fintype.card { j : Fin n | ∃ i, M i j ≠ 0 }

/-
The Hamming weight of a vector is equal to the Hamming weight of its matrix representation.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma weight_eq_weight_mat {m n : ℕ} (v : Vec F (m * n)) :
    weightVec v = weightMat (vecToMat (m := m) (n := n) v) := by
  unfold KroneckerGated.weightMat;
  simp +decide only [weightVec, Fintype.card_ofFinset];
  refine' Finset.card_bij ( fun p hp => ⟨ ⟨ p / n, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt p ] ⟩, ⟨ p % n, Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by aesop_cat ⟩ ⟩ ) _ _ _ <;> simp +decide [ Nat.div_add_mod' ];
  · intro a ha; convert ha; simp +decide [ KroneckerGated.vecToMat, Nat.div_add_mod' ] ;
  · exact fun a₁ ha₁ a₂ ha₂ h₁ h₂ => Fin.ext <| by nlinarith [ Nat.mod_add_div a₁ n, Nat.mod_add_div a₂ n ] ;
  · intro a b hb
    use ⟨a.val * n + b.val, by
      nlinarith [ Fin.is_lt a, Fin.is_lt b ]⟩
    generalize_proofs at *;
    simp_all +decide [ Fin.ext_iff, Nat.add_div ];
    exact ⟨ Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt b ] ) ( Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero <| by aesop ) |>.2 <| by linarith [ Fin.is_lt b ] ), hb, Nat.mod_eq_of_lt <| Fin.is_lt b ⟩

/-
Matrix multiplication and transposition definitions.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def matMul {m n p : ℕ} (A : Mat F m n) (B : Mat F n p) : Mat F m p :=
  fun i k => ∑ j, A i j * B j k

def matTranspose {m n : ℕ} (A : Mat F m n) : Mat F n m :=
  fun i j => A j i

/-
The encoding of a message using the Kronecker product code corresponds to the matrix operation G' X G^T, where X is the matrix representation of the message.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma kronecker_encode_eq {m n m' n' : ℕ} (G : Mat F m n) (G' : Mat F m' n')
    (x : Vec F (n' * n)) :
    vecToMat (m := m') (n := m) (Matrix.mulVec (kroneckerCode (LinearCode.mk m' n' G') (LinearCode.mk m n G)).G x)
    = matMul (matMul G' (vecToMat (m := n') (n := n) x)) (matTranspose G) := by
  ext ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; simp +decide [ KroneckerGated.kroneckerCode, Matrix.mulVec ] ; ring;
  unfold KroneckerGated.vecToMat KroneckerGated.matMul KroneckerGated.matTranspose Matrix.mulVec
  generalize_proofs at *;
  simp +decide [ dotProduct, Finset.sum_mul _ _ _ ];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun q _ => ( ⟨ q.val % n, by
    exact Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ⟩, ⟨ q.val / n, by
    exact Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt q ] ; ⟩ ) ) _ _ _ _ <;> simp +decide [ Nat.div_add_mod' ]
  all_goals generalize_proofs at *;
  · exact fun a₁ a₂ h₁ h₂ => Fin.ext <| by nlinarith [ Nat.mod_add_div a₁ n, Nat.mod_add_div a₂ n ] ;
  · intro a b; use ⟨ b.val * n + a.val, by
      nlinarith [ Fin.is_lt a, Fin.is_lt b ] ⟩ ; simp +decide [ Nat.mod_eq_of_lt, Nat.div_eq_of_lt, * ]
    generalize_proofs at *;
    exact Fin.ext ( Nat.le_antisymm ( Nat.le_of_lt_succ <| by nlinarith [ Nat.div_mul_le_self ( b * n + a ) n, Fin.is_lt a, Fin.is_lt b ] ) ( Nat.le_of_lt_succ <| by nlinarith [ Nat.div_add_mod ( b * n + a ) n, Nat.mod_lt ( b * n + a ) ( Fin.pos a ), Fin.is_lt a, Fin.is_lt b ] ) );
  · simp +decide [ Nat.add_div, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ add_comm, Nat.add_mul_div_left _ _ ( Nat.pos_of_ne_zero ( by aesop_cat : m ≠ 0 ) ), mul_comm ];
    simp +decide [ Nat.div_eq_of_lt hj, mul_comm ];
    exact fun a => Or.inl ( mul_comm _ _ )

/-
If a matrix X is non-zero, then X * G^T has at least d non-zero columns, where d is the distance of G.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma cols_nonzero_ge_dist {k : ℕ} (G : LinearCode F) (d : ℕ)
    (h_dist : distance G ≥ d) (X : Mat F k G.n) (hX : X ≠ 0) :
    nonZeroCols (matMul X (matTranspose G.G)) ≥ d := by
  -- Since X is non-zero, there exists a row i such that X_i is non-zero.
  obtain ⟨i, hi⟩ : ∃ i : Fin k, X i ≠ 0 := by
    contrapose! hX; aesop;
  -- Since $X_i$ is non-zero, the encoding $G(X_i)$ has weight at least $d$.
  have h_weight : weightVec (Matrix.mulVec G.G (X i)) ≥ d := by
    contrapose! h_dist;
    refine' lt_of_le_of_lt ( csInf_le _ _ ) _;
    exact ↑ ( KroneckerGated.weightVec ( Matrix.mulVec G.G ( X i ) ) );
    · exact ⟨ 0, fun w hw => hw.choose_spec.2.symm ▸ Nat.cast_nonneg _ ⟩;
    · exact ⟨ X i, hi, rfl ⟩;
    · exact WithTop.coe_lt_coe.mpr h_dist;
  refine' le_trans h_weight ( Fintype.card_le_of_injective _ _ );
  refine' fun x => ⟨ x.val, _ ⟩;
  all_goals simp +decide [ Function.Injective ];
  exact ⟨ i, by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using x.2 ⟩

/-
The weight of the matrix product G'Z is at least d' times the number of non-zero columns of Z, given that G' has distance at least d'.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma weight_ge_dist_mul_cols {m n : ℕ} (G' : LinearCode F) (d' : ℕ)
    (h_dist' : distance G' ≥ d') (Z : Mat F G'.n n) :
    weightMat (matMul G'.G Z) ≥ d' * nonZeroCols Z := by
  -- For each non-zero column $z_j$ of $Z$, the weight of $G' * z_j$ is at least $d'$.
  have h_col_weight : ∀ j : Fin n, (∃ i : Fin G'.n, Z i j ≠ 0) → weightVec (fun i => ∑ k, G'.G i k * Z k j) ≥ d' := by
    intro j hj
    unfold distance at h_dist';
    refine' Nat.cast_le.mp ( le_trans h_dist' _ );
    refine' csInf_le _ ⟨ fun i => Z i j, _, rfl ⟩ <;> simp_all +decide [ funext_iff, Matrix.mulVec ];
  -- Summing the weights of the columns of $G' * Z$ gives us the total weight.
  have h_sum_weight : weightMat (KroneckerGated.matMul G'.G Z) = ∑ j : Fin n, weightVec (fun i => ∑ k, G'.G i k * Z k j) := by
    -- Matrix weight = sum of column weights (counting by fibers)
    -- The total number of nonzero entries in G'.G * Z equals the sum over columns j
    -- of the number of nonzero entries in column j.
    simp only [weightMat, Fintype.card_subtype, weightVec, matMul]
    -- This is a standard counting argument: count pairs (i,j) by fiber over j
    have : Fintype.card { p : Fin G'.m × Fin n | ∑ j, G'.G p.1 j * Z j p.2 ≠ 0 } =
           ∑ j : Fin n, Fintype.card { i : Fin G'.m | ∑ k, G'.G i k * Z k j ≠ 0 } := by
      rw [← Fintype.card_sigma]
      refine Fintype.card_congr ⟨fun ⟨⟨i, j⟩, h⟩ => ⟨j, ⟨i, h⟩⟩, fun ⟨j, ⟨i, h⟩⟩ => ⟨⟨i, j⟩, h⟩, ?_, ?_⟩
      · intro ⟨⟨i, j⟩, h⟩; rfl
      · intro ⟨j, ⟨i, h⟩⟩; rfl
    convert this using 2 <;> simp only [Set.coe_setOf, Set.mem_setOf_eq, Fintype.card_subtype]
  have h_sum_weight_ge : ∑ j : Fin n, weightVec (fun i => ∑ k, G'.G i k * Z k j) ≥ ∑ j : Fin n, if (∃ i : Fin G'.n, Z i j ≠ 0) then d' else 0 := by
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> [ exact h_col_weight j ‹_›; exact Nat.zero_le _ ] ;
  convert h_sum_weight_ge using 1 ; simp +decide [ KroneckerGated.nonZeroCols, mul_comm ] ; ring;
  simp +decide [ Finset.sum_ite, Fintype.card_subtype ] ; ring;

end AristotleLemmas

theorem kronecker_product_distance {k m n m' : ℕ}
    (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n)
    (hGm' : G'.m = m') (hGn' : G'.n = k)
    {d : ℕ} {d' : ℕ}
    (h_dist : distance G ≥ d)
    (h_dist' : distance G' ≥ d') :
    distance (kroneckerCode G' G) ≥ d' * d := by
  simp_all +decide [ KroneckerGated.distance ];
  intro b x hx hb
  have h_weight : weightVec (encode (kroneckerCode G' G) x) ≥ d' * d := by
    -- Let $X = \text{vecToMat } x$. Since $x \neq 0$, $X \neq 0$.
    set X : Mat F G'.n G.n := vecToMat (m := G'.n) (n := G.n) x
    have hX_nonzero : X ≠ 0 := by
      contrapose! hx;
      ext i; exact (by
      convert congr_fun ( congr_fun hx ⟨ i.val / G.n, by
        exact Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt i, show ( KroneckerGated.kroneckerCode G' G ).n = G'.n * G.n from rfl ] ; ⟩ ) ⟨ i.val % G.n, by
        by_cases h : G.n = 0 <;> simp_all +decide [ Nat.mod_lt ];
        · exact absurd i.2 ( by simp +decide [ hGn.symm, h, KroneckerGated.kroneckerCode ] );
        · exact Nat.mod_lt _ ( Nat.pos_of_ne_zero h ) ⟩ using 1
      generalize_proofs at *;
      exact congr_arg _ ( by simp +decide [ Nat.div_add_mod' ] ))
    have hX_weight : weightVec (encode (kroneckerCode G' G) x) = weightMat (matMul G'.G (matMul X (matTranspose G.G))) := by
      convert weight_eq_weight_mat _ using 2
      generalize_proofs at *; (
      convert ( kronecker_encode_eq G.G G'.G x ) |> Eq.symm using 1
      generalize_proofs at *; (
      ext i k; simp +decide [ KroneckerGated.matMul ] ; ring;
      simp +decide only [Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc] ; exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ;))
    have hX_weight_ge : weightMat (matMul G'.G (matMul X (matTranspose G.G))) ≥ d' * nonZeroCols (matMul X (matTranspose G.G)) := by
      apply weight_ge_dist_mul_cols G' d' (by
      simp +decide [ KroneckerGated.distance ] at * ; aesop;) (matMul X (matTranspose G.G));
      exact 0
    have hX_nonzero_cols : nonZeroCols (matMul X (matTranspose G.G)) ≥ d := by
      apply cols_nonzero_ge_dist G d (by
      refine' le_csInf _ _ <;> norm_num
      generalize_proofs at *; (
      by_cases h : ∃ x : KroneckerGated.Vec F G.n, x ≠ 0 <;> simp_all +decide [ Set.Nonempty ];
      · exact ⟨ _, h.choose, h.choose_spec, rfl ⟩;
      · exact hX_nonzero ( funext fun i => funext fun j => h _ |> fun h => by simpa using congr_fun h _ ));
      exact fun b x hx hb => hb.symm ▸ WithTop.coe_le_coe.mpr ( h_dist _ _ hx rfl )) X hX_nonzero
      skip
    have hX_weight_final : weightVec (encode (kroneckerCode G' G) x) ≥ d' * d := by
      exact hX_weight.symm ▸ hX_weight_ge.trans' ( Nat.mul_le_mul_left _ hX_nonzero_cols )
    exact hX_weight_final
  exact_mod_cast h_weight.trans' (Nat.mul_le_mul (Nat.cast_le.mpr le_rfl) le_rfl)

end KroneckerGated

end
