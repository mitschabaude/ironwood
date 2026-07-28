import Zcash.Snark.Soundness.Deployed.Binding

/-!
# AGM relations and the programmed-basis DL reduction

The deployed soundness code can return `NontrivialRelation g U W`: explicit coefficients for a
relation among `(g, U, W)`. Merely proving that such a relation exists says nothing in a prime-order
group. Computing its coefficients is the security break.

This module turns that relation into a plain discrete-log solution, by programming every basis
slot from the DL challenge rather than guessing which slot the relation will hit — see
`§ The programmed-basis relation-to-DL adapter` below.

The representation types borrow basic structure from ArkLib's AGM `Basic.lean`
(<https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/AGM/Basic.lean#L13-L14>). ArkLib is not a
dependency or reference proof: its adversary layer is unfinished. This repository defines and
proves the operational prover, certificate, and reductions used here.

## What is formalized here

* Representations over a public basis (`GroupRepresentation`, `AlgebraicPoint`,
  `AlgebraicRelationWitness`).
* The known-log eliminator (`discreteLogOfBasis_of_relation`): a relation with a nonzero
  coefficient at one slot yields that slot's log when all other logs are known. Its augmented-basis
  forms serve the binding-signature reductions.
* The programmed-basis relation-to-DL adapter (`discreteLogOfChallenge_of_relation`) and its
  extract-or-miss form (`programmedExtractOrMiss`), used by the deployed capstone.

## Computational boundary

`Soundness.AGM.Prover` adds representations to prover and certificate data.
`Soundness.AGM.Peel` and `.Capstone` compute an IPA opening or relation.
`Soundness.AGM.Probability` prices the reduction's single failure hyperplane at `1/|F|`, and
`.ProbabilityVesta` applies it to Vesta.

The explicit-certificate path is computable. Its boundary is AGM, plain-DL hardness, ideal random
oracles, an unproved polynomial AFK call bound, and an external PPT-adversary restriction.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Evaluate an AGM representation over an arbitrary finite public basis. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- Coefficients over `basis` whose MSM equals `target`.

Every group element output by an algebraic prover carries this data. -/
structure GroupRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  coeffs : ι → F
  hEq : representationEval basis coeffs = target

/-- A group element bundled with an AGM representation over `basis`. -/
structure AlgebraicPoint {ι : Type*} [Fintype ι] (basis : ι → G) where
  point : G
  repr : GroupRepresentation (F := F) basis point

namespace AlgebraicPoint

/-- The coefficients carried by an algebraic point. -/
def coeffs {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) : ι → F :=
  P.repr.coeffs

@[simp] theorem hEq {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) :
    representationEval basis P.coeffs = P.point :=
  P.repr.hEq

end AlgebraicPoint

/-- `representationEval` specializes to the existing `commitGen` MSM over `Fin n`. -/
theorem representationEval_fin {n : ℕ} (basis : Fin n → G) (coeffs : Fin n → F) :
    representationEval basis coeffs = commitGen basis coeffs := rfl

/-- A scalar `log` such that `log • B = target`.

The cryptographic reading requires `B ≠ 0`. If `B = 0`, only `target = 0` is representable. -/
structure DiscreteLogRepresentation (B target : G) where
  log : F
  hEq : log • B = target

/-- Explicit nonzero coefficients whose MSM over `basis` is zero. -/
structure AlgebraicRelationWitness {ι : Type*} [Fintype ι] (basis : ι → G) where
  coeffs : ι → F
  nontrivial : coeffs ≠ 0
  relation : representationEval basis coeffs = 0

namespace AlgebraicRelationWitness

/-- A relation witness is the same data as a representation of the identity. -/
def toGroupRepresentation {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    GroupRepresentation (F := F) basis (0 : G) :=
  { coeffs := r.coeffs
    hEq := r.relation }

/-- A relation witness also gives an algebraic point for the identity. -/
def toAlgebraicPoint {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    AlgebraicPoint (F := F) basis :=
  { point := 0
    repr := r.toGroupRepresentation }

/-- A nontrivial finite relation has a nonzero coefficient at some basis slot.

`Soundness.AGM.Probability` uses this slot as the pivot of its hyperplane counting. -/
theorem exists_nonzero_coeff {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    ∃ i, r.coeffs i ≠ 0 := by
  by_contra h
  apply r.nontrivial
  funext i
  exact not_not.mp (not_exists.mp h i)

end AlgebraicRelationWitness

/-- The known-log contribution of every basis slot except the challenge slot. -/
def relationLogExcept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (logs coeffs : ι → F) (challenge : ι) : F :=
  (Finset.univ.erase challenge).sum fun i => coeffs i * logs i

/-- If every non-challenge basis element has a known log over `B`, then a relation separates into the
challenge term plus a known scalar multiple of `B`. -/
theorem representationEval_eq_challenge_add_known {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : G) (basis : ι → G) (logs coeffs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • B) :
    representationEval basis coeffs =
      coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • B := by
  have hsum : ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
      = relationLogExcept logs coeffs challenge • B := by
    calc
      ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
          = (Finset.univ.erase challenge).sum (fun i => coeffs i • (logs i • B)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hknown i (Finset.mem_erase.mp hi).1]
      _ = (Finset.univ.erase challenge).sum (fun i => (coeffs i * logs i) • B) := by
            simp [smul_smul]
      _ = relationLogExcept logs coeffs challenge • B := by
            rw [relationLogExcept, Finset.sum_smul]
  calc
    representationEval basis coeffs
        = ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
            + coeffs challenge • basis challenge := by
          rw [representationEval, ← Finset.sum_erase_add _ _ (Finset.mem_univ challenge)]
    _ = coeffs challenge • basis challenge
            + ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i) := by
          abel
    _ = coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • B := by
          rw [hsum]

/-- Recover the challenge slot's discrete log from a relation that has a nonzero coefficient there.

The challenge slot is fixed before the relation is returned, and the logs of every other slot are
known. -/
def discreteLogOfBasis_of_relation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : G) (basis : ι → G) (logs : ι → F) (challenge : ι)
    (r : AlgebraicRelationWitness (F := F) basis)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • B)
    (hcoeff : r.coeffs challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (basis challenge) := by
  let known : F := relationLogExcept logs r.coeffs challenge
  refine ⟨(r.coeffs challenge)⁻¹ * (-known), ?_⟩
  have hsplit := representationEval_eq_challenge_add_known B basis logs r.coeffs challenge hknown
  have hzero : r.coeffs challenge • basis challenge + known • B = 0 := by
    rw [← hsplit]
    exact r.relation
  have hmul : r.coeffs challenge • basis challenge = (-known) • B := by
    calc
      r.coeffs challenge • basis challenge = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.coeffs challenge)⁻¹ • X)) hmul
  have hlog : basis challenge = ((r.coeffs challenge)⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hcoeff] using hscale
  exact hlog.symm

/-! ### The programmed-basis relation-to-DL adapter

Jaeger–Tessaro Lemma 3 (<https://eprint.iacr.org/2020/1213>): every slot is programmed from the
challenge `C` as `x i • B + y i • C`, so a returned relation reads
`0 = (∑ i, aᵢ·xᵢ) • B + (∑ i, aᵢ·yᵢ) • C` and the reduction divides by `∑ i, aᵢ·yᵢ`. Its only
failure is the hyperplane `∑ i, aᵢ·yᵢ = 0`, which `Soundness.AGM.Probability` prices at
`1/|F|`. -/

/-- A DL challenge programmed into every basis slot: slot `i` presents `x i • B + y i • C`.

For a challenge in the base's span — `C = z • B`, as the DL game supplies — uniform pairs
`(x i, y i)` present uniform slot logs `x i + z * y i`, so the simulation is perfect;
`Soundness.AGM.Probability.programmedRelSet_card` proves that counting. -/
structure ProgrammedBasisEmbedding {ι : Type*} [Fintype ι] (B C : G) (basis : ι → G) where
  x : ι → F
  y : ι → F
  programmed : ∀ i, basis i = x i • B + y i • C

/-- Over a programmed basis, a representation separates into base and challenge components. -/
theorem representationEval_programmed {ι : Type*} [Fintype ι]
    (B C : G) (basis : ι → G) (x y coeffs : ι → F)
    (hprog : ∀ i, basis i = x i • B + y i • C) :
    representationEval basis coeffs =
      (∑ i, coeffs i * x i) • B + (∑ i, coeffs i * y i) • C := by
  calc
    representationEval basis coeffs
        = ∑ i, ((coeffs i * x i) • B + (coeffs i * y i) • C) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hprog i, smul_add, smul_smul, smul_smul]
    _ = (∑ i, coeffs i * x i) • B + (∑ i, coeffs i * y i) • C := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]

/-- Recover the challenge's discrete log from a relation with nonzero challenge component — a
field solve for `C`, with no slot guess. -/
def discreteLogOfChallenge_of_relation {ι : Type*} [Fintype ι]
    (B C : G) (basis : ι → G) (x y : ι → F)
    (r : AlgebraicRelationWitness (F := F) basis)
    (hprog : ∀ i, basis i = x i • B + y i • C)
    (hpair : (∑ i, r.coeffs i * y i) ≠ 0) :
    DiscreteLogRepresentation (F := F) B C := by
  refine ⟨(∑ i, r.coeffs i * y i)⁻¹ * (-(∑ i, r.coeffs i * x i)), ?_⟩
  have hzero : (∑ i, r.coeffs i * x i) • B + (∑ i, r.coeffs i * y i) • C = 0 := by
    rw [← representationEval_programmed B C basis x y r.coeffs hprog]
    exact r.relation
  have hmul : (∑ i, r.coeffs i * y i) • C = (-(∑ i, r.coeffs i * x i)) • B := by
    calc
      (∑ i, r.coeffs i * y i) • C = -((∑ i, r.coeffs i * x i) • B) :=
        eq_neg_of_add_eq_zero_right hzero
      _ = (-(∑ i, r.coeffs i * x i)) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (∑ i, r.coeffs i * y i)⁻¹ • X)) hmul
  have hlog : C = ((∑ i, r.coeffs i * y i)⁻¹ * (-(∑ i, r.coeffs i * x i))) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hpair] using hscale
  exact hlog.symm

/-- The result of testing one returned relation against the challenge programming. Both branches
retain that same relation: *either* it yields the challenge's discrete log, *or* its component
against `y` is zero. -/
abbrev ProgrammedRelationOutcome {ι : Type*} [Fintype ι] (B C : G) (basis : ι → G)
    (y : ι → F) : Type _ :=
  Σ' r : AlgebraicRelationWitness (F := F) basis,
    DiscreteLogRepresentation (F := F) B C ⊕' ((∑ i, r.coeffs i * y i) = 0)

/-- Extract the challenge's discrete log, or return proof that the same relation has zero
challenge component. -/
def programmedExtractOrMiss {ι : Type*} [Fintype ι] [DecidableEq F]
    (B C : G) {basis : ι → G}
    (embedding : ProgrammedBasisEmbedding (F := F) B C basis)
    (r : AlgebraicRelationWitness (F := F) basis) :
    ProgrammedRelationOutcome (F := F) B C basis embedding.y := by
  refine ⟨r, ?_⟩
  if hpair : (∑ i, r.coeffs i * embedding.y i) ≠ 0 then
    exact PSum.inl (discreteLogOfChallenge_of_relation B C basis embedding.x embedding.y r
      embedding.programmed hpair)
  else
    exact PSum.inr (not_ne_iff.mp hpair)

/-- The shared computed-data relation over the augmented basis `(g, U, W)`. -/
abbrev AugmentedRelationWitness {n : ℕ} (g : Fin n → G) (U W : G) :=
  Zcash.NontrivialRelation (F := F) g U W

/-- The augmented basis index: URS-generator slots plus two slots for `U` and `W`. -/
abbrev AugmentedIndex (n : ℕ) := Sum (Fin n) (Fin 2)

namespace AugmentedIndex

/-- The slot for a URS generator. -/
def gen {n : ℕ} (i : Fin n) : AugmentedIndex n := Sum.inl i

/-- The slot for `U`. -/
def u {n : ℕ} : AugmentedIndex n := Sum.inr 0

/-- The slot for `W`. -/
def w {n : ℕ} : AugmentedIndex n := Sum.inr 1

end AugmentedIndex

/-- Interpret the augmented index as the public basis `(g, U, W)`. -/
def augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G) : AugmentedIndex n → G
  | Sum.inl i => g i
  | Sum.inr j => if j = 0 then U else W

/-- Split an augmented public basis into its URS generators, `U`, and `W`. -/
def ursOfAugmentedBasis (k : ℕ) (basis : AugmentedIndex (2 ^ k) → G) : URS G :=
  { k := k
    g := fun i => basis (AugmentedIndex.gen i)
    u := basis AugmentedIndex.u
    w := basis AugmentedIndex.w }

omit [AddCommGroup G] in
/-- Splitting an augmented basis into a URS and reassembling it loses no public group element. -/
@[simp] theorem augmentedBasis_ursOfAugmentedBasis (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) :
    augmentedBasis (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w = basis := by
  funext i
  rcases i with i | j
  · rfl
  · fin_cases j <;> simp [augmentedBasis, ursOfAugmentedBasis, AugmentedIndex.u,
      AugmentedIndex.w]

/-- The coefficients of an augmented relation as one representation vector. -/
def augmentedCoeffs {n : ℕ} (a : Fin n → F) (alpha beta : F) : AugmentedIndex n → F
  | Sum.inl i => a i
  | Sum.inr j => if j = 0 then alpha else beta

/-- Evaluating an augmented representation is the MSM used by `NontrivialRelation`. -/
theorem representationEval_augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G)
    (a : Fin n → F) (alpha beta : F) :
    representationEval (augmentedBasis g U W) (augmentedCoeffs a alpha beta) =
      commitGen g a + alpha • U + beta • W := by
  simp [representationEval, augmentedBasis, augmentedCoeffs, commitGen, Fintype.sum_sum_type,
    add_assoc]

namespace AugmentedRelationWitness

/-- The same relation witness, viewed as a generic algebraic relation over the augmented basis. -/
def toAlgebraicRelationWitness {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  { coeffs := augmentedCoeffs r.a r.α r.β
    nontrivial := by
      intro hzero
      have ha : r.a = 0 := by
        funext i
        have h := congrFun hzero (AugmentedIndex.gen i)
        simpa [AugmentedIndex.gen, augmentedCoeffs] using h
      have halpha : r.α = 0 := by
        have h := congrFun hzero (AugmentedIndex.u)
        simpa [AugmentedIndex.u, augmentedCoeffs] using h
      have hbeta : r.β = 0 := by
        have h := congrFun hzero (AugmentedIndex.w)
        simpa [AugmentedIndex.w, augmentedCoeffs] using h
      rcases r.nontrivial with hnt | hnt
      · exact hnt ha
      · rcases hnt with hnt | hnt
        · exact hnt halpha
        · exact hnt hbeta
    relation := by
      rw [representationEval_augmentedBasis]
      exact r.relation }

/-- The same relation witness, viewed as an AGM representation of zero over the augmented basis. -/
def toGroupRepresentation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    GroupRepresentation (F := F) (augmentedBasis g U W) (0 : G) :=
  r.toAlgebraicRelationWitness.toGroupRepresentation

end AugmentedRelationWitness

/-- A commitment collision gives an explicit nontrivial algebraic relation over the URS generators. -/
def relationWitnessOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    AlgebraicRelationWitness (F := F) urs.g := by
  let r := NontrivialDLRelation.ofCollision urs hcollision hneq
  exact { coeffs := r.coeffs, nontrivial := r.nontrivial, relation := r.relation }

/-- A commitment collision gives an AGM representation of the identity over the URS generators. -/
def groupRepresentationOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    GroupRepresentation (F := F) urs.g (0 : G) :=
  (relationWitnessOfCollision urs hneq hcollision).toGroupRepresentation

/-- Extend a relation over `g` to `(g,U,W)` with zero `U` and `W` coefficients for the augmented
DL reduction. -/
def AlgebraicRelationWitness.augment {n : ℕ} {g : Fin n → G} (U W : G)
    (r : AlgebraicRelationWitness (F := F) g) :
    AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  AugmentedRelationWitness.toAlgebraicRelationWitness
    { a := r.coeffs
      α := 0
      β := 0
      nontrivial := Or.inl r.nontrivial
      relation := by
        rw [zero_smul, zero_smul, add_zero, add_zero]
        exact r.relation }

/-- Use an augmented relation to solve DL when it hits the fixed challenge slot. -/
def discreteLogOfAugmentedRelationAtChallenge {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (logs : AugmentedIndex n → F) (challenge : AugmentedIndex n)
    (r : AugmentedRelationWitness (F := F) g U W)
    (hknown : ∀ i, i ≠ challenge → augmentedBasis g U W i = logs i • B)
    (hcoeff : augmentedCoeffs r.a r.α r.β challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (augmentedBasis g U W challenge) :=
  discreteLogOfBasis_of_relation B (augmentedBasis g U W) logs challenge
    r.toAlgebraicRelationWitness hknown hcoeff

/-- Recover the discrete log of `U` from an augmented relation with a nonzero `U` coefficient.

The logs of every URS generator and `W` over `B` must be known. -/
def discreteLogOfU_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (wLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hW : W = wLog • B) (halpha : r.α ≠ 0) :
    DiscreteLogRepresentation (F := F) B U :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog 0 wLog)
    AugmentedIndex.u r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · exact absurd rfl hi
        · simpa [augmentedBasis, augmentedCoeffs] using hW)
    (by simpa [augmentedCoeffs, AugmentedIndex.u] using halpha)

/-- Recover the discrete log of `W` from an augmented relation with a nonzero `W` coefficient.

The logs of every URS generator and `U` over `B` must be known. -/
def discreteLogOfW_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (uLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hU : U = uLog • B) (hbeta : r.β ≠ 0) :
    DiscreteLogRepresentation (F := F) B W :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog uLog 0)
    AugmentedIndex.w r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · simpa [augmentedBasis, augmentedCoeffs] using hU
        · exact absurd rfl hi)
    (by simpa [augmentedCoeffs, AugmentedIndex.w] using hbeta)

end Zcash.Snark
