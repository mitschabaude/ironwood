import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedSqueeze

/-!
# The prefixed `x` squeeze

The concrete constraint bad set reads the pre-`x` transcript and the four earlier Fiat–Shamir
answers.  These facts prove that the earlier points remain pinned when the `x` answer is
resampled, then price the resulting one-level bad-root event directly.  No multiopen rewind or
fourth-root continuation threshold is involved.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

variable {shape : Shape}

/-- Every pre-`x` squeeze point is a strict prefix of the `x` squeeze point. -/
theorem preIpaLen_lt_x (shape : Shape) (n0 : Nat) {i : Fin 11} (hi : (i : Nat) < 4) :
    preIpaLen shape n0 i < preIpaLen shape n0 4 := by
  have hcase : (i : Nat) = 0 ∨ (i : Nat) = 1 ∨ (i : Nat) = 2 ∨ (i : Nat) = 3 := by omega
  rcases hcase with h | h | h | h
  · obtain rfl : i = ⟨0, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨1, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨2, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨3, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]

/-- Equal `x` squeeze points imply equal earlier squeeze points. -/
theorem algebraicFullPrefixesPre_eq_of_x_eq
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p q : AlgebraicWfProof basis vk instanceCommitment)
    (h : algebraicFullPrefixesPre init p 4 = algebraicFullPrefixesPre init q 4)
    {i : Fin 11} (hi : (i : Nat) < 4) :
    algebraicFullPrefixesPre init p i = algebraicFullPrefixesPre init q i := by
  apply Subtype.ext
  have hval : preIpaSqueezePoints init p.proof.1 4 = preIpaSqueezePoints init q.proof.1 4 :=
    congrArg Subtype.val h
  have hpreP := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init p.proof.1 i)
    (preIpaSqueezePoints_prefix init p.proof.1 4)
    (by
      rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
        preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2]
      exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  have hpreQ := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init q.proof.1 i)
    (preIpaSqueezePoints_prefix init q.proof.1 4)
    (by
      rw [preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2,
        preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2]
      exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  show preIpaSqueezePoints init p.proof.1 i = preIpaSqueezePoints init q.proof.1 i
  rw [List.prefix_iff_eq_take.mp hpreP, List.prefix_iff_eq_take.mp hpreQ,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2, hval]

/-- An earlier squeeze point differs from the `x` point because their lengths differ. -/
theorem algebraicFullPrefixesPre_ne_x
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) {i : Fin 11} (hi : (i : Nat) < 4) :
    algebraicFullPrefixesPre init p i ≠ algebraicFullPrefixesPre init p 4 := by
  intro hEq
  have hlen : (preIpaSqueezePoints init p.proof.1 i).length =
      (preIpaSqueezePoints init p.proof.1 4).length :=
    congrArg (fun t : List (TranscriptElt Fp VestaG) => t.length) (congrArg Subtype.val hEq)
  rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2] at hlen
  exact absurd hlen (Nat.ne_of_lt (preIpaLen_lt_x shape init.length hi))

open ComputedAlgebraicFSFamily in
/-- The pre-`x` transcript and earlier answers remain pinned while resampling `x`, so a bad-root
event at `x` costs only `(Q + 1) * epsilon`.

The discharge toolkit for `DeployedConstraintXSqueezeSchedule.pinned`: once the `x` prefix is
stable under reprogramming (`hstab`), the earlier answers are too — their squeeze points are
strict sub-prefixes. -/
theorem badX_le_via_squeeze_prefixed {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedAlgebraicFSFamily shape)
    (goodX : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.Coins -> Prop)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin 4 -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {epsilon : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) <= epsilon)
    (hcontX : forall basis, {coins : family.Coins | ¬ goodX basis coins} <=
      {coins : family.Coins |
        coins.1 (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins.1) 4) ∈
          badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) 4)
            (fun i : Fin 4 => coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ goodX q.1 q.2})
      <= (family.Q + 1 : Nat) * epsilon := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ goodX q.1 q.2} =
      {x : (↥(Set.range query) -> VestaG) × family.Coins | x.2 ∈
        (fun setup => {coins : family.Coins |
          ¬ goodX (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      ¬ goodX (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  set basis' := orchardGeneratorROBasis query setup with hbasis'
  refine le_trans (MeasureTheory.measure_mono (hcontX basis')) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | O (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) 4) ∈
        badF basis' (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) 4)
          (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) (i.castLE (by omega))))})
    (fun _ => ?_)
  refine xEscTable_measure_le (family.adversary basis')
    (fun p => algebraicFullPrefixesPre family.init p 4)
    (fun p O => badF basis' (algebraicFullPrefixesPre family.init p 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init p (i.castLE (by omega)))))
    ?_ (fun p O => hbad basis' _ _) (family.queryBound basis')
  intro O v
  have hx := hstab basis' O v
  show badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)) 4)
      (fun i : Fin 4 => (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)
        (algebraicFullPrefixesPre family.init ((family.adversary basis').run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) 4) v)) (i.castLE (by omega)))) =
    badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis').run O) (i.castLE (by omega))))
  rw [hx]
  congr 1
  funext i
  rw [algebraicFullPrefixesPre_eq_of_x_eq family.init _ _ hx
      (show ((i.castLE (by omega) : Fin 11) : Nat) < 4 from i.isLt),
    Function.update_of_ne
      (algebraicFullPrefixesPre_ne_x family.init _
        (show ((i.castLE (by omega) : Fin 11) : Nat) < 4 from i.isLt))]

/-! ## Discharging the stability input

`badX_le_via_squeeze_prefixed`'s `hstab` is resampling-shaped: updating the oracle at the run's own `x` squeeze
point leaves the point unchanged. For a Fiat–Shamir prover this is a consequence of a more
natural property — the pre-`x` prefix reads only answers at strictly shorter transcripts — and
that property implies `hstab` outright: the update point has exactly the `x` prefix's length, so
no strictly shorter answer moves. -/

/-- **Fiat–Shamir prefix-determinism.** The adversary's `x` squeeze point reads only oracle
answers at transcripts strictly shorter than the `x` prefix: two tables agreeing below that
length produce the same `x` squeeze point. Every sequential Fiat–Shamir prover has this shape —
its pre-`x` commitments are functions of the earlier challenges alone. -/
def XPrefixDetermined (family : ComputedAlgebraicFSFamily shape) : Prop :=
  ∀ basis (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp),
    (∀ t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length 4 → O t = O' t) →
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4
      = algebraicFullPrefixesPre family.init ((family.adversary basis).run O') 4

/-- Prefix-determinism discharges the squeeze-point stability input: the update point is the `x`
prefix itself, of exactly the `x` prefix's length, so every strictly shorter answer is untouched
and the determinism hypothesis applies. -/
theorem hstab_of_xPrefixDetermined (family : ComputedAlgebraicFSFamily shape)
    (hdet : XPrefixDetermined family) :
    ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4
        = algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4 := by
  intro basis O v
  refine hdet basis _ O ?_
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) 4).val.length
      = preIpaLen shape family.init.length 4 :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 4
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

end Zcash.Snark
