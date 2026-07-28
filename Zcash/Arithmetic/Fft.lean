/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.Domain
import Zcash.Arithmetic.Group

/-!
# The Rust-mirroring group FFT and the derived Lagrange basis

`bestFftG` is halo2's `best_fft` (`arithmetic.rs:192-256`) over an arbitrary `Fp`-module `G`:
the bit-reversal permutation (`bitreverse`), a precomputed twiddle table, and `log_n` rounds of
decimation-in-time butterflies. `derivedUrsGLagrange` runs it at the inverse root `omegaInvOf`
and scales by `n⁻¹` to obtain the Lagrange-basis generators of a monomial URS
(`Params::new`, `poly/commitment.rs:75-88`).

These are pure arithmetic: they mention only `Fp`, `URS` and the module action, and nothing
from the Clean circuit layer, so kernel transplants and accelerator lanes certify against
them without importing the keygen pipeline. Keeping `bestFftG` generic over the `Fp`-module
means its field instance (the scalar inverse DFT) and its group instances share one
definition, so no scalar-vs-group agreement lemma ever needs to exist.

The last section abstracts the loop nest itself (`fftGen`) and reduces it to pure folds
(`fftGen_eq_folds`). That is the shared vocabulary every carrier transplant of this FFT is
proven against.
-/

namespace Zcash.Arithmetic

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Lagrange URS derivation (`poly/commitment.rs:75-88`, `arithmetic.rs:192`) -/

/-- `bitreverse(n, l)` — reverse the low `l` bits of `n` (`best_fft`'s local `bitreverse`,
`arithmetic.rs:193-200`). -/
def bitreverse (n l : ℕ) : ℕ := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- The size-`2^k` root of unity's inverse, `omega⁻¹ = omega^(2^k − 1)` (order `2^k`).
This is halo2's `alpha_inv` (`ROOT_OF_UNITY_INV` squared `S − k` times,
`poly/commitment.rs:76-79`), computed here from `omegaOf` since both are the same
primitive `2^k`-th root. -/
def omegaInvOf (k : ℕ) : Fp := powFast (omegaOf k) (2 ^ k - 1)

/-- In-place radix-2 DIT FFT over the group `G` with `Fp` twiddles, mirroring
`best_fft(a, omega, log_n)` (`arithmetic.rs:192-256`): bit-reversal permutation, precomputed
twiddle powers `[omega^0 … omega^(n/2−1)]`, then `log_n` rounds of decimation-in-time
butterflies `(a, b) ↦ (a + tw·b, a − tw·b)`. The scalar action `tw·b` is the same
`ZMod.val • point` convention `commitLagrange` uses (Rust's iterative and recursive
`best_fft` branches compute this identical result; we mirror the iterative one,
`arithmetic.rs:223-252`). -/
def bestFftG (a0 : Array G) (omega : Fp) (logN : ℕ) : Array G := Id.run do
  let n := a0.size
  let mut a := a0
  -- bit-reversal permutation (`arithmetic.rs:207-212`)
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  -- precompute twiddles `[omega^0 … omega^(n/2 − 1)]` (`arithmetic.rs:215-221`)
  let mut tw : Array Fp := Array.mkEmpty (n / 2)
  let mut w : Fp := 1
  for _ in [0:n / 2] do
    tw := tw.push w
    w := w * omega
  -- `log_n` rounds of butterflies (`arithmetic.rs:223-252`)
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := twdl.val • a[bIdx]!
        a := a.set! aIdx (aOld + t)
        a := a.set! bIdx (aOld - t)
    half := chunk
  return a

/-- The Lagrange-basis generators derived from a monomial URS by inverse FFT and
`n⁻¹` scaling, exactly as in halo2's `Params::new`. -/
def derivedUrsGLagrange (urs : URS G) : List G :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftG monomial.toArray (omegaInvOf urs.k) urs.k).toList.map
    fun point => minv.val • point

/-! ## The loop nest, abstracted

Every transplant of `bestFftG` onto a faster carrier is the *same* loop nest with the element
type, the butterfly operations and the twiddle type swapped out. `fftGen` is that nest, so a
transplant and its statement surface are recognized as two instances of it — both by `rfl`, since
the loop bodies are textually the schedule below — and `fftGen_eq_folds` then converts the whole
imperative nest into pure `List.foldl`s over three named steps (`permStep`, `butterflyGen`,
`roundFoldGen`). A simulation proof only has to push its invariant through those three.

Nothing here mentions `Fp`, `G` or the module action: these are the shape of the algorithm, not
of the group FFT. -/

/-- The radix-2 DIT FFT loop nest with the element type, the butterfly operations and the twiddle
type all abstracted. `bestFftG` is the instance at the group's `(+)`, `(−)` and `ZMod.val`-smul
(with the twiddle table factored out); a carrier transplant is the instance at its own
operations. -/
def fftGen {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (a0 : Array α) (tw : Array τ) (logN : ℕ) : Array α := Id.run do
  let n := a0.size
  let mut a := a0
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := smul twdl a[bIdx]!
        a := a.set! aIdx (add aOld t)
        a := a.set! bIdx (sub aOld t)
    half := chunk
  return a

/-- Phase 1 of `fftGen`, extracted verbatim: the bit-reversal permutation. -/
private def brPermGen {α : Type} [Inhabited α] (a0 : Array α) (logN : ℕ) : Array α := Id.run do
  let mut a := a0
  for k in [0:a0.size] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  return a

/-- Phase 2 of `fftGen`, extracted verbatim: the `logN` butterfly rounds. -/
private def roundsGen {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (n : ℕ) (tw : Array τ) (a0 : Array α) (logN : ℕ) : Array α := Id.run do
  let mut a := a0
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := smul twdl a[bIdx]!
        a := a.set! aIdx (add aOld t)
        a := a.set! bIdx (sub aOld t)
    half := chunk
  return a

private theorem fftGen_decompose {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (a0 : Array α) (tw : Array τ) (logN : ℕ) :
    fftGen add sub smul a0 tw logN
      = roundsGen add sub smul a0.size tw (brPermGen a0 logN) logN := rfl

/-- One step of the bit-reversal permutation. -/
def permStep {α : Type} [Inhabited α] (logN : ℕ) (a : Array α) (k : ℕ) : Array α :=
  if k < bitreverse k logN then
    (a.set! k a[bitreverse k logN]!).set! (bitreverse k logN) a[k]!
  else a

private theorem brPermGen_eq_foldl {α : Type} [Inhabited α] (a0 : Array α) (logN : ℕ) :
    brPermGen a0 logN = (List.range a0.size).foldl (permStep logN) a0 := by
  show (forIn (m := Id) [0:a0.size] a0 (fun k a =>
      if k < bitreverse k logN then
        pure (ForInStep.yield ((a.set! k a[bitreverse k logN]!).set! (bitreverse k logN) a[k]!))
      else pure (ForInStep.yield a)) >>= fun r => (pure r : Id (Array α))) = _
  simp only [← apply_ite (fun (z : Array α) => pure (f := Id) (ForInStep.yield z))]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl]
  rfl

/-- A single butterfly `(c, j)` of a round at width `half`, as a pure array step. -/
def butterflyGen {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (n half : ℕ) (tw : Array τ) (c j : ℕ) (a : Array α) : Array α :=
  (a.set! (c * (2 * half) + j)
      (add a[c * (2 * half) + j]!
        (smul tw[j * (n / (2 * half))]! a[c * (2 * half) + half + j]!))).set!
    (c * (2 * half) + half + j)
      (sub a[c * (2 * half) + j]!
        (smul tw[j * (n / (2 * half))]! a[c * (2 * half) + half + j]!))

/-- One round of butterflies at width `half`, as a pure double fold. -/
def roundFoldGen {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (n half : ℕ) (tw : Array τ) (a0 : Array α) : Array α :=
  (List.range (n / (2 * half))).foldl
    (fun a c => (List.range half).foldl
      (fun a j => butterflyGen add sub smul n half tw c j a) a) a0

private theorem roundsGen_eq_foldl {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (n : ℕ) (tw : Array τ) (a0 : Array α) (logN : ℕ) :
    roundsGen add sub smul n tw a0 logN =
      ((List.range logN).foldl (fun (p : MProd (Array α) ℕ) _ =>
        ⟨roundFoldGen add sub smul n p.2 tw p.1, 2 * p.2⟩) ⟨a0, 1⟩).1 := by
  show (forIn (m := Id) [0:logN] (⟨a0, 1⟩ : MProd (Array α) ℕ) (fun _ p =>
      (forIn (m := Id) [0:n / (2 * p.2)] p.1 (fun c a =>
        ForInStep.yield <$> forIn (m := Id) [0:p.2] a (fun j a =>
          pure (ForInStep.yield (butterflyGen add sub smul n p.2 tw c j a)))) >>= fun a =>
        pure (ForInStep.yield (⟨a, 2 * p.2⟩ : MProd (Array α) ℕ)))) >>= fun r =>
      match r with | ⟨a, _⟩ => (pure a : Id (Array α))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl,
    map_pure, pure_bind]
  rfl

private theorem foldl_rounds_half {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (n : ℕ) (tw : Array τ) (l : ℕ) (a : Array α) :
    (List.range l).foldl (fun (p : MProd (Array α) ℕ) _ =>
        ⟨roundFoldGen add sub smul n p.2 tw p.1, 2 * p.2⟩) ⟨a, 1⟩ =
      ⟨(List.range l).foldl (fun a r => roundFoldGen add sub smul n (2 ^ r) tw a) a, 2 ^ l⟩ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    refine congrArg₂ MProd.mk rfl ?_
    rw [pow_succ]
    ring

/-- The generic loop nest as a permutation fold followed by `logN` round folds. -/
theorem fftGen_eq_folds {α τ : Type} [Inhabited α] [Inhabited τ] (add sub : α → α → α)
    (smul : τ → α → α) (a0 : Array α) (tw : Array τ) (logN : ℕ) :
    fftGen add sub smul a0 tw logN
      = (List.range logN).foldl (fun a r => roundFoldGen add sub smul a0.size (2 ^ r) tw a)
          ((List.range a0.size).foldl (permStep logN) a0) := by
  rw [fftGen_decompose, roundsGen_eq_foldl, foldl_rounds_half, brPermGen_eq_foldl]

end Zcash.Arithmetic
