/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.Fft

/-!
# The DFT specification of `bestFftG`

`bestFftG` (`Zcash.Arithmetic.Fft`) is the Rust-mirroring radix-2 DIT group FFT —
bit-reversal permutation, twiddle table, `logN` rounds of imperative butterflies. This module
proves its full mathematical specification: for an input of size `2^logN` and a primitive
`2^logN`-th root of unity `ω`, the output is the group-valued discrete Fourier transform

  `bestFftG a ω logN [i] = ∑ₖ ω^(i·k) • a[k]`   (`bestFftG_dft`),

generic in an `Fp`-module `G`. The `Module Fp G` premise is what lets the algorithm's
`ZMod.val`-smuls compose across rounds (`ZMod.val (x*y) ≡ x.val * y.val [MOD p]` is exactly
`val_smul` + `smul_smul` through the module action).

## Shape of the proof

* `bitrev` is a pure structural spelling of the imperative `bitreverse`
  (`bitreverse_eq_bitrev`), with the low-bit and high-bit recursions, the range bound and the
  involution `bitrev_bitrev` proved by induction.
* `bestFftG` is split — definitionally, `bestFftG_decompose` is `rfl` — into its three
  verbatim phases `brPermImp`/`twImp`/`roundsImp`, and each imperative phase is converted to a
  pure `List.foldl` through the core `forIn`-to-`foldl` lemmas (the same route
  `Arithmetic/Fft.lean` takes for the loop nest itself).
* A round of butterflies is characterized by the written/fresh fold invariant `InvG`, a
  disjointness argument: each butterfly reads only the two cells it writes, so after the round
  every cell holds its gathered value `gOutG`.
* The heart is `ct_step`, the Cooley–Tukey butterfly identity for the bit-reversed DFT sums,
  and `rounds_dft`, the induction over rounds with the invariant "after round `r`, each
  `2^r`-block holds the size-`2^r` DFT of its bit-reversal-permuted slice". The minus branch
  uses `ω^(2^(logN−1)) = −1` from primitivity (`pow_half_eq_neg_one`).

## Wiring corollaries

`derivedUrsGLagrange` is the scaled inverse FFT of the monomial URS, and this module supplies
what the verifier side spends on it: the DFT spec itself, `derivedUrsGLagrange_length`, and
`omegaInvOf_isPrimitiveRoot` (from `omegaInvOf_eq_inv` and the certified domain root).

`Zcash/Snark/Keygen/Lagrange.lean` puts them together into
`derivedUrsGLagrange_generator_eq` — the `i`-th derived Lagrange generator is the monomial
commitment to the closed Lagrange coefficient row `n⁻¹ · ω^(−i·t)` — and from there into the
per-URS setup obligations of the fixed- and permutation-commitment identification theorems,
with no native certificate. That step names `commit`, which is verifier-side vocabulary, so it
cannot live here.
-/

namespace Zcash.Arithmetic

/-! ## The pure bit-reversal function -/

/-- Pure structural spelling of `bitreverse`: peel the low bit of `n` onto the top of the
accumulator, `l` times. -/
def bitrev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | l + 1, n => n % 2 * 2 ^ l + bitrev l (n / 2)

theorem bitrev_zero (n : ℕ) : bitrev 0 n = 0 := rfl

theorem bitrev_succ (l n : ℕ) : bitrev (l + 1) n = n % 2 * 2 ^ l + bitrev l (n / 2) := rfl

private theorem brStep_eq (r m : ℕ) : r <<< 1 ||| m &&& 1 = 2 * r + m % 2 := by
  rw [Nat.and_one_is_mod, ← Nat.shiftLeft_add_eq_or_of_lt (i := 1) (by omega),
    Nat.shiftLeft_eq]
  ring

private theorem bitreverse_eq_foldl (n l : ℕ) :
    bitreverse n l =
      ((List.range l).foldl (fun (p : MProd ℕ ℕ) _ => ⟨p.1 / 2, 2 * p.2 + p.1 % 2⟩)
        ⟨n, 0⟩).2 := by
  show (forIn (m := Id) [0:l] (⟨n, 0⟩ : MProd ℕ ℕ) (fun _ p =>
      pure (ForInStep.yield ⟨p.1 >>> 1, p.2 <<< 1 ||| p.1 &&& 1⟩)) >>= fun r =>
        match r with | ⟨_, r⟩ => (pure r : Id ℕ)) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl,
    brStep_eq, Nat.shiftRight_one]
  rfl

private theorem foldl_bitrev (l : ℕ) : ∀ r m : ℕ,
    (List.range l).foldl (fun (p : MProd ℕ ℕ) _ => ⟨p.1 / 2, 2 * p.2 + p.1 % 2⟩)
        (⟨m, r⟩ : MProd ℕ ℕ) = ⟨m / 2 ^ l, r * 2 ^ l + bitrev l m⟩ := by
  induction l with
  | zero => intro r m; simp [bitrev]
  | succ l ih =>
    intro r m
    rw [List.range_succ_eq_map]
    simp only [List.foldl_cons, List.foldl_map, ih]
    refine congrArg₂ MProd.mk ?_ ?_
    · rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [pow_succ]
      ring
    · rw [bitrev_succ]
      ring

/-- The imperative `bitreverse` computes the pure recursion `bitrev`. -/
theorem bitreverse_eq_bitrev (n l : ℕ) : bitreverse n l = bitrev l n := by
  rw [bitreverse_eq_foldl, foldl_bitrev]
  simp

theorem bitrev_lt (l n : ℕ) : bitrev l n < 2 ^ l := by
  induction l generalizing n with
  | zero => simp [bitrev]
  | succ l ih =>
    have h1 := ih (n / 2)
    have h2 : n % 2 * 2 ^ l ≤ 2 ^ l := by
      calc n % 2 * 2 ^ l ≤ 1 * 2 ^ l := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ l := one_mul _
    rw [bitrev_succ, pow_succ]
    omega

/-- The dual recursion: peel the top bit of `n` onto the bottom. -/
theorem bitrev_succ_high (l n : ℕ) (hn : n < 2 ^ (l + 1)) :
    bitrev (l + 1) n = 2 * bitrev l (n % 2 ^ l) + n / 2 ^ l := by
  induction l generalizing n with
  | zero =>
    simp only [bitrev, pow_zero, Nat.div_one] at hn ⊢
    omega
  | succ l ih =>
    have hn2 : n / 2 < 2 ^ (l + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← pow_succ]
      exact hn
    rw [bitrev_succ (l + 1) n, ih _ hn2, bitrev_succ l (n % 2 ^ (l + 1))]
    have hm2 : n % 2 ^ (l + 1) % 2 = n % 2 :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
    have hmd : n % 2 ^ (l + 1) / 2 = n / 2 % 2 ^ l := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    have hdd : n / 2 / 2 ^ l = n / 2 ^ (l + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [hm2, hmd, hdd]
    ring

private theorem tile_div {d q r : ℕ} (hr : r < d) : (q * d + r) / d = q := by
  rw [Nat.mul_comm q d, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

private theorem tile_mod {d q r : ℕ} (hr : r < d) : (q * d + r) % d = r := by
  rw [Nat.mul_comm q d, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- Uniqueness of the `(quotient, remainder)` tiling — the workhorse behind both the
bit-reversal pairing and the butterfly disjointness argument. -/
private theorem tile_inj {d q r q' r' : ℕ} (hr : r < d) (hr' : r' < d)
    (h : q * d + r = q' * d + r') : q = q' ∧ r = r' :=
  ⟨by rw [← tile_div (q := q) hr, h, tile_div hr'],
   by rw [← tile_mod (q := q) hr, h, tile_mod hr']⟩

/-- `bitrev l` is an involution on `[0, 2^l)`. -/
theorem bitrev_bitrev (l n : ℕ) (hn : n < 2 ^ l) : bitrev l (bitrev l n) = n := by
  induction l generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    rfl
  | succ l ih =>
    rw [bitrev_succ l n, bitrev_succ_high l _ (by rw [← bitrev_succ]; exact bitrev_lt _ _)]
    have hx : bitrev l (n / 2) < 2 ^ l := bitrev_lt _ _
    have h1 : (n % 2 * 2 ^ l + bitrev l (n / 2)) % 2 ^ l = bitrev l (n / 2) :=
      tile_mod hx
    have h2 : (n % 2 * 2 ^ l + bitrev l (n / 2)) / 2 ^ l = n % 2 :=
      tile_div hx
    rw [h1, h2, ih _ (by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← pow_succ]
      exact hn)]
    omega

private theorem bitrev_two_mul (r u : ℕ) : bitrev (r + 1) (2 * u) = bitrev r u := by
  rw [bitrev_succ]
  have h1 : 2 * u % 2 = 0 := by omega
  have h2 : 2 * u / 2 = u := by omega
  rw [h1, h2, zero_mul, zero_add]

private theorem bitrev_two_mul_add_one (r u : ℕ) :
    bitrev (r + 1) (2 * u + 1) = 2 ^ r + bitrev r u := by
  rw [bitrev_succ]
  have h1 : (2 * u + 1) % 2 = 1 := by omega
  have h2 : (2 * u + 1) / 2 = u := by omega
  rw [h1, h2, one_mul]

/-! ## The three phases of `bestFftG`, extracted verbatim -/

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- Phase 1 of `bestFftG`: the bit-reversal permutation loop, extracted verbatim. -/
private def brPermImp (a0 : Array G) (logN : ℕ) : Array G := Id.run do
  let mut a := a0
  for k in [0:a0.size] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  return a

/-- Phase 2 of `bestFftG`: the twiddle table `[ω^0 … ω^(m−1)]`, extracted verbatim. -/
private def twImp (omega : Fp) (m : ℕ) : Array Fp := Id.run do
  let mut tw : Array Fp := Array.mkEmpty m
  let mut w : Fp := 1
  for _ in [0:m] do
    tw := tw.push w
    w := w * omega
  return tw

/-- Phase 3 of `bestFftG`: the `logN` butterfly rounds, extracted verbatim. -/
private def roundsImp (n : ℕ) (tw : Array Fp) (a0 : Array G) (logN : ℕ) : Array G := Id.run do
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
        let t := twdl.val • a[bIdx]!
        a := a.set! aIdx (aOld + t)
        a := a.set! bIdx (aOld - t)
    half := chunk
  return a

/-- `bestFftG` is definitionally the composition of its three phases. -/
private theorem bestFftG_decompose (a0 : Array G) (omega : Fp) (logN : ℕ) :
    bestFftG a0 omega logN =
      roundsImp a0.size (twImp omega (a0.size / 2)) (brPermImp a0 logN) logN := rfl

/-! ## The imperative phases as pure folds -/

omit [AddCommGroup G] in
private theorem brPermImp_eq_foldl (a0 : Array G) (logN : ℕ) :
    brPermImp a0 logN =
      (List.range a0.size).foldl (fun a k =>
        if k < bitreverse k logN then
          (a.set! k a[bitreverse k logN]!).set! (bitreverse k logN) a[k]!
        else a) a0 := by
  show (forIn (m := Id) [0:a0.size] a0 (fun k a =>
      if k < bitreverse k logN then
        pure (ForInStep.yield ((a.set! k a[bitreverse k logN]!).set! (bitreverse k logN) a[k]!))
      else pure (ForInStep.yield a)) >>= fun r => (pure r : Id (Array G))) = _
  simp only [← apply_ite (fun (z : Array G) => pure (f := Id) (ForInStep.yield z))]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl]
  rfl

private theorem twImp_eq_foldl (omega : Fp) (m : ℕ) :
    twImp omega m =
      ((List.range m).foldl
        (fun (p : MProd (Array Fp) Fp) _ => ⟨p.1.push p.2, p.2 * omega⟩)
        ⟨Array.mkEmpty m, 1⟩).1 := by
  show (forIn (m := Id) [0:m] (⟨Array.mkEmpty m, 1⟩ : MProd (Array Fp) Fp) (fun _ p =>
      pure (ForInStep.yield ⟨p.1.push p.2, p.2 * omega⟩)) >>= fun r =>
        match r with | ⟨tw, _⟩ => (pure tw : Id (Array Fp))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl]
  rfl

/-- The twiddle fold builds exactly the power table `[ω^0 … ω^(l−1)]`. -/
private theorem twFold_eq (omega : Fp) (m l : ℕ) :
    (List.range l).foldl (fun (p : MProd (Array Fp) Fp) _ => ⟨p.1.push p.2, p.2 * omega⟩)
        ⟨Array.mkEmpty m, 1⟩ =
      ⟨((List.range l).map (omega ^ ·)).toArray, omega ^ l⟩ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    refine congrArg₂ MProd.mk ?_ (by rw [pow_succ])
    rw [List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]

/-- The twiddled point of butterfly `(c, j)`: `tw[j·(n/chunk)]!.val • a[bIdx]!`, exactly as
computed by `bestFftG`'s inner loop. -/
private def twiddledPointG (n half : ℕ) (tw : Array Fp) (a : Array G) (c j : ℕ) : G :=
  (tw[j * (n / (2 * half))]!).val • a[c * (2 * half) + half + j]!

/-- A single butterfly of `bestFftG` as a pure array step. -/
private def butterflyG (n half : ℕ) (tw : Array Fp) (c j : ℕ) (a : Array G) : Array G :=
  (a.set! (c * (2 * half) + j) (a[c * (2 * half) + j]! + twiddledPointG n half tw a c j)).set!
    (c * (2 * half) + half + j) (a[c * (2 * half) + j]! - twiddledPointG n half tw a c j)

/-- One round of `bestFftG` butterflies at width `half`, as a pure double fold. -/
private def roundFold (n half : ℕ) (tw : Array Fp) (a0 : Array G) : Array G :=
  (List.range (n / (2 * half))).foldl
    (fun a c => (List.range half).foldl (fun a j => butterflyG n half tw c j a) a) a0

private theorem roundsImp_eq_foldl (n : ℕ) (tw : Array Fp) (a0 : Array G) (logN : ℕ) :
    roundsImp n tw a0 logN =
      ((List.range logN).foldl (fun (p : MProd (Array G) ℕ) _ =>
        ⟨roundFold n p.2 tw p.1, 2 * p.2⟩) ⟨a0, 1⟩).1 := by
  show (forIn (m := Id) [0:logN] (⟨a0, 1⟩ : MProd (Array G) ℕ) (fun _ p =>
      (forIn (m := Id) [0:n / (2 * p.2)] p.1 (fun c a =>
        ForInStep.yield <$> forIn (m := Id) [0:p.2] a (fun j a =>
          pure (ForInStep.yield (butterflyG n p.2 tw c j a)))) >>= fun a =>
        pure (ForInStep.yield (⟨a, 2 * p.2⟩ : MProd (Array G) ℕ)))) >>= fun r =>
      match r with | ⟨a, _⟩ => (pure a : Id (Array G))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl,
    map_pure, pure_bind]
  rfl

private theorem foldl_rounds_half (n : ℕ) (tw : Array Fp) (l : ℕ) (a : Array G) :
    (List.range l).foldl (fun (p : MProd (Array G) ℕ) _ =>
        ⟨roundFold n p.2 tw p.1, 2 * p.2⟩) ⟨a, 1⟩ =
      ⟨(List.range l).foldl (fun a r => roundFold n (2 ^ r) tw a) a, 2 ^ l⟩ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    refine congrArg₂ MProd.mk rfl ?_
    rw [pow_succ]
    ring

/-- The butterfly-rounds loop of `bestFftG` is the fold of `logN` pure rounds at widths
`2^0, …, 2^(logN−1)`. -/
private theorem roundsImp_eq_rounds (n : ℕ) (tw : Array Fp) (a0 : Array G) (logN : ℕ) :
    roundsImp n tw a0 logN =
      (List.range logN).foldl (fun a r => roundFold n (2 ^ r) tw a) a0 := by
  rw [roundsImp_eq_foldl, foldl_rounds_half]

/-! ## The bit-reversal permutation, characterized -/

omit [AddCommGroup G] in
/-- `getElem!` through `set!`, in unconditional form. -/
private theorem getElem!_set' (r : Array G) (p i : ℕ) (v : G) :
    (r.set! p v)[i]! = if p = i ∧ p < r.size then v else r[i]! := by
  by_cases hi : i < r.size
  · rw [getElem!_pos (r.set! p v) i (by simpa using hi), getElem!_pos r i hi]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hpi : p = i
    · subst hpi; simp [hi]
    · rw [if_neg (fun hc => hpi hc.1)]
      exact Array.getElem_setIfInBounds_ne hi hpi
  · rw [getElem!_neg (r.set! p v) i (by simpa using hi), getElem!_neg r i hi,
      if_neg (by omega)]

omit [AddCommGroup G] in
/-- The fold invariant of the bit-reversal loop: a cell holds its swapped value as soon as
either endpoint of its pair has been processed, and its original value before that. -/
private theorem brFold_inv (a0 : Array G) (logN : ℕ) (hsize : a0.size = 2 ^ logN) :
    ∀ t, t ≤ a0.size →
      ((List.range t).foldl (fun a k =>
          if k < bitrev logN k then
            (a.set! k a[bitrev logN k]!).set! (bitrev logN k) a[k]!
          else a) a0).size = a0.size ∧
      ∀ i, i < a0.size →
        ((List.range t).foldl (fun a k =>
            if k < bitrev logN k then
              (a.set! k a[bitrev logN k]!).set! (bitrev logN k) a[k]!
            else a) a0)[i]! =
          if i < t ∨ bitrev logN i < t then a0[bitrev logN i]! else a0[i]! := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp, fun i hi => ?_⟩
    simp only [List.range_zero, List.foldl_nil]
    rw [if_neg (by omega)]
  | succ t ih =>
    intro ht
    obtain ⟨ihs, ihv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set r := (List.range t).foldl (fun a k =>
        if k < bitrev logN k then
          (a.set! k a[bitrev logN k]!).set! (bitrev logN k) a[k]!
        else a) a0 with hr
    clear_value r
    have htn : t < 2 ^ logN := by omega
    have hrt : bitrev logN t < 2 ^ logN := bitrev_lt logN t
    have hrrt : bitrev logN (bitrev logN t) = t := bitrev_bitrev logN t htn
    have hstep : ∀ (x : Array G) (p q : ℕ) (v w : G),
        ((x.set! p v).set! q w).size = x.size := by
      intro x p q v w
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    constructor
    · split
      · rw [hstep, ihs]
      · exact ihs
    · intro i hi
      have hin : i < 2 ^ logN := by omega
      have hri : bitrev logN i < 2 ^ logN := bitrev_lt logN i
      have hrri : bitrev logN (bitrev logN i) = i := bitrev_bitrev logN i hin
      by_cases hswap : t < bitrev logN t
      · rw [if_pos hswap, getElem!_set', getElem!_set']
        have hsX : (r.set! t r[bitrev logN t]!).size = a0.size := by
          simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, ihs]
        by_cases hirt : i = bitrev logN t
        · rw [if_pos ⟨hirt.symm, by rw [hsX, hsize]; exact hrt⟩]
          have hbrieq : bitrev logN i = t := by rw [hirt, hrrt]
          rw [ihv t (by omega), if_neg (by omega), if_pos (Or.inr (by omega)), hbrieq]
        · rw [if_neg (fun hc => hirt hc.1.symm)]
          by_cases hit : i = t
          · rw [if_pos ⟨hit.symm, by rw [ihs, hsize]; exact htn⟩]
            rw [ihv (bitrev logN t) (by omega), if_neg (by omega),
              if_pos (Or.inl (by omega)), hit]
          · rw [if_neg (fun hc => hit hc.1.symm), ihv i hi]
            have hne : bitrev logN i ≠ t := fun he => hirt (by rw [← he, hrri])
            have hcnd : (i < t + 1 ∨ bitrev logN i < t + 1) ↔
                (i < t ∨ bitrev logN i < t) := by omega
            rw [if_congr hcnd rfl rfl]
      · rw [if_neg hswap, ihv i hi]
        by_cases hit : i = t
        · subst hit
          by_cases hrtt : bitrev logN i < i
          · rw [if_pos (Or.inr hrtt), if_pos (Or.inl (by omega))]
          · have heq : bitrev logN i = i := by omega
            rw [heq, ite_self, ite_self]
        · by_cases hbt : bitrev logN i = t
          · have hi_eq : i = bitrev logN t := by rw [← hbt, hrri]
            have hilt : i < t := by omega
            rw [if_pos (Or.inl hilt), if_pos (Or.inl (by omega))]
          · have hcnd : (i < t + 1 ∨ bitrev logN i < t + 1) ↔
                (i < t ∨ bitrev logN i < t) := by omega
            rw [if_congr hcnd rfl rfl]

/-! ## The round invariant: written cells hold their gathered value

The disjointness argument, with the butterfly scalar action `tw.val • ·` of the transparent
`bestFftG`. -/

private def Written (half c jc i : ℕ) : Prop :=
  ∃ c' j', j' < half ∧ (c' < c ∨ (c' = c ∧ j' < jc)) ∧
    (i = c' * (2 * half) + j' ∨ i = c' * (2 * half) + half + j')

private theorem not_written_a {half c jc : ℕ} (hjc : jc < half) :
    ¬ Written half c jc (c * (2 * half) + jc) := by
  rintro ⟨c', j', hj', horder, heq | heq⟩
  · obtain ⟨rfl, rfl⟩ := tile_inj (by omega) (by omega) heq.symm
    rcases horder with h | ⟨-, h⟩ <;> omega
  · rw [show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega] at heq
    obtain ⟨-, h⟩ := tile_inj (by omega) (by omega) heq.symm
    omega

private theorem not_written_b {half c jc : ℕ} (hjc : jc < half) :
    ¬ Written half c jc (c * (2 * half) + half + jc) := by
  rintro ⟨c', j', hj', horder, heq | heq⟩
  · rw [show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega] at heq
    obtain ⟨-, h⟩ := tile_inj (by omega) (by omega) heq.symm
    omega
  · rw [show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega,
      show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega] at heq
    obtain ⟨rfl, h⟩ := tile_inj (by omega) (by omega) heq.symm
    rcases horder with h2 | ⟨-, h2⟩ <;> omega

private theorem written_succ {half c jc i : ℕ} (hjc : jc < half) :
    Written half c (jc + 1) i ↔
      Written half c jc i ∨ i = c * (2 * half) + jc ∨ i = c * (2 * half) + half + jc := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    rcases horder with hlt | ⟨rfl, hj⟩
    · exact Or.inl ⟨c', j', hj', Or.inl hlt, heq⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Or.inl ⟨c', j', hj', Or.inr ⟨rfl, hj⟩, heq⟩
      · rcases heq with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  · rintro (⟨c', j', hj', horder, heq⟩ | rfl | rfl)
    · refine ⟨c', j', hj', ?_, heq⟩
      rcases horder with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Nat.lt_succ_of_lt h⟩
    · exact ⟨c, jc, hjc, Or.inr ⟨rfl, Nat.lt_succ_self _⟩, Or.inl rfl⟩
    · exact ⟨c, jc, hjc, Or.inr ⟨rfl, Nat.lt_succ_self _⟩, Or.inr rfl⟩

private theorem written_roll {half c i : ℕ} :
    Written half c half i ↔ Written half (c + 1) 0 i := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    refine ⟨c', j', hj', Or.inl ?_, heq⟩
    rcases horder with h | ⟨rfl, h⟩ <;> omega
  · rintro ⟨c', j', hj', horder, heq⟩
    refine ⟨c', j', hj', ?_, heq⟩
    rcases horder with h | ⟨-, h⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, hj'⟩
    · omega

private theorem written_final {n half i : ℕ} :
    Written half (n / (2 * half)) 0 i ↔ i / (2 * half) < n / (2 * half) ∧ 0 < half := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    have hc' : c' < n / (2 * half) := by rcases horder with h | ⟨-, h⟩ <;> omega
    refine ⟨?_, by omega⟩
    rcases heq with rfl | rfl
    · rw [tile_div (by omega)]; exact hc'
    · rw [show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega,
        tile_div (by omega)]
      exact hc'
  · rintro ⟨hdiv, hhalf⟩
    have hmod : i % (2 * half) < 2 * half := Nat.mod_lt _ (by omega)
    have hi : i = i / (2 * half) * (2 * half) + i % (2 * half) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod i (2 * half)).symm
    by_cases hlt : i % (2 * half) < half
    · exact ⟨i / (2 * half), i % (2 * half), hlt, Or.inl hdiv, Or.inl hi⟩
    · exact ⟨i / (2 * half), i % (2 * half) - half, by omega, Or.inl hdiv, Or.inr (by omega)⟩

/-- The final value of a written index, gathered from the pre-round array: the `+`-leg for the
first half of its chunk, the `−`-leg for the second. -/
private def gOutG (n half : ℕ) (tw : Array Fp) (a : Array G) (i : ℕ) : G :=
  if i % (2 * half) < half then
    a[i]! + twiddledPointG n half tw a (i / (2 * half)) (i % (2 * half))
  else
    a[i - half]! - twiddledPointG n half tw a (i / (2 * half)) (i % (2 * half) - half)

private theorem gOutG_a {n half : ℕ} {tw : Array Fp} {a : Array G} {c jc : ℕ}
    (hjc : jc < half) :
    gOutG n half tw a (c * (2 * half) + jc) =
      a[c * (2 * half) + jc]! + twiddledPointG n half tw a c jc := by
  rw [gOutG, tile_mod (by omega), tile_div (by omega), if_pos hjc]

private theorem gOutG_b {n half : ℕ} {tw : Array Fp} {a : Array G} {c jc : ℕ}
    (hjc : jc < half) :
    gOutG n half tw a (c * (2 * half) + half + jc) =
      a[c * (2 * half) + jc]! - twiddledPointG n half tw a c jc := by
  rw [gOutG, show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega,
    tile_mod (by omega), tile_div (by omega), if_neg (by omega),
    show c * (2 * half) + (half + jc) - half = c * (2 * half) + jc from by omega,
    show half + jc - half = jc from by omega]

private theorem getElem!_butterflyG {n half : ℕ} {tw : Array Fp} {c j : ℕ}
    (r : Array G) (i : ℕ) :
    (butterflyG n half tw c j r)[i]! =
      if c * (2 * half) + half + j = i ∧ c * (2 * half) + half + j < r.size then
        r[c * (2 * half) + j]! - twiddledPointG n half tw r c j
      else if c * (2 * half) + j = i ∧ c * (2 * half) + j < r.size then
        r[c * (2 * half) + j]! + twiddledPointG n half tw r c j
      else r[i]! := by
  rw [butterflyG, getElem!_set', getElem!_set']
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private structure InvG (n half : ℕ) (tw : Array Fp) (a : Array G) (c jc : ℕ)
    (r : Array G) : Prop where
  size_eq : r.size = a.size
  written : ∀ i, i < a.size → Written half c jc i → r[i]! = gOutG n half tw a i
  fresh : ∀ i, ¬ Written half c jc i → r[i]! = a[i]!

private theorem invG_step {n half : ℕ} {tw : Array Fp} {a : Array G} {c jc : ℕ}
    {r : Array G} (hjc : jc < half) (h : InvG n half tw a c jc r) :
    InvG n half tw a c (jc + 1) (butterflyG n half tw c jc r) := by
  have hra : r[c * (2 * half) + jc]! = a[c * (2 * half) + jc]! :=
    h.fresh _ (not_written_a hjc)
  have hrb : r[c * (2 * half) + half + jc]! = a[c * (2 * half) + half + jc]! :=
    h.fresh _ (not_written_b hjc)
  have htP : twiddledPointG n half tw r c jc = twiddledPointG n half tw a c jc := by
    rw [twiddledPointG, twiddledPointG, hrb]
  have hsize : (butterflyG n half tw c jc r).size = a.size := by
    rw [butterflyG]; simpa using h.size_eq
  refine ⟨hsize, ?_, ?_⟩
  · intro i hi hw
    rcases (written_succ hjc).mp hw with hw' | rfl | rfl
    · have hia : c * (2 * half) + jc ≠ i := fun he =>
        not_written_a hjc (by rw [he]; exact hw')
      have hib : c * (2 * half) + half + jc ≠ i := fun he =>
        not_written_b hjc (by rw [he]; exact hw')
      rw [getElem!_butterflyG, if_neg (fun hc => hib hc.1), if_neg (fun hc => hia hc.1)]
      exact h.written i hi hw'
    · rw [getElem!_butterflyG, if_neg (fun hc => absurd hc.1 (by omega)),
        if_pos ⟨rfl, by rw [h.size_eq]; exact hi⟩, hra, htP, gOutG_a hjc]
    · rw [getElem!_butterflyG, if_pos ⟨rfl, by rw [h.size_eq]; exact hi⟩, hra, htP,
        gOutG_b hjc]
  · intro i hnw
    have hia : c * (2 * half) + jc ≠ i := fun he =>
      hnw ((written_succ hjc).mpr (Or.inr (Or.inl he.symm)))
    have hib : c * (2 * half) + half + jc ≠ i := fun he =>
      hnw ((written_succ hjc).mpr (Or.inr (Or.inr he.symm)))
    rw [getElem!_butterflyG, if_neg (fun hc => hib hc.1), if_neg (fun hc => hia hc.1)]
    exact h.fresh i fun hw => hnw ((written_succ hjc).mpr (Or.inl hw))

private theorem invG_inner {n half : ℕ} {tw : Array Fp} {a : Array G} {c : ℕ} :
    ∀ (k jc : ℕ) (r : Array G), jc + k ≤ half → InvG n half tw a c jc r →
      InvG n half tw a c (jc + k)
        ((List.range' jc k).foldl (fun b j => butterflyG n half tw c j b) r)
  | 0, jc, r, _, h => by simpa using h
  | k + 1, jc, r, hk, h => by
    rw [List.range'_succ]
    simp only [List.foldl_cons]
    have h2 := invG_inner k (jc + 1) (butterflyG n half tw c jc r) (by omega)
      (invG_step (by omega) h)
    rw [show jc + (k + 1) = jc + 1 + k from by omega]
    exact h2

private theorem invG_chunk {n half : ℕ} {tw : Array Fp} {a : Array G} {c : ℕ}
    {r : Array G} (h : InvG n half tw a c 0 r) :
    InvG n half tw a (c + 1) 0
      ((List.range half).foldl (fun b j => butterflyG n half tw c j b) r) := by
  have h1 := invG_inner (c := c) half 0 r (by omega) h
  rw [List.range_eq_range' (n := half)]
  have h2 : InvG n half tw a c half ((List.range' 0 half).foldl
      (fun b j => butterflyG n half tw c j b) r) := by simpa using h1
  exact ⟨h2.size_eq,
    fun i hi hw => h2.written i hi (written_roll.mpr hw),
    fun i hnw => h2.fresh i fun hw => hnw (written_roll.mp hw)⟩

private theorem invG_outer {n half : ℕ} {tw : Array Fp} {a : Array G} :
    ∀ (k c : ℕ) (r : Array G), InvG n half tw a c 0 r →
      InvG n half tw a (c + k) 0
        ((List.range' c k).foldl
          (fun b c' => (List.range half).foldl (fun b' j => butterflyG n half tw c' j b') b) r)
  | 0, c, r, h => by simpa using h
  | k + 1, c, r, h => by
    rw [List.range'_succ]
    simp only [List.foldl_cons]
    have h3 := invG_outer k (c + 1) _ (invG_chunk h)
    rw [show c + (k + 1) = c + 1 + k from by omega]
    exact h3

private theorem invG_init (n half : ℕ) (tw : Array Fp) (a : Array G) :
    InvG n half tw a 0 0 a :=
  ⟨rfl,
   fun _ _ hw => by
     rcases hw with ⟨c', j', -, horder, -⟩
     rcases horder with h | ⟨-, h⟩ <;> omega,
   fun _ _ => rfl⟩

/-- The full characterization of a butterfly round: sizes agree, and every written cell holds
its gathered value. -/
private theorem roundFold_inv (n half : ℕ) (tw : Array Fp) (a : Array G) :
    InvG n half tw a (n / (2 * half)) 0 (roundFold n half tw a) := by
  rw [roundFold, List.range_eq_range' (n := n / (2 * half))]
  have h := invG_outer (n / (2 * half)) 0 a (invG_init n half tw a)
  simpa using h

/-! ## The Cooley–Tukey identity -/

/-- The `ZMod.val`-smul the algorithm computes is the `Fp`-module action. -/
private theorem val_smul {G : Type} [AddCommGroup G] [Module Fp G] (c : Fp) (x : G) :
    c.val • x = c • x := by
  rw [← Nat.cast_smul_eq_nsmul Fp c.val x, ZMod.natCast_rightInverse c]

private theorem sum_range_even_odd {M : Type} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ t ∈ Finset.range (2 * m), f t =
      (∑ u ∈ Finset.range m, f (2 * u)) + ∑ u ∈ Finset.range m, f (2 * u + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (n := m), Finset.sum_range_succ (n := m)]
    abel

/-- Half the full order lands on `−1` (the butterfly minus sign). -/
private theorem pow_half_eq_neg_one {omega : Fp} {logN : ℕ}
    (homega : IsPrimitiveRoot omega (2 ^ logN)) (hl : 1 ≤ logN) :
    omega ^ 2 ^ (logN - 1) = -1 := by
  have hsq : omega ^ 2 ^ (logN - 1) * omega ^ 2 ^ (logN - 1) = 1 := by
    rw [← pow_add]
    have h2 : 2 ^ (logN - 1) + 2 ^ (logN - 1) = 2 ^ logN := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    rw [h2, homega.pow_eq_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h (homega.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos _).ne'
      (Nat.pow_lt_pow_right (by omega) (by omega)))
  · exact h

/-- Only `J mod 2^r` matters in an FFT exponent at stride `2^(logN−r)`. -/
private theorem pow_exp_reduce {omega : Fp} {logN : ℕ}
    (homega : IsPrimitiveRoot omega (2 ^ logN)) {r : ℕ} (hr : r ≤ logN) (J u : ℕ) :
    omega ^ (2 ^ (logN - r) * J * u) = omega ^ (2 ^ (logN - r) * (J % 2 ^ r) * u) := by
  have hp : (2 : ℕ) ^ (logN - r) * 2 ^ r = 2 ^ logN := by
    rw [← pow_add]
    congr 1
    omega
  conv_lhs => rw [show J = 2 ^ r * (J / 2 ^ r) + J % 2 ^ r from
    (Nat.div_add_mod J (2 ^ r)).symm]
  have he : 2 ^ (logN - r) * (2 ^ r * (J / 2 ^ r) + J % 2 ^ r) * u =
      2 ^ logN * (J / 2 ^ r * u) + 2 ^ (logN - r) * (J % 2 ^ r) * u := by
    rw [← hp]
    ring
  rw [he, pow_add, pow_mul, homega.pow_eq_one, one_pow, one_mul]

/-- The second-half twiddle factor is the negated first-half one. -/
private theorem twiddle_neg {omega : Fp} {logN : ℕ}
    (homega : IsPrimitiveRoot omega (2 ^ logN)) {r : ℕ} (hr : r + 1 ≤ logN) (j : ℕ) :
    omega ^ (2 ^ (logN - (r + 1)) * (2 ^ r + j)) = -omega ^ (2 ^ (logN - (r + 1)) * j) := by
  have hp : (2 : ℕ) ^ (logN - (r + 1)) * 2 ^ r = 2 ^ (logN - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [Nat.mul_add, pow_add, hp, pow_half_eq_neg_one homega (by omega), neg_one_mul]

/-- **The Cooley–Tukey butterfly identity**: a size-`2^(r+1)` bit-reversed DFT sum splits into
the two size-`2^r` half sums combined through the twiddle factor. -/
private theorem ct_step {G : Type} [AddCommGroup G] [Module Fp G]
    {omega : Fp} {logN r : ℕ} (hr : r + 1 ≤ logN)
    (homega : IsPrimitiveRoot omega (2 ^ logN)) (g : ℕ → G) (J : ℕ) :
    ∑ t ∈ Finset.range (2 ^ (r + 1)),
        (omega ^ (2 ^ (logN - (r + 1)) * J * t)) • g (bitrev (r + 1) t) =
      (∑ u ∈ Finset.range (2 ^ r),
        (omega ^ (2 ^ (logN - r) * (J % 2 ^ r) * u)) • g (bitrev r u)) +
      (omega ^ (2 ^ (logN - (r + 1)) * J)) •
        ∑ u ∈ Finset.range (2 ^ r),
          (omega ^ (2 ^ (logN - r) * (J % 2 ^ r) * u)) • g (2 ^ r + bitrev r u) := by
  have hpow2 : (2 : ℕ) ^ (logN - (r + 1)) * 2 = 2 ^ (logN - r) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [pow_succ' 2 r, sum_range_even_odd, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [bitrev_two_mul]
    have he : 2 ^ (logN - (r + 1)) * J * (2 * u) = 2 ^ (logN - r) * J * u := by
      rw [← hpow2]
      ring
    rw [he, pow_exp_reduce homega (by omega) J u]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [bitrev_two_mul_add_one, smul_smul, ← pow_add]
    have ho : 2 ^ (logN - (r + 1)) * J * (2 * u + 1) =
        2 ^ (logN - (r + 1)) * J + 2 ^ (logN - r) * J * u := by
      rw [← hpow2]
      ring
    rw [ho]
    congr 1
    rw [pow_add, pow_add, pow_exp_reduce homega (by omega) J u]

/-! ## The round induction: after round `r`, every `2^r`-block is a DFT -/

/-- The DIT invariant: after the first `r` butterfly rounds on the bit-reversal-permuted input
`b`, cell `i` holds the size-`2^r` bit-reversed DFT of `b`'s block `i / 2^r`, evaluated at
in-block frequency `i mod 2^r`. -/
private theorem rounds_dft {G : Type} [AddCommGroup G] [Inhabited G] [Module Fp G]
    (b : Array G) (omega : Fp) (logN : ℕ)
    (hsize : b.size = 2 ^ logN) (homega : IsPrimitiveRoot omega (2 ^ logN))
    (tw : Array Fp) (htw : ∀ x, x < 2 ^ logN / 2 → tw[x]! = omega ^ x) :
    ∀ r, r ≤ logN →
      ((List.range r).foldl (fun a s => roundFold (2 ^ logN) (2 ^ s) tw a) b).size =
        2 ^ logN ∧
      ∀ i, i < 2 ^ logN →
        ((List.range r).foldl (fun a s => roundFold (2 ^ logN) (2 ^ s) tw a) b)[i]! =
          ∑ t ∈ Finset.range (2 ^ r),
            (omega ^ (2 ^ (logN - r) * (i % 2 ^ r) * t)) •
              b[i / 2 ^ r * 2 ^ r + bitrev r t]! := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨by simpa using hsize, fun i hi => ?_⟩
    simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.sub_zero, Nat.mod_one,
      Nat.div_one, mul_one, mul_zero, zero_mul, Finset.sum_range_one, bitrev_zero,
      add_zero, one_smul]
  | succ r ih =>
    intro hr1
    obtain ⟨ihs, ihv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set A := (List.range r).foldl (fun a s => roundFold (2 ^ logN) (2 ^ s) tw a) b with hA
    clear_value A
    have hinv := roundFold_inv (2 ^ logN) (2 ^ r) tw A
    have hchunk : (2 : ℕ) * 2 ^ r = 2 ^ (r + 1) := (pow_succ' 2 r).symm
    have hdvd : (2 : ℕ) ^ (r + 1) ∣ 2 ^ logN := pow_dvd_pow 2 hr1
    have hquot : 2 ^ logN / (2 * 2 ^ r) = 2 ^ (logN - (r + 1)) := by
      rw [hchunk, Nat.pow_div hr1 (by omega)]
    have hhalfN : (2 : ℕ) ^ logN / 2 = 2 ^ (logN - 1) := by
      conv_lhs => rw [show (2 : ℕ) ^ logN = 2 ^ (logN - 1) * 2 from by
        rw [← pow_succ]; congr 1; omega]
      rw [Nat.mul_div_cancel _ (by omega)]
    have htwv : ∀ j, j < 2 ^ r →
        tw[j * (2 ^ logN / (2 * 2 ^ r))]! = omega ^ (2 ^ (logN - (r + 1)) * j) := by
      intro j hj
      rw [hquot, htw _ (by
        calc j * 2 ^ (logN - (r + 1)) < 2 ^ r * 2 ^ (logN - (r + 1)) :=
              mul_lt_mul_of_pos_right hj (Nat.two_pow_pos _)
          _ = 2 ^ (logN - 1) := by rw [← pow_add]; congr 1; omega
          _ = 2 ^ logN / 2 := hhalfN.symm), Nat.mul_comm]
    constructor
    · rw [hinv.size_eq, ihs]
    · intro i hi
      have hc : i / (2 * 2 ^ r) < 2 ^ logN / (2 * 2 ^ r) := by
        rw [hchunk]
        exact Nat.div_lt_div_of_lt_of_dvd hdvd hi
      have hval := hinv.written i (by rw [ihs]; exact hi)
        (written_final.mpr ⟨hc, Nat.two_pow_pos r⟩)
      rw [hval]
      set c := i / (2 * 2 ^ r) with hcdef
      set J := i % (2 * 2 ^ r) with hJdef
      have hJlt : J < 2 * 2 ^ r := by
        rw [hJdef]
        exact Nat.mod_lt _ (by positivity)
      have hidec : i = c * (2 * 2 ^ r) + J := by
        rw [hcdef, hJdef, Nat.mul_comm]
        exact (Nat.div_add_mod i (2 * 2 ^ r)).symm
      have hiq : i / 2 ^ (r + 1) = c := by rw [hcdef, hchunk]
      have him : i % 2 ^ (r + 1) = J := by rw [hJdef, hchunk]
      rw [hiq, him, ct_step hr1 homega (fun x => b[c * 2 ^ (r + 1) + x]!) J, gOutG]
      have hE : c * (2 * 2 ^ r) = 2 * c * 2 ^ r := by ring
      by_cases hJr : J < 2 ^ r
      · rw [if_pos hJr, twiddledPointG, htwv J hJr, val_smul]
        have hi2 : i = 2 * c * 2 ^ r + J := by rw [hidec]; ring
        have him2 : i % 2 ^ r = J := by conv_lhs => rw [hi2, tile_mod hJr]
        have hid2 : i / 2 ^ r = 2 * c := by conv_lhs => rw [hi2, tile_div hJr]
        have hx2eq : c * (2 * 2 ^ r) + 2 ^ r + J = (2 * c + 1) * 2 ^ r + J := by ring
        have hx2lt : (2 * c + 1) * 2 ^ r + J < 2 ^ logN := by
          calc (2 * c + 1) * 2 ^ r + J < (2 * c + 1) * 2 ^ r + 2 ^ r := by omega
            _ = (c + 1) * (2 * 2 ^ r) := by ring
            _ ≤ 2 ^ logN / (2 * 2 ^ r) * (2 * 2 ^ r) :=
                Nat.mul_le_mul_right _ (by omega)
            _ = 2 ^ logN := by rw [hchunk]; exact Nat.div_mul_cancel hdvd
        rw [ihv i hi, him2, hid2, hx2eq, ihv _ hx2lt, tile_mod hJr, tile_div hJr,
          Nat.mod_eq_of_lt hJr]
        congr 1
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [show 2 * c * 2 ^ r = c * 2 ^ (r + 1) from by rw [← hchunk]; ring]
        · refine congrArg₂ (· • ·) rfl ?_
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [show (2 * c + 1) * 2 ^ r + bitrev r t =
            c * 2 ^ (r + 1) + (2 ^ r + bitrev r t) from by rw [← hchunk]; ring]
      · rw [if_neg hJr]
        obtain ⟨j, hj, hJeq⟩ : ∃ j, j < 2 ^ r ∧ J = 2 ^ r + j :=
          ⟨J - 2 ^ r, by omega, by omega⟩
        rw [show J - 2 ^ r = j from by omega, twiddledPointG, htwv j hj, val_smul]
        have hi3 : i - 2 ^ r = 2 * c * 2 ^ r + j := by omega
        have hxeq : c * (2 * 2 ^ r) + 2 ^ r + j = (2 * c + 1) * 2 ^ r + j := by ring
        have hA3 : (2 * c + 1) * 2 ^ r = 2 * c * 2 ^ r + 2 ^ r := by ring
        have hxi : (2 * c + 1) * 2 ^ r + j = i := by omega
        rw [hi3, ihv _ (by omega), tile_mod hj, tile_div hj,
          hxeq, ihv _ (by omega), tile_mod hj, tile_div hj]
        rw [hJeq, Nat.add_mod_left, Nat.mod_eq_of_lt hj, twiddle_neg homega hr1 j,
          neg_smul, sub_eq_add_neg]
        congr 1
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [show 2 * c * 2 ^ r = c * 2 ^ (r + 1) from by rw [← hchunk]; ring]
        · congr 1
          refine congrArg₂ (· • ·) rfl ?_
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [show (2 * c + 1) * 2 ^ r + bitrev r t =
            c * 2 ^ (r + 1) + (2 ^ r + bitrev r t) from by rw [← hchunk]; ring]

/-! ## The main theorem -/

/-- **`bestFftG` computes the group DFT**: on an input of size `2^logN`, with a primitive
`2^logN`-th root of unity `ω` and `G` an `Fp`-module, every output cell is the DFT sum
`∑ₖ ω^(i·k) • a0[k]`. -/
theorem bestFftG_dft {G : Type} [AddCommGroup G] [Inhabited G] [Module Fp G]
    (a0 : Array G) (omega : Fp) (logN : ℕ)
    (hsize : a0.size = 2 ^ logN)
    (homega : IsPrimitiveRoot omega (2 ^ logN))
    (i : Fin (2 ^ logN)) :
    (bestFftG a0 omega logN)[(i : ℕ)]! =
      ∑ k : Fin (2 ^ logN), (omega ^ ((i : ℕ) * (k : ℕ))) • a0[(k : ℕ)]! := by
  -- the bit-reversal-permuted input
  obtain ⟨hbs, hbv⟩ := brFold_inv a0 logN hsize a0.size le_rfl
  set b := (List.range a0.size).foldl (fun a k =>
      if k < bitrev logN k then
        (a.set! k a[bitrev logN k]!).set! (bitrev logN k) a[k]!
      else a) a0 with hb
  have hbrPerm : brPermImp a0 logN = b := by
    rw [brPermImp_eq_foldl, hb]
    simp only [bitreverse_eq_bitrev]
  have hbsize : b.size = 2 ^ logN := by rw [hbs, hsize]
  have hbval : ∀ x, x < 2 ^ logN → b[x]! = a0[bitrev logN x]! := by
    intro x hx
    rw [hbv x (by omega), if_pos (Or.inl (by omega))]
  -- the twiddle table
  have htwv : ∀ x, x < 2 ^ logN / 2 →
      (twImp omega (a0.size / 2))[x]! = omega ^ x := by
    intro x hx
    rw [twImp_eq_foldl, twFold_eq, hsize]
    have hx' : x < ((List.range (2 ^ logN / 2)).map (omega ^ ·)).length := by
      simpa using hx
    rw [getElem!_pos _ _ (by simpa using hx')]
    simp
  -- the DFT invariant at the final round
  rw [hsize] at htwv
  obtain ⟨-, hval⟩ := rounds_dft b omega logN hbsize homega
    (twImp omega (2 ^ logN / 2)) htwv logN le_rfl
  rw [bestFftG_decompose, roundsImp_eq_rounds, hsize, hbrPerm, hval (i : ℕ) i.isLt]
  rw [Fin.sum_univ_eq_sum_range fun k => (omega ^ ((i : ℕ) * k)) • a0[k]!]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htlt : t < 2 ^ logN := Finset.mem_range.mp ht
  rw [Nat.sub_self, pow_zero, one_mul, Nat.mod_eq_of_lt i.isLt,
    Nat.div_eq_of_lt i.isLt, Nat.zero_mul, Nat.zero_add,
    hbval (bitrev logN t) (bitrev_lt logN t), bitrev_bitrev logN t htlt]

/-! ## Wiring corollaries: the derived Lagrange URS -/

omit [AddCommGroup G] [Inhabited G] in
private theorem foldl_size_preserved {α : Type} (l : List α) (f : Array G → α → Array G)
    (hf : ∀ a x, (f a x).size = a.size) : ∀ a0 : Array G, (l.foldl f a0).size = a0.size := by
  induction l with
  | nil => intro a0; rfl
  | cons x xs ih =>
    intro a0
    rw [List.foldl_cons, ih, hf]

/-- `bestFftG` preserves the array size (unconditionally). -/
theorem bestFftG_size (a0 : Array G) (omega : Fp) (logN : ℕ) :
    (bestFftG a0 omega logN).size = a0.size := by
  rw [bestFftG_decompose, roundsImp_eq_rounds, brPermImp_eq_foldl]
  rw [foldl_size_preserved _ _ (fun a r => (roundFold_inv a0.size (2 ^ r) _ a).size_eq)]
  refine foldl_size_preserved _ _ (fun a k => ?_) a0
  split
  · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  · rfl

/-- The derived Lagrange basis has full domain length. -/
theorem derivedUrsGLagrange_length (urs : URS G) :
    (derivedUrsGLagrange urs).length = 2 ^ urs.k := by
  rw [derivedUrsGLagrange]
  simp [bestFftG_size]

/-- `omegaInvOf k` is the inverse of the domain root (`ω⁻¹ = ω^(2^k − 1)`). -/
theorem omegaInvOf_eq_inv (k : ℕ) (hk : k ≤ 32) : omegaInvOf k = (omegaOf k)⁻¹ := by
  rw [omegaInvOf, powFast_eq_pow]
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← pow_succ', show 2 ^ k - 1 + 1 = 2 ^ k from by
    have := Nat.two_pow_pos k; omega]
  exact (omegaOf_isPrimitiveRoot k hk).pow_eq_one

/-- `omegaInvOf k` is itself a primitive `2^k`-th root of unity. -/
theorem omegaInvOf_isPrimitiveRoot (k : ℕ) (hk : k ≤ 32) :
    IsPrimitiveRoot (omegaInvOf k) (2 ^ k) := by
  rw [omegaInvOf_eq_inv k hk]
  exact (omegaOf_isPrimitiveRoot k hk).inv

end Zcash.Arithmetic
