import Zcash.Snark.Verifier.Assemble

/-!
# Canonical commitment references for assembled queries

In the verifier-generated query list, every occurrence of one `CommitmentId` carries the same
commitment reference.  This invariant lets soundness proofs recover the exact pre-challenge
commitment behind a routed member.
-/

namespace Zcash.Snark

open Classical

/-- The commitment reference canonically named by a verifier slot.  All branches except
`vanishingH` are independent of `ch.x`; the vanishing branch is the explicitly reassembled
quotient commitment and is handled separately by the pre-`x` quotient connector. -/
def assembledCommitment {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    CommitmentId -> CommitmentRef shape.k F G
  | .instanceCol p i =>
      if hp : p < shape.numProofs then .point (instanceCommitment ⟨p, hp⟩ i) else .point default
  | .adviceCol p i =>
      if hp : p < shape.numProofs then .point (finFnG (ps.adviceCommitments ⟨p, hp⟩) i)
      else .point default
  | .fixedCol i => .point (vk.fixedCommitment i)
  | .permProduct p s =>
      if hp : p < shape.numProofs then .point (finFnG (ps.permutationProduct ⟨p, hp⟩) s)
      else .point default
  | .lookupProduct p l =>
      if hp : p < shape.numProofs then .point (finFnG (ps.lookupProduct ⟨p, hp⟩) l)
      else .point default
  | .lookupPermInput p l =>
      if hp : p < shape.numProofs then .point (finFnG (ps.lookupPermutedInput ⟨p, hp⟩) l)
      else .point default
  | .lookupPermTable p l =>
      if hp : p < shape.numProofs then .point (finFnG (ps.lookupPermutedTable ⟨p, hp⟩) l)
      else .point default
  | .permCommon c => .point (finFnG vk.permutationCommonCommitment c)
  | .vanishingH => .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))
  | .randomPoly => .point ps.vanishingRandom

private theorem columnQueries_commitment_eq_assembled_instance {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ columnQueries vk.omega ch.x (instanceCommitment p)
      (CommitmentId.instanceCol p) vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p))) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [columnQueries] at hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  simp only [assembledCommitment, p.isLt, ↓reduceDIte]

private theorem columnQueries_commitment_eq_assembled_advice {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ columnQueries vk.omega ch.x (finFnG (ps.adviceCommitments p))
      (CommitmentId.adviceCol p) vk.adviceQueryLayout (List.ofFn (ps.adviceEvals p))) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [columnQueries] at hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  simp only [assembledCommitment, p.isLt, ↓reduceDIte]

private theorem columnQueries_commitment_eq_assembled_fixed {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) {q : VerifierQuery shape.k F G}
    (hq : q ∈ columnQueries vk.omega ch.x vk.fixedCommitment CommitmentId.fixedCol
      vk.fixedQueryLayout (List.ofFn ps.fixedEvals)) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [columnQueries] at hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  rfl

private theorem permutationQueries_commitment_eq_assembled {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ permutationQueries ch.x (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : Int) + 1)))
      (CommitmentId.permProduct p)
      (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [permutationQueries] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    have hj' : j < shape.numPermutationSets := by
      simpa [List.length_zip, List.length_ofFn] using hj
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
        List.getElem_range]
    · rcases List.mem_cons.mp hq with rfl | hq
      · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
          List.getElem_range]
      · exact absurd hq List.not_mem_nil
  · obtain ⟨e, he, hq⟩ := List.mem_filterMap.mp hq
    have he' : e ∈ (List.ofFn (fun s =>
        (ps.permutationProduct p s, ps.permutationSetEvals p s))).zip
          (List.range (List.ofFn (fun s =>
            (ps.permutationProduct p s, ps.permutationSetEvals p s))).length) := by
      exact List.mem_reverse.mp (List.mem_of_mem_drop he)
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp he'
    subst e
    have hj' : j < shape.numPermutationSets := by
      simpa [List.length_zip, List.length_ofFn] using hj
    obtain ⟨le, -, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
      List.getElem_range]

private theorem lookupQueries_commitment_eq_assembled {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ lookupQueries ch.x (rotateOmega vk.omega ch.x (-1))
      (rotateOmega vk.omega ch.x 1) (CommitmentId.lookupProduct p)
      (CommitmentId.lookupPermInput p) (CommitmentId.lookupPermTable p)
      (List.ofFn (fun l =>
        ({ product := ps.lookupProduct p l, permutedInput := ps.lookupPermutedInput p l,
           permutedTable := ps.lookupPermutedTable p l }, ps.lookupEvals p l)))) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [lookupQueries] at hq
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
  have hj' : j < shape.numLookups := by
    simpa [List.length_zip, List.length_ofFn] using hj
  rcases List.mem_cons.mp hq with rfl | hq
  · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
      List.getElem_range]
  · rcases List.mem_cons.mp hq with rfl | hq
    · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
        List.getElem_range]
    · rcases List.mem_cons.mp hq with rfl | hq
      · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
          List.getElem_range]
      · rcases List.mem_cons.mp hq with rfl | hq
        · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
            List.getElem_range]
        · rcases List.mem_cons.mp hq with rfl | hq
          · simp [assembledCommitment, p.isLt, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
              List.getElem_range]
          · exact absurd hq List.not_mem_nil

private theorem permutationCommonQueries_commitment_eq_assembled {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) {q : VerifierQuery shape.k F G}
    (hq : q ∈ permutationCommonQueries ch.x CommitmentId.permCommon
      (List.ofFn (fun c => (vk.permutationCommonCommitment c,
        ps.permutationCommonEvals c)))) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  rw [permutationCommonQueries] at hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
  have hj' : j < shape.numPermutationColumns := by
    simpa [List.length_zip, List.length_ofFn] using hj
  simp [assembledCommitment, finFnG, hj', List.getElem_zip, List.getElem_ofFn,
    List.getElem_range]

/-- Every query emitted by `assembleQueries` carries the canonical commitment reference named by
its structural slot identity. -/
theorem assembleQueries_commitment_eq_assembled {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) {q : VerifierQuery shape.k F G}
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch) :
    q.commitment = assembledCommitment vk instanceCommitment ps ch q.commId := by
  simp only [assembleQueries] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qs, hqs, hq⟩ := List.mem_flatten.mp hq
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hqs
        rcases List.mem_append.mp hq with hq | hq
        · rcases List.mem_append.mp hq with hq | hq
          · rcases List.mem_append.mp hq with hq | hq
            · exact columnQueries_commitment_eq_assembled_instance vk instanceCommitment ps ch p hq
            · exact columnQueries_commitment_eq_assembled_advice vk instanceCommitment ps ch p hq
          · exact permutationQueries_commitment_eq_assembled vk instanceCommitment ps ch p hq
        · exact lookupQueries_commitment_eq_assembled vk instanceCommitment ps ch p hq
      · exact columnQueries_commitment_eq_assembled_fixed vk instanceCommitment ps ch hq
    · exact permutationCommonQueries_commitment_eq_assembled vk instanceCommitment ps ch hq
  · simp only [vanishingQueries] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact absurd hq List.not_mem_nil

/-- Two verifier-generated queries carrying the same slot identity carry the same commitment
reference. -/
theorem assembleQueries_commitment_eq_of_commId {shape : Shape} {F G : Type*}
    [Field F] [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) {q q' : VerifierQuery shape.k F G}
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch) (hq' : q' ∈ assembleQueries vk instanceCommitment ps ch)
    (hid : q'.commId = q.commId) : q'.commitment = q.commitment := by
  rw [assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq', hid,
    <- assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq]

end Zcash.Snark
