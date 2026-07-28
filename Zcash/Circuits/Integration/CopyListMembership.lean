import Zcash.Circuits.Integration.PermutationReplay

/-!
# Declared copies resolve into the keygen copy list

The copy-replay witness needs, per declared Clean copy, a value-agreement fact; for the
cell/cell and cell/instance kinds that fact transports through the keygen permutation,
whose copy list is the floor planner's. This module proves the membership half: every
non-constant declared copy, resolved to absolute permutation-column coordinates, is a
member of the V1 copy list. (Constant copies consume the positional constants
allocation; their membership couples to the allocation walk and lives with the
constants instantiation.)
-/

namespace Zcash.Snark

open Halo2
open Halo2.Layout

/-- Resolve a non-constant declared copy to the keygen copy tuple: region cells through
the placement, instance endpoints at their absolute rows. Constant endpoints resolve to
`none` — their cells are the planner's positional constants allocation. -/
def resolveDeclared (permCols : List ColRef) (starts : List ℕ) :
    CopyEndpoint Fp × CopyEndpoint Fp → Option (ℕ × ℕ × ℕ × ℕ)
  | (.cell l, .cell r) =>
      some ((resolveCell permCols starts l).1, (resolveCell permCols starts l).2,
        (resolveCell permCols starts r).1, (resolveCell permCols starts r).2)
  | (.cell c, .instance col row) =>
      some ((resolveCell permCols starts c).1, (resolveCell permCols starts c).2,
        permIndex permCols col.toAny, row)
  | _ => none

/-- The declared-copy extraction is a `filterMap`. -/
theorem regionDeclaredCopies_eq_filterMap (body : RegionOperations Fp) :
    regionDeclaredCopies body = body.filterMap regionOperationDeclaredCopy? := by
  induction body with
  | nil => rfl
  | cons op rest ih =>
      rw [regionDeclaredCopies, List.filterMap_cons]
      cases hop : regionOperationDeclaredCopy? (F := Fp) op with
      | none => simpa [hop] using ih
      | some copy => simpa [hop] using ih

/-- A resolvable declared copy of a region body is among the region's extracted
equality/instance copies. -/
theorem mem_regionCopiesSplit_fst_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ regionDeclaredCopies body) :
    tuple ∈ (regionCopiesSplit permCols starts body consts).1 := by
  rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hmem
  obtain ⟨op, hop, hcopy⟩ := hmem
  simp only [regionCopiesSplit]
  rw [List.mem_filterMap]
  refine ⟨op, hop, ?_⟩
  cases op with
  | constrainEqual a b =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainInstance cell col row =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainConstant cell value =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp [resolveDeclared] at hres
  | assignAdvice col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | assignFixed col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | enableGate gate off => simp [regionOperationDeclaredCopy?] at hcopy
  | enableLookup arg enabled off => simp [regionOperationDeclaredCopy?] at hcopy

/-- **Every resolvable declared copy is in the V1 copy list**: region-local copies land
in their region's extracted stream, layouter-level instance copies inline, and the
whole equality/instance stream prefixes the copy list. -/
theorem mem_V1_copyList_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ operationDeclaredCopies ops) :
    tuple ∈ V1.copyList permCols starts ops consts := by
  suffices h : tuple ∈ (V1.go permCols starts ops consts).1.1 by
    rw [V1.copyList]
    exact List.mem_append_left _ h
  induction ops generalizing consts with
  | nil => simp [operationDeclaredCopies] at hmem
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [operationDeclaredCopies] at hmem
          rcases hsplit : regionCopiesSplit permCols starts body consts with
            ⟨eqs, cnsts, cs'⟩
          rcases hgo : V1.go permCols starts rest cs' with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hsplit, hgo]
          rcases List.mem_append.mp hmem with hcopy | hcopy
          · refine List.mem_append_left _ ?_
            have := mem_regionCopiesSplit_fst_of_declared permCols starts body consts
              copy tuple hres hcopy
            rwa [hsplit] at this
          · refine List.mem_append_right _ ?_
            have := ih cs' hcopy
            rwa [hgo] at this
      | constrainInstance cell col row =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          rcases List.mem_cons.mp hmem with hcopy | hcopy
          · subst hcopy
            simp only [resolveDeclared] at hres
            obtain rfl := Option.some.inj hres
            exact List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ ?_
            have := ih consts hcopy
            rwa [hgo] at this
      | loadTable tbl values =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          have := ih consts hmem
          rwa [hgo] at this

/-- Decode raw copy tuples into typed cells under a bounds certificate. -/
def decodeCopies (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    List (FlatCell numCols n × FlatCell numCols n) :=
  raw.attach.map fun t =>
    ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
      (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))

/-- Decoding then re-encoding is the identity: the bounds certificate is the whole
content of the `hcopies` hypothesis. -/
theorem decodeCopies_map (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    (decodeCopies numCols n raw h).map
        (fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) = raw := by
  rw [decodeCopies, List.map_map]
  have : (fun (t : { x // x ∈ raw }) => t.1) =
      ((fun p : (FlatCell numCols n × FlatCell numCols n) =>
          (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) ∘
        fun t : { x // x ∈ raw } =>
          ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
            (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))) := by
    funext t
    rfl
  rw [← this]
  exact List.attach_map_subtype_val raw

/-- The constant-declaration sites of a region body, in body order. -/
def constSites : RegionOperations Fp → List (Cell × Fp)
  | [] => []
  | .constrainConstant cell value :: rest => (cell, value) :: constSites rest
  | _ :: rest => constSites rest

/-- The constants half of a region's copy extraction, in closed zipped form: each
constant site pairs with the next allocation-map entry — the constants cell on the
left, the site's resolved cell on the right — and the tail of the map is returned. -/
theorem regionCopiesSplit_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ))
    (hlen : (constSites body).length ≤ consts.length) :
    (regionCopiesSplit permCols starts body consts).2.1 =
      ((constSites body).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (regionCopiesSplit permCols starts body consts).2.2 =
        consts.drop (constSites body).length := by
  induction body generalizing consts with
  | nil => exact ⟨rfl, rfl⟩
  | cons op rest ih =>
      cases op with
      | constrainConstant cell value =>
          cases consts with
          | nil => simp [constSites] at hlen
          | cons entry cs =>
              have hlen' : (constSites rest).length ≤ cs.length := by
                simpa [constSites] using hlen
              obtain ⟨ih1, ih2⟩ := ih cs hlen'
              constructor
              · show (permIndex permCols (ColRef.toAny (.fixed entry.2.1)), entry.2.2,
                    (resolveCell permCols starts cell).1,
                    (resolveCell permCols starts cell).2) ::
                    (regionCopiesSplit permCols starts rest cs).2.1 = _
                rw [ih1]
                rfl
              · show (regionCopiesSplit permCols starts rest cs).2.2 = _
                rw [ih2]
                rfl
      | constrainEqual a b =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | constrainInstance cell col row =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | assignAdvice col off val =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | assignFixed col off val =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | enableGate gate off =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | enableLookup arg enabled off =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩

/-- Zipping ignores the second list beyond the first's length. -/
theorem zip_take_length {α β : Type*} (a : List α) (c : List β) :
    a.zip (c.take a.length) = a.zip c := by
  induction a generalizing c with
  | nil => rfl
  | cons x xs ih =>
      cases c with
      | nil => rfl
      | cons y ys => simp [ih]

/-- The constant-declaration sites of a whole operation stream: region sites in region
order (V1 defers them all to the end of synthesis, in this order). -/
def operationConstSites : Operations Fp → List (Cell × Fp)
  | [] => []
  | .region _ body :: rest => constSites body ++ operationConstSites rest
  | .constrainInstance _ _ _ :: rest => operationConstSites rest
  | .loadTable _ _ :: rest => operationConstSites rest

/-- A declared region constant copy occurs in the region's positional constants stream. -/
theorem mem_constSites_of_declared_constant
    (body : RegionOperations Fp) (cell : Cell) (value : Fp)
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        regionDeclaredCopies body) :
    (cell, value) ∈ constSites body := by
  induction body with
  | nil =>
      simp [regionDeclaredCopies] at hcopy
  | cons operation rest ih =>
      cases operation with
      | constrainConstant assignedCell assignedValue =>
          rw [regionDeclaredCopies, constSites] at *
          simp only [regionOperationDeclaredCopy?, List.mem_cons] at hcopy
          rcases hcopy with heq | hrest
          · obtain ⟨rfl, rfl⟩ := heq
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hrest)
      | constrainEqual left right =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | constrainInstance copyCell column row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | assignAdvice column row value =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | assignFixed column row value =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | enableGate gate row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | enableLookup argument enabled row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)

/-- A declared constant copy occurs in V1's whole-synthesis positional stream. -/
theorem mem_operationConstSites_of_declared_constant
    (ops : Operations Fp) (cell : Cell) (value : Fp)
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        operationDeclaredCopies ops) :
    (cell, value) ∈ operationConstSites ops := by
  induction ops with
  | nil =>
      simp [operationDeclaredCopies] at hcopy
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites, List.mem_append]
          rcases List.mem_append.mp hcopy with hbody | hrest
          · exact Or.inl
              (mem_constSites_of_declared_constant body cell value hbody)
          · exact Or.inr (ih hrest)
      | constrainInstance copyCell column row =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites]
          rcases List.mem_cons.mp hcopy with heq | hrest
          · cases heq
          · exact ih hrest
      | loadTable table values =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites]
          exact ih hcopy

/-- Every member of the left list occurs in its zip when the right list is long enough. -/
theorem exists_mem_zip_of_mem_left
    {α β : Type} (left : List α) (right : List β)
    (hlen : left.length ≤ right.length)
    {value : α} (hvalue : value ∈ left) :
    ∃ paired, (value, paired) ∈ left.zip right := by
  induction left generalizing right with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      cases right with
      | nil =>
          simp at hlen
      | cons paired rest =>
          rw [List.mem_cons] at hvalue
          rcases hvalue with rfl | htail
          · exact ⟨paired, List.mem_cons_self⟩
          · have hlen' : tail.length ≤ rest.length := by
              simpa using hlen
            obtain ⟨other, hother⟩ := ih rest hlen' htail
            exact ⟨other, List.mem_cons_of_mem _ hother⟩

/-- The V1 constants stream in closed zipped form: every constant site across the
stream pairs with its allocation-map entry, in region-then-body order. -/
theorem V1_go_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ))
    (hlen : (operationConstSites ops).length ≤ consts.length) :
    (V1.go permCols starts ops consts).1.2 =
      ((operationConstSites ops).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (V1.go permCols starts ops consts).2 =
        consts.drop (operationConstSites ops).length := by
  induction ops generalizing consts with
  | nil => exact ⟨rfl, rfl⟩
  | cons op rest ih =>
      cases op with
      | region name body =>
          have hbody : (constSites body).length ≤ consts.length := by
            refine le_trans ?_ hlen
            simp [operationConstSites]
          obtain ⟨hsplit1, hsplit2⟩ :=
            regionCopiesSplit_snd_eq permCols starts body consts hbody
          have hrest : (operationConstSites rest).length ≤
              (consts.drop (constSites body).length).length := by
            rw [List.length_drop]
            have := hlen
            simp only [operationConstSites, List.length_append] at this
            omega
          rcases hsplitEq : regionCopiesSplit permCols starts body consts with
            ⟨eqs, cnsts, cs'⟩
          rcases hgoEq : V1.go permCols starts rest cs' with ⟨⟨r1, r2⟩, cs''⟩
          have hcs' : cs' = consts.drop (constSites body).length := by
            rw [hsplitEq] at hsplit2
            exact hsplit2
          obtain ⟨ih1, ih2⟩ := ih (consts.drop (constSites body).length)
            hrest
          constructor
          · show (V1.go permCols starts (.region name body :: rest) consts).1.2 = _
            simp only [V1.go, hsplitEq, hgoEq]
            have hcnsts : cnsts = ((constSites body).zip consts).map (fun se =>
                (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
                  (resolveCell permCols starts se.1.1).1,
                  (resolveCell permCols starts se.1.1).2)) := by
              rw [hsplitEq] at hsplit1
              exact hsplit1
            rw [hcnsts]
            have hr2 : r2 = ((operationConstSites rest).zip
                (consts.drop (constSites body).length)).map (fun se =>
                (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
                  (resolveCell permCols starts se.1.1).1,
                  (resolveCell permCols starts se.1.1).2)) := by
              rw [hcs'] at hgoEq
              rw [hgoEq] at ih1
              exact ih1
            rw [hr2]
            conv_rhs =>
              rw [show operationConstSites (.region name body :: rest) =
                constSites body ++ operationConstSites rest from rfl,
                show consts = consts.take (constSites body).length ++
                  consts.drop (constSites body).length from
                  (List.take_append_drop _ _).symm]
            rw [List.zip_append (by rw [List.length_take]; omega),
              List.map_append, zip_take_length]
          · show (V1.go permCols starts (.region name body :: rest) consts).2 = _
            simp only [V1.go, hsplitEq, hgoEq]
            have : cs'' = (consts.drop (constSites body).length).drop
                (operationConstSites rest).length := by
              rw [hcs'] at hgoEq
              rw [hgoEq] at ih2
              exact ih2
            rw [this, List.drop_drop]
            rw [show operationConstSites (.region name body :: rest) =
              constSites body ++ operationConstSites rest from rfl]
            rw [List.length_append]
      | constrainInstance cell col row =>
          rcases hgoEq : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [operationConstSites] using hlen)
          rw [hgoEq] at ih1 ih2
          exact ⟨by simp only [V1.go, hgoEq]; exact ih1,
            by simp only [V1.go, hgoEq]; exact ih2⟩
      | loadTable tbl values =>
          rcases hgoEq : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [operationConstSites] using hlen)
          rw [hgoEq] at ih1 ih2
          exact ⟨by simp only [V1.go, hgoEq]; exact ih1,
            by simp only [V1.go, hgoEq]; exact ih2⟩

/-- Every declared copy has a `Cell` left endpoint, and its right endpoint is a cell,
an instance read, or a constant — so every declared copy either resolves or is a
constant declaration. -/
theorem declared_shape (ops : Operations Fp) (permCols : List ColRef)
    (starts : List ℕ) :
    ∀ copy ∈ operationDeclaredCopies ops,
      (∃ tuple, resolveDeclared permCols starts copy = some tuple) ∨
        ∃ c v, copy = (.cell c, .constant v) := by
  intro copy hmem
  induction ops with
  | nil => simp [operationDeclaredCopies] at hmem
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [operationDeclaredCopies] at hmem
          rcases List.mem_append.mp hmem with hcopy | hcopy
          · rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hcopy
            obtain ⟨rop, _, hop⟩ := hcopy
            cases rop with
            | constrainEqual a b =>
                obtain rfl := Option.some.inj hop
                exact Or.inl ⟨_, rfl⟩
            | constrainConstant cell value =>
                obtain rfl := Option.some.inj hop
                exact Or.inr ⟨cell, value, rfl⟩
            | constrainInstance cell col row =>
                obtain rfl := Option.some.inj hop
                exact Or.inl ⟨_, rfl⟩
            | assignAdvice col off val => simp [regionOperationDeclaredCopy?] at hop
            | assignFixed col off val => simp [regionOperationDeclaredCopy?] at hop
            | enableGate gate off => simp [regionOperationDeclaredCopy?] at hop
            | enableLookup arg enabled off => simp [regionOperationDeclaredCopy?] at hop
          · exact ih hcopy
      | constrainInstance cell col row =>
          rw [operationDeclaredCopies] at hmem
          rcases List.mem_cons.mp hmem with hcopy | hcopy
          · subst hcopy
            exact Or.inl ⟨_, rfl⟩
          · exact ih hcopy
      | loadTable tbl values =>
          rw [operationDeclaredCopies] at hmem
          exact ih hmem

end Zcash.Snark
