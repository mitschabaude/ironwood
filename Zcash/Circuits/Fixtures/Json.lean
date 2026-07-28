import Lean.Data.Json
import Zcash.Circuits.Fixtures.FixtureTypes
import Zcash.Circuits.Fixtures.Stamp

/-!
# JSON codecs and the loader for VK fixtures

The large generated fixtures (the whole-circuit Action CS and layout dumps) are stored
as `.json` DATA files, not Lean literals: elaborating a ~1 MB fixture as a Lean term
costs ~40 s and gigabytes of RSS, while `Json.parse` + decode of the same data runs in
~150 ms at `#eval` time. The consuming test loads the file inside its `#eval` check, so
a parse failure (or a failed load) is a build failure exactly as with `#guard`.

**Integrity**: two independent guards, neither of which recomputes a hash inside Lean (no
fast SHA-256 exists in the toolchain, and a hand-rolled one is not worth maintaining):

* *Semantic* — the `CircuitCheck` `#eval`s reconstruct the Lean CS/layout and assert it
  equals the parsed fixture (`TestVk*`), so a fixture that drifts from the Lean circuit
  model fails the build.
* *Content* — every fixture's SHA-256 is pinned in `Zcash/Circuits/Fixtures/SHA256SUMS`
  and enforced by the `Fixtures/*.json` guard in `.github/workflows/lean.yml`
  (`sha256sum -c`, the OS tool). SHA-256 (rather than a non-cryptographic checksum) means
  the pin also resists a *crafted* swap, not just accidental drift. The loaders resolve a
  fixture by name through the pins (`pinnedPath`), so an unpinned file cannot be read.

**Rebuild tracking**: Lake tracks a module's imports, not the `.json` files a `#eval` reads,
so a regenerated fixture on its own leaves the semantic check cached and unrun locally.
`Stamp.lean` — the pins as Lean data, generated from `SHA256SUMS` by `stamp.sh` — puts the
fixture content in the import graph. Refreshing a fixture obliges refreshing `SHA256SUMS`,
and the stamp with it (CI diffs the two), which is a source change Lake follows: the tests
below re-elaborate and their checks re-run. Regenerate both from this directory, listing the
files in the committed order (the stamp follows it):

    sha256sum <files> > SHA256SUMS && ./stamp.sh > Stamp.lean

Small fixtures (the Add/Mul doc-test pairs, the SelMaps) stay as readable Lean
literals; only the whole-circuit Action dumps use this path.
-/

namespace Zcash.Circuits.Fixtures.Json

open Lean (Json JsonNumber)
open Fixtures
open Halo2 (RichExpression)

/-- The fixture directory, relative to the repository root — where `lake` runs, and so the
working directory of an elaborating `#eval`. -/
def fixtureDir : System.FilePath := "Zcash/Circuits/Fixtures"

/-- The path of a content-pinned fixture, by file name. A name the stamp does not list is
an `IO` error, so a test cannot consume a fixture that `SHA256SUMS` leaves unpinned. -/
def pinnedPath (file : String) : IO System.FilePath := do
  unless Stamp.entries.any (fun e => e.1 == file) do
    throw <| IO.userError
      s!"fixture {file} is not pinned in {fixtureDir}/SHA256SUMS (see PROVENANCE.md)"
  return fixtureDir / file

/-- Read a JSON fixture and parse it. A missing file or parse error is an `IO` error → a
build failure at the consuming `#eval`. Content integrity is enforced out of band (see the
module header): the SHA-256 pin in `SHA256SUMS` + the `CircuitCheck` reconstruction. -/
def loadJson (path : System.FilePath) : IO Json := do
  let bytes ← IO.FS.readBinFile path
  IO.ofExcept (Json.parse (String.fromUTF8! bytes) |>.mapError IO.userError)

/-! ## Primitive codecs

Field elements are decimal strings of their canonical `ZMod.val` (JSON-number precision
is tool-dependent; strings are safe everywhere). Small numbers are JSON numbers.
-/

def jNat (n : ℕ) : Json := Json.num (JsonNumber.fromNat n)
def jInt (i : ℤ) : Json := Json.num (JsonNumber.fromInt i)
def jFp (c : Fp) : Json := Json.str (toString c.val)

def getNat : Json → Except String ℕ
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then .ok n.mantissa.toNat
      else .error s!"expected nat, got {n}"
  | j => .error s!"expected nat, got {j.compress}"

def getInt : Json → Except String ℤ
  | .num n => if n.exponent == 0 then .ok n.mantissa else .error s!"expected int, got {n}"
  | j => .error s!"expected int, got {j.compress}"

def getFp : Json → Except String Fp
  | .str s => match s.toNat? with
    | some n => .ok (n : Fp)
    | none => .error s!"expected decimal field element, got {s}"
  | j => .error s!"expected field-element string, got {j.compress}"

def getArr : Json → Except String (Array Json)
  | .arr a => .ok a
  | j => .error s!"expected array, got {j.compress}"

def getStr : Json → Except String String
  | .str s => .ok s
  | j => .error s!"expected string, got {j.compress}"

def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field {name}"

def decodeList {α : Type} (j : Json) (f : Json → Except String α) : Except String (List α) := do
  let a ← getArr j
  a.foldrM (fun x acc => do pure ((← f x) :: acc)) []

/-! ## Flat tuple codecs (arrays, not nested pairs — external tools read these) -/

def jPairNatInt : ℕ × ℤ → Json
  | (a, b) => Json.arr #[jNat a, jInt b]

def getPairNatInt (j : Json) : Except String (ℕ × ℤ) := do
  match ← getArr j with
  | #[a, b] => pure (← getNat a, ← getInt b)
  | _ => .error "expected [nat, int]"

def jTriple : ℕ × ℕ × ℕ → Json
  | (a, b, c) => Json.arr #[jNat a, jNat b, jNat c]

def getTriple (j : Json) : Except String (ℕ × ℕ × ℕ) := do
  match ← getArr j with
  | #[a, b, c] => pure (← getNat a, ← getNat b, ← getNat c)
  | _ => .error "expected [nat, nat, nat]"

def jQuad : ℕ × ℕ × ℕ × ℕ → Json
  | (a, b, c, d) => Json.arr #[jNat a, jNat b, jNat c, jNat d]

def getQuad (j : Json) : Except String (ℕ × ℕ × ℕ × ℕ) := do
  match ← getArr j with
  | #[a, b, c, d] => pure (← getNat a, ← getNat b, ← getNat c, ← getNat d)
  | _ => .error "expected [nat, nat, nat, nat]"

/-! ## Gate-polynomial `RichExpression` (tagged arrays)

The dumped gates are post-compression, hence selector-free, so no `selector` tag occurs. -/

def jExpr : RichExpression Fp → Json
  | .constant c => Json.arr #["c", jFp c]
  | .fixed i => Json.arr #["f", jNat i]
  | .advice i => Json.arr #["a", jNat i]
  | .instance i => Json.arr #["i", jNat i]
  | .negated e => Json.arr #["neg", jExpr e]
  | .sum a b => Json.arr #["+", jExpr a, jExpr b]
  | .product a b => Json.arr #["*", jExpr a, jExpr b]
  | .scaled e c => Json.arr #["s", jExpr e, jFp c]
  | .selector i => Json.arr #["sel", jNat i]

partial def getExpr (j : Json) : Except String (RichExpression Fp) := do
  match ← getArr j with
  | #[.str "c", c] => pure (.constant (← getFp c))
  | #[.str "f", i] => pure (.fixed (← getNat i))
  | #[.str "a", i] => pure (.advice (← getNat i))
  | #[.str "i", i] => pure (.instance (← getNat i))
  | #[.str "neg", e] => pure (.negated (← getExpr e))
  | #[.str "+", a, b] => pure (.sum (← getExpr a) (← getExpr b))
  | #[.str "*", a, b] => pure (.product (← getExpr a) (← getExpr b))
  | #[.str "s", e, c] => pure (.scaled (← getExpr e) (← getFp c))
  | _ => .error s!"unknown RichExpression node {j.compress}"

/-! ## `CsFixture` -/

def jCsFixture (f : CsFixture) : Json :=
  Json.mkObj [
    ("numAdviceColumns", jNat f.numAdviceColumns),
    ("numFixedColumns", jNat f.numFixedColumns),
    ("numInstanceColumns", jNat f.numInstanceColumns),
    ("numSelectors", jNat f.numSelectors),
    ("adviceQueryLayout", Json.arr (f.adviceQueryLayout.map jPairNatInt).toArray),
    ("fixedQueryLayout", Json.arr (f.fixedQueryLayout.map jPairNatInt).toArray),
    ("instanceQueryLayout", Json.arr (f.instanceQueryLayout.map jPairNatInt).toArray),
    ("gates", Json.arr (f.gates.map jExpr).toArray),
    ("lookups", Json.arr (f.lookups.map fun l => Json.mkObj [
      ("inputs", Json.arr (l.inputs.map jExpr).toArray),
      ("tables", Json.arr (l.tables.map jExpr).toArray)]).toArray)]

def getCsFixture (j : Json) : Except String CsFixture := do
  pure {
    numAdviceColumns := ← getNat (← field j "numAdviceColumns"),
    numFixedColumns := ← getNat (← field j "numFixedColumns"),
    numInstanceColumns := ← getNat (← field j "numInstanceColumns"),
    numSelectors := ← getNat (← field j "numSelectors"),
    adviceQueryLayout := ← decodeList (← field j "adviceQueryLayout") getPairNatInt,
    fixedQueryLayout := ← decodeList (← field j "fixedQueryLayout") getPairNatInt,
    instanceQueryLayout := ← decodeList (← field j "instanceQueryLayout") getPairNatInt,
    gates := ← decodeList (← field j "gates") getExpr,
    lookups := ← decodeList (← field j "lookups") fun l => do
      pure { inputs := ← decodeList (← field l "inputs") getExpr,
             tables := ← decodeList (← field l "tables") getExpr } }

/-! ## `LayoutFixture` -/

def jColRef : ColRef → Json
  | .advice i => Json.arr #["advice", jNat i]
  | .fixed i => Json.arr #["fixed", jNat i]
  | .instance i => Json.arr #["instance", jNat i]

def getColRef (j : Json) : Except String ColRef := do
  match ← getArr j with
  | #[.str "advice", i] => pure (.advice (← getNat i))
  | #[.str "fixed", i] => pure (.fixed (← getNat i))
  | #[.str "instance", i] => pure (.instance (← getNat i))
  | _ => .error s!"unknown ColRef {j.compress}"

def jRegion (r : RegionPlacement) : Json :=
  Json.arr #[jNat r.index, Json.str r.name, jNat r.start]

def getRegion (j : Json) : Except String RegionPlacement := do
  match ← getArr j with
  | #[i, .str n, s] => pure { index := ← getNat i, name := n, start := ← getNat s }
  | _ => .error s!"expected [index, name, start], got {j.compress}"

def jLayoutFixture (f : LayoutFixture) : Json :=
  Json.mkObj [
    ("k", jNat f.k),
    ("n", jNat f.n),
    ("regions", Json.arr (f.regions.map jRegion).toArray),
    ("permColumns", Json.arr (f.permColumns.map jColRef).toArray),
    ("copyList", Json.arr (f.copyList.map jQuad).toArray),
    ("sigma", Json.arr (f.sigma.map jQuad).toArray),
    ("constants", Json.arr (f.constants.map jTriple).toArray),
    ("fixed", Json.arr (f.fixed.map jTriple).toArray)]

def getLayoutFixture (j : Json) : Except String LayoutFixture := do
  pure {
    k := ← getNat (← field j "k"),
    n := ← getNat (← field j "n"),
    regions := ← decodeList (← field j "regions") getRegion,
    permColumns := ← decodeList (← field j "permColumns") getColRef,
    copyList := ← decodeList (← field j "copyList") getQuad,
    sigma := ← decodeList (← field j "sigma") getQuad,
    constants := ← decodeList (← field j "constants") getTriple,
    fixed := ← decodeList (← field j "fixed") getTriple }

/-! ## Checked loaders

Both take a fixture's file name and resolve it through `pinnedPath`, so the only fixtures
a test can read are the ones `SHA256SUMS` pins.
-/

def loadCsFixture (file : String) : IO CsFixture := do
  IO.ofExcept ((getCsFixture (← loadJson (← pinnedPath file))).mapError IO.userError)

def loadLayoutFixture (file : String) : IO LayoutFixture := do
  IO.ofExcept ((getLayoutFixture (← loadJson (← pinnedPath file))).mapError IO.userError)

/-- `#eval`-check helper: named boolean checks, first failure reported. -/
def runChecks (checks : List (String × Bool)) : IO Unit := do
  for (name, ok) in checks do
    unless ok do
      throw <| IO.userError s!"VK fixture check FAILED: {name}"

end Zcash.Circuits.Fixtures.Json
