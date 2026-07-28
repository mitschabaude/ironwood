import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# `assert_axioms` — a concise, build-checked trust-boundary bound

A sibling of Mathlib's `assert_no_sorry` (same `collectAxioms` machinery) that asserts an *upper
bound* on a declaration's trusted base. Unlike a `#guard_msgs`-pinned `#print axioms`, it does not
hard-code the pretty-printed axiom list, so it stays green across toolchain bumps that rename the
`native_decide` axiom — while still failing the build the moment a declaration reaches beyond its
declared tier (a `sorry`, an unexpected axiom, or `native_decide` where none was permitted).

The `#guard_msgs`-pinned form remains the right tool when the *exact* axiom set is the claim.

Both commands require their argument to be written fully qualified (`checkFullyQualified`):
an unqualified name resolves through the census file's `open`s, so a same-base-name cousin in
an opened namespace can silently capture an entry meant for a declaration that is not in scope
at all — the assertion then reads as covering one theorem while checking another.

This command is also used in CompElliptic (`CompElliptic/Meta/AxiomCheck.lean`); changes here
should be reflected there and vice versa.
-/

open Lean Elab Command

namespace Zcash.Meta

/-- The standard axioms of Lean's trusted base — the whole budget for a general theorem. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- An axiom introduced by `native_decide`: its name carries a `native_decide` component
(e.g. `..._native.native_decide.ax_1_1`). Matching on the component rather than the full name keeps
the check stable across the toolchain-dependent axiom naming. -/
def isNativeDecideAxiom (n : Name) : Bool :=
  n.components.any (· == `native_decide)

/-- Assertion names must be written fully qualified. Resolution through `open`s is
context-dependent: a same-base-name cousin in an opened namespace can silently capture an
entry meant for a declaration that is not even in scope, so the assertion reads as covering
one theorem while checking another. Requiring the written name to equal the resolved
constant's full name (an optional `_root_.` prefix is accepted) makes every entry
independent of the file's `open`s and turns the wrong-cousin case into a loud error. -/
def checkFullyQualified (n : Ident) (resolved : Name) : CommandElabM Unit := do
  let written := n.getId
  unless written == resolved || written == rootNamespace ++ resolved do
    throwError "{n} is not written fully qualified: it resolves to '{resolved}'. \
      Write the full name so the entry does not depend on this file's `open`s."

/-- The declaration a `native_decide` axiom certifies: the axiom name's components strictly
before its first `_native` / `native_decide` component
(e.g. `Foo.bar._native.native_decide.ax_1_1` is owned by `Foo.bar`). -/
def nativeAxiomOwner (ax : Name) : Name :=
  (ax.components.takeWhile fun c => c != `_native && c != `native_decide).foldl
    Name.append Name.anonymous

/-- Render a list of owners as the text to write inside `+native(...)`. -/
def ownersText (owners : List Name) : String :=
  ", ".intercalate (owners.map toString)

/-- `+native` must name the owning declaration(s) of exactly the `native_decide` axioms the
entry actually reaches, fully qualified. A bare `+native` would permit a `native_decide`
axiom smuggled in by *any* declaration entering the dependency cone; naming the owners makes
the census state precisely which native certificates are trusted, and a new native axiom —
or a stale annotation — fails the build with the list to write. -/
def checkNativeAllowance (n : Ident) (axs : Array Name) (allowed : Option (Array Name)) :
    CommandElabM Unit := do
  let owners := (axs.filter isNativeDecideAxiom |>.map nativeAxiomOwner).toList.eraseDups
  match allowed with
  | none =>
    unless owners.isEmpty do
      throwError "{n} depends on native_decide axiom(s); name their owning declaration(s): \
        write '+native({ownersText owners})'"
  | some allowedArr =>
    let allowedL := allowedArr.toList.eraseDups
    if owners.isEmpty then
      throwError "{n} reaches no native_decide axiom; drop the '+native(...)' flag"
    unless owners.all allowedL.contains && allowedL.all owners.contains do
      throwError "{n}: '+native' names {allowedL} but the native_decide axiom(s) present \
        are owned by {owners}; write '+native({ownersText owners})'"

/-- The `+native(A, B)` flag: the parenthesized, comma-separated owner list is required. -/
syntax nativeFlag := "+native" "(" ident,+ ")"

/-- Extract the annotation list from an optional `+native(A, B)` flag: `none` when the flag
is absent, `some names` with the parenthesized list otherwise. -/
def nativeAnnotation (native : Option (TSyntax ``nativeFlag)) : Option (Array Name) :=
  native.map fun stx => stx.raw[2].getSepArgs.map (·.getId)

/--
`assert_axioms foo` fails the build unless `foo` depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular, no `sorry` and no `native_decide`.

`assert_axioms foo +native(D₁, ...)` additionally permits `native_decide` compiler-trust axioms —
exactly those owned by the named declarations, written fully qualified. The axiom names' tails are
toolchain-dependent, so entries name the owning declarations rather than the axioms themselves.
Any other axiom (including `sorryAx`) is still rejected, as is a stale or incomplete list.
-/
elab "assert_axioms " n:ident native:(nativeFlag)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  checkFullyQualified n name
  let axs ← collectAxioms name
  let allowed := nativeAnnotation native
  checkNativeAllowance n axs allowed
  let unexpected := axs.filter fun ax =>
    !standardAxioms.contains ax && !(allowed.isSome && isNativeDecideAxiom ax)
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

/--
`assert_computable foo` fails the build unless `foo` is a plain `def` — an actual
definition, not marked `noncomputable` — depending on no axioms beyond `propext` / `Quot.sound`.
This is the breaks-as-computed-data check: the data is genuinely computed, and with
`Classical.choice` excluded it cannot have been conjured from mere propositional existence even
in erased positions.

`assert_computable foo +choice` additionally permits `Classical.choice`. Together with the
plain-`def` check this asserts choice enters only through erased `Prop` fields: had it touched the
data, the definition could not have compiled as a plain `def`. `+native(D₁, ...)` likewise permits
the named declarations' `native_decide` compiler-trust axioms.

The plain-`def` check guards a gap in "computability is compiler-enforced": marking a reduction
`noncomputable` later would still build, silently voiding the convention; this assertion catches
it.
-/
elab "assert_computable " n:ident choice:("+choice")? native:(nativeFlag)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  checkFullyQualified n name
  let env ← getEnv
  let info ← liftCoreM <| getConstInfo name
  unless info matches .defnInfo _ do
    throwError "{n} is not a def"
  if Lean.isNoncomputable env name then
    throwError "{n} is marked noncomputable"
  let axs ← collectAxioms name
  let allowChoice := choice.isSome
  let allowed := nativeAnnotation native
  checkNativeAllowance n axs allowed
  let unexpected := axs.filter fun ax =>
    !(ax == ``propext || ax == ``Quot.sound
      || (allowChoice && ax == ``Classical.choice)
      || (allowed.isSome && isNativeDecideAxiom ax))
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

end Zcash.Meta
