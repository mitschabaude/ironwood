import Zcash.Security.Ledger.Statement

/-!
# Orchard Action key binding

This is the key-binding interface enforced by the deployed Orchard Action
circuit.  It is intentionally separate from the Recovery Statement adapter:
the circuit opens

`SinsemillaHashToPoint(Extract(akP), nk) + [rivk] CommitIvkR`

and does not enforce the Recovery Statement's additional key-derivation
constraints.
-/

namespace Zcash.Security.KeyBinding.Pool

open Zcash.Security.Ledger
open scoped Zcash.Security.RandomOracle

variable {F G B : Type*}

/-- The successful opening retained by the Orchard bridge. -/
structure Witness (F G B : Type*) where
  ivk : B
  akP : G
  nk : B
  rivk : F
  hashPoint : G

/-- The part of a witness which a key-binding break must change. -/
structure BreakProjection (F B : Type*) where
  ak : B
  nk : B
  rivk : F
deriving DecidableEq

def Witness.breakProjection (extract : G → B) (w : Witness F G B) :
    BreakProjection F B :=
  ⟨extract w.akP, w.nk, w.rivk⟩

section

variable [AddCommGroup G] [SMul F G] [Zero B]

/-- The successful circuit opening and the protocol-required nonzero incoming
viewing key. -/
structure KB
    (extract : G → B) (hash : B → B → Option G) (commitIvkR : G)
    (w : Witness F G B) : Prop where
  hash_eq : hash (extract w.akP) w.nk = some w.hashPoint
  ivk_eq : w.ivk = extract (w.hashPoint + w.rivk • commitIvkR)
  ivk_ne : w.ivk ≠ 0

/-- Two valid openings of the same `ivk` which disagree on an opening
projection.  A later cryptographic layer may reduce this event to the
appropriate Sinsemilla/DLR relation. -/
structure Break
    (extract : G → B) (hash : B → B → Option G) (commitIvkR : G)
    (w₁ w₂ : Witness F G B) : Prop where
  kb₁ : KB extract hash commitIvkR w₁
  kb₂ : KB extract hash commitIvkR w₂
  ivk_eq : w₁.ivk = w₂.ivk
  projection_ne : w₁.breakProjection extract ≠ w₂.breakProjection extract

/-- The deployed Orchard key-binding predicate as the games-facing interface.
`extract_pm` is the ±-fibre property of the extraction (`Extract_ℙ` concretely: equal
extracted coordinates pin the point up to y-sign); it discharges the games'
`break_of_akP_ne` from the break projection, exactly as `break_of_nk_ne` is discharged
from its `nk` component. -/
def toInterface
    (extract : G → B) (hash : B → B → Option G) (commitIvkR : G)
    (extract_pm : ∀ P Q : G, extract P = extract Q → P =± Q) :
    KeyBindingInterface (Witness F G B) G B B where
  ivk := Witness.ivk
  nk := Witness.nk
  akP := Witness.akP
  KB := KB extract hash commitIvkR
  Break := Break extract hash commitIvkR
  break_of_nk_ne {w₁ w₂} h₁ h₂ hivk hnk := by
    refine ⟨h₁, h₂, hivk, fun heq => hnk ?_⟩
    exact congrArg BreakProjection.nk heq
  break_of_akP_ne {w₁ w₂} h₁ h₂ hivk hne := by
    refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
    exact extract_pm _ _ (congrArg BreakProjection.ak heq)

end

end Zcash.Security.KeyBinding.Pool
