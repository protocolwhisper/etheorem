import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.Update

/-!
# `SizzLeanTests.PresetSymbolicCap`: symbolic (preset-resolved) caps

Acceptance spike for `deriving SSZRepr` over a container whose
collection cap is a *symbolic*, instance-resolved expression rather
than a `Nat` literal.

The consensus-spec framework declares containers parameterised by a
`[Preset]` instance, so a field width is a projection like
`Const.validatorRegistryLimit`, concrete only once the `[Preset]`
instance is fixed (at the runner). The handler used to evaluate every
cap to a literal at derive time and throw otherwise; it now splices the
cap *expression* through symbolically, keeping the literal fast path
for the fully-concrete case.

This file pins the contract: a `[Preset]`-generic container derives
`SSZRepr` with no literal-cap error, and at a concrete `@[reducible]`
preset instance every downstream consumer reduces.

* The type-level width and the `SSZType` shape reduce by `rfl`.
* `hashTreeRoot` of a value reduces (definitionally for the uncached
  path, computationally under `native_decide`).
* `sszUpdate` followed by `hashTreeRoot` reduces, cached and uncached.

## The local `[Preset]` stand-in

`Preset` here is a one-field class, the minimal stand-in for the
framework's preset class. `Const.validatorRegistryLimit` is the
preset-resolved projection that lands inside the field type, mirroring
the real `Const.*` surface. The concrete `testPreset` instance is
`@[reducible]` so its projection reduces to a literal under `rfl` /
`decide` / `native_decide`. Its cap is a small `8` (not the spec's
`2^40`) purely to keep `native_decide` fast; the symbolic mechanism is
identical at any value.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SizzLeanTests.PresetSymbolicCap

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr

/-- Minimal stand-in for the framework's preset class: a bag of
preset-sensitive caps resolved through an instance. -/
class Preset where
  validatorRegistryLimit : Nat

namespace Const

/-- Preset-resolved cap projection, the symbolic width that lands
inside a container field type. `@[reducible]` so it unfolds to the
instance's literal under `rfl` once a concrete `[Preset]` is fixed. -/
@[reducible] def validatorRegistryLimit [P : Preset] : Nat :=
  P.validatorRegistryLimit

end Const

/-- A concrete, `@[reducible]` preset. `reducible` is what lets the
symbolic cap `Const.validatorRegistryLimit` reduce to the literal `8`
in `rfl` / `native_decide` goals. The cap is deliberately small to
keep the merkleization that `native_decide` evaluates cheap. -/
@[reducible] instance testPreset : Preset where
  validatorRegistryLimit := 8

/-- A `[Preset]`-generic container with one symbolic-cap `SSZList`
field plus a flat `UInt64`. The cap `Const.validatorRegistryLimit` is
an instance-resolved projection, not a literal; `deriving SSZRepr` must
splice it through symbolically. -/
structure Registry [P : Preset] where
  validators : SSZList UInt64 (Const.validatorRegistryLimit (P := P))
  marker     : UInt64
deriving DecidableEq, SSZRepr

/-! ## The cap stays symbolic in the derived shape, concrete at a preset

The derive above succeeded with no "cannot evaluate cap to a Nat
literal" error: the generic instance carries `.list (.uintN 64)
Const.validatorRegistryLimit`. Fixing the preset reduces that cap to
the literal. -/

/-- Type-level width reduces: the symbolic-cap field type is
definitionally the concrete-capacity type once the preset is fixed. -/
example :
    SSZList UInt64 (Const.validatorRegistryLimit (P := testPreset))
      = SSZList UInt64 8 := rfl

/-- The derived `SSZType` shape reduces: the cap inside the `.list`
descriptor becomes the literal `8` at `testPreset`. -/
example :
    (SSZRepr.shape (T := @Registry testPreset))
      = .container [.list (.uintN 64) 8, .uintN 64] := rfl

/-! ## Fixtures at the concrete preset -/

private def r0 : @Registry testPreset where
  validators := ⟨#[10, 20, 30], by decide⟩
  marker     := 0xabcd

private def grownList : SSZList UInt64 (Const.validatorRegistryLimit (P := testPreset)) :=
  ⟨#[1, 2, 3, 4, 5, 6], by decide⟩

/-! ## `serialize` / `deserialize` reduce

The cap is only a validity bound for the wire format (the list's bytes
are its elements plus a length offset), so this is the easy consumer:
the round-trip reduces under `native_decide` at the concrete preset. -/

/-- `deserialize ∘ serialize` round-trips the symbolic-cap value.
Compared through `.toOption` because the error arm `SSZError` carries
no `DecidableEq`; the `.ok` payload is what the round-trip asserts. -/
example :
    (SSZ.deserialize (SSZ.serialize r0)).toOption = some r0 := by
  native_decide

/-! ## `hashTreeRoot` reduces

The uncached root is *definitionally* the spec root (`rfl`); the cached
root agrees computationally (`native_decide`). Both require the
symbolic cap to reduce so the Merkle tree depth is concrete. -/

/-- Uncached `hashTreeRoot` is the spec `hashTreeRoot`, by `rfl`. This
is the symbolic-state-transition case: both sides are the same opaque
`Sha256` computation, so no concrete bytes and no compiler axiom are
needed (CLAUDE.md "Proofs involving SSZ hashes", case 1). -/
example :
    (UncachedSSZ.ofValue Sha256 r0).hashTreeRoot
      = SSZ.hashTreeRoot Sha256 r0 := rfl

/-- Cached `hashTreeRoot` agrees with the spec root, under
`native_decide` (the FFI `Sha256` reduces to concrete bytes only
through the compiler, case 2). This is the cache-spine consumer the
task flagged as riskiest: the spine walk runs over a field whose
subtree depth comes from the now-concrete cap. -/
example :
    (TreeBacked.ofValue Sha256 r0).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 r0 := by
  native_decide

/-! ## `sszUpdate` followed by `hashTreeRoot`, both flavours

Whole-field updates: the flat `marker` and the symbolic-cap
`validators` list. The cached path walks the Merkle spine and rebuilds
the list field's subtree at the preset-resolved depth; the uncached
path is a plain view rewrite. Each is checked against the spec root of
the directly-updated value. -/

/-- Cached: update the flat field. -/
example :
    let t : TreeBacked Sha256 (@Registry testPreset) := TreeBacked.ofValue Sha256 r0
    let t' := sszUpdate t with marker := 0x1234
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ r0 with marker := 0x1234 } : @Registry testPreset) := by
  native_decide

/-- Cached: replace the whole symbolic-cap list. Exercises rebuilding
the list field's subtree at the preset-resolved depth. -/
example :
    let t : TreeBacked Sha256 (@Registry testPreset) := TreeBacked.ofValue Sha256 r0
    let t' := sszUpdate t with validators := grownList
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ r0 with validators := grownList } : @Registry testPreset) := by
  native_decide

/-- Cached: both fields in one statement. -/
example :
    let t : TreeBacked Sha256 (@Registry testPreset) := TreeBacked.ofValue Sha256 r0
    let t' := sszUpdate t with
      validators := grownList,
      marker     := 0x9999
    let expected : @Registry testPreset :=
      { r0 with validators := grownList, marker := 0x9999 }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- Cached, through the user-facing `SSZ.FastBox`. -/
example :
    let box : SSZ.Box Sha256 (@Registry testPreset) := SSZ.FastBox r0
    let box' := sszUpdate box with validators := grownList
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256 ({ r0 with validators := grownList } : @Registry testPreset) := by
  native_decide

/-- Cached: a single element-index write into the symbolic-cap list.
The list element is a packed basic (`UInt64`), so the cached path
rebuilds the owning field's subtree at the preset-resolved depth (the
`projDrop` owner-rebuild path). The index form returns `Except`, so the
root is read through `.toOption.map`. -/
example :
    let t : TreeBacked Sha256 (@Registry testPreset) := TreeBacked.ofValue Sha256 r0
    let expected : @Registry testPreset :=
      { r0 with validators := r0.validators.set! 1 99 }
    (sszUpdate t with validators[1] := 99).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

/-- Uncached: a plain view rewrite, root by `native_decide`. -/
example :
    let t : UncachedSSZ Sha256 (@Registry testPreset) := UncachedSSZ.ofValue Sha256 r0
    let t' := sszUpdate t with marker := 0x1234
    t'.hashTreeRoot =
      SSZ.hashTreeRoot Sha256 ({ r0 with marker := 0x1234 } : @Registry testPreset) := by
  native_decide

/-- Uncached: the symbolic-cap list replacement. The uncached
`sszUpdate` reduces to `{ view := { t.view with validators := … } }`,
so its root is *definitionally* the spec root of the rewritten value. -/
example :
    let t : UncachedSSZ Sha256 (@Registry testPreset) := UncachedSSZ.ofValue Sha256 r0
    let t' := sszUpdate t with validators := grownList
    t'.hashTreeRoot =
      SSZ.hashTreeRoot Sha256 ({ r0 with validators := grownList } : @Registry testPreset) := rfl

end SizzLeanTests.PresetSymbolicCap
