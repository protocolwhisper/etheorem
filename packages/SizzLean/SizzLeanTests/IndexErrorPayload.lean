import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.Update

/-!
# `SizzLeanTests.IndexErrorPayload`: `IndexError` carries idx and bound

Acceptance gates for change 4: an out-of-range index-form `sszGet` /
`sszUpdate` rejects with `IndexError.indexError idx bound` carrying the real
offending index and the owner's current length, not a payload-free tag. A
consumer lifting the miss then reports `outOfBounds idx bound` with real
numbers.

The reject value is checked directly: `IndexError` has `DecidableEq`, so the
read path (whose `.ok` payload is a basic type) compares whole, and the write
paths compare through `errOf`, which projects out the error so the cache
value's lack of `DecidableEq` is irrelevant. The uncached and box-on-uncached
paths reduce in the kernel (`decide`); the cached paths build an FFI-hashed
tree, so they use `native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.IndexErrorPayload

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr

/-- A container with a basic-element list field. Three elements, so any index
`≥ 3` is out of range. -/
structure S where
  xs     : SSZList UInt64 8
  marker : UInt64
deriving DecidableEq, Inhabited, SSZRepr

private def s0 : S := { xs := ⟨#[10, 20, 30], by decide⟩, marker := 0 }

/-- Project the error out of an `Except IndexError _`. Lets the write-path
checks below compare the reject value without a `DecidableEq` on the cache
type in the `.ok` arm. -/
private def errOf {α : Type} : Except IndexError α → Option IndexError
  | .ok _    => none
  | .error e => some e

/-! ## Read path (`sszGet`): the miss carries the real index and bound

`sszGet b xs[i]` returns `Except IndexError UInt64`. `Except` carries no
`DecidableEq`, so the error is compared through `errOf` and the success
through `Except.toOption`. -/

/-- Out of range: index `7`, bound `3`. -/
example : errOf (sszGet (UncachedSSZ.ofValue Sha256 s0) xs[7])
    = some (IndexError.indexError 7 3) := by decide

/-- In range: the read succeeds with the element. -/
example : (sszGet (UncachedSSZ.ofValue Sha256 s0) xs[2]).toOption
    = some 30 := by decide

/-! ## Write path (`sszUpdate`): the issue-time guard carries idx and bound -/

/-- Uncached: out-of-range write rejects with the real index and bound. -/
example : errOf (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with xs[5] := 99)
    = some (IndexError.indexError 5 3) := by decide

/-- Uncached: an in-range write does not reject. -/
example : errOf (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with xs[1] := 99)
    = none := by decide

/-- Cached: same reject value through the Merkle-aware path. -/
example : errOf (sszUpdate (TreeBacked.ofValue Sha256 s0) with xs[5] := 99)
    = some (IndexError.indexError 5 3) := by native_decide

/-- Box on the uncached flavour (`PureBox`): the reject rides out through the
two-arm match's `.map`. -/
example : errOf (sszUpdate (SSZ.PureBox s0) with xs[5] := 99)
    = some (IndexError.indexError 5 3) := by decide

/-- Box on the cached flavour (`FastBox`): same value, FFI path. -/
example : errOf (sszUpdate (SSZ.FastBox s0) with xs[5] := 99)
    = some (IndexError.indexError 5 3) := by native_decide

/-! ## Multi-clause guard: the *first* out-of-range index wins (program order)

The issue-time guard chains the per-clause checks in source order and
short-circuits on the first failure, so the reported index/bound are the
first offending clause's. -/

/-- First clause in range, second out of range: the second's `5 3` surfaces. -/
example : errOf (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with
      xs[1] := 7, xs[5] := 9) = some (IndexError.indexError 5 3) := by decide

/-- Both out of range: the *first* clause's `6 3` surfaces, not the second's. -/
example : errOf (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with
      xs[6] := 7, xs[5] := 9) = some (IndexError.indexError 6 3) := by decide

end SizzLeanTests.IndexErrorPayload
