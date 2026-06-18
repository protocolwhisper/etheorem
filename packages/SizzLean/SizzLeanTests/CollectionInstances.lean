import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.CollectionInstances`: `Inhabited` / `Ord` / `Hashable`

Acceptance gates for the library-provided default / ordering / hashing
instances on the SSZ collection types (`SSZList`, `Bitlist`, `Bitvector`).

* `Inhabited` (change 2): `default` resolves for `SSZList` / `Bitlist` and is
  the empty collection. A container's genesis anchor needs every field type
  inhabited, so these belong with the type, not in a downstream consumer.
* `Ord` / `Hashable` (change 3): resolve for all three collection types,
  ordering lexicographically over the underlying array and hashing its
  elements. A container whose fields are all SSZ types then picks up `Ord` /
  `Hashable` from Lean's standard `deriving` with no per-type escape hatch,
  shown by `AllSSZ` below.

`Ord` / `Hashable` for the `Array`-backed types reduce through well-founded
recursion (`Array.compareLex`), so the behavioural checks use `native_decide`
rather than kernel `decide`. The resolution checks are plain `inferInstance` /
`rfl`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.CollectionInstances

open SizzLean SizzLean.Repr

/-! ## Change 2: `Inhabited` resolves; the default is the empty collection -/

example : (default : SSZList UInt64 8).val = #[] := rfl
example : (default : Bitlist 8).val = #[] := rfl
example : (default : SSZList UInt64 8).val.size = 0 := rfl

/-- `Bitvector` derives `Inhabited` (the all-zero vector), so a container with
a `Bitvector` field is inhabited too. -/
example : Inhabited (Bitvector 16) := inferInstance

/-! ## Change 3: `Ord` resolves and orders lexicographically -/

example : Ord (SSZList UInt64 8) := inferInstance
example : Ord (Bitlist 8) := inferInstance
example : Ord (Bitvector 16) := inferInstance

/-- Element-wise: differing at the second element orders by it. -/
example :
    compare (⟨#[1, 2], by decide⟩ : SSZList UInt64 8) ⟨#[1, 3], by decide⟩
      = Ordering.lt := by native_decide

/-- Equal arrays compare equal. -/
example :
    compare (⟨#[1, 2], by decide⟩ : SSZList UInt64 8) ⟨#[1, 2], by decide⟩
      = Ordering.eq := by native_decide

/-- A shorter prefix orders before its extension (`Array` lex). -/
example :
    compare (⟨#[1], by decide⟩ : SSZList UInt64 8) ⟨#[1, 2], by decide⟩
      = Ordering.lt := by native_decide

/-- `Bitlist` orders over its bit array. -/
example :
    compare (⟨#[true, false], by decide⟩ : Bitlist 8) ⟨#[true, true], by decide⟩
      = Ordering.lt := by native_decide

/-- `Bitvector` orders numerically through `BitVec`'s own `Ord`. -/
example : compare (⟨3#16⟩ : Bitvector 16) ⟨5#16⟩ = Ordering.lt := by native_decide

/-! ## Change 3: `Hashable` resolves and computes -/

example : Hashable (SSZList UInt64 8) := inferInstance
example : Hashable (Bitlist 8) := inferInstance
example : Hashable (Bitvector 16) := inferInstance

/-- Two arrays built from the same elements hash equally (the instance folds
the element hashes of the underlying array). -/
example :
    hash (⟨#[1, 2, 3], by decide⟩ : SSZList UInt64 8)
      = hash (⟨(#[1, 2] ++ #[3]), by decide⟩ : SSZList UInt64 8) := by native_decide

example :
    hash (⟨#[true, false], by decide⟩ : Bitlist 8)
      = hash (⟨#[true, false], by decide⟩ : Bitlist 8) := by native_decide

/-! ## A container whose fields are all SSZ types gets `Ord` / `Hashable`

Lean's standard `deriving Ord, Hashable` generates field-wise comparison /
hashing that requires `Ord` / `Hashable` on each field type. With the
collection-type instances above in scope, an all-SSZ-field container derives
both with no per-field escape hatch. The `deriving` clause compiling *is* the
test; the examples confirm the result computes. -/
structure AllSSZ where
  xs : SSZList UInt64 8
  bs : Bitlist 8
  bv : Bitvector 16
deriving DecidableEq, Ord, Hashable, SSZRepr

private def a0 : AllSSZ :=
  { xs := ⟨#[1, 2], by decide⟩, bs := ⟨#[true], by decide⟩, bv := ⟨7#16⟩ }

private def a1 : AllSSZ :=
  { xs := ⟨#[1, 3], by decide⟩, bs := ⟨#[true], by decide⟩, bv := ⟨7#16⟩ }

example : compare a0 a0 = Ordering.eq := by native_decide
example : compare a0 a1 = Ordering.lt := by native_decide
example : hash a0 = hash a0 := by native_decide

end SizzLeanTests.CollectionInstances
