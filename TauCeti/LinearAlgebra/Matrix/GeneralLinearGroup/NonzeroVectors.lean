/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.mulVec` as the scalar action of a square matrix on a vector, which the action below
-- restricts.
public import Mathlib.LinearAlgebra.Matrix.Action
-- `GL n R` and its coercion to matrices occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `MulAction.toPermHom` is the permutation representation the faithfulness instance below feeds.
public import Mathlib.Algebra.Group.Action.End

/-!
# The action of a general linear group on the nonzero vectors

An invertible matrix carries nonzero vectors to nonzero vectors, so the `Matrix.mulVec` action of
`GL n R` on `n → R` restricts to the subtype of nonzero vectors. This file records that restricted
action and proves it **faithful**: two invertible matrices agreeing on every nonzero vector agree on
the zero vector for free, hence agree everywhere, hence are equal.

Through `MulAction.toPermHom` the faithful action is a group embedding

`GL n R ↪ Equiv.Perm {v : n → R // v ≠ 0}`,

the **permutation representation on the nonzero vectors**. Over a finite field the target is finite,
and comparing orders can make the embedding an isomorphism; that is how
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ZModTwo.lean` identifies `GL₂(𝔽₂)` with the
symmetric group on three letters.

## Main definitions and results

* `Matrix.GeneralLinearGroup.mulActionNeZero`: the action of `GL n R` on the nonzero vectors of
  `n → R`.
* `Matrix.GeneralLinearGroup.faithfulSMulNeZero`: that action is faithful, so `MulAction.toPermHom`
  embeds `GL n R` into the symmetric group on the nonzero vectors.

## Implementation notes

The ambient action is Mathlib's `Module (Matrix n n R) (n → R)` of
`Mathlib/LinearAlgebra/Matrix/Action.lean`, transported to the units by `Units.instMulAction`; no
new action on `n → R` is introduced here, only its restriction to a subtype.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **An invertible matrix kills only the zero vector.** The inverse matrix undoes the
multiplication, so `g • v` vanishes exactly when `v` does. -/
@[simp]
theorem smul_eq_zero_iff (g : GL n R) {v : n → R} : g • v = (0 : n → R) ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  calc v = (g⁻¹ * g) • v := by rw [inv_mul_cancel, one_smul]
    _ = g⁻¹ • (g • v) := mul_smul _ _ _
    _ = 0 := by rw [h, smul_zero]

/-- **A general linear group acts on the nonzero vectors.** The restriction of the `Matrix.mulVec`
action of `GL n R` on `n → R` to the subtype of nonzero vectors, which is preserved because the
matrix is invertible (`Matrix.GeneralLinearGroup.smul_eq_zero_iff`). -/
instance mulActionNeZero : MulAction (GL n R) {v : n → R // v ≠ 0} where
  smul g v := ⟨g • (v : n → R), fun h => v.2 ((smul_eq_zero_iff g).mp h)⟩
  one_smul v := Subtype.ext (one_smul _ (v : n → R))
  mul_smul g h v := Subtype.ext (mul_smul g h (v : n → R))

/-- The action on nonzero vectors is the ambient action, read on the underlying vector. -/
@[simp]
theorem coe_smul_ne_zero (g : GL n R) (v : {v : n → R // v ≠ 0}) :
    ((g • v : {v : n → R // v ≠ 0}) : n → R) = g • (v : n → R) :=
  rfl

/-- **The action on the nonzero vectors is faithful.** Two matrices agreeing on every nonzero vector
agree on the zero vector as well, so they agree on all of `n → R` and are therefore equal
(`Matrix.ext_iff_mulVec`). No hypothesis on `R` is needed: over the zero ring there are no nonzero
vectors, but there is also only one matrix.

Through `MulAction.toPerm_injective` this makes `MulAction.toPermHom` an embedding of `GL n R` into
the symmetric group on the nonzero vectors of `n → R`. -/
instance faithfulSMulNeZero : FaithfulSMul (GL n R) {v : n → R // v ≠ 0} where
  eq_of_smul_eq_smul {g h} hgh := by
    refine Units.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_)
    rcases eq_or_ne v 0 with rfl | hv
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
    · exact congrArg Subtype.val (hgh ⟨v, hv⟩)

/-- **The permutation attached to an invertible matrix**, read on the underlying vector: it
multiplies by the matrix. -/
@[simp]
theorem coe_toPermHom_apply_ne_zero (g : GL n R) (v : {v : n → R // v ≠ 0}) :
    ((MulAction.toPermHom (GL n R) {v : n → R // v ≠ 0} g v : {v : n → R // v ≠ 0}) : n → R) =
      (g : Matrix n n R) *ᵥ (v : n → R) :=
  rfl

end Matrix.GeneralLinearGroup
