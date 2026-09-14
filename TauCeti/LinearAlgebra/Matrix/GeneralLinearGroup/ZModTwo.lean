/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The permutation action of `GL n R` on the nonzero vectors, and its faithfulness, are what the
-- isomorphism below upgrades to a bijection.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroVectors
-- `TauCeti.jordanGL` is the transvection whose permutation is computed below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `Equiv.permCongrHom` transports the symmetric group along a relabelling of the three vectors.
public import Mathlib.GroupTheory.Perm.Basic
-- Non-public: `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul` is used only inside a proof.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: `ZMod 2` is used as a field only inside the order computation.
import Mathlib.Algebra.Field.ZMod

/-!
# `GL₂(𝔽₂)` is the symmetric group on three letters

The plane `𝔽₂²` has exactly three nonzero vectors, and an invertible matrix permutes them. Over
`𝔽₂` that permutation representation

`GL₂(𝔽₂) → Equiv.Perm {v : Fin 2 → ZMod 2 // v ≠ 0}`

is faithful for the reason it is faithful over any commutative ring
(`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NonzeroVectors.lean`), and both groups have six
elements — `|GL₂(𝔽_q)| = (q² - 1) q (q - 1)` is `3 · 2 · 1` at `q = 2`, and `3! = 6` — so it is an
**isomorphism**: `TauCeti.gl2ZModTwoMulEquivPerm`. Relabelling the three vectors gives the familiar
form `GL₂(𝔽₂) ≅ S₃`, `TauCeti.gl2ZModTwoMulEquivPermFinThree`.

This is the degenerate case of the representation theory of `GL₂(𝔽_q)`: at `q = 2` the split torus
is trivial, so there are no split semisimple classes and no principal series with distinct
characters, and the character table of `GL₂(𝔽₂)` is that of `S₃` rather than an instance of the
uniform four-family picture. The isomorphism proved here is what lets that case be checked against
the symmetric group instead of against the general family.

The isomorphism is pinned, not merely asserted: `TauCeti.gl2ZModTwoMulEquivPerm_apply_coe` evaluates
it as multiplication of a vector by the matrix, and
`TauCeti.toPermHom_jordanGL_one_one_zmodTwo` computes the permutation of the transvection
`!![1, 1; 0, 1]` to be the transposition exchanging `(0, 1)` and `(1, 1)`.

## Main definitions and results

* `TauCeti.card_ne_zero_pi_zmodTwo`: the plane over `𝔽₂` has three nonzero vectors.
* `TauCeti.natCard_GL_fin_two_zmodTwo`: `|GL₂(𝔽₂)| = 6`.
* `TauCeti.gl2ZModTwoMulEquivPerm`: **`GL₂(𝔽₂)` is the symmetric group on the three nonzero
  vectors**, with `TauCeti.gl2ZModTwoMulEquivPerm_apply_coe` evaluating it.
* `TauCeti.toPermHom_jordanGL_one_one_zmodTwo`: the transvection `!![1, 1; 0, 1]` acts as a
  transposition.
* `TauCeti.gl2ZModTwoMulEquivPermFinThree`: **`GL₂(𝔽₂) ≅ S₃`**, the same isomorphism after a
  relabelling of the three nonzero vectors by `Fin 3`.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, where `GL₂(𝔽₂) ≅ S₃` is the separately-checked degenerate case of the character table of
  `GL₂(𝔽_q)`.
-/

public section

open Matrix

namespace TauCeti

/-- **The plane over `𝔽₂` has three nonzero vectors**, namely `(1, 0)`, `(0, 1)` and `(1, 1)`. -/
theorem card_ne_zero_pi_zmodTwo : Fintype.card {v : Fin 2 → ZMod 2 // v ≠ 0} = 3 := by
  decide

/-- **`GL₂(𝔽₂)` has six elements**, the value `(q² - 1) · q (q - 1)` of
`TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul` at `q = 2`. -/
theorem natCard_GL_fin_two_zmodTwo : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  have h := natCard_GL_fin_two_eq_sq_sub_one_mul (ZMod 2)
  rwa [ZMod.card] at h

private theorem card_perm_ne_zero_pi_zmodTwo :
    Fintype.card (Equiv.Perm {v : Fin 2 → ZMod 2 // v ≠ 0}) = 6 := by
  rw [Fintype.card_perm, card_ne_zero_pi_zmodTwo]
  rfl

private theorem toPermHom_zmodTwo_injective :
    Function.Injective
      (MulAction.toPermHom (GL (Fin 2) (ZMod 2)) {v : Fin 2 → ZMod 2 // v ≠ 0}) := by
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective

private theorem toPermHom_zmodTwo_bijective :
    Function.Bijective
      (MulAction.toPermHom (GL (Fin 2) (ZMod 2)) {v : Fin 2 → ZMod 2 // v ≠ 0}) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨toPermHom_zmodTwo_injective, ?_⟩
  rw [card_perm_ne_zero_pi_zmodTwo, ← Nat.card_eq_fintype_card, natCard_GL_fin_two_zmodTwo]

/-- **`GL₂(𝔽₂)` is the symmetric group on the three nonzero vectors of `𝔽₂²`.** The permutation
representation on the nonzero vectors is injective over any commutative ring; over `𝔽₂` the two
groups have the same order `6`, so it is bijective.

The isomorphism is `MulAction.toPermHom`, so it is evaluated by
`TauCeti.gl2ZModTwoMulEquivPerm_apply_coe`: no property of the construction beyond bijectivity is
hidden in it. -/
noncomputable def gl2ZModTwoMulEquivPerm :
    GL (Fin 2) (ZMod 2) ≃* Equiv.Perm {v : Fin 2 → ZMod 2 // v ≠ 0} :=
  MulEquiv.ofBijective _ toPermHom_zmodTwo_bijective

/-- The isomorphism `TauCeti.gl2ZModTwoMulEquivPerm` sends an invertible matrix to the permutation
of the nonzero vectors it induces: it multiplies a vector by that matrix. -/
@[simp]
theorem gl2ZModTwoMulEquivPerm_apply_coe (g : GL (Fin 2) (ZMod 2))
    (v : {v : Fin 2 → ZMod 2 // v ≠ 0}) :
    ((gl2ZModTwoMulEquivPerm g v : {v : Fin 2 → ZMod 2 // v ≠ 0}) : Fin 2 → ZMod 2) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ (v : Fin 2 → ZMod 2) :=
  (rfl)

/-- **The transvection `!![1, 1; 0, 1]` acts as a transposition**: it fixes `(1, 0)` and exchanges
`(0, 1)` with `(1, 1)`. Together with the observation that the three nonzero vectors are permuted
faithfully, this exhibits the isomorphism concretely; in particular the image of `GL₂(𝔽₂)` contains
a transposition, as it must, the two groups being equal in order. -/
theorem toPermHom_jordanGL_one_one_zmodTwo :
    MulAction.toPermHom (GL (Fin 2) (ZMod 2)) {v : Fin 2 → ZMod 2 // v ≠ 0} (jordanGL 1 1) =
      Equiv.swap ⟨![0, 1], by decide⟩ ⟨![1, 1], by decide⟩ := by
  refine Equiv.ext fun v => Subtype.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_toPermHom_apply_ne_zero, coe_jordanGL, Units.val_one]
  revert v
  decide

/-- **`GL₂(𝔽₂) ≅ S₃`.** The isomorphism `TauCeti.gl2ZModTwoMulEquivPerm` with the three nonzero
vectors of `𝔽₂²` relabelled by `Fin 3`. The relabelling is an arbitrary chosen bijection, so unlike
`TauCeti.gl2ZModTwoMulEquivPerm` this isomorphism has no canonical description on elements; the
nonzero-vector form is the one to compute with. -/
noncomputable def gl2ZModTwoMulEquivPermFinThree :
    GL (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3) :=
  gl2ZModTwoMulEquivPerm.trans (Fintype.equivFinOfCardEq card_ne_zero_pi_zmodTwo).permCongrHom

end TauCeti
