/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Transfer Systems and the O-Index

This file defines transfer systems on finite groups (Balchin–Barnes–Roitzheim),
the minimal admissible subgroup, and the O-index. These are the key
combinatorial objects for the O-slice connectivity characterization theorem.

## Main definitions

* `TransferSystem G` — An incomplete transfer system on a group G
* `TransferSystem.minAdmissible O H` — The minimal O-admissible subgroup of H
* `TransferSystem.oIndex O J` — The O-index [J : J_O]

## References

* [Balchin–Barnes–Roitzheim, *N_∞-operads and associahedra*, Definition 2.4]
* [Hill–Hopkins–Ravenel, *On the nonexistence of elements of Kervaire invariant one*]
* [Hill–Yarnall, *A new formulation of the equivariant slice filtration*]
-/

variable {G : Type*} [Group G]

/-! ### Conjugation helpers -/

/-- The `MonoidHom` sending `x ↦ g * x * g⁻¹`. -/
def conjMonoidHom (g : G) : G →* G where
  toFun x := g * x * g⁻¹
  map_one' := by group
  map_mul' _ _ := by group

@[simp]
lemma conjMonoidHom_apply (g x : G) : conjMonoidHom g x = g * x * g⁻¹ := rfl

lemma conjMonoidHom_comp (g h : G) :
    (conjMonoidHom g).comp (conjMonoidHom h) = conjMonoidHom (g * h) := by
  ext x; simp [conjMonoidHom_apply]; group

lemma conjMonoidHom_one : conjMonoidHom (1 : G) = MonoidHom.id G := by
  ext x; simp [conjMonoidHom_apply]

/-- The subgroup `g K g⁻¹`, i.e., the image of `K` under conjugation by `g`. -/
def Subgroup.conjBy (K : Subgroup G) (g : G) : Subgroup G :=
  K.map (conjMonoidHom g)

@[simp]
lemma Subgroup.mem_conjBy {K : Subgroup G} {g x : G} :
    x ∈ K.conjBy g ↔ g⁻¹ * x * g ∈ K := by
  simp only [Subgroup.conjBy, Subgroup.mem_map, conjMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; convert hy using 1; group
  · intro h; exact ⟨g⁻¹ * x * g, h, by group⟩

/-- Conjugating by an element of a subgroup fixes the subgroup. -/
lemma Subgroup.conjBy_eq_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.conjBy g = H := by
  sorry

/-- Double conjugation. -/
lemma Subgroup.conjBy_conjBy (K : Subgroup G) (g h : G) :
    (K.conjBy g).conjBy h = K.conjBy (h * g) := by
  sorry

/-- Conjugating by 1 is the identity. -/
@[simp]
lemma Subgroup.conjBy_one (K : Subgroup G) : K.conjBy 1 = K := by
  sorry

/-! ### Transfer system definition -/

/-- A **transfer system** on a group `G` is a relation on `Subgroup G` that refines
inclusion and satisfies conjugation invariance and a restriction axiom.
This models an incomplete transfer system associated to an `N_∞` operad
(Balchin–Barnes–Roitzheim, Definition 2.4). -/
structure TransferSystem (G : Type*) [Group G] where
  /-- The admissibility relation: `rel K H` means K is O-admissible in H. -/
  rel : Subgroup G → Subgroup G → Prop
  /-- Admissibility refines subgroup inclusion. -/
  rel_le : ∀ {K H : Subgroup G}, rel K H → K ≤ H
  /-- Every subgroup is admissible in itself. -/
  rel_refl : ∀ (H : Subgroup G), rel H H
  /-- Admissibility is transitive. -/
  rel_trans : ∀ {K L H : Subgroup G}, rel K L → rel L H → rel K H
  /-- Conjugation invariance: admissibility is preserved under conjugation. -/
  rel_conj : ∀ {K H : Subgroup G} (g : G), rel K H →
    rel (K.conjBy g) (H.conjBy g)
  /-- Restriction axiom: if `K ⊆_O H` and `J ≤ H`, then `K ⊓ J ⊆_O J`. -/
  rel_restrict : ∀ {K H : Subgroup G} (J : Subgroup G),
    rel K H → J ≤ H → rel (K ⊓ J) J

namespace TransferSystem

variable (O : TransferSystem G)

/-! ### Closure under intersection -/

/-- Binary intersection preserves admissibility: if `K₁ ⊆_O H` and `K₂ ⊆_O H`,
then `K₁ ⊓ K₂ ⊆_O H`. -/
theorem rel_inf {H K₁ K₂ : Subgroup G} (h₁ : O.rel K₁ H) (h₂ : O.rel K₂ H) :
    O.rel (K₁ ⊓ K₂) H := by
  -- K₂ ≤ H by rel_le, so by restriction K₁ ⊓ K₂ ⊆_O K₂
  -- Then by transitivity K₁ ⊓ K₂ ⊆_O H
  exact O.rel_trans (O.rel_restrict K₂ h₁ (O.rel_le h₂)) h₂

/-- Conjugation by an element of `H` preserves admissibility within `H`. -/
theorem rel_conjBy_of_mem {K H : Subgroup G} (hKH : O.rel K H)
    {g : G} (hg : g ∈ H) : O.rel (K.conjBy g) H := by
  sorry

/-! ### Minimal admissible subgroup -/

section MinAdmissible

variable [Fintype G] [DecidableEq G]

/-- The set of O-admissible subgroups of `H` is nonempty. -/
theorem admissible_nonempty (H : Subgroup G) :
    ∃ K : Subgroup G, O.rel K H :=
  ⟨H, O.rel_refl H⟩

/-- There exists a unique minimal O-admissible subgroup of `H`.
This uses finiteness of `G` and closure of admissibility under `⊓`. -/
theorem minAdmissible_exists (H : Subgroup G) :
    ∃ M : Subgroup G, O.rel M H ∧ ∀ K, O.rel K H → M ≤ K := by
  sorry

/-- The minimal O-admissible subgroup of `H`. -/
noncomputable def minAdmissible (H : Subgroup G) : Subgroup G :=
  (O.minAdmissible_exists H).choose

/-- The minimal admissible subgroup is admissible in `H`. -/
theorem minAdmissible_rel (H : Subgroup G) : O.rel (O.minAdmissible H) H :=
  (O.minAdmissible_exists H).choose_spec.1

/-- The minimal admissible subgroup is below every admissible subgroup of `H`. -/
theorem minAdmissible_le {H K : Subgroup G} (hK : O.rel K H) :
    O.minAdmissible H ≤ K :=
  (O.minAdmissible_exists H).choose_spec.2 K hK

/-- The minimal admissible subgroup is a subgroup of `H`. -/
theorem minAdmissible_le_self (H : Subgroup G) : O.minAdmissible H ≤ H :=
  O.rel_le (O.minAdmissible_rel H)

/-- Conjugation invariance of `minAdmissible`:
`(gHg⁻¹)_O = g · H_O · g⁻¹`. -/
theorem minAdmissible_conjBy (H : Subgroup G) (g : G) :
    O.minAdmissible (H.conjBy g) = (O.minAdmissible H).conjBy g := by
  sorry

/-! ### The O-index -/

/-- The **O-index** of `J`, defined as `[J : J_O]` where `J_O` is the
minimal O-admissible subgroup of `J`. -/
noncomputable def oIndex (J : Subgroup G) : ℕ :=
  (O.minAdmissible J).relIndex J

/-- The O-index is always positive. -/
theorem oIndex_pos (J : Subgroup G) : 0 < O.oIndex J := by
  sorry

/-- The O-index is invariant under conjugation. -/
theorem oIndex_conjBy (J : Subgroup G) (g : G) :
    O.oIndex (J.conjBy g) = O.oIndex J := by
  sorry

/-- The O-index of the trivial group is 1. -/
theorem oIndex_bot : O.oIndex (⊥ : Subgroup G) = 1 := by
  sorry

end MinAdmissible

end TransferSystem
