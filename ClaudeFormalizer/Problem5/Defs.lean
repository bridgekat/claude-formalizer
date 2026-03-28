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
  ext x
  simp only [Subgroup.mem_conjBy]
  constructor
  · intro h
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [← this]
    exact H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg

/-- Double conjugation. -/
lemma Subgroup.conjBy_conjBy (K : Subgroup G) (g h : G) :
    (K.conjBy g).conjBy h = K.conjBy (h * g) := by
  ext x
  simp only [Subgroup.mem_conjBy]
  constructor
  · intro hx
    convert hx using 1; group
  · intro hx
    convert hx using 1; group

/-- Conjugating by 1 is the identity. -/
@[simp]
lemma Subgroup.conjBy_one (K : Subgroup G) : K.conjBy 1 = K := by
  ext x
  simp only [Subgroup.mem_conjBy, inv_one, one_mul, mul_one]

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
  rw [← H.conjBy_eq_of_mem hg]
  exact O.rel_conj g hKH

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
  classical
  suffices h : ∀ M : Subgroup G, O.rel M H →
      ∃ M₀ : Subgroup G, O.rel M₀ H ∧ ∀ K, O.rel K H → M₀ ≤ K from
    h H (O.rel_refl H)
  intro M
  apply (wellFounded_lt (α := Subgroup G)).induction
    (C := fun M => O.rel M H →
      ∃ M₀ : Subgroup G, O.rel M₀ H ∧ ∀ K, O.rel K H → M₀ ≤ K) M
  intro M ih hM
  by_cases hmin : ∀ K, O.rel K H → M ≤ K
  · exact ⟨M, hM, hmin⟩
  · push_neg at hmin
    obtain ⟨K, hKH, hKM⟩ := hmin
    have hinfH : O.rel (K ⊓ M) H := O.rel_inf hKH hM
    have hlt : K ⊓ M < M := lt_of_le_of_ne inf_le_right (fun heq => hKM (heq ▸ inf_le_left))
    exact ih (K ⊓ M) hlt hinfH

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
  -- Helper: conjBy is monotone
  have conjBy_mono : ∀ (A B : Subgroup G) (h : G), A ≤ B → A.conjBy h ≤ B.conjBy h := by
    intro A B h hAB x hx
    rw [Subgroup.mem_conjBy] at hx ⊢
    exact hAB hx
  apply le_antisymm
  · -- minAdmissible (H.conjBy g) ≤ (minAdmissible H).conjBy g
    exact O.minAdmissible_le (O.rel_conj g (O.minAdmissible_rel H))
  · -- (minAdmissible H).conjBy g ≤ minAdmissible (H.conjBy g)
    -- Conjugating minAdmissible (H.conjBy g) by g⁻¹ gives something admissible in H
    have h1 : O.rel ((O.minAdmissible (H.conjBy g)).conjBy g⁻¹) H := by
      have := O.rel_conj g⁻¹ (O.minAdmissible_rel (H.conjBy g))
      rwa [Subgroup.conjBy_conjBy, inv_mul_cancel, Subgroup.conjBy_one] at this
    -- By minimality: minAdmissible H ≤ (minAdmissible (H.conjBy g)).conjBy g⁻¹
    have h2 := O.minAdmissible_le h1
    -- Conjugate both sides by g
    have h3 := conjBy_mono _ _ g h2
    rwa [Subgroup.conjBy_conjBy, mul_inv_cancel, Subgroup.conjBy_one] at h3

/-! ### The O-index -/

/-- The **O-index** of `J`, defined as `[J : J_O]` where `J_O` is the
minimal O-admissible subgroup of `J`. -/
noncomputable def oIndex (J : Subgroup G) : ℕ :=
  (O.minAdmissible J).relIndex J

/-- The O-index is always positive. -/
theorem oIndex_pos (J : Subgroup G) : 0 < O.oIndex J := by
  unfold oIndex
  simp only [Subgroup.relIndex]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-- The O-index is invariant under conjugation. -/
theorem oIndex_conjBy (J : Subgroup G) (g : G) :
    O.oIndex (J.conjBy g) = O.oIndex J := by
  unfold oIndex
  rw [O.minAdmissible_conjBy J g]
  -- Now goal: ((minAdmissible J).conjBy g).relIndex (J.conjBy g) = (minAdmissible J).relIndex J
  -- conjBy g = map (conjMonoidHom g), and conjMonoidHom g is injective
  simp only [Subgroup.conjBy]
  exact Subgroup.relIndex_map_map_of_injective _ _ (fun x y hxy => by
    simp only [conjMonoidHom_apply] at hxy
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hxy]
    _ = y := by group)

/-- The O-index of the trivial group is 1. -/
theorem oIndex_bot : O.oIndex (⊥ : Subgroup G) = 1 := by
  unfold oIndex
  -- minAdmissible ⊥ ≤ ⊥, so minAdmissible ⊥ = ⊥
  have h : O.minAdmissible ⊥ = ⊥ := le_antisymm (O.minAdmissible_le_self ⊥) bot_le
  rw [h, Subgroup.relIndex_bot_right]

end MinAdmissible

end TransferSystem
