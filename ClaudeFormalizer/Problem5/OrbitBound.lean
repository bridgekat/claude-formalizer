/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClaudeFormalizer.Problem5.Defs

/-!
# The Orbit Counting Lemma

This file proves the key combinatorial result: for a transfer system `O`,
if `K` is O-admissible in `H` and `J ≤ H`, then every `J`-orbit on the
coset space `H/K` has cardinality at most `||J||_O`. As a consequence,
the number of `J`-orbits on `H/K` is at least `⌈[H:K] / ||J||_O⌉`.

## Main results

* `TransferSystem.stabilizerAdmissible` — The stabilizer `J ⊓ gKg⁻¹` is
  O-admissible in `J`
* `TransferSystem.relIndex_inf_conjBy_le_oIndex` — `[J : J ⊓ gKg⁻¹] ≤ ||J||_O`
* `orbit_card_le_oIndex` — Every orbit has cardinality `≤ ||J||_O`
* `nOrbits_mul_oIndex_ge` — `(# orbits) · ||J||_O ≥ [H:K]`

## References

* [Hill–Yarnall, Theorem 2.5] for the analogous result in the complete case.
-/

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace TransferSystem

variable (O : TransferSystem G)

/-! ### Stabilizer admissibility -/

/-- **Stabilizer admissibility**: if `K ⊆_O H`, `J ≤ H`, and `g ∈ H`, then
`J ⊓ gKg⁻¹ ⊆_O J`.

This is the key group-theoretic lemma. The proof uses:
1. `K ⊆_O H` ⟹ `gKg⁻¹ ⊆_O gHg⁻¹` (conjugation axiom)
2. `g ∈ H` ⟹ `gHg⁻¹ = H` (normality-like property for elements of H)
3. `gKg⁻¹ ⊆_O H` and `J ≤ H` ⟹ `gKg⁻¹ ⊓ J ⊆_O J` (restriction axiom)
4. `gKg⁻¹ ⊓ J = J ⊓ gKg⁻¹` (commutativity of `⊓`) -/
theorem stabilizerAdmissible {K H J : Subgroup G} (hKH : O.rel K H)
    (hJH : J ≤ H) {g : G} (hg : g ∈ H) :
    O.rel (J ⊓ K.conjBy g) J := by
  -- K.conjBy g ⊆_O H (by conjugation invariance + g ∈ H)
  have h1 : O.rel (K.conjBy g) H := O.rel_conjBy_of_mem hKH hg
  -- (K.conjBy g) ⊓ J ⊆_O J (by restriction, since J ≤ H)
  have h2 : O.rel (K.conjBy g ⊓ J) J := O.rel_restrict J h1 hJH
  -- J ⊓ K.conjBy g = K.conjBy g ⊓ J
  rwa [inf_comm] at h2

/-- `J_O ≤ J ⊓ gKg⁻¹`: the minimal admissible subgroup of `J` is
contained in the stabilizer. -/
theorem minAdmissible_le_inf_conjBy {K H J : Subgroup G} (hKH : O.rel K H)
    (hJH : J ≤ H) {g : G} (hg : g ∈ H) :
    O.minAdmissible J ≤ J ⊓ K.conjBy g :=
  O.minAdmissible_le (O.stabilizerAdmissible hKH hJH hg)

/-- **Index bound**: `[J : J ⊓ gKg⁻¹] ≤ ||J||_O`.

Since `J_O ≤ J ⊓ gKg⁻¹ ≤ J`, the index `[J : J ⊓ gKg⁻¹]` is bounded
above by `[J : J_O] = ||J||_O`. -/
theorem relIndex_inf_conjBy_le_oIndex {K H J : Subgroup G} (hKH : O.rel K H)
    (hJH : J ≤ H) {g : G} (hg : g ∈ H) :
    (J ⊓ K.conjBy g).relIndex J ≤ O.oIndex J := by
  -- minAdmissible J ≤ J ⊓ K.conjBy g
  have hle : O.minAdmissible J ≤ J ⊓ K.conjBy g :=
    O.minAdmissible_le_inf_conjBy hKH hJH hg
  -- By monotonicity: (J ⊓ K.conjBy g).relIndex J ≤ (minAdmissible J).relIndex J
  unfold oIndex
  exact Subgroup.relIndex_le_of_le_left hle (by
    simp only [Subgroup.relIndex]
    exact Subgroup.FiniteIndex.index_ne_zero)

end TransferSystem

/-! ### Orbit counting on coset spaces -/

section OrbitCounting

open MulAction

set_option maxHeartbeats 800000 in
/-- Every `J`-orbit on `H/K` has cardinality at most `||J||_O`.

The stabilizer of a coset `xK` under the left `J`-action is `J ∩ xKx⁻¹`.
By `stabilizerAdmissible`, this intersection is O-admissible in `J`, hence
contains `J_O`. By orbit-stabilizer, the orbit has size
`[J : J ∩ xKx⁻¹] ≤ [J : J_O] = ||J||_O`. -/
theorem orbit_card_le_oIndex (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H)
    (q : ↥H ⧸ K.subgroupOf H) :
    Nat.card (orbit (↥(J.subgroupOf H)) q) ≤ O.oIndex J := by
  -- Get a representative x : ↥H for the coset q
  obtain ⟨x, rfl⟩ := @QuotientGroup.mk_surjective _ _ (K.subgroupOf H) q
  -- Orbit size = stabilizer index (orbit-stabilizer theorem)
  rw [Nat.card_congr (orbitEquivQuotientStabilizer _ _)]
  set M := O.minAdmissible J
  -- Key step: (M.subgroupOf H).subgroupOf (J.subgroupOf H) ≤ stabilizer of the coset xK
  -- because every m ∈ minAdmissible J satisfies m ∈ J ⊓ K.conjBy x,
  -- hence m fixes the coset xK under left multiplication.
  have h_incl : (M.subgroupOf H).subgroupOf (J.subgroupOf H) ≤
      stabilizer (↥(J.subgroupOf H)) ((QuotientGroup.mk (s := K.subgroupOf H)) x) := by
    intro ⟨⟨m, hm_H⟩, hm_J⟩ hm_M
    simp only [Subgroup.mem_subgroupOf] at hm_M hm_J
    rw [mem_stabilizer_iff]
    show (QuotientGroup.mk (s := K.subgroupOf H)) (⟨m, hm_H⟩ * x) =
         (QuotientGroup.mk (s := K.subgroupOf H)) x
    rw [QuotientGroup.eq]
    simp only [Subgroup.mem_subgroupOf]
    -- Simplify the quotient equality condition
    have key : ((⟨m, hm_H⟩ : ↥H) * x)⁻¹ * x = ⟨(x : G)⁻¹ * m⁻¹ * (x : G),
      H.mul_mem (H.mul_mem (H.inv_mem x.2) (H.inv_mem hm_H)) x.2⟩ := by
      ext; push_cast; group
    simp only [key]
    show (x : G)⁻¹ * m⁻¹ * (x : G) ∈ K
    -- m ∈ minAdmissible J ≤ J ⊓ K.conjBy x, so m ∈ K.conjBy x
    have hmin_le := O.minAdmissible_le_inf_conjBy hKH hJH x.2
    have hm_conj : m ∈ K.conjBy (x : G) := (Subgroup.mem_inf.mp (hmin_le hm_M)).2
    rw [Subgroup.mem_conjBy] at hm_conj
    -- x⁻¹ * m * x ∈ K, so x⁻¹ * m⁻¹ * x = (x⁻¹ * m * x)⁻¹ ∈ K
    have := K.inv_mem hm_conj
    convert this using 1; group
  -- Index bound: stabilizer.index ≤ oIndex J
  calc (stabilizer (↥(J.subgroupOf H)) ((QuotientGroup.mk (s := K.subgroupOf H)) x)).index
      ≤ ((M.subgroupOf H).subgroupOf (J.subgroupOf H)).index := Subgroup.index_antitone h_incl
    _ = (M.subgroupOf H).relIndex (J.subgroupOf H) := rfl
    _ = M.relIndex J := Subgroup.relIndex_subgroupOf hJH
    _ = O.oIndex J := rfl

/-- **Orbit counting theorem**: `(# J-orbits on H/K) · ||J||_O ≥ [H:K]`.

Partitioning `H/K` into `J`-orbits, each of size `≤ ||J||_O`:
`[H:K] = Σ |orbit_i| ≤ (# orbits) · ||J||_O`. -/
theorem nOrbits_mul_oIndex_ge (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H) :
    Nat.card (orbitRel.Quotient (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)) *
      O.oIndex J ≥ K.relIndex H := by
  rw [ge_iff_le, Subgroup.relIndex, Subgroup.index]
  haveI : Fintype (orbitRel.Quotient (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)) :=
    Fintype.ofFinite _
  -- Decompose H/K into the disjoint union of J-orbits
  rw [Nat.card_congr (selfEquivSigmaOrbits' (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)),
      Nat.card_sigma]
  -- Sum of orbit sizes ≤ (# orbits) * oIndex J
  conv_rhs => rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← smul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro ω _
  -- Each orbit has size ≤ oIndex J
  rw [Nat.card_congr (Equiv.setCongr (orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq'))]
  exact orbit_card_le_oIndex O hKH hKle hJH ω.out

/-- **Orbit counting corollary**: `# J-orbits ≥ ⌈[H:K] / ||J||_O⌉`.

This is the form used in the main theorem. -/
theorem nOrbits_ge_ceil_div (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H) :
    (Nat.card (orbitRel.Quotient (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)) : ℤ) ≥
      ⌈((K.relIndex H : ℚ) / (O.oIndex J : ℚ))⌉ := by
  -- From nOrbits_mul_oIndex_ge: nOrbits * oIndex J ≥ relIndex
  have h := nOrbits_mul_oIndex_ge O hKH hKle hJH
  -- So (nOrbits : ℤ) ≥ ⌈relIndex / oIndex⌉
  rw [ge_iff_le, Int.ceil_le]
  rw [div_le_iff₀ (Nat.cast_pos.mpr (O.oIndex_pos J) : (0 : ℚ) < (O.oIndex J : ℚ))]
  push_cast
  exact_mod_cast h

end OrbitCounting
