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
  sorry

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
  sorry

end TransferSystem

/-! ### Orbit counting on coset spaces -/

section OrbitCounting

open MulAction

/-- Every `J`-orbit on `H/K` has cardinality at most `||J||_O`.

The stabilizer of a coset `xK` under the left `J`-action is `J ∩ xKx⁻¹`.
By `stabilizerAdmissible`, this intersection is O-admissible in `J`, hence
contains `J_O`. By orbit-stabilizer, the orbit has size
`[J : J ∩ xKx⁻¹] ≤ [J : J_O] = ||J||_O`. -/
theorem orbit_card_le_oIndex (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H)
    (q : ↥H ⧸ K.subgroupOf H) :
    Nat.card (orbit (↥(J.subgroupOf H)) q) ≤ O.oIndex J := by
  sorry

/-- **Orbit counting theorem**: `(# J-orbits on H/K) · ||J||_O ≥ [H:K]`.

Partitioning `H/K` into `J`-orbits, each of size `≤ ||J||_O`:
`[H:K] = Σ |orbit_i| ≤ (# orbits) · ||J||_O`. -/
theorem nOrbits_mul_oIndex_ge (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H) :
    Nat.card (orbitRel.Quotient (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)) *
      O.oIndex J ≥ K.relIndex H := by
  sorry

/-- **Orbit counting corollary**: `# J-orbits ≥ ⌈[H:K] / ||J||_O⌉`.

This is the form used in the main theorem. -/
theorem nOrbits_ge_ceil_div (O : TransferSystem G) {H K J : Subgroup G}
    (hKH : O.rel K H) (hKle : K ≤ H) (hJH : J ≤ H) :
    (Nat.card (orbitRel.Quotient (↥(J.subgroupOf H)) (↥H ⧸ K.subgroupOf H)) : ℤ) ≥
      ⌈((K.relIndex H : ℚ) / (O.oIndex J : ℚ))⌉ := by
  sorry

end OrbitCounting
