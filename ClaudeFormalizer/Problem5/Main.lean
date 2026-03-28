/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClaudeFormalizer.Problem5.OrbitBound
import ClaudeFormalizer.Problem5.Framework

/-!
# Main Theorem: O-Slice Connectivity via Geometric Fixed Points

This file proves the main characterization theorem: a connective G-spectrum
`X` belongs to the O-slice category `Σ≥n^O` if and only if for every
subgroup `J ≤ G`, the geometric fixed point spectrum `Φ^J(X)` is
`⌈n / ||J||_O⌉`-connective.

## Main results

* `SliceFramework.necessity` — The forward direction: `X ∈ Σ≥n^O` implies
  the connectivity bounds.
* `SliceFramework.sufficiency` — The reverse direction: the connectivity
  bounds imply `X ∈ Σ≥n^O`.
* `SliceFramework.main_theorem` — The full characterization (iff).

## Proof overview

**Necessity** is proved by combining:
1. The closure axiom (connectivity bounds propagate from generators)
2. The Mackey + orbit bound axiom (each cell satisfies the bound)
3. Monotonicity of ceiling division in the numerator

**Sufficiency** follows directly from the `conn_implies_slice` axiom,
which encapsulates the isotropy separation and induction argument.

## References

* [Hill–Yarnall, Theorem 2.5]
* [Hill–Hopkins–Ravenel, Section 4.1]
-/

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace SliceFramework

variable [S : SliceFramework G]

/-! ### Arithmetic helper -/

/-- Ceiling division is monotone in the numerator (for positive denominator). -/
private lemma ceil_div_le_ceil_div_of_le {a b : ℕ} {d : ℕ} (hab : a ≤ b)
    (hd : 0 < d) :
    ⌈((a : ℚ) / (d : ℚ))⌉ ≤ ⌈((b : ℚ) / (d : ℚ))⌉ := by
  gcongr

/-! ### Necessity: forward direction -/

/-- **Necessity**: if `X ∈ Σ≥n^O`, then `Φ^J(X)` is `⌈n/||J||_O⌉`-connective
for every `J ≤ G`.

**Proof**: By the closure axiom, it suffices to check the generators (cells).
For a cell `(H, K)` with `K ⊆_O H` and `[H:K] ≥ n`:
- The Mackey+orbit bound axiom gives `geomConn J (cell) ≥ ⌈[H:K]/||J||_O⌉`.
- Since `[H:K] ≥ n` and `||J||_O > 0`: `⌈[H:K]/||J||_O⌉ ≥ ⌈n/||J||_O⌉`.
- By monotonicity: `geomConn J (cell) ≥ ⌈n/||J||_O⌉`. -/
theorem necessity (O : TransferSystem G) (n : ℕ) (X : S.GSpectrum)
    (hX : S.inOSlice O n X) (J : Subgroup G) :
    S.geomConn J X ⌈((n : ℚ) / (O.oIndex J : ℚ))⌉ := by
  apply S.slice_geomConn_of_cell_geomConn O n J
  · intro H K hKle hKH hge
    apply S.geomConn_mono _ (S.cell_conn_bound O hKle J hKH)
    exact ceil_div_le_ceil_div_of_le hge (O.oIndex_pos J)
  · exact hX

/-! ### Sufficiency: reverse direction -/

/-- **Sufficiency**: if `Φ^J(X)` is `⌈n/||J||_O⌉`-connective for all `J`,
then `X ∈ Σ≥n^O`.

This follows directly from the `conn_implies_slice` axiom, which
encapsulates the induction on `|G|`, isotropy separation, and
geometric localization. -/
theorem sufficiency (O : TransferSystem G) (n : ℕ) (X : S.GSpectrum)
    (h : ∀ J : Subgroup G,
      S.geomConn J X ⌈((n : ℚ) / (O.oIndex J : ℚ))⌉) :
    S.inOSlice O n X :=
  S.conn_implies_slice O n X h

/-! ### Main theorem -/

/-- **Main Theorem** (Problem 5): Let `O` be an incomplete transfer system
on a finite group `G` and `n ≥ 0`. A connective G-spectrum `X` belongs to
the O-slice category `Σ≥n^O` if and only if for every subgroup `J ≤ G`,
the geometric fixed point spectrum `Φ^J(X)` is `⌈n/||J||_O⌉`-connective.

The forward direction uses the orbit counting lemma (proved in
`OrbitBound.lean`) via the Mackey formula axiom. The reverse direction
uses the isotropy separation axiom. -/
theorem main_theorem (O : TransferSystem G) (n : ℕ) (X : S.GSpectrum) :
    S.inOSlice O n X ↔
      ∀ J : Subgroup G,
        S.geomConn J X ⌈((n : ℚ) / (O.oIndex J : ℚ))⌉ :=
  ⟨necessity O n X, sufficiency O n X⟩

end SliceFramework
