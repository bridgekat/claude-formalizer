/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# PSD Square Root

Construction and properties of the positive semidefinite square root of a PSD matrix
using the spectral theorem.
-/

namespace ClaudeFormalizer

open Matrix

variable {d : ℕ}

/-- The PSD square root of a PSD matrix, defined via spectral decomposition.
For `B ≥ 0` with spectral decomposition `B = U Λ U^T`,
we define `sqrt(B) = U √Λ U^T`. -/
noncomputable def psdSqrt (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) :
    Matrix (Fin d) (Fin d) ℝ :=
  let U := hB.isHermitian.eigenvectorUnitary
  let sqrtEigs := fun i => Real.sqrt (hB.isHermitian.eigenvalues i)
  (U : Matrix (Fin d) (Fin d) ℝ) * diagonal sqrtEigs * (star U : Matrix (Fin d) (Fin d) ℝ)

/-- The PSD square root is PSD. -/
lemma psdSqrt_posSemidef (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) :
    (psdSqrt B hB).PosSemidef := by
  simp only [psdSqrt]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [posSemidef_diagonal_iff]
  intro i
  exact Real.sqrt_nonneg _

/-- The PSD square root is Hermitian (symmetric over ℝ). -/
lemma psdSqrt_isHermitian (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) :
    (psdSqrt B hB).IsHermitian := by
  simp only [psdSqrt, star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose _ (isHermitian_diagonal _)

set_option maxHeartbeats 400000 in
/-- The PSD square root squares to the original matrix: `(√B)² = B`. -/
lemma psdSqrt_sq (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) :
    psdSqrt B hB * psdSqrt B hB = B := by
  simp only [psdSqrt]
  -- Reassociate (U * D * U*) * (U * D * U*) = U * (D * (U* * U) * D) * U*
  have step1 : forall (U D Us : Matrix (Fin d) (Fin d) ℝ),
      U * D * Us * (U * D * Us) = U * (D * (Us * U) * D) * Us := by
    intros; simp [mul_assoc]
  rw [step1, Unitary.coe_star_mul_self]
  -- Collapse D * 1 * D = D * D, then diagonal multiplication
  simp only [mul_one]
  rw [diagonal_mul_diagonal]
  -- sqrt(lambda_i) * sqrt(lambda_i) = lambda_i
  have h_eigs : (fun i => Real.sqrt (hB.isHermitian.eigenvalues i) *
      Real.sqrt (hB.isHermitian.eigenvalues i)) = fun i => hB.isHermitian.eigenvalues i := by
    ext i; exact Real.mul_self_sqrt (hB.eigenvalues_nonneg i)
  rw [h_eigs]
  -- U * diagonal(eigenvalues) * U* = B by the spectral theorem
  conv_rhs => rw [hB.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp [RCLike.ofReal_real_eq_id]

/-- Every PSD matrix factors as `C * Cᴴ` for some `C`. -/
lemma PosSemidef.exists_factor {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosSemidef) :
    ∃ C : Matrix (Fin d) (Fin d) ℝ, C * Cᴴ = B := by
  exact ⟨psdSqrt B hB, by
    rw [(psdSqrt_isHermitian B hB).eq]
    exact psdSqrt_sq B hB⟩

end ClaudeFormalizer
