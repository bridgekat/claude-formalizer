/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ClaudeFormalizer.TraceLoewner
import ClaudeFormalizer.PSDSqrt

/-!
# Barrier Potential and One-Sided Barrier Lemma

Defines the barrier potential function `Φ_u(M) = tr((uI - M)⁻¹)` and proves the
one-sided barrier lemma from the BSS method.
-/

namespace ClaudeFormalizer

open Matrix
open scoped MatrixOrder

set_option maxHeartbeats 800000

variable {d : ℕ}

/-! ### Helper lemmas -/

private lemma trace_nonneg_of_posSemidef {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) : 0 ≤ trace P := by
  rw [hP.isHermitian.trace_eq_sum_eigenvalues]
  apply Finset.sum_nonneg; intro i _; exact_mod_cast hP.eigenvalues_nonneg i

private lemma trace_mul_nonneg_of_psd' {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ trace (A * B) := by
  let C := psdSqrt A hA
  have hC := psdSqrt_isHermitian A hA
  rw [← psdSqrt_sq A hA, Matrix.mul_assoc, trace_mul_comm C (C * B)]
  have : C * B * C = C * B * Cᴴ := by rw [hC.eq]
  rw [this]
  exact trace_nonneg_of_posSemidef (PosSemidef.mul_mul_conjTranspose_same hB C)

private lemma resolvent_identity {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ := by
  rw [mul_sub, sub_mul, Matrix.mul_assoc (B⁻¹) A (A⁻¹), mul_nonsing_inv _ hA, mul_one]
  conv_rhs => rw [show B⁻¹ * B * A⁻¹ = (B⁻¹ * B) * A⁻¹ from rfl]
  rw [nonsing_inv_mul _ hB, one_mul]

/-- The barrier potential function: `Φ_u(M) = tr((u·I - M)⁻¹)`.
Well-defined when `u·I - M` is positive definite (hence invertible). -/
noncomputable def barrierPotential (u : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  trace ((u • (1 : Matrix (Fin d) (Fin d) ℝ) - M)⁻¹)

/-- The potential at zero: `Φ_u(0) = d/u` for `u > 0`. -/
lemma barrierPotential_zero (u : ℝ) (hu : 0 < u) :
    barrierPotential u (0 : Matrix (Fin d) (Fin d) ℝ) = d / u := by
  unfold barrierPotential
  rw [sub_zero]
  have hu' : u ≠ 0 := ne_of_gt hu
  have hdet : IsUnit (u • (1 : Matrix (Fin d) (Fin d) ℝ)).det := by
    rw [det_smul, det_one, mul_one]
    exact IsUnit.pow _ (Ne.isUnit hu')
  have hinv : (u • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ =
      u⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    calc (u • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
        = (u • 1)⁻¹ * ((u • 1) * (u⁻¹ • 1)) := by
          rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hu', one_smul, mul_one]
      _ = ((u • 1)⁻¹ * (u • 1)) * (u⁻¹ • 1) := by rw [mul_assoc]
      _ = 1 * (u⁻¹ • 1) := by rw [nonsing_inv_mul _ hdet]
      _ = u⁻¹ • 1 := by rw [one_mul]
  rw [hinv, trace_smul, trace_one]
  simp [smul_eq_mul, Fintype.card_fin]
  field_simp

/-- Monotonicity: for fixed `M ≺ uI`, the potential decreases as `u` increases. -/
lemma barrierPotential_anti {u u' : ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    (_hM : M.IsHermitian)
    (hMu : (u • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosDef)
    (huu' : u ≤ u') :
    barrierPotential u' M ≤ barrierPotential u M := by
  unfold barrierPotential
  set A := u • (1 : Matrix (Fin d) (Fin d) ℝ) - M with hAdef
  set B := u' • (1 : Matrix (Fin d) (Fin d) ℝ) - M with hBdef
  have hBpd : B.PosDef := by
    have : B = A + (u' - u) • 1 := by simp [hAdef, hBdef, sub_smul]
    rw [this]
    exact PosDef.add_posSemidef hMu (PosSemidef.one.smul (sub_nonneg.mpr huu'))
  have hAdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hMu.isUnit
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hBpd.isUnit
  rw [← sub_nonneg, ← trace_sub]
  have hAB : A - B = (u - u') • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    simp [hAdef, hBdef, sub_smul]
  have hkey : A⁻¹ - B⁻¹ = (u' - u) • (B⁻¹ * A⁻¹) := by
    have h1 : A⁻¹ - B⁻¹ = -(B⁻¹ - A⁻¹) := by abel
    rw [h1, resolvent_identity hAdet hBdet, hAB, mul_smul_comm, smul_mul_assoc, mul_one,
        ← neg_smul]
    congr 1; ring
  rw [hkey, trace_smul, smul_eq_mul]
  exact mul_nonneg (sub_nonneg.mpr huu')
    (trace_mul_nonneg_of_psd' hBpd.inv.posSemidef hMu.inv.posSemidef)

/-- Potential drop bound: `Φ_u(M) - Φ_{u+δ}(M) ≥ δ · tr(U²)` where `U = ((u+δ)I - M)⁻¹`. -/
private lemma sq_inv_posSemidef {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) :
    (B⁻¹ * B⁻¹).PosSemidef := by
  rw [show B⁻¹ * B⁻¹ = (B⁻¹)ᴴ * B⁻¹ from by rw [hB.inv.isHermitian.eq]]
  exact posSemidef_conjTranspose_mul_self B⁻¹

lemma barrierPotential_drop {u δ : ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    (_hM : M.IsHermitian)
    (hMu : (u • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosDef)
    (hδ : 0 < δ) :
    let U := ((u + δ) • (1 : Matrix (Fin d) (Fin d) ℝ) - M)⁻¹
    δ * trace (U * U) ≤ barrierPotential u M - barrierPotential (u + δ) M := by
  intro U
  unfold barrierPotential
  set A := u • (1 : Matrix (Fin d) (Fin d) ℝ) - M with hAdef
  set B := (u + δ) • (1 : Matrix (Fin d) (Fin d) ℝ) - M with hBdef
  have hBpd : B.PosDef := by
    have : B = A + δ • 1 := by rw [hAdef, hBdef, add_smul]; abel
    rw [this]
    exact PosDef.add_posSemidef hMu (PosSemidef.one.smul (le_of_lt hδ))
  have hAdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hMu.isUnit
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hBpd.isUnit
  show δ * trace (U * U) ≤ trace A⁻¹ - trace B⁻¹
  have hUB : U = B⁻¹ := rfl
  rw [hUB, ← trace_sub]
  -- Resolvent: A⁻¹ - B⁻¹ = δ • (B⁻¹ * A⁻¹)
  have hBA : B - A = δ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hAdef, hBdef, add_smul]; abel
  have hAinvBinv : A⁻¹ - B⁻¹ = δ • (B⁻¹ * A⁻¹) := by
    have h1 : A⁻¹ - B⁻¹ = -(B⁻¹ - A⁻¹) := by abel
    rw [h1, resolvent_identity hAdet hBdet]
    have hAB : A - B = -(δ • 1) := by rw [← hBA]; abel
    rw [hAB, mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hAinvBinv, trace_smul, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
  -- trace(B⁻²) ≤ trace(B⁻¹ * A⁻¹)
  rw [← sub_nonneg, ← trace_sub, show B⁻¹ * A⁻¹ - B⁻¹ * B⁻¹ = B⁻¹ * (A⁻¹ - B⁻¹) from
    by rw [← mul_sub]]
  rw [hAinvBinv, mul_smul_comm, trace_smul, smul_eq_mul]
  apply mul_nonneg (le_of_lt hδ)
  rw [← mul_assoc]
  exact trace_mul_nonneg_of_psd' (sq_inv_posSemidef hBpd) hMu.inv.posSemidef

/-! ### Woodbury identity helpers -/

private lemma key_cancel {K : Matrix (Fin d) (Fin d) ℝ} (hIK : IsUnit (1 - K).det) :
    (1 - K)⁻¹ - 1 - K * (1 - K)⁻¹ = (0 : Matrix (Fin d) (Fin d) ℝ) := by
  have h2 : (1 - K)⁻¹ - K * (1 - K)⁻¹ = 1 := by
    rw [show (1 - K)⁻¹ - K * (1 - K)⁻¹ = (1 - K) * (1 - K)⁻¹ from by rw [sub_mul, one_mul]]
    exact mul_nonsing_inv _ hIK
  have : (1 - K)⁻¹ - 1 - K * (1 - K)⁻¹ = ((1 - K)⁻¹ - K * (1 - K)⁻¹) - 1 := by abel
  rw [this, h2, sub_self]

/-- Woodbury matrix identity: `(N - CC)⁻¹ = U + UC(I-K)⁻¹CU`
where `U = N⁻¹` and `K = CUC`, verified by multiplication. -/
private lemma woodbury_mul {N C U K : Matrix (Fin d) (Fin d) ℝ}
    (hNU : N * U = 1) (hK : K = C * U * C) (hIK : IsUnit (1 - K).det) :
    (N - C * C) * (U + U * C * (1 - K)⁻¹ * C * U) = 1 := by
  simp only [sub_mul, mul_add, Matrix.mul_assoc]
  rw [show N * U = 1 from hNU]
  rw [show N * (U * (C * ((1 - K)⁻¹ * (C * U)))) =
      N * U * (C * ((1 - K)⁻¹ * (C * U))) from by simp only [Matrix.mul_assoc]]
  rw [hNU, one_mul]
  rw [show C * (C * (U * (C * ((1 - K)⁻¹ * (C * U))))) =
      C * (C * U * C) * ((1 - K)⁻¹ * (C * U)) from by simp only [Matrix.mul_assoc]]
  rw [← hK]
  rw [show (1 : Matrix (Fin d) (Fin d) ℝ) - C * (C * U) +
      (C * ((1 - K)⁻¹ * (C * U)) - C * K * ((1 - K)⁻¹ * (C * U))) =
      1 + C * (((1 - K)⁻¹ - 1 - K * (1 - K)⁻¹) * (C * U)) from by
    simp only [mul_sub, sub_mul, one_mul, Matrix.mul_assoc]; abel]
  rw [key_cancel hIK, zero_mul, mul_zero, add_zero]

/-! ### Main barrier lemma -/

theorem barrier_lemma {u u' : ℝ} {M B : Matrix (Fin d) (Fin d) ℝ}
    (_hM : M.IsHermitian) (hB : B.PosSemidef)
    (hMu : (u • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosDef)
    (_huu' : u < u')
    (hMu' : (u' • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosDef) :
    let U := (u' • (1 : Matrix (Fin d) (Fin d) ℝ) - M)⁻¹
    let gap := barrierPotential u M - barrierPotential u' M
    0 < gap →
    trace (B * U) + trace (B * (U * U)) / gap ≤ 1 →
    (u' • (1 : Matrix (Fin d) (Fin d) ℝ) - (M + B)).PosDef ∧
      barrierPotential u' (M + B) ≤ barrierPotential u M := by
  intro U gap hgap hbarrier
  -- Setup: N = u'I - M (PD), U = N⁻¹, C = psdSqrt(B), K = CUC
  set N := u' • (1 : Matrix (Fin d) (Fin d) ℝ) - M with hNdef
  set C := psdSqrt B hB with hCdef
  have hCH : C.IsHermitian := psdSqrt_isHermitian B hB
  have hCC : C * C = B := psdSqrt_sq B hB
  set K := C * U * C with hKdef
  -- N * U = I (since N is PD hence invertible)
  have hNU : N * U = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hMu'.isUnit)
  -- tr(K) = tr(CUC) = tr(BU) by cyclic trace
  have htrK : trace K = trace (B * U) := by
    rw [hKdef]
    -- K = (C*U)*C. trace((C*U)*C) = trace(C*(C*U)) by cyclic.
    -- = trace((C*C)*U) = trace(B*U)
    rw [trace_mul_comm (C * U) C, ← Matrix.mul_assoc C C U, hCC]
  -- U is the inverse of PD N, so U is PD
  have hUpd : U.PosDef := hMu'.inv
  -- K is PSD (congruence of PD U by C)
  have hKpsd : K.PosSemidef := by
    rw [hKdef, show C * U * C = C * U * Cᴴ from by rw [hCH.eq]]
    exact PosSemidef.mul_mul_conjTranspose_same hUpd.posSemidef C
  -- tr(K) < 1: from barrier condition and nonnegativity of tr(BU²)/gap
  have htrK_lt : trace K < 1 := by
    rw [htrK]
    have hBU2_nonneg : 0 ≤ trace (B * (U * U)) := by
      -- trace(B*(U*U)) = trace((U*U)*B)  [cyclic]
      -- = trace(U*(U*B))  [assoc]
      -- = trace((U*B)*U)  [cyclic]
      -- = trace(U*B*Uᴴ)  [U hermitian]
      -- >= 0  [congruence PSD]
      rw [trace_mul_comm B (U * U)]
      rw [Matrix.mul_assoc U U B, trace_mul_comm U (U * B)]
      rw [show U * B * U = U * B * Uᴴ from by rw [hUpd.isHermitian.eq]]
      exact trace_nonneg_of_posSemidef (PosSemidef.mul_mul_conjTranspose_same hB U)
    have hterm_nonneg : 0 ≤ trace (B * (U * U)) / gap := div_nonneg hBU2_nonneg (le_of_lt hgap)
    -- From barrier: tr(BU) + nonneg ≤ 1, so tr(BU) ≤ 1.
    -- For strict <: if tr(BU) = 1 then tr(BU²)/gap ≤ 0, so tr(BU²) = 0 (since ≥ 0).
    -- trace(UBU) = 0 and UBU PSD ⟹ UBU = 0 ⟹ BU = 0 ⟹ tr(BU) = 0, contradiction.
    -- So tr(BU) < 1.
    by_contra h
    push_neg at h
    have hBU_le : trace (B * U) ≤ 1 := by linarith
    have hBU_eq : trace (B * U) = 1 := le_antisymm hBU_le h
    have hBU2_zero : trace (B * (U * U)) = 0 := by
      have h1 : trace (B * (U * U)) / gap ≤ 0 := by linarith [hbarrier, hBU_eq]
      have h2 : trace (B * (U * U)) ≤ 0 := by
        have h3 := mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hgap)
        rwa [div_mul_cancel₀ _ (ne_of_gt hgap)] at h3
      exact le_antisymm h2 hBU2_nonneg
    -- UBU is PSD with trace 0, so UBU = 0
    -- This is a deep fact about PSD matrices. Use sorry for this subgoal.
    have : trace (B * U) = 0 := by
      -- Step 1: trace(B*(U*U)) = trace(U*B*U) by cyclic trace
      have hUBU_trace : trace (U * B * U) = 0 := by
        rw [Matrix.mul_assoc, trace_mul_comm U (B * U)]
        rw [show B * U * U = B * (U * U) from Matrix.mul_assoc B U U]
        exact hBU2_zero
      -- Step 2: UBU = U*B*U^H since U is Hermitian (PD implies Hermitian)
      have hUBU_psd : (U * B * U).PosSemidef := by
        rw [show U * B * U = U * B * Uᴴ from by rw [hUpd.isHermitian.eq]]
        exact PosSemidef.mul_mul_conjTranspose_same hB U
      -- Step 3: UBU PSD with trace 0 implies UBU = 0
      have hUBU_zero : U * B * U = 0 :=
        hUBU_psd.trace_eq_zero_iff.mp hUBU_trace
      -- Step 4: U invertible, so B = U⁻¹ * 0 * U⁻¹ = 0
      have hUdet : IsUnit U.det :=
        (isUnit_iff_isUnit_det U).mp hUpd.isUnit
      have hB_zero : B = 0 := by
        have h1 : U⁻¹ * (U * (B * U)) * U⁻¹ = B := by
          rw [nonsing_inv_mul_cancel_left U (B * U) hUdet,
              Matrix.mul_assoc B U U⁻¹,
              mul_nonsing_inv U hUdet, mul_one]
        rw [← h1, ← Matrix.mul_assoc U B U, hUBU_zero, mul_zero, zero_mul]
      rw [hB_zero, zero_mul, trace_zero]
    linarith [hBU_eq, this]
  -- (I - K) is invertible
  have hIK_isUnit : IsUnit (1 - K) := isUnit_one_sub_of_posSemidef_trace_lt hKpsd htrK_lt
  have hIK_det : IsUnit (1 - K).det := (isUnit_iff_isUnit_det _).mp hIK_isUnit
  -- Woodbury: (N - CC) * W = I where W = U + UC(I-K)⁻¹CU
  set W := U + U * C * (1 - K)⁻¹ * C * U with hWdef
  have hWoodbury : (N - C * C) * W = 1 := woodbury_mul hNU hKdef.symm hIK_det
  -- N - CC = u'I - (M + B)
  have hNCC : N - C * C = u' • (1 : Matrix (Fin d) (Fin d) ℝ) - (M + B) := by
    rw [hNdef, hCC]; abel
  -- W is PD (we need this to conclude (N-CC) is PD)
  -- W = U + U * (C * (I-K)⁻¹ * C) * U
  -- U is PD (inverse of PD). The second summand is PSD (congruence of PSD by U).
  -- Sum of PD and PSD is PD.
  have hWpd : W.PosDef := by
    -- C * (1-K)⁻¹ * Cᴴ is PSD (congruence of (1-K)⁻¹ which is PD)
    have hIK_pd : (1 - K)⁻¹.PosDef :=
      (posDef_one_sub_of_posSemidef_trace_lt hKpsd (htrK ▸ htrK_lt)).inv
    have hP_psd : (C * (1 - K)⁻¹ * C).PosSemidef := by
      rw [show C * (1 - K)⁻¹ * C = C * (1 - K)⁻¹ * Cᴴ from by rw [hCH.eq]]
      exact PosSemidef.mul_mul_conjTranspose_same hIK_pd.posSemidef C
    -- U * P * U is PSD where P = C(I-K)⁻¹C
    have hUPU_psd : (U * (C * (1 - K)⁻¹ * C) * U).PosSemidef := by
      rw [show U * (C * (1 - K)⁻¹ * C) * U = U * (C * (1 - K)⁻¹ * C) * Uᴴ from by
        rw [hMu'.inv.isHermitian.eq]]
      exact PosSemidef.mul_mul_conjTranspose_same hP_psd U
    -- W = U + U*P*U (rewrite to match)
    rw [hWdef, show U + U * C * (1 - K)⁻¹ * C * U =
        U + U * (C * (1 - K)⁻¹ * C) * U from by simp only [Matrix.mul_assoc]]
    exact PosDef.add_posSemidef hMu'.inv hUPU_psd
  -- Part 1: (u'I - (M+B)).PosDef
  -- Since (N - CC) * W = I and W is PD (hence invertible), N-CC = W⁻¹.
  -- W PD ⟹ W⁻¹ PD by PosDef.inv.
  have hPart1 : (u' • (1 : Matrix (Fin d) (Fin d) ℝ) - (M + B)).PosDef := by
    rw [← hNCC]
    -- W PD implies W invertible
    have hW_isUnit : IsUnit W := hWpd.isUnit
    have hW_det : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW_isUnit
    -- (N-CC) is invertible: (N-CC)*W = 1 and W invertible
    have hNCC_det : IsUnit (N - C * C).det := by
      rw [← isUnit_iff_isUnit_det]
      exact isUnit_of_mul_eq_one _ hWoodbury
    -- (N-CC)⁻¹ = W
    have hNCC_inv : (N - C * C)⁻¹ = W := by
      calc (N - C * C)⁻¹
          = (N - C * C)⁻¹ * ((N - C * C) * W) := by rw [hWoodbury, mul_one]
        _ = ((N - C * C)⁻¹ * (N - C * C)) * W := by rw [Matrix.mul_assoc]
        _ = 1 * W := by rw [nonsing_inv_mul _ hNCC_det]
        _ = W := one_mul W
    -- W PD, so W⁻¹ = N-CC is PD
    rw [show N - C * C = W⁻¹ from by
      rw [← hNCC_inv]; exact (nonsing_inv_nonsing_inv _ hNCC_det).symm]
    exact hWpd.inv
  -- Part 2: Φ_{u'}(M+B) ≤ Φ_u(M)
  have hPart2 : barrierPotential u' (M + B) ≤ barrierPotential u M := by
    -- Φ_{u'}(M+B) = trace((u'I-(M+B))⁻¹) = trace(W) (from Woodbury)
    -- We need: (u'I - (M+B))⁻¹ = W. We showed (N-CC)*W = 1 and N-CC = u'I-(M+B).
    unfold barrierPotential
    -- Step 1: rewrite (u'I-(M+B))⁻¹ = W
    have hNCC_det : IsUnit (N - C * C).det :=
      (isUnit_iff_isUnit_det _).mp (isUnit_of_mul_eq_one _ hWoodbury)
    have hInv : (u' • (1 : Matrix (Fin d) (Fin d) ℝ) - (M + B))⁻¹ = W := by
      rw [← hNCC]
      calc (N - C * C)⁻¹
          = (N - C * C)⁻¹ * ((N - C * C) * W) := by rw [hWoodbury, mul_one]
        _ = ((N - C * C)⁻¹ * (N - C * C)) * W := by rw [Matrix.mul_assoc]
        _ = 1 * W := by rw [nonsing_inv_mul _ hNCC_det]
        _ = W := one_mul W
    rw [hInv]
    -- Step 2: trace(W) = trace(U) + trace(UC(I-K)⁻¹CU)
    -- W = U + U*C*(1-K)⁻¹*C*U
    rw [hWdef]
    rw [trace_add]
    -- Goal: trace(U) + trace(second term) ≤ trace((uI-M)⁻¹)
    -- trace(U) = Φ_{u'}(M) = trace((u'I-M)⁻¹) by definition
    -- So need: trace(second term) ≤ Φ_u(M) - Φ_{u'}(M) = gap
    -- Step 3: bound the second trace term
    -- trace(UC(I-K)⁻¹CU) = trace(CU²C(I-K)⁻¹) [cyclic]
    -- ≤ trace(CU²C) * 1/(1-tr(K)) [resolvent Loewner bound]
    -- = trace(BU²) / (1-tr(BU))
    -- And barrier condition gives: trace(BU²)/(1-tr(BU)) ≤ gap
    -- So trace(U) + gap ≤ trace(U) + gap = Φ_u(M). ✓
    --
    -- Need: trace(U) + trace(second term) ≤ trace((uI-M)⁻¹)
    -- i.e., trace(second term) ≤ gap = barrierPotential u M - barrierPotential u' M
    suffices hsuff : trace (U * C * (1 - K)⁻¹ * C * U) ≤ gap by
      show trace U + trace (U * C * (1 - K)⁻¹ * C * U) ≤ trace ((u • 1 - M)⁻¹)
      have hgap_eq : gap = trace ((u • 1 - M)⁻¹) - trace U := by
        unfold gap barrierPotential; ring
      linarith
    -- Step A: trace(U*C*(1-K)⁻¹*C*U) = trace((1-K)⁻¹ * C * U * U * C) by cyclic trace
    have hcyclic : trace (U * C * (1 - K)⁻¹ * C * U) =
        trace ((1 - K)⁻¹ * (C * (U * U) * C)) := by
      -- trace(ABCDE) = trace(BCDEA) = trace(CDEAB) by cyclic trace
      -- trace(U * C * IK * C * U) = trace(IK * C * U * U * C)
      -- where IK = (1-K)⁻¹
      set IK := (1 - K)⁻¹
      -- Step 1: trace(U*C*IK*C*U) = trace((C*IK*C*U)*U)  [cyclic, move U from front to back]
      rw [show U * C * IK * C * U = U * (C * IK * C * U) from by
        simp only [Matrix.mul_assoc]]
      rw [trace_mul_comm U (C * IK * C * U)]
      -- Step 2: trace(C*IK*C*U*U) = trace((IK*C*U*U)*C) [cyclic, move C from front to back]
      rw [show C * IK * C * U * U = C * (IK * C * U * U) from by
        simp only [Matrix.mul_assoc]]
      rw [trace_mul_comm C (IK * C * U * U)]
      -- Now both sides are trace(IK * C * U * U * C) up to association
      simp only [Matrix.mul_assoc]
    -- Step B: trace(CU²C) = trace(BU²)
    have hCU2C_eq : trace (C * (U * (U * C))) = trace (B * (U * U)) := by
      rw [trace_mul_comm C (U * (U * C))]
      -- trace(U * (U * C) * C) = trace(B * (U * U))
      rw [show U * (U * C) * C = (U * U) * (C * C) from by simp only [Matrix.mul_assoc]]
      rw [hCC, trace_mul_comm (U * U) B]
    -- Step C: (1-K)⁻¹ ≤ (1/(1-tr(K))) * I in Loewner order
    -- CU²C is PSD
    have hUU_psd : (U * U).PosSemidef := sq_inv_posSemidef hMu'
    have hCU2C_psd : (C * (U * (U * C))).PosSemidef := by
      rw [show C * (U * (U * C)) = C * (U * U) * Cᴴ from by
        simp only [Matrix.mul_assoc]; rw [hCH.eq]]
      exact PosSemidef.mul_mul_conjTranspose_same hUU_psd C
    -- Set P = C * (U * (U * C)), the fully right-associated form from hcyclic
    -- By trace monotonicity and Loewner bound:
    have hLoewner := inv_one_sub_loewner_bound hKpsd (htrK ▸ htrK_lt)
    have hle := trace_mul_le_of_loewner_le hLoewner hCU2C_psd
    -- hle : trace((1-K)⁻¹ * P) ≤ trace((1/(1-tr(K))) • I * P)
    -- Simplify RHS: (c • I) * P = c • P, trace(c • P) = c * trace(P)
    have htrace_bound : trace ((1 - K)⁻¹ * (C * (U * (U * C)))) ≤
        trace (C * (U * (U * C))) / (1 - trace K) := by
      rw [smul_mul_assoc, one_mul, trace_smul, smul_eq_mul, one_div] at hle
      rwa [← div_eq_inv_mul] at hle
    -- From barrier condition: tr(BU²)/(1-tr(K)) ≤ gap
    have h1K_pos : 0 < 1 - trace K := by rw [htrK]; linarith [htrK_lt]
    have hBU2_le : trace (B * (U * U)) / (1 - trace K) ≤ gap := by
      rw [div_le_iff₀ h1K_pos, htrK]
      have h1 : trace (B * (U * U)) / gap ≤ 1 - trace (B * U) := by linarith [hbarrier]
      have h2 : trace (B * (U * U)) ≤ (1 - trace (B * U)) * gap := by
        rwa [div_le_iff₀ hgap] at h1
      nlinarith
    have hcyclic' : trace (U * C * (1 - K)⁻¹ * C * U) =
        trace ((1 - K)⁻¹ * (C * (U * (U * C)))) := by
      rw [hcyclic]; congr 1; simp only [Matrix.mul_assoc]
    calc trace (U * C * (1 - K)⁻¹ * C * U)
        = trace ((1 - K)⁻¹ * (C * (U * (U * C)))) := hcyclic'
      _ ≤ trace (C * (U * (U * C))) / (1 - trace K) := htrace_bound
      _ = trace (B * (U * U)) / (1 - trace K) := by rw [hCU2C_eq]
      _ ≤ gap := hBU2_le
  exact ⟨hPart1, hPart2⟩

end ClaudeFormalizer
