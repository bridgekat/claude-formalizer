/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Trace and Loewner order lemmas

Technical lemmas about matrix trace, PSD matrices, and the Loewner order
needed for the barrier method proof.
-/

namespace ClaudeFormalizer

open Matrix Finset Polynomial
open scoped MatrixOrder

set_option maxHeartbeats 400000

variable {d : ℕ}

/-! ### Helper lemmas -/

/-- `det(1 - K) = charpoly(K).eval 1` via the characteristic polynomial. -/
private lemma charpoly_eval_one_eq_det_one_sub (K : Matrix (Fin d) (Fin d) ℝ) :
    K.charpoly.eval 1 = (1 - K).det := by
  unfold charpoly
  change (Polynomial.evalRingHom 1) K.charmatrix.det = (1 - K).det
  rw [(Polynomial.evalRingHom (1 : ℝ)).map_det, RingHom.mapMatrix_apply]
  congr 1; ext i j; unfold charmatrix
  simp [Matrix.sub_apply, Matrix.one_apply, Polynomial.eval_sub, Polynomial.eval_C,
    Matrix.scalar_apply]
  split <;> simp_all

/-- For Hermitian `K`, `det(1 - K) = ∏ᵢ (1 - μᵢ)` where `μᵢ` are the eigenvalues of `K`. -/
private lemma det_one_sub_eq_prod_eigenvalues (K : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.IsHermitian) :
    (1 - K).det = ∏ i, (1 - hK.eigenvalues i) := by
  rw [← charpoly_eval_one_eq_det_one_sub, hK.charpoly_eq]
  simp [eval_prod, eval_sub, eval_X, eval_C]

/-! ### Main lemmas -/

/-- Trace of a product of PSD matrices is nonneg. -/
lemma trace_mul_nonneg_of_posSemidef
    {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ trace (A * B) := by
  obtain ⟨R, hR⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hA
  rw [hR, Matrix.mul_assoc, trace_mul_comm]
  exact (hB.mul_mul_conjTranspose_same R).trace_nonneg

/-- Trace monotonicity: if `A ≤ B` in Loewner order and `C` is PSD,
then `tr(A * C) ≤ tr(B * C)`. -/
lemma trace_mul_le_of_loewner_le
    {A B C : Matrix (Fin d) (Fin d) ℝ}
    (hAB : (B - A).PosSemidef) (hC : C.PosSemidef) :
    trace (A * C) ≤ trace (B * C) := by
  have key : 0 ≤ trace ((B - A) * C) := trace_mul_nonneg_of_posSemidef hAB hC
  have expand : trace ((B - A) * C) = trace (B * C) - trace (A * C) := by simp [sub_mul]
  linarith

/-- For a PSD matrix `K` with `tr(K) < 1`, every eigenvalue is `< 1`. -/
lemma eigenvalues_lt_one_of_posSemidef_trace_lt
    {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosSemidef) (htr : trace K < 1) :
    ∀ i, hK.isHermitian.eigenvalues i < 1 := by
  intro i
  have hnn : ∀ j, 0 ≤ hK.isHermitian.eigenvalues j := hK.eigenvalues_nonneg
  have hsum : ∑ j, hK.isHermitian.eigenvalues j = trace K := by
    have := hK.isHermitian.trace_eq_sum_eigenvalues; simp at this; linarith
  linarith [Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)]

/-- For PSD `K` with `tr(K) < 1`, the matrix `I - K` is invertible. -/
lemma isUnit_one_sub_of_posSemidef_trace_lt
    {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosSemidef) (htr : trace K < 1) :
    IsUnit (1 - K) := by
  rw [isUnit_iff_isUnit_det, det_one_sub_eq_prod_eigenvalues K hK.isHermitian]
  exact IsUnit.mk0 _ (ne_of_gt (Finset.prod_pos fun i _ =>
    by linarith [eigenvalues_lt_one_of_posSemidef_trace_lt hK htr i, hK.eigenvalues_nonneg i]))

set_option maxHeartbeats 800000 in
/-- For PSD `K` with `tr(K) < 1`, the matrix `I - K` is positive definite. -/
lemma posDef_one_sub_of_posSemidef_trace_lt
    {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosSemidef) (htr : trace K < 1) :
    (1 - K).PosDef := by
  set hH := hK.isHermitian
  set U := hH.eigenvectorUnitary
  set mu := hH.eigenvalues
  have heig_lt := eigenvalues_lt_one_of_posSemidef_trace_lt hK htr
  have hK_spec : K = (U : Matrix (Fin d) (Fin d) ℝ) *
      diagonal (fun i => mu i) * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    have : (RCLike.ofReal ∘ mu : Fin d → ℝ) = mu := by
      ext i; simp [RCLike.ofReal_real_eq_id]
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [this]
  have h1K : (1 : Matrix (Fin d) (Fin d) ℝ) - K =
      (U : Matrix (Fin d) (Fin d) ℝ) * diagonal (fun i => 1 - mu i) *
        star (U : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hK_spec, show (1 : Matrix (Fin d) (Fin d) ℝ) =
        (U : Matrix _ _ ℝ) * 1 * star (U : Matrix _ _ ℝ) from by simp]
    rw [← sub_mul, ← Matrix.mul_sub, ← diagonal_one, ← diagonal_sub]
  have hDiag_pd : PosDef (diagonal (fun i => 1 - mu i)) := by
    rw [posDef_diagonal_iff]; intro i; linarith [heig_lt i]
  rw [h1K]
  exact Unitary.isUnit_coe.posDef_star_right_conjugate_iff.mpr hDiag_pd

set_option maxHeartbeats 6400000 in
/-- Loewner bound on resolvent: if `K ≥ 0` and `tr(K) < 1`,
then `(I - K)⁻¹ ≤ (1 - tr(K))⁻¹ · I` in Loewner order. -/
lemma inv_one_sub_loewner_bound
    {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosSemidef) (htr : trace K < 1) :
    ((1 / (1 - trace K)) • (1 : Matrix (Fin d) (Fin d) ℝ) - (1 - K)⁻¹).PosSemidef := by
  set hKH := hK.isHermitian
  set μ := hKH.eigenvalues; set t := trace K; set c := 1 / (1 - t)
  set U : Matrix (Fin d) (Fin d) ℝ := ↑hKH.eigenvectorUnitary
  have ht : 0 < 1 - t := by linarith
  have hμ_lt : ∀ i, μ i < 1 := eigenvalues_lt_one_of_posSemidef_trace_lt hK htr
  have hμ_nn : ∀ i, 0 ≤ μ i := hK.eigenvalues_nonneg
  have hμ_le_t : ∀ i, μ i ≤ t := by
    intro i; have : ∑ j, μ j = t := by
      have := hKH.trace_eq_sum_eigenvalues; simp at this; linarith
    linarith [Finset.single_le_sum (fun j _ => hμ_nn j) (Finset.mem_univ i)]
  have h1μ : ∀ i, 0 < 1 - μ i := fun i => by linarith [hμ_lt i]
  have hUU : U * star U = 1 := by
    have := hKH.eigenvectorUnitary.prop; rwa [mem_unitaryGroup_iff] at this
  have hUU' : star U * U = 1 := by
    have := hKH.eigenvectorUnitary.prop; rwa [mem_unitaryGroup_iff'] at this
  have hKspec : K = U * diagonal μ * star U := by
    conv_lhs => rw [hKH.spectral_theorem]; simp; rfl
  set ν : Fin d → ℝ := fun i => 1 / (1 - μ i)
  set Xinv := U * diagonal ν * star U
  have key : ∀ i, (1 - μ i) * ν i = 1 := fun i => by
    simp only [ν]; rw [one_div, mul_inv_cancel₀ (ne_of_gt (h1μ i))]
  -- (1-K) * X = 1, so X = (1-K)^{-1}
  have hinvX : (1 - K) * Xinv = 1 := by
    rw [hKspec]; simp only [Xinv]
    have h1sub : (1 : Matrix _ _ ℝ) - U * diagonal μ * star U =
        U * (1 - diagonal μ) * star U := by
      have : U * (1 - diagonal μ) * star U = U * star U - U * diagonal μ * star U := by
        calc U * (1 - diagonal μ) * star U
            = (U * 1 - U * diagonal μ) * star U := by rw [Matrix.mul_sub]
          _ = U * 1 * star U - U * diagonal μ * star U := by rw [Matrix.sub_mul]
          _ = U * star U - U * diagonal μ * star U := by rw [Matrix.mul_one]
      rw [this, hUU]
    rw [h1sub]
    -- Combine the two conjugated matrices into one
    -- (U (1-D) U^*) (U diag(ν) U^*) = U ((1-D) ν) U^*
    -- via U^* U = 1
    calc U * (1 - diagonal μ) * star U * (U * diagonal ν * star U)
        = U * (1 - diagonal μ) * (star U * U) * diagonal ν * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (1 - diagonal μ) * 1 * diagonal ν * star U := by rw [hUU']
      _ = U * ((1 - diagonal μ) * diagonal ν) * star U := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    have h1d : (1 : Matrix _ _ ℝ) - diagonal μ = diagonal (1 - μ) := by
      ext i j; simp [diagonal, one_apply]; split <;> simp_all
    rw [h1d, diagonal_mul_diagonal]
    have hprod : (fun i => (1 - μ) i * ν i) = fun _ => (1 : ℝ) := by
      ext i; simp [Pi.sub_apply, key]
    rw [hprod, diagonal_one, Matrix.mul_one, hUU]
  rw [← (inv_eq_right_inv hinvX).symm]
  -- c*I - Xinv = U * (c*I - diagonal ν) * star U
  have hsmul_sub : c • (1 : Matrix _ _ ℝ) - Xinv =
      U * (c • 1 - diagonal ν) * star U := by
    simp only [Xinv]
    have : U * (c • 1 - diagonal ν) * star U = c • (U * star U) - U * diagonal ν * star U := by
      calc U * (c • 1 - diagonal ν) * star U
          = (U * (c • 1) - U * diagonal ν) * star U := by rw [Matrix.mul_sub]
        _ = U * (c • 1) * star U - U * diagonal ν * star U := by rw [Matrix.sub_mul]
        _ = c • (U * 1) * star U - U * diagonal ν * star U := by rw [Algebra.mul_smul_comm]
        _ = c • (U * 1 * star U) - U * diagonal ν * star U := by rw [Algebra.smul_mul_assoc]
        _ = c • (U * star U) - U * diagonal ν * star U := by rw [Matrix.mul_one]
    rw [this, hUU]
  rw [hsmul_sub]
  have hdiag : c • (1 : Matrix _ _ ℝ) - diagonal ν = diagonal (fun i => c - ν i) := by
    ext i j; simp [smul_apply, one_apply, diagonal]; split <;> simp_all
  rw [hdiag]
  exact (posSemidef_diagonal_iff.mpr fun i => by
    simp only [c, ν]
    rw [div_sub_div _ _ (ne_of_gt ht) (ne_of_gt (h1μ i))]
    exact div_nonneg (by linarith [hμ_le_t i]) (mul_pos ht (h1μ i)).le
  ).mul_mul_conjTranspose_same U

/-- A sum of PSD matrices is dominated by the total sum in Loewner order.
If `A_i ≥ 0` for all `i`, then for any `S ⊆ T`, `∑_{i ∈ S} A_i ≤ ∑_{i ∈ T} A_i`. -/
lemma sum_posSemidef_le_sum {ι : Type*} {S T : Finset ι}
    (hST : S ⊆ T)
    (A : ι → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i ∈ T, (A i).PosSemidef) :
    (∑ i ∈ T, A i - ∑ i ∈ S, A i).PosSemidef := by
  classical
  rw [← Finset.sum_sdiff_eq_sub hST]
  exact Matrix.posSemidef_sum _ fun i hi => hA i (Finset.sdiff_subset hi)

end ClaudeFormalizer
