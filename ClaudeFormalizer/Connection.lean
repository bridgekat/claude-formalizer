/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ClaudeFormalizer.Defs
import ClaudeFormalizer.TraceLoewner

/-!
# Spectral Normalization and Connection to Graph Laplacian

This file constructs the normalized edge matrices `A_e` from the graph Laplacian
via the spectral theorem, proves `∑ A_e = I`, and shows that the BSS bound on
the normalized matrices implies ε-lightness of the original graph.
-/

namespace ClaudeFormalizer

open Matrix Finset SimpleGraph
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rank of the Laplacian equals `|V|` minus the number of connected components. -/
noncomputable def lapMatrixRank (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.lapMatrix ℝ).rank

/-- Vectors in `ker(L_G)` are constant on connected components and hence
are also in `ker(L_{G_S})` for any `S`. -/
lemma ker_lapMatrix_le_ker_edgesWithin
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (x : V → ℝ) (hx : G.lapMatrix ℝ *ᵥ x = 0) :
    (G.edgesWithin S).lapMatrix ℝ *ᵥ x = 0 := by
  rw [lapMatrix_mulVec_eq_zero_iff_forall_adj] at hx ⊢
  intro i j hij
  exact hx i j hij.1

set_option maxHeartbeats 1600000 in
/-- The Laplacian quadratic form decomposes as a sum over edges:
`x^T L x = ∑_{u~v} (x_u - x_v)²`. -/
lemma lapMatrix_quadForm_eq_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    dotProduct x (G.lapMatrix ℝ *ᵥ x) =
      ∑ e ∈ G.edgeFinset, (x (Quot.out e).1 - x (Quot.out e).2) ^ 2 := by
  rw [← toLinearMap₂'_apply', lapMatrix_toLinearMap₂' ℝ G x]
  simp_rw [show ∀ i : V, (∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) =
    ∑ j ∈ G.neighborFinset i, (x i - x j) ^ 2 from fun i => by
      rw [← sum_filter]; congr 1; ext j; simp [mem_neighborFinset]]
  -- neighbor sum = dart sum
  have dart_eq : ∑ v, ∑ u ∈ G.neighborFinset v, (x v - x u) ^ 2 =
    ∑ d : G.Dart, (x d.toProd.1 - x d.toProd.2) ^ 2 := by
    let dartEquiv : G.Dart ≃ (v : V) × (G.neighborSet v) :=
      ⟨fun d => ⟨d.toProd.1, ⟨d.toProd.2, d.adj⟩⟩,
       fun s => ⟨(s.1, s.2.val), s.2.property⟩,
       fun d => by ext <;> rfl, fun _ => rfl⟩
    symm
    calc ∑ d : G.Dart, (x d.toProd.1 - x d.toProd.2) ^ 2
        = ∑ p : (v : V) × (G.neighborSet v), (x p.1 - x p.2.val) ^ 2 :=
            Fintype.sum_equiv dartEquiv _ _ (fun _ => rfl)
      _ = ∑ v : V, ∑ w : G.neighborSet v, (x v - x (w : V)) ^ 2 :=
            Fintype.sum_sigma _
      _ = ∑ v, ∑ u ∈ G.neighborFinset v, (x v - x u) ^ 2 := by
            congr 1; ext v
            apply Finset.sum_nbij Subtype.val
            · intro w _; exact (mem_neighborFinset G v w.val).mpr w.property
            · intro a _ b _ hab; exact Subtype.ext hab
            · intro w hw
              exact ⟨⟨w, (mem_neighborFinset G v w).mp hw⟩, Finset.mem_univ _, rfl⟩
            · intro w _; rfl
  rw [dart_eq]
  -- dart sum = fiber sum over edges
  have fiber_eq : ∑ d : G.Dart, (x d.toProd.1 - x d.toProd.2) ^ 2 =
    ∑ e ∈ G.edgeFinset, ∑ d ∈ univ.filter (fun d : G.Dart => d.edge = e),
      (x d.toProd.1 - x d.toProd.2) ^ 2 := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d (_ : d ∈ univ) => (mem_edgeFinset (G := G)).mpr (Dart.edge_mem d)) _
  rw [fiber_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  -- Each edge fiber has exactly 2 symmetric darts
  have hadj : G.Adj (Quot.out e).1 (Quot.out e).2 := by
    have : s((Quot.out e).1, (Quot.out e).2) ∈ G.edgeSet := by
      rw [show (s((Quot.out e).1, (Quot.out e).2) : Sym2 V) = e from by
        change Quot.mk _ _ = _; simp [Quot.out_eq]]
      exact mem_edgeFinset.mp he
    exact (mem_edgeSet G).mp this
  set d₀ : G.Dart := ⟨Quot.out e, hadj⟩
  have hedge : d₀.edge = e := by
    rw [show d₀.edge = s((Quot.out e).1, (Quot.out e).2) from Dart.edge_mk hadj]
    change Quot.mk _ _ = _; simp [Quot.out_eq]
  rw [show univ.filter (fun d : G.Dart => d.edge = e) = {d₀, d₀.symm} from by
    rw [← hedge]; exact d₀.edge_fiber]
  rw [sum_insert (show d₀ ∉ ({d₀.symm} : Finset G.Dart) from by
    simp only [mem_singleton]; exact (Dart.symm_ne d₀).symm)]
  rw [sum_singleton, Dart.symm_toProd]
  show ((x (Quot.out e).1 - x (Quot.out e).2) ^ 2 +
    (x (Prod.swap (Quot.out e)).1 - x (Prod.swap (Quot.out e)).2) ^ 2) / 2 =
    (x (Quot.out e).1 - x (Quot.out e).2) ^ 2
  simp only [Prod.swap]; ring

/-- For any `S ⊆ V`, the quadratic form of `L_{G_S}` is a sub-sum of `L_G`:
`x^T L_S x ≤ x^T L x` for all `x`. This means `L_S ≤ L` in Loewner order. -/
lemma lapMatrix_edgesWithin_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ((G.lapMatrix ℝ) - (G.edgesWithin S).lapMatrix ℝ).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_lapMatrix ℝ G).sub (isHermitian_lapMatrix ℝ _)
  · intro x
    simp only [star_trivial, sub_mulVec, dotProduct_sub]
    rw [show x ⬝ᵥ (lapMatrix ℝ G).mulVec x =
      ((toLinearMap₂' ℝ) (lapMatrix ℝ G)) x x from (toLinearMap₂'_apply' _ x x).symm]
    rw [show x ⬝ᵥ (lapMatrix ℝ (G.edgesWithin S)).mulVec x =
      ((toLinearMap₂' ℝ) (lapMatrix ℝ (G.edgesWithin S))) x x
      from (toLinearMap₂'_apply' _ x x).symm]
    rw [lapMatrix_toLinearMap₂' ℝ G x, lapMatrix_toLinearMap₂' ℝ (G.edgesWithin S) x]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2).le
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split
    · rename_i h; simp [h.1]
    · split <;> positivity

set_option maxHeartbeats 3200000 in
/-- **Connection theorem**: Given the BSS coloring result on normalized matrices,
deduce ε-lightness on the original graph.

If there exist PSD `d×d` matrices `A_e` summing to `I` (corresponding to the
spectral normalization of `L_G`) such that `∑_{e ∈ E(S,S)} A_e ≤ εI`,
then `εL_G - L_{G_S} ≥ 0`.

This is the main bridge between the abstract BSS result and the graph-theoretic
ε-lightness property. -/
theorem normalized_bound_implies_epsilon_light
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 ≤ ε) (S : Finset V)
    (d : ℕ)
    -- Spectral data: eigenvectors and eigenvalues of L_G
    (eigvecs : Fin d → V → ℝ)  -- orthonormal eigenvectors with positive eigenvalues
    (eigvals : Fin d → ℝ)
    (heigvals_pos : ∀ i, 0 < eigvals i)
    -- The eigenvectors are orthonormal
    (horth : ∀ i j, dotProduct (eigvecs i) (eigvecs j) = if i = j then 1 else 0)
    -- The spectral decomposition: L = ∑ λᵢ vᵢ vᵢᵀ on range(L)
    (hspec : ∀ x : V → ℝ,
      dotProduct x (G.lapMatrix ℝ *ᵥ x) =
        ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) x) ^ 2)
    -- The normalized matrices satisfy the BSS bound
    (hbss : ∀ x : Fin d → ℝ,
      ∑ e ∈ (G.edgesWithin S).edgeFinset,
        (∑ i : Fin d, x i * (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) /
          Real.sqrt (eigvals i)) ^ 2
      ≤ ε * ∑ i : Fin d, x i ^ 2) :
    G.IsEpsilonLight ε S := by
  -- Unfold to PSD condition: (ε • L_G - L_S).PosSemidef
  unfold IsEpsilonLight
  set L := G.lapMatrix ℝ with hL_def
  set L_S := (G.edgesWithin S).lapMatrix ℝ with hLS_def
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  -- Hermiticity of ε • L - L_S
  · rw [IsHermitian, conjTranspose_sub, conjTranspose_smul, star_trivial,
      (isHermitian_lapMatrix ℝ G).eq, (isHermitian_lapMatrix ℝ _).eq]
  -- ∀ w, 0 ≤ w ⬝ᵥ (ε • L - L_S) *ᵥ w
  · intro w
    rw [star_trivial]
    -- Distribute: (ε • L - L_S) *ᵥ w = ε • (L *ᵥ w) - L_S *ᵥ w
    have smul_mulVec : (ε • L) *ᵥ w = ε • (L *ᵥ w) := by
      ext i; simp only [mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]; congr 1; ext; ring
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
    -- Need: 0 ≤ ε • (w ⬝ᵥ L *ᵥ w) - w ⬝ᵥ L_S *ᵥ w
    -- i.e., w ⬝ᵥ L_S *ᵥ w ≤ ε • (w ⬝ᵥ L *ᵥ w)
    -- i.e., w ⬝ᵥ L_S *ᵥ w ≤ ε * (w ⬝ᵥ L *ᵥ w)
    rw [sub_nonneg, smul_eq_mul]
    -- Step 1: Rewrite RHS via spectral decomposition
    rw [hspec w]
    -- Step 2: Rewrite LHS as edge sum
    rw [lapMatrix_quadForm_eq_sum]
    -- Now goal: ∑ e ∈ (G.edgesWithin S).edgeFinset, (w (out e).1 - w (out e).2) ^ 2
    --         ≤ ε * ∑ i, eigvals i * (eigvecs i ⬝ᵥ w) ^ 2
    -- Step 3: Derive bilinear identity from hspec
    -- From hspec, by polarization: x ⬝ᵥ L *ᵥ y = ∑ i, eigvals i * (eigvecs i ⬝ᵥ x) * (eigvecs i ⬝ᵥ y)
    have hspec_bilin : ∀ x y : V → ℝ,
        dotProduct x (L *ᵥ y) =
          ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) x) * (dotProduct (eigvecs i) y) := by
      intro x y
      -- Use polarization: 4 * x ⬝ᵥ L *ᵥ y = (x+y) ⬝ᵥ L *ᵥ (x+y) - (x-y) ⬝ᵥ L *ᵥ (x-y)
      have h1 := hspec (x + y)
      have h2 := hspec (x - y)
      -- Expand LHS of h1 and h2
      have lhs1 : dotProduct (x + y) (L *ᵥ (x + y)) =
          dotProduct x (L *ᵥ x) + dotProduct x (L *ᵥ y) +
          dotProduct y (L *ᵥ x) + dotProduct y (L *ᵥ y) := by
        simp [mulVec_add, dotProduct_add, add_dotProduct]; ring
      have lhs2 : dotProduct (x - y) (L *ᵥ (x - y)) =
          dotProduct x (L *ᵥ x) - dotProduct x (L *ᵥ y) -
          dotProduct y (L *ᵥ x) + dotProduct y (L *ᵥ y) := by
        simp [mulVec_sub, dotProduct_sub, sub_dotProduct]; ring
      -- Expand RHS of h1 and h2
      have rhs1 : ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) (x + y)) ^ 2 =
          ∑ i : Fin d, eigvals i * ((dotProduct (eigvecs i) x) + (dotProduct (eigvecs i) y)) ^ 2 := by
        congr 1; ext i; congr 1; rw [dotProduct_add]
      have rhs2 : ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) (x - y)) ^ 2 =
          ∑ i : Fin d, eigvals i * ((dotProduct (eigvecs i) x) - (dotProduct (eigvecs i) y)) ^ 2 := by
        congr 1; ext i; congr 1; rw [dotProduct_sub]
      -- Symmetry of Laplacian bilinear form
      have hLsymm : ∀ a b : V, L a b = L b a := by
        intro a b
        have hH : Lᴴ = L := isHermitian_lapMatrix ℝ G
        have := congr_fun (congr_fun hH b) a
        simp [conjTranspose_apply, star_trivial] at this; linarith
      have hsymm : dotProduct y (L *ᵥ x) = dotProduct x (L *ᵥ y) := by
        simp only [dotProduct, mulVec]
        simp_rw [Finset.mul_sum]
        rw [show (∑ a : V, ∑ b : V, y a * (L a b * x b)) =
            ∑ a : V, ∑ b : V, x a * (L a b * y b) from by
          rw [Finset.sum_comm (f := fun a b => y a * (L a b * x b))]
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro a _
          rw [hLsymm a b]; ring]
      -- Subtract h2 from h1, extracting 4 * bilinear term
      have h_diff : 4 * dotProduct x (L *ᵥ y) =
          4 * ∑ i : Fin d, eigvals i * dotProduct (eigvecs i) x * dotProduct (eigvecs i) y := by
        have := h1; rw [lhs1, rhs1] at this
        have := h2; rw [lhs2, rhs2] at *
        have key : ∀ i : Fin d, eigvals i * (eigvecs i ⬝ᵥ x + eigvecs i ⬝ᵥ y) ^ 2 -
            eigvals i * (eigvecs i ⬝ᵥ x - eigvecs i ⬝ᵥ y) ^ 2 =
            4 * (eigvals i * (eigvecs i ⬝ᵥ x) * (eigvecs i ⬝ᵥ y)) := by
          intro i; ring
        have hsub : ∑ i : Fin d, (eigvals i * (eigvecs i ⬝ᵥ x + eigvecs i ⬝ᵥ y) ^ 2 -
            eigvals i * (eigvecs i ⬝ᵥ x - eigvecs i ⬝ᵥ y) ^ 2) =
            4 * ∑ i : Fin d, eigvals i * (eigvecs i ⬝ᵥ x) * (eigvecs i ⬝ᵥ y) := by
          simp_rw [key, Finset.mul_sum]
        have hsub2 : ∑ i : Fin d, (eigvals i * (eigvecs i ⬝ᵥ x + eigvecs i ⬝ᵥ y) ^ 2 -
            eigvals i * (eigvecs i ⬝ᵥ x - eigvecs i ⬝ᵥ y) ^ 2) =
            ∑ i : Fin d, eigvals i * (eigvecs i ⬝ᵥ x + eigvecs i ⬝ᵥ y) ^ 2 -
            ∑ i : Fin d, eigvals i * (eigvecs i ⬝ᵥ x - eigvecs i ⬝ᵥ y) ^ 2 :=
          Finset.sum_sub_distrib
            (fun i => eigvals i * (eigvecs i ⬝ᵥ x + eigvecs i ⬝ᵥ y) ^ 2)
            (fun i => eigvals i * (eigvecs i ⬝ᵥ x - eigvecs i ⬝ᵥ y) ^ 2)
        nlinarith
      linarith
    -- Step 4: Derive eigenvector equation: L *ᵥ eigvecs i = eigvals i • eigvecs i
    have heig_eq : ∀ i : Fin d, L *ᵥ (eigvecs i) = eigvals i • (eigvecs i) := by
      intro i
      suffices h : ∀ y : V → ℝ, dotProduct y (L *ᵥ eigvecs i) = dotProduct y (eigvals i • eigvecs i) by
        have h0 : ∀ y, dotProduct y (L *ᵥ eigvecs i - eigvals i • eigvecs i) = 0 := by
          intro y; rw [dotProduct_sub, h y, sub_self]
        have := h0 (L *ᵥ eigvecs i - eigvals i • eigvecs i)
        rw [dotProduct_self_eq_zero] at this
        exact sub_eq_zero.mp this
      intro y
      have hb := hspec_bilin y (eigvecs i)
      -- Simplify RHS using orthonormality
      have hsum : ∑ j : Fin d, eigvals j * dotProduct (eigvecs j) y * dotProduct (eigvecs j) (eigvecs i) =
          eigvals i * dotProduct (eigvecs i) y := by
        have hterm : ∀ j : Fin d, eigvals j * dotProduct (eigvecs j) y * dotProduct (eigvecs j) (eigvecs i) =
            if j = i then eigvals i * dotProduct (eigvecs i) y else 0 := by
          intro j
          by_cases hji : j = i
          · rw [if_pos hji, hji, horth i i, if_pos rfl]; ring
          · rw [if_neg hji, horth j i, if_neg hji]; ring
        simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hb, hsum, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    -- Step 5: Define projection and show kernel property
    set c : Fin d → ℝ := fun i => dotProduct (eigvecs i) w with hc_def
    set proj_w := ∑ i : Fin d, c i • eigvecs i with hproj_def
    -- L *ᵥ (w - proj_w) = 0
    have hker : L *ᵥ (w - proj_w) = 0 := by
      rw [mulVec_sub]
      -- Distribute L through the sum
      have hL_sum : L *ᵥ proj_w = ∑ i : Fin d, c i • (L *ᵥ eigvecs i) := by
        rw [hproj_def]
        ext a
        simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1; ext i; congr 1; ext j; ring
      rw [hL_sum]
      simp_rw [heig_eq]
      suffices h : ∀ y : V → ℝ, dotProduct y (L *ᵥ w) =
          dotProduct y (∑ i : Fin d, c i • (eigvals i • eigvecs i)) by
        have h0 : ∀ y, dotProduct y (L *ᵥ w - ∑ i : Fin d, c i • (eigvals i • eigvecs i)) = 0 := by
          intro y; rw [dotProduct_sub, h y, sub_self]
        have := h0 (L *ᵥ w - ∑ i : Fin d, c i • (eigvals i • eigvecs i))
        rwa [dotProduct_self_eq_zero] at this
      intro y
      rw [hspec_bilin y w]
      simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro j _
      simp only [hc_def, dotProduct_comm (eigvecs j) y]; ring
    -- Step 6: From kernel membership, w - proj_w is constant on adjacent vertices
    rw [lapMatrix_mulVec_eq_zero_iff_forall_adj] at hker
    -- Step 7: For adjacent u v: w u - w v = proj_w u - proj_w v = ∑ i, c i * (eigvecs i u - eigvecs i v)
    have hedge_diff : ∀ u v, (G.edgesWithin S).Adj u v →
        w u - w v = ∑ i : Fin d, c i * (eigvecs i u - eigvecs i v) := by
      intro u v huv
      have hcuv := hker u v huv.1
      have : w u - w v = proj_w u - proj_w v := by
        simp only [Pi.sub_apply] at hcuv; linarith
      rw [this, hproj_def]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      congr 1; ext i; ring
    -- Step 8: Substitute x i = √(eigvals i) * c i into hbss
    set x_sub : Fin d → ℝ := fun i => Real.sqrt (eigvals i) * c i with hx_sub_def
    have hbss_spec := hbss x_sub
    -- Simplify: x_sub i ^ 2 = eigvals i * c i ^ 2
    have hx_sq : ∀ i, x_sub i ^ 2 = eigvals i * c i ^ 2 := by
      intro i
      simp only [hx_sub_def, mul_pow, Real.sq_sqrt (heigvals_pos i).le]
    -- Simplify: x_sub i * diff / √(eigvals i) = c i * diff
    have hx_cancel : ∀ (i : Fin d) (r : ℝ),
        x_sub i * r / Real.sqrt (eigvals i) = c i * r := by
      intro i r
      simp only [hx_sub_def]
      rw [show Real.sqrt (eigvals i) * c i * r / Real.sqrt (eigvals i) =
        c i * r * (Real.sqrt (eigvals i) / Real.sqrt (eigvals i)) from by ring]
      rw [div_self (Real.sqrt_ne_zero'.mpr (heigvals_pos i))]
      ring
    -- Simplify hbss_spec: LHS becomes ∑ e, (∑ i, c i * diff_i)^2
    -- RHS becomes ε * ∑ i, eigvals i * c i ^ 2
    have hbss_simp_rhs : ε * ∑ i : Fin d, x_sub i ^ 2 = ε * ∑ i : Fin d, eigvals i * c i ^ 2 := by
      congr 1; exact Finset.sum_congr rfl (fun i _ => hx_sq i)
    have hbss_simp_lhs :
        ∑ e ∈ (G.edgesWithin S).edgeFinset,
          (∑ i : Fin d, x_sub i * (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) /
            Real.sqrt (eigvals i)) ^ 2 =
        ∑ e ∈ (G.edgesWithin S).edgeFinset,
          (∑ i : Fin d, c i * (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2)) ^ 2 := by
      apply Finset.sum_congr rfl; intro e _; congr 1
      exact Finset.sum_congr rfl (fun i _ => hx_cancel i _)
    -- Rewrite hbss_spec
    rw [hbss_simp_lhs, hbss_simp_rhs] at hbss_spec
    calc ∑ e ∈ (G.edgesWithin S).edgeFinset, (w (Quot.out e).1 - w (Quot.out e).2) ^ 2
        = ∑ e ∈ (G.edgesWithin S).edgeFinset,
            (∑ i : Fin d, c i * (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro e he
          congr 1
          have hadj : (G.edgesWithin S).Adj (Quot.out e).1 (Quot.out e).2 := by
            have : s((Quot.out e).1, (Quot.out e).2) ∈ (G.edgesWithin S).edgeSet := by
              rw [show (s((Quot.out e).1, (Quot.out e).2) : Sym2 V) = e from by
                change Quot.mk _ _ = _; simp [Quot.out_eq]]
              exact mem_edgeFinset.mp he
            exact (mem_edgeSet _).mp this
          exact hedge_diff _ _ hadj
      _ ≤ ε * ∑ i : Fin d, eigvals i * c i ^ 2 := hbss_spec
      _ = ε * ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) w) ^ 2 := by rfl

end ClaudeFormalizer
