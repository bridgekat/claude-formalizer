/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ClaudeFormalizer.Defs
import ClaudeFormalizer.Coloring
import ClaudeFormalizer.Connection

/-!
# Main Theorem: Large ε-Light Vertex Subsets

Combines the BSS coloring theorem with the spectral normalization connection
to prove the main result: every graph has an ε-light subset of size ≥ (ε/256)|V|.
-/

open Matrix Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Helper lemmas for degenerate cases -/

/-- The Laplacian of a graph with no adjacencies is zero. -/
private lemma lapMatrix_eq_zero_of_no_adj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ u v : V, ¬G.Adj u v) :
    G.lapMatrix ℝ = 0 := by
  ext i j
  simp only [lapMatrix, sub_apply, zero_apply, degMatrix, diagonal_apply, adjMatrix_apply]
  rw [if_neg (h i j), sub_zero]
  split_ifs
  · norm_cast; unfold degree; convert card_empty
    rw [neighborFinset, Set.toFinset_eq_empty]
    ext w; simp [SimpleGraph.mem_neighborSet, h]
  · rfl

/-! ### Degenerate cases -/

/-- Case ε = 0: the empty set is 0-light, with size 0 ≥ 0. -/
lemma epsilon_light_empty_of_eps_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsEpsilonLight 0 ∅ := by
  unfold IsEpsilonLight
  have : (G.edgesWithin (∅ : Finset V)).lapMatrix ℝ = 0 :=
    lapMatrix_eq_zero_of_no_adj _ fun u v ⟨_, hu, _⟩ => absurd hu (notMem_empty u)
  rw [zero_smul, zero_sub, this, neg_zero]
  exact PosSemidef.zero

/-- Case: edgeless graph. `S = V` is ε-light for any ε. -/
lemma epsilon_light_univ_of_edgeless
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.edgeFinset = ∅) (ε : ℝ) (hε : 0 ≤ ε) :
    G.IsEpsilonLight ε univ := by
  have hbot : G = ⊥ := edgeFinset_eq_empty.mp hG
  have hno : ∀ u v : V, ¬G.Adj u v := fun u v h => by subst hbot; exact h
  have hno2 : ∀ u v : V, ¬(G.edgesWithin univ).Adj u v :=
    fun u v ⟨h, _, _⟩ => hno u v h
  unfold IsEpsilonLight
  rw [lapMatrix_eq_zero_of_no_adj G hno, lapMatrix_eq_zero_of_no_adj _ hno2]
  simp [PosSemidef.zero]

/-- Case: single vertex. `{v}` is ε-light for any ε ≥ 0. -/
lemma epsilon_light_singleton
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ε : ℝ) (hε : 0 ≤ ε) :
    G.IsEpsilonLight ε {v} := by
  have : (G.edgesWithin ({v} : Finset V)).lapMatrix ℝ = 0 :=
    lapMatrix_eq_zero_of_no_adj _ fun u w ⟨hadj, hu, hw⟩ => by
      rw [mem_singleton.mp hu, mem_singleton.mp hw] at hadj
      exact G.loopless.irrefl v hadj
  unfold IsEpsilonLight
  rw [this, sub_zero]
  exact (posSemidef_lapMatrix ℝ G).smul hε

/-- Size bound for small graphs (n ≤ 3): a singleton has size ≥ εn/256. -/
lemma singleton_size_bound
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (n : ℕ) (hn : n ≤ 3) (hn0 : 0 < n) :
    ε / 256 * (n : ℝ) ≤ 1 := by
  have h2 : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  have h3 : ε / 256 ≤ 1 / 256 := div_le_div_of_nonneg_right hε₁ (by norm_num)
  nlinarith

/-! ### Spectral normalization and assembly -/

/-! #### Spectral data definitions -/

/-- The positive eigenvalue indices of the Laplacian. -/
private noncomputable def posEigenvalueFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun i => 0 < (isHermitian_lapMatrix ℝ G).eigenvalues i

/-- The number of positive eigenvalues. -/
private noncomputable def posEigenvalueCount
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (posEigenvalueFinset G).card

/-- Equivalence between `Fin d` and the positive eigenvalue indices. -/
private noncomputable def posEigenvalueEquiv
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (posEigenvalueCount G) ≃ (posEigenvalueFinset G) :=
  (posEigenvalueFinset G).equivFin.symm

/-- The positive eigenvalues, indexed by `Fin d`. -/
private noncomputable def posEigenvals
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (posEigenvalueCount G) → ℝ :=
  fun k => (isHermitian_lapMatrix ℝ G).eigenvalues ((posEigenvalueEquiv G k).val : V)

/-- The eigenvectors for positive eigenvalues as plain functions `V → ℝ`. -/
private noncomputable def posEigenvecs
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (posEigenvalueCount G) → V → ℝ :=
  fun k => (WithLp.equiv 2 (V → ℝ))
    ((isHermitian_lapMatrix ℝ G).eigenvectorBasis ((posEigenvalueEquiv G k).val : V))

/-! #### Properties of spectral data -/

private lemma posEigenvals_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : Fin (posEigenvalueCount G)) : 0 < posEigenvals G k := by
  unfold posEigenvals
  have hk := (posEigenvalueEquiv G k).property
  simp only [posEigenvalueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hk

private lemma posEigenvalueCount_pos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : 0 < posEigenvalueCount G := by
  rw [posEigenvalueCount, Finset.card_pos]
  -- G has edges => L_G ≠ 0 => some eigenvalue is nonzero => some eigenvalue is positive
  -- (since L is PSD, all eigenvalues are ≥ 0, so nonzero means positive)
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  -- All eigenvalues are ≤ 0
  have hall : ∀ i : V, (isHermitian_lapMatrix ℝ G).eigenvalues i ≤ 0 := by
    intro i
    by_contra hi
    push_neg at hi
    have : i ∈ posEigenvalueFinset G := by
      simp only [posEigenvalueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    rw [h] at this; simp at this
  -- Since L is PSD, eigenvalues ≥ 0, so all eigenvalues = 0
  have hpsd := posSemidef_lapMatrix ℝ G
  have hall0 : ∀ i : V, (isHermitian_lapMatrix ℝ G).eigenvalues i = 0 := by
    intro i
    have hge : 0 ≤ (isHermitian_lapMatrix ℝ G).eigenvalues i := by
      have := hpsd.eigenvalues_nonneg i
      simp only [Matrix.IsHermitian.eigenvalues] at this ⊢
      exact this
    linarith [hall i]
  -- All eigenvalues zero means L = 0
  have hL0 : G.lapMatrix ℝ = 0 := by
    rwa [← Matrix.IsHermitian.eigenvalues_eq_zero_iff (isHermitian_lapMatrix ℝ G), funext_iff]
  -- But G has edges, so L ≠ 0
  obtain ⟨e, he⟩ := hG
  have hadj : G.Adj (Quot.out e).1 (Quot.out e).2 := by
    have : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).mp he
    exact (SimpleGraph.mem_edgeSet G).mp (by
      rw [show s((Quot.out e).1, (Quot.out e).2) = e from by
        change Quot.mk _ _ = _; simp [Quot.out_eq]]
      exact this)
  -- Use adjacency to show L has a nonzero entry
  have hne : (Quot.out e).1 ≠ (Quot.out e).2 := G.ne_of_adj hadj
  have : (G.lapMatrix ℝ) (Quot.out e).1 (Quot.out e).2 = -1 := by
    simp [lapMatrix, sub_apply, degMatrix, diagonal_apply, adjMatrix_apply, hne, hadj]
  rw [hL0] at this
  simp at this

private lemma posEigenvalueCount_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    posEigenvalueCount G ≤ Fintype.card V := by
  unfold posEigenvalueCount posEigenvalueFinset
  exact (Finset.card_filter_le _ _).trans (Finset.card_univ.le)

set_option maxHeartbeats 400000 in
/-- Loewner bound on outer-product sum implies sum-of-squares bound. -/
private lemma loewner_to_sum_sq {d : ℕ} {ι : Type*} (S : Finset ι)
    (w : ι → Fin d → ℝ) (ε : ℝ)
    (hpsd : (ε • (1 : Matrix (Fin d) (Fin d) ℝ) -
      ∑ e ∈ S, vecMulVec (w e) (w e)).PosSemidef) :
    ∀ x : Fin d → ℝ,
      ∑ e ∈ S, (dotProduct (w e) x) ^ 2 ≤ ε * ∑ i, x i ^ 2 := by
  intro x
  have h := hpsd.dotProduct_mulVec_nonneg x
  rw [star_trivial, sub_mulVec, dotProduct_sub] at h
  have h1 : dotProduct x ((ε • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x) = ε * ∑ i, x i ^ 2 := by
    rw [smul_mulVec ε (1 : Matrix (Fin d) (Fin d) ℝ) x, one_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1; simp [dotProduct, sq]
  have h2 : dotProduct x ((∑ e ∈ S, vecMulVec (w e) (w e)) *ᵥ x) =
      ∑ e ∈ S, (dotProduct (w e) x) ^ 2 := by
    rw [sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl; intro e _
    simp only [dotProduct, vecMulVec, mulVec, of_apply]
    simp_rw [Finset.mul_sum, ← Finset.sum_product']
    rw [show (∑ p ∈ univ ×ˢ univ, x p.1 * (w e p.1 * w e p.2 * x p.2)) =
      (∑ i, w e i * x i) * (∑ j, w e j * x j) from by
      rw [Finset.sum_product]; simp_rw [Finset.mul_sum, Finset.sum_mul]
      congr 1; ext i; congr 1; ext j; ring]
    ring
  rw [h1, h2] at h; linarith

/-- Spectral extraction: the Laplacian's positive-eigenvalue spectral data and
the normalization identity ∑_e vecMulVec(w_e)(w_e) = I.

Given a graph G with edges on n ≥ 4 vertices, the Laplacian L_G has d ≥ 1 positive
eigenvalues (where d = rank(L_G) ≤ n). The eigenvectors form an orthonormal set,
L decomposes as ∑ λᵢ vᵢ vᵢᵀ on its range, and the normalized edge outer products
sum to the identity on ℝ^d. -/
private lemma spectral_extraction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty)
    (hn : 4 ≤ Fintype.card V) :
    ∃ (d : ℕ) (_ : 0 < d) (_ : d ≤ Fintype.card V)
      (eigvecs : Fin d → V → ℝ) (eigvals : Fin d → ℝ),
      (∀ i, 0 < eigvals i) ∧
      (∀ i j, dotProduct (eigvecs i) (eigvecs j) = if i = j then 1 else 0) ∧
      (∀ x : V → ℝ, dotProduct x (G.lapMatrix ℝ *ᵥ x) =
        ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) x) ^ 2) ∧
      (let A : Sym2 V → Matrix (Fin d) (Fin d) ℝ := fun e =>
        vecMulVec (fun i => (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) /
          Real.sqrt (eigvals i))
          (fun i => (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) /
          Real.sqrt (eigvals i))
      ∑ e ∈ G.edgeFinset, A e = 1) := by
  set d := posEigenvalueCount G
  set hL := isHermitian_lapMatrix ℝ G
  set b := hL.eigenvectorBasis (𝕜 := ℝ) with hb_def
  set evals := hL.eigenvalues with hevals_def
  set eigvecs := posEigenvecs G
  set eigvals := posEigenvals G
  refine ⟨d, posEigenvalueCount_pos G hG, posEigenvalueCount_le_card G, eigvecs, eigvals,
    posEigenvals_pos G, ?_, ?_, ?_⟩
  -- Goal 1: Orthonormality
  · intro i j
    set i' := (posEigenvalueEquiv G i).val with hi'_def
    set j' := (posEigenvalueEquiv G j).val with hj'_def
    -- Convert dotProduct to inner product on EuclideanSpace
    have key : dotProduct (eigvecs i) (eigvecs j) = @inner ℝ _ _ (b i') (b j') := by
      show dotProduct (posEigenvecs G i) (posEigenvecs G j) = _
      unfold posEigenvecs
      change dotProduct ((b i').ofLp) ((b j').ofLp) = _
      have : @inner ℝ _ _ (b i') (b j') = dotProduct ((b j').ofLp) (star ((b i').ofLp)) :=
        EuclideanSpace.inner_eq_star_dotProduct (b i') (b j')
      rw [star_trivial, dotProduct_comm] at this
      exact this.symm
    trans (if i' = j' then (1 : ℝ) else 0)
    · rw [key]; exact b.inner_eq_ite i' j'
    · by_cases hij : i = j
      · subst hij; simp [show i' = j' from rfl]
      · have hi'j' : i' ≠ j' := by
          intro h; apply hij
          have h2 : (posEigenvalueEquiv G i : posEigenvalueFinset G) =
              (posEigenvalueEquiv G j : posEigenvalueFinset G) :=
            Subtype.ext h
          exact (posEigenvalueEquiv G).injective h2
        simp [hij, hi'j']
  -- Goal 2: Spectral quadratic form
  · intro x
    -- Step 1: All-eigenvalue version: x^T L x = ∑ k : V, evals k * (b_k . x)²
    -- Convert x to EuclideanSpace
    set xe := (WithLp.toLp 2 x : EuclideanSpace ℝ V) with hxe_def
    -- Coefficients in eigenbasis
    set c : V → ℝ := fun k => @inner ℝ _ _ (b k) xe with hc_def
    -- x^T L x = dotProduct x (L *v x)
    -- L *v x = L *v (∑ k, c k • b k) = ∑ k, c k • (L *v b k) = ∑ k, c k • (evals k • b k)
    --        = ∑ k, c k * evals k • b k
    -- Step 2: L *v (b k) = evals k • (b k)
    have heig : ∀ k : V, G.lapMatrix ℝ *ᵥ ↑(b k) = evals k • ↑(b k) :=
      hL.mulVec_eigenvectorBasis
    -- Step 3: Express x via basis expansion
    have hx_expand : xe = ∑ k : V, c k • b k :=
      (b.sum_repr' xe).symm
    -- Step 4: Compute L *v x
    -- L *v x = ∑ k, c k * evals k • (b k).ofLp
    have hLx : G.lapMatrix ℝ *ᵥ x =
        ∑ k : V, (c k * evals k) • (b k : EuclideanSpace ℝ V).ofLp := by
      conv_lhs => rw [show x = (xe : EuclideanSpace ℝ V).ofLp from rfl]
      rw [hx_expand]
      -- ofLp distributes: (∑ k, c k • b k).ofLp = ∑ k, c k • (b k).ofLp
      have hofLp_sum : (∑ k, c k • b k : EuclideanSpace ℝ V).ofLp =
          ∑ k : V, c k • (b k : EuclideanSpace ℝ V).ofLp := by
        simp [WithLp.ofLp_sum, WithLp.ofLp_smul]
      rw [hofLp_sum, mulVec_sum]
      congr 1; ext k
      rw [mulVec_smul, heig k, smul_smul, mul_comm]
    -- Step 5: Compute x^T (L *v x) = ∑ k, evals k * c k²
    have hall : dotProduct x (G.lapMatrix ℝ *ᵥ x) = ∑ k : V, evals k * c k ^ 2 := by
      rw [hLx]
      simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
      -- Each term: x . (c k * evals k • b k) = c k * evals k * (x . b k)
      --   = c k * evals k * c k = evals k * c k²
      congr 1; ext k
      -- Show x . (b k).ofLp = c k
      have hdot_eq : x ⬝ᵥ (b k : EuclideanSpace ℝ V).ofLp = c k := by
        -- c k = inner (b k) xe, inner is defn equal to ofLp y . star(ofLp x)
        simp only [hc_def]
        show x ⬝ᵥ (b k).ofLp = @inner ℝ _ _ (b k) xe
        change x ⬝ᵥ (b k).ofLp = xe.ofLp ⬝ᵥ star ((b k).ofLp)
        simp only [star_trivial]
        rfl
      rw [hdot_eq]; ring
    -- Step 6: Split into positive vs non-positive eigenvalue terms
    rw [hall]
    -- ∑ k : V = ∑ k ∈ posEigenvalueFinset G + ∑ k ∉ posEigenvalueFinset G
    -- Non-positive terms vanish (eigenvalue ≤ 0, but PSD so ≥ 0, hence = 0)
    have hzero : ∀ k : V, k ∉ posEigenvalueFinset G → evals k * c k ^ 2 = 0 := by
      intro k hk
      simp only [posEigenvalueFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      have hge : 0 ≤ evals k := (posSemidef_lapMatrix ℝ G).eigenvalues_nonneg k
      have : evals k = 0 := le_antisymm hk hge
      rw [this, zero_mul]
    rw [show (∑ k : V, evals k * c k ^ 2) =
        ∑ k ∈ posEigenvalueFinset G, evals k * c k ^ 2 from by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun k => k ∈ posEigenvalueFinset G)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [show ∑ x ∈ Finset.univ.filter (fun k => k ∉ posEigenvalueFinset G),
          evals x * c x ^ 2 = 0 from by
        apply Finset.sum_eq_zero; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hzero k hk]
      simp]
    -- Now reindex the sum from posEigenvalueFinset G to Fin d
    -- We need: ∑ k ∈ posEigenvalueFinset G, evals k * c k ^ 2
    --        = ∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) x) ^ 2
    -- Strategy: convert ∑ over Finset to ∑ over Fin d via the equivFin
    conv_rhs => rw [show (∑ i : Fin d, eigvals i * (dotProduct (eigvecs i) x) ^ 2) =
        ∑ i : Fin d, evals ((posEigenvalueEquiv G i).val : V) *
          c ((posEigenvalueEquiv G i).val : V) ^ 2 from by
      congr 1; ext i
      simp only [posEigenvals, posEigenvecs, eigvals, eigvecs]
      congr 1
      congr 1
      -- Show dotProduct (posEigenvecs G i) x = c ((posEigenvalueEquiv G i).val)
      show dotProduct ((b ((posEigenvalueEquiv G i).val : V)).ofLp) x =
          @inner ℝ _ _ (b ((posEigenvalueEquiv G i).val : V)) xe
      -- inner (b v) xe = ofLp xe . star(ofLp (b v)) = x . (b v).ofLp
      -- Goal: dotProduct (posEigenvecs G i) x = inner (b v) xe
      -- = ofLp xe . star (ofLp (b v)) = ofLp xe . ofLp (b v) = x . (b v).ofLp
      -- = (b v).ofLp . x  (by dotProduct_comm)
      -- And posEigenvecs G i = (b v).ofLp
      -- So it reduces to: (b v).ofLp . x = x . (b v).ofLp
      change dotProduct ((b _).ofLp) x = (xe).ofLp ⬝ᵥ star ((b _).ofLp)
      rw [star_trivial, dotProduct_comm]]
    -- Now both sides sum the same function, just with different indexing
    rw [← Finset.sum_coe_sort (posEigenvalueFinset G)]
    set g : ↥(posEigenvalueFinset G) → ℝ := fun v => evals (v : V) * c (v : V) ^ 2
    show (∑ v : ↥(posEigenvalueFinset G), g v) =
        ∑ i : Fin d, g ((posEigenvalueEquiv G) i)
    rw [(posEigenvalueEquiv G).sum_comp g]
  -- Goal 3: Normalized edge matrix sum = identity
  · -- Need: ∑ e ∈ G.edgeFinset, A e = 1 where A e = vecMulVec w w
    -- Proof: entry (i,j) of ∑ A_e = delta_{ij}
    -- (∑ A_e)_{ij} = ∑_e w_e(i) * w_e(j)
    --   = ∑_e (b_i(u) - b_i(v)) * (b_j(u) - b_j(v)) / (sqrt(λ_i) * sqrt(λ_j))
    --   = [b_i^T L b_j] / (sqrt(λ_i) * sqrt(λ_j))  [by polarization]
    --   = λ_j * δ_{ij} / (sqrt(λ_i) * sqrt(λ_j))
    --   = δ_{ij}
    -- Step 1: Bilinear form via polarization
    -- First prove: dotProduct f (L *v g) = ∑ e, (f u - f v)(g u - g v)
    -- Using lapMatrix_quadForm_eq_sum and polarization identity
    have hquad := ClaudeFormalizer.lapMatrix_quadForm_eq_sum G
    -- Polarization: 4 * f^T L g = (f+g)^T L (f+g) - (f-g)^T L (f-g)
    have hbilin : ∀ f g : V → ℝ, dotProduct f (G.lapMatrix ℝ *ᵥ g) =
        ∑ e ∈ G.edgeFinset,
          (f (Quot.out e).1 - f (Quot.out e).2) * (g (Quot.out e).1 - g (Quot.out e).2) := by
      intro f' g'
      have h1 := hquad (f' + g')
      have h2 := hquad (f' - g')
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2
      have hlhs1 : dotProduct (f' + g') (G.lapMatrix ℝ *ᵥ (f' + g')) =
          dotProduct f' (G.lapMatrix ℝ *ᵥ f') + dotProduct f' (G.lapMatrix ℝ *ᵥ g') +
          dotProduct g' (G.lapMatrix ℝ *ᵥ f') + dotProduct g' (G.lapMatrix ℝ *ᵥ g') := by
        simp [mulVec_add, dotProduct_add, add_dotProduct]; ring
      have hlhs2 : dotProduct (f' - g') (G.lapMatrix ℝ *ᵥ (f' - g')) =
          dotProduct f' (G.lapMatrix ℝ *ᵥ f') - dotProduct f' (G.lapMatrix ℝ *ᵥ g') -
          dotProduct g' (G.lapMatrix ℝ *ᵥ f') + dotProduct g' (G.lapMatrix ℝ *ᵥ g') := by
        simp [mulVec_sub, dotProduct_sub, sub_dotProduct]; ring
      -- Symmetry of bilinear form
      have hLsymm : ∀ a b : V, (G.lapMatrix ℝ) a b = (G.lapMatrix ℝ) b a := by
        intro a' b'
        have hH : (G.lapMatrix ℝ)ᴴ = G.lapMatrix ℝ := isHermitian_lapMatrix ℝ G
        have := congr_fun (congr_fun hH b') a'
        simp [conjTranspose_apply, star_trivial] at this; linarith
      have hsymm : dotProduct g' (G.lapMatrix ℝ *ᵥ f') =
          dotProduct f' (G.lapMatrix ℝ *ᵥ g') := by
        simp only [dotProduct, mulVec]; simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun a b => g' a * ((G.lapMatrix ℝ) a b * f' b))]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b' _
        rw [hLsymm a b']; ring
      -- Extract 4 * bilinear = diff of quadratic
      have hdiff : 4 * dotProduct f' (G.lapMatrix ℝ *ᵥ g') =
          4 * ∑ e ∈ G.edgeFinset,
            (f' (Quot.out e).1 - f' (Quot.out e).2) * (g' (Quot.out e).1 - g' (Quot.out e).2) := by
        rw [hlhs1, hsymm] at h1; rw [hlhs2, hsymm] at h2
        have hrhs_diff : ∀ e : Sym2 V,
            ((f' + g') (Quot.out e).1 - (f' + g') (Quot.out e).2) ^ 2 -
            ((f' - g') (Quot.out e).1 - (f' - g') (Quot.out e).2) ^ 2 =
            4 * ((f' (Quot.out e).1 - f' (Quot.out e).2) *
                 (g' (Quot.out e).1 - g' (Quot.out e).2)) := by
          intro e; simp only [Pi.add_apply, Pi.sub_apply]; ring
        have hsum_sub := Finset.sum_sub_distrib
            (fun e => ((f' + g') (Quot.out e).1 - (f' + g') (Quot.out e).2) ^ 2)
            (fun e => ((f' - g') (Quot.out e).1 - (f' - g') (Quot.out e).2) ^ 2)
            (s := G.edgeFinset)
        have hsum_eq : ∑ e ∈ G.edgeFinset,
            (((f' + g') (Quot.out e).1 - (f' + g') (Quot.out e).2) ^ 2 -
             ((f' - g') (Quot.out e).1 - (f' - g') (Quot.out e).2) ^ 2) =
            4 * ∑ e ∈ G.edgeFinset,
              (f' (Quot.out e).1 - f' (Quot.out e).2) *
              (g' (Quot.out e).1 - g' (Quot.out e).2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _; exact hrhs_diff e
        rw [hsum_sub] at hsum_eq
        -- Combine: h1 - h2 gives 4*fLg = ∑(f+g)^2 - ∑(f-g)^2
        -- hsum_eq: ∑(f+g)^2 - ∑(f-g)^2 = 4 * ∑ cross
        -- So 4*fLg = 4*∑cross, cancel 4
        -- But hsum_eq uses (f'+g') notation while h1 uses expanded form
        -- Let's convert hsum_eq to match
        have hsum_eq2 : ∑ x ∈ G.edgeFinset,
            (f' (Quot.out x).1 + g' (Quot.out x).1 -
             (f' (Quot.out x).2 + g' (Quot.out x).2)) ^ 2 -
            ∑ x ∈ G.edgeFinset,
            (f' (Quot.out x).1 - g' (Quot.out x).1 -
             (f' (Quot.out x).2 - g' (Quot.out x).2)) ^ 2 =
            4 * ∑ e ∈ G.edgeFinset,
              (f' (Quot.out e).1 - f' (Quot.out e).2) *
              (g' (Quot.out e).1 - g' (Quot.out e).2) := by
          convert hsum_eq using 2 <;> (ext x; simp [Pi.add_apply, Pi.sub_apply])
        linarith
      have h4ne : (4 : ℝ) ≠ 0 := by norm_num
      exact mul_left_cancel₀ h4ne hdiff
    -- Step 2: Eigenvector equation: L *v (b k).ofLp = evals k • (b k).ofLp
    -- (already have heig)
    -- Step 3: Compute b_i^T L b_j
    have heig_bilin : ∀ i j : Fin d,
        ∑ e ∈ G.edgeFinset,
          (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) *
          (eigvecs j (Quot.out e).1 - eigvecs j (Quot.out e).2) =
        if i = j then eigvals i else 0 := by
      intro i' j'
      set vi := (posEigenvalueEquiv G i').val with hvi_def
      set vj := (posEigenvalueEquiv G j').val with hvj_def
      rw [← hbilin]
      -- L *v (b k) = evals k • (b k)
      have heig : ∀ k : V, G.lapMatrix ℝ *ᵥ ↑(b k) = evals k • ↑(b k) :=
        hL.mulVec_eigenvectorBasis
      rw [show (G.lapMatrix ℝ *ᵥ (eigvecs j' : V → ℝ)) = eigvals j' • (eigvecs j' : V → ℝ) from
        heig vj]
      rw [dotProduct_smul, smul_eq_mul]
      -- dotProduct (eigvecs i') (eigvecs j') = δ_{i'j'} (from orthonormality, Goal 1)
      -- We already proved orthonormality, so use the existential witness
      by_cases hij : i' = j'
      · subst hij
        simp only [if_true]
        -- dotProduct (eigvecs i') (eigvecs i') = 1
        have h1 : dotProduct (eigvecs i') (eigvecs i') = 1 := by
          change dotProduct (posEigenvecs G i') (posEigenvecs G i') = 1
          unfold posEigenvecs
          change dotProduct ((b vi).ofLp) ((b vi).ofLp) = 1
          -- Convert to inner product
          have hinner : @inner ℝ _ _ (b vi) (b vi) =
              (b vi : EuclideanSpace ℝ V).ofLp ⬝ᵥ star ((b vi : EuclideanSpace ℝ V).ofLp) :=
            EuclideanSpace.inner_eq_star_dotProduct (b vi) (b vi)
          rw [star_trivial, dotProduct_comm] at hinner
          rw [← hinner]
          exact_mod_cast b.inner_eq_ite vi vi |>.trans (by simp)
        rw [h1, mul_one]
      · simp only [hij, if_false]
        have h0 : dotProduct (eigvecs i') (eigvecs j') = 0 := by
          change dotProduct (posEigenvecs G i') (posEigenvecs G j') = 0
          unfold posEigenvecs
          change dotProduct ((b vi).ofLp) ((b vj).ofLp) = 0
          have hinner : @inner ℝ _ _ (b vi) (b vj) =
              (b vj : EuclideanSpace ℝ V).ofLp ⬝ᵥ star ((b vi : EuclideanSpace ℝ V).ofLp) :=
            EuclideanSpace.inner_eq_star_dotProduct (b vi) (b vj)
          rw [star_trivial, dotProduct_comm] at hinner
          rw [← hinner]
          have hne : vi ≠ vj := by
            intro h; apply hij
            have h2 : (posEigenvalueEquiv G i' : posEigenvalueFinset G) =
                (posEigenvalueEquiv G j' : posEigenvalueFinset G) :=
              Subtype.ext h
            exact (posEigenvalueEquiv G).injective h2
          exact_mod_cast b.inner_eq_ite vi vj |>.trans (by simp [hne])
        rw [h0, mul_zero]
    -- Step 4: Show the matrix identity entry-wise
    ext i' j'
    simp only [one_apply]
    have hsum_entry : ∀ (S : Finset (Sym2 V)) (f : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
        (a : Fin d) (b : Fin d),
        (∑ e ∈ S, f e) a b = ∑ e ∈ S, f e a b := by
      intro S f a b
      rw [show (∑ e ∈ S, f e) a b = ((∑ e ∈ S, f e) a) b from rfl]
      rw [show (∑ e ∈ S, f e) a = ∑ e ∈ S, (f e) a from Finset.sum_apply a S (fun e => f e)]
      exact Finset.sum_apply b S (fun e => (f e) a)
    rw [hsum_entry]
    simp only [vecMulVec_apply, div_mul_div_comm]
    rw [← Finset.sum_div]
    rw [heig_bilin i' j']
    by_cases hij : i' = j'
    · subst hij
      simp only [if_true]
      rw [div_eq_one_iff_eq (ne_of_gt (mul_pos (Real.sqrt_pos.mpr (posEigenvals_pos G i'))
          (Real.sqrt_pos.mpr (posEigenvals_pos G i'))))]
      exact (Real.mul_self_sqrt (posEigenvals_pos G i').le).symm
    · simp [hij]

/-! ### Main theorem proof -/

/-- Assembly of spectral extraction + BSS coloring + Loewner conversion + connection. -/
lemma exists_spectral_data_and_bss
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (hG : G.edgeFinset.Nonempty) :
    ∃ S : Finset V, G.IsEpsilonLight ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨d, hd, hdn, eigvecs, eigvals, heig_pos, horth, hspec, hnorm⟩ :=
    spectral_extraction G hG hn
  -- Define normalized edge vectors and matrices
  set w : Sym2 V → Fin d → ℝ := fun e i =>
    (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) / Real.sqrt (eigvals i) with hw_def
  set A : Sym2 V → Matrix (Fin d) (Fin d) ℝ := fun e => vecMulVec (w e) (w e) with hA_def
  -- A_e are PSD (outer products)
  have hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef := fun e _ => by
    simp only [A]
    rw [show vecMulVec (w e) (w e) = vecMulVec (w e) (star (w e)) from by simp [star_trivial]]
    exact posSemidef_vecMulVec_self_star _
  -- A_e sum to identity (from spectral normalization)
  have hA_sum : ∑ e ∈ G.edgeFinset, A e = 1 := hnorm
  -- Apply BSS coloring
  obtain ⟨S, hloewner, hsize⟩ :=
    ClaudeFormalizer.bss_coloring G hd A hA_psd hA_sum ε hε hε1 hn hdn
  refine ⟨S, ?_, hsize⟩
  -- Convert Loewner bound to BSS bound via loewner_to_sum_sq
  have hew : ClaudeFormalizer.edgeMatrixSumWithin G A S =
      ∑ e ∈ (G.edgesWithin S).edgeFinset, A e := rfl
  rw [hew] at hloewner
  have hbss_raw := loewner_to_sum_sq ((G.edgesWithin S).edgeFinset)
    (fun e => w e) ε hloewner
  have hbss : ∀ x : Fin d → ℝ,
      ∑ e ∈ (G.edgesWithin S).edgeFinset,
        (∑ i : Fin d, x i * (eigvecs i (Quot.out e).1 - eigvecs i (Quot.out e).2) /
          Real.sqrt (eigvals i)) ^ 2
      ≤ ε * ∑ i : Fin d, x i ^ 2 := by
    intro x; have := hbss_raw x
    convert this using 2 with e
    congr 1; simp only [dotProduct, w]; congr 1; ext i; ring
  exact ClaudeFormalizer.normalized_bound_implies_epsilon_light G ε hε.le S d eigvecs eigvals
    heig_pos horth hspec hbss

/-- **Main Theorem**: For every simple graph `G = (V, E)` and `ε ∈ [0, 1]`,
there exists an ε-light subset `S ⊆ V` with `|S| ≥ (ε/256)|V|`.

This proves the existence of large ε-light subsets with constant `c = 1/256`. -/
theorem exists_large_epsilon_light_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ∃ S : Finset V, G.IsEpsilonLight ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  -- Case split on ε = 0
  by_cases hε : ε = 0
  · subst hε; exact ⟨∅, epsilon_light_empty_of_eps_zero G, by simp⟩
  -- Now ε > 0
  have hε_pos : 0 < ε := lt_of_le_of_ne hε₀ (Ne.symm hε)
  -- Case split on whether graph has edges
  by_cases hG : G.edgeFinset = ∅
  · refine ⟨univ, epsilon_light_univ_of_edgeless G hG ε hε₀, ?_⟩
    rw [card_univ]
    have : ε / 256 ≤ (1 : ℝ) := by linarith
    have : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Graph has edges
  have hG' : G.edgeFinset.Nonempty := Finset.nonempty_of_ne_empty hG
  -- Case split on |V| ≤ 3 vs |V| ≥ 4
  by_cases hn : Fintype.card V ≤ 3
  · -- Small n case: pick any vertex, use singleton
    have hne : Nonempty V := by obtain ⟨e, _⟩ := hG'; exact ⟨e.out.1⟩
    have hn0 : 0 < Fintype.card V := Fintype.card_pos
    obtain ⟨v⟩ := hne
    refine ⟨{v}, epsilon_light_singleton G v ε hε₀, ?_⟩
    simp only [card_singleton]
    exact_mod_cast singleton_size_bound ε hε₀ hε₁ _ hn hn0
  · push_neg at hn
    exact exists_spectral_data_and_bss G ε hε_pos hε₁ (by omega) hG'
