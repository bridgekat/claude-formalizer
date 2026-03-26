/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ClaudeFormalizer.Defs
import ClaudeFormalizer.BarrierLemma

/-!
# BSS Coloring Theorem

The core combinatorial result: given PSD matrices indexed by edges of a graph
summing to the identity, there exists a large vertex subset whose internal edges
have small total matrix contribution (in Loewner order).

## Proof structure

The proof follows the BSS barrier method (Section 5 of DetailedProof.tex):
1. Set parameters r = ⌈16/ε⌉, u₀ = ε/2, δ = ε/n, k = ⌊n/4⌋
2. Iteratively color k vertices with r colors maintaining `M_t ≺ u_t I` and
   `Φ_{u_t}(M_t) ≤ d/u₀` via the barrier lemma
3. After k steps, u_k ≤ 3ε/4 < ε so M_k ≺ ε·I
4. Extract the largest color class S by pigeonhole: |S| ≥ k/r ≥ εn/256
5. Since S is a color class, edgeMatrixSumWithin(S) ≤ M_k ≺ ε·I

The proof is decomposed into:
- Helper lemmas about `edgeMatrixSumWithin`
- `bss_iteration_result`: the core iteration producing a good coloring
- `bss_coloring`: assembly using `psd_smul_sub_mono` and the iteration result
-/

namespace ClaudeFormalizer

open Matrix Finset SimpleGraph
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of matrices `A e` over edges `e` of graph `G` restricted to subset `S`. -/
noncomputable def edgeMatrixSumWithin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ) (S : Finset V) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ e ∈ (G.edgesWithin S).edgeFinset, A e

/-- Averaging lemma: if the sum of nonneg reals over a finite set has average < 1,
then some element is < 1. -/
lemma exists_lt_one_of_avg_lt_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (havg : ∑ i, f i < Fintype.card ι) :
    ∃ i, f i < 1 := by
  by_contra h
  push_neg at h
  have : (Fintype.card ι : ℝ) ≤ ∑ i, f i :=
    calc (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
      _ ≤ ∑ i, f i := Finset.sum_le_sum (fun i _ => h i)
  linarith

/-- The largest subset in a partition has size at least total/parts. -/
lemma exists_large_part {n r : ℕ} (hr : 0 < r)
    (parts : Fin r → Finset (Fin n))
    (hpart : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (htotal : ∀ v ∈ Finset.biUnion univ parts, True) :
    ∃ a, (Finset.biUnion univ parts).card / r ≤ (parts a).card := by
  by_contra h
  push_neg at h
  set T := Finset.biUnion univ parts with hT_def
  have hd : ∀ x ∈ (univ : Finset (Fin r)),
      ∀ y ∈ (univ : Finset (Fin r)), x ≠ y → Disjoint (parts x) (parts y) :=
    fun x _ y _ hxy => hpart x y hxy
  have hsum : T.card = ∑ i ∈ (univ : Finset (Fin r)), (parts i).card := by
    show (Finset.biUnion univ parts).card = _
    exact Finset.card_biUnion hd
  have strict : ∑ i ∈ (univ : Finset (Fin r)), (parts i).card <
      ∑ _i ∈ (univ : Finset (Fin r)), (T.card / r) := by
    apply Finset.sum_lt_sum
    · intro i _; exact le_of_lt (h i)
    · exact ⟨⟨0, hr⟩, Finset.mem_univ _, h ⟨0, hr⟩⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at strict
  have key := Nat.div_mul_le_self T.card r
  rw [mul_comm] at key
  omega

/-! ### Helper lemmas for edgeMatrixSumWithin -/

/-- The edgeMatrixSumWithin for any subset S is PSD when all edge matrices are PSD. -/
lemma edgeMatrixSumWithin_posSemidef
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (S : Finset V) :
    (edgeMatrixSumWithin G A S).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e he
  exact hA_psd e (SimpleGraph.edgeFinset_mono (edgesWithin_le G S) he)

/-- Loewner monotonicity: edgeMatrixSumWithin for a subset is bounded by total. -/
lemma edgeMatrixSumWithin_le_total
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (S : Finset V) :
    (∑ e ∈ G.edgeFinset, A e - edgeMatrixSumWithin G A S).PosSemidef := by
  apply sum_posSemidef_le_sum
  · intro e he
    exact SimpleGraph.edgeFinset_mono (edgesWithin_le G S) he
  · exact hA_psd

/-- If `(u·I - M).PosSemidef` and `u ≤ ε`, then `(ε·I - M).PosSemidef`. -/
lemma psd_smul_sub_mono {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    {u ε : ℝ} (huε : u ≤ ε)
    (hMu : (u • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosSemidef) :
    (ε • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosSemidef := by
  have key : ε • (1 : Matrix (Fin d) (Fin d) ℝ) - M =
      (u • 1 - M) + (ε - u) • 1 := by simp [sub_smul]
  rw [key]
  exact PosSemidef.add hMu (PosSemidef.one.smul (sub_nonneg.mpr huε))

/-- Loewner monotonicity for subsets. -/
lemma edgesWithin_mono_subset (G : SimpleGraph V) {S₁ S₂ : Finset V} (h : S₁ ⊆ S₂) :
    G.edgesWithin S₁ ≤ G.edgesWithin S₂ :=
  fun _ _ ⟨hadj, hu, hv⟩ => ⟨hadj, h hu, h hv⟩

lemma edgeMatrixSumWithin_mono
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    {S₁ S₂ : Finset V} (h : S₁ ⊆ S₂) :
    (edgeMatrixSumWithin G A S₂ - edgeMatrixSumWithin G A S₁).PosSemidef := by
  unfold edgeMatrixSumWithin
  apply sum_posSemidef_le_sum
  · exact SimpleGraph.edgeFinset_mono (edgesWithin_mono_subset G h)
  · intro e he
    exact hA_psd e (SimpleGraph.edgeFinset_mono (edgesWithin_le G S₂) he)

/-! ### Arithmetic helper lemmas for BSS parameters -/

/-- `ε/2 + ⌊n/4⌋ · (ε/n) ≤ ε` when `n ≥ 4` and `ε > 0`. -/
private lemma u_final_le_eps {n : ℕ} {ε : ℝ} (hn : 4 ≤ n) (hε : 0 < ε) :
    ε / 2 + (↑(n / 4) : ℝ) * (ε / ↑n) ≤ ε := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h_div : (↑(n / 4) : ℝ) ≤ (↑n : ℝ) / 4 := Nat.cast_div_le
  have h1 : (↑(n / 4) : ℝ) * (ε / ↑n) ≤ (↑n / 4) * (ε / ↑n) :=
    mul_le_mul_of_nonneg_right h_div (div_nonneg hε.le hn_pos.le)
  have h2 : (↑n : ℝ) / 4 * (ε / ↑n) = ε / 4 := by field_simp
  linarith

/-! ### BSS Iteration Helpers -/

/-- `edgeMatrixSumWithin` on the empty set is zero (no edges exist within `∅`). -/
private lemma edgeMatrixSumWithin_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ) :
    edgeMatrixSumWithin G A ∅ = 0 := by
  unfold edgeMatrixSumWithin
  have : (G.edgesWithin ∅).edgeFinset = ∅ :=
    SimpleGraph.edgeFinset_eq_empty.mpr
      (by ext u v; exact ⟨fun ⟨_, hu, _⟩ => absurd hu (Finset.notMem_empty _),
        fun h => h.elim⟩)
  rw [this, Finset.sum_empty]

/-- The monochromatic edge sum is Hermitian. -/
private lemma isHermitian_color_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    {r : ℕ} (parts : Fin r → Finset V) :
    (∑ γ, edgeMatrixSumWithin G A (parts γ)).IsHermitian :=
  (isSelfAdjoint_sum Finset.univ fun γ _ =>
    (edgeMatrixSumWithin_posSemidef G A hA_psd (parts γ)).isHermitian.isSelfAdjoint).isHermitian

/-- The double sum of cross-edge matrix contributions is bounded by the identity.
For each `(v, γ)` with `v` uncolored, the edges from `v` to `parts γ` form pairwise
disjoint subsets of the graph's edge set, so their total contribution is at most
`∑ A e = 1`. -/
private lemma disjoint_cross_edge_sum_le_identity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    {r : ℕ} (parts : Fin r → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (R : Finset V)
    (hR : ∀ v ∈ R, ∀ i, v ∉ parts i) :
    (1 - ∑ v ∈ R, ∑ γ : Fin r,
      (edgeMatrixSumWithin G A (insert v (parts γ)) -
       edgeMatrixSumWithin G A (parts γ))).PosSemidef := by
  -- Define cross-edge set E(v,γ)
  let E : V → Fin r → Finset (Sym2 V) := fun v γ =>
    (G.edgesWithin (insert v (parts γ))).edgeFinset \
    (G.edgesWithin (parts γ)).edgeFinset
  -- Helper: s(e.out.1, e.out.2) = e
  have hmk : ∀ e : Sym2 V, s((Quot.out e).1, (Quot.out e).2) = e :=
    fun e => by change Quot.mk _ _ = _; simp [Quot.out_eq]
  -- Subset: edgesWithin(parts γ) ⊆ edgesWithin(insert v (parts γ))
  have hsub : ∀ v γ, (G.edgesWithin (parts γ)).edgeFinset ⊆
      (G.edgesWithin (insert v (parts γ))).edgeFinset :=
    fun v γ => edgeFinset_mono (edgesWithin_mono_subset G (Finset.subset_insert v (parts γ)))
  -- Helper: extract adjacency from edgeFinset membership via Quot.out
  have hadj_of_mem : ∀ {H : SimpleGraph V} [DecidableRel H.Adj] {e : Sym2 V},
      e ∈ H.edgeFinset → H.Adj (Quot.out e).1 (Quot.out e).2 := by
    intro H _ e he
    have h := mem_edgeFinset.mp he
    rwa [← hmk e] at h
  -- Step 1: B(v,γ) = ∑ e ∈ E(v,γ), A e
  have hB_eq : ∀ v, ∀ γ : Fin r,
      edgeMatrixSumWithin G A (insert v (parts γ)) -
      edgeMatrixSumWithin G A (parts γ) = ∑ e ∈ E v γ, A e := by
    intro v γ; show _ = ∑ e ∈ _ \ _, A e
    simp only [edgeMatrixSumWithin]
    rw [Finset.sum_sdiff_eq_sub (hsub v γ)]
  -- Step 2: An edge in E(v,γ) has v as an endpoint (when v ∉ parts γ)
  have hv_in_edge : ∀ v, ∀ γ : Fin r, v ∉ parts γ → ∀ e ∈ E v γ, v ∈ e := by
    intro v γ hv_not e he
    dsimp only [E] at he
    obtain ⟨he_in, he_not⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hG_adj, ha_in, hb_in⟩ := hadj_of_mem he_in
    rw [Finset.mem_insert] at ha_in hb_in
    -- NOT both endpoints in parts γ
    have hnot_both : ¬((Quot.out e).1 ∈ parts γ ∧ (Quot.out e).2 ∈ parts γ) := by
      intro ⟨ha, hb⟩
      exact he_not (by rw [← hmk e]; exact mem_edgeFinset.mpr ⟨hG_adj, ha, hb⟩)
    -- At least one endpoint is v; show v ∈ s(a,b) = e
    rw [← hmk e]
    rcases ha_in with ha_eq | ha_part <;> rcases hb_in with hb_eq | hb_part
    · exact absurd (ha_eq ▸ hb_eq ▸ hG_adj) (G.loopless.irrefl _)
    · exact ha_eq ▸ Sym2.mem_mk_left _ _
    · exact hb_eq ▸ Sym2.mem_mk_right _ _
    · exact absurd ⟨ha_part, hb_part⟩ hnot_both
  -- Step 3: E(v,γ) are pairwise disjoint over (v, γ) ∈ R ×ˢ univ
  have hE_disj : Set.PairwiseDisjoint (↑(R ×ˢ (Finset.univ : Finset (Fin r))))
      (fun p : V × Fin r => E p.1 p.2) := by
    intro ⟨v₁, γ₁⟩ h₁ ⟨v₂, γ₂⟩ h₂ hne
    have hv₁R : v₁ ∈ R := (Finset.mem_product.mp h₁).1
    have hv₂R : v₂ ∈ R := (Finset.mem_product.mp h₂).1
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    have hv₁e : v₁ ∈ e := hv_in_edge v₁ γ₁ (hR v₁ hv₁R γ₁) e he₁
    have hv₂e : v₂ ∈ e := hv_in_edge v₂ γ₂ (hR v₂ hv₂R γ₂) e he₂
    -- Get adjacency and membership from he₁
    have he₁' : (G.edgesWithin (insert v₁ (parts γ₁))).Adj (Quot.out e).1 (Quot.out e).2 := by
      dsimp only [E] at he₁; exact hadj_of_mem (Finset.mem_sdiff.mp he₁).1
    obtain ⟨hG_adj, ha₁, hb₁⟩ := he₁'
    rw [Finset.mem_insert] at ha₁ hb₁
    -- Get membership from he₂
    have he₂' : (G.edgesWithin (insert v₂ (parts γ₂))).Adj (Quot.out e).1 (Quot.out e).2 := by
      dsimp only [E] at he₂; exact hadj_of_mem (Finset.mem_sdiff.mp he₂).1
    obtain ⟨_, ha₂, hb₂⟩ := he₂'
    rw [Finset.mem_insert] at ha₂ hb₂
    -- v₁, v₂ ∈ {a, b} where a = e.out.1, b = e.out.2
    rw [← hmk e, Sym2.mem_iff] at hv₁e hv₂e
    by_cases hvv : v₁ = v₂
    · -- Same vertex, different colors
      subst hvv
      have hγne : γ₁ ≠ γ₂ := fun h => hne (Prod.ext rfl h)
      -- v₁ ∈ {a, b}. Case split:
      obtain hv_eq | hv_eq := hv₁e
      · -- v₁ = a: then b ∉ parts because "not both in parts" for both γ₁, γ₂
        -- Actually b must be in both parts: b ∈ insert v₁ (parts γᵢ), b ≠ v₁ (loopless)
        have hb_γ₁ : (Quot.out e).2 ∈ parts γ₁ := by
          rcases hb₁ with h | h
          · exact absurd (h.trans hv_eq).symm (G.ne_of_adj hG_adj)
          · exact h
        have hb_γ₂ : (Quot.out e).2 ∈ parts γ₂ := by
          rcases hb₂ with h | h
          · exact absurd (h.trans hv_eq).symm (G.ne_of_adj hG_adj)
          · exact h
        exact absurd hb_γ₂ (Finset.disjoint_left.mp (hdisjoint γ₁ γ₂ hγne) hb_γ₁)
      · -- v₁ = b: then a must be in both parts
        have ha_γ₁ : (Quot.out e).1 ∈ parts γ₁ := by
          rcases ha₁ with h | h
          · exact absurd (h.trans hv_eq) (G.ne_of_adj hG_adj)
          · exact h
        have ha_γ₂ : (Quot.out e).1 ∈ parts γ₂ := by
          rcases ha₂ with h | h
          · exact absurd (h.trans hv_eq) (G.ne_of_adj hG_adj)
          · exact h
        exact absurd ha_γ₂ (Finset.disjoint_left.mp (hdisjoint γ₁ γ₂ hγne) ha_γ₁)
    · -- Different vertices: v₁ and v₂ both in s(a,b), so e = s(v₁,v₂)
      -- v₂ ∈ insert v₁ (parts γ₁) means v₂ = v₁ or v₂ ∈ parts γ₁
      -- Since v₂ ≠ v₁ and v₂ ∈ R (so v₂ ∉ parts γ₁), contradiction
      -- First: identify which endpoint is v₂
      obtain hv₁_eq | hv₁_eq := hv₁e <;> obtain hv₂_eq | hv₂_eq := hv₂e
      · -- v₁ = a, v₂ = a: contradicts v₁ ≠ v₂
        exact hvv (hv₁_eq.trans hv₂_eq.symm)
      · -- v₁ = a, v₂ = b: b ∈ insert v₁ (parts γ₁), b ≠ v₁, so b ∈ parts γ₁
        have : (Quot.out e).2 ∈ parts γ₁ := by
          rcases hb₁ with h | h
          · exact absurd (h.trans hv₁_eq).symm (G.ne_of_adj hG_adj)
          · exact h
        exact hR v₂ hv₂R γ₁ (hv₂_eq ▸ this)
      · -- v₁ = b, v₂ = a: a ∈ insert v₁ (parts γ₁), a ≠ v₁, so a ∈ parts γ₁
        have : (Quot.out e).1 ∈ parts γ₁ := by
          rcases ha₁ with h | h
          · exact absurd (h.trans hv₁_eq) (G.ne_of_adj hG_adj)
          · exact h
        exact hR v₂ hv₂R γ₁ (hv₂_eq ▸ this)
      · -- v₁ = b, v₂ = b: contradicts v₁ ≠ v₂
        exact hvv (hv₁_eq.trans hv₂_eq.symm)
  -- Step 4: E(v,γ) ⊆ G.edgeFinset
  have hE_sub : ∀ v ∈ R, ∀ γ : Fin r, E v γ ⊆ G.edgeFinset := by
    intro v _ γ e he; dsimp only [E] at he
    exact edgeFinset_mono (edgesWithin_le G (insert v (parts γ))) (Finset.sdiff_subset he)
  -- Step 5: Rewrite and conclude
  rw [← hA_sum]
  have hsum_eq : ∑ v ∈ R, ∑ γ : Fin r,
      (edgeMatrixSumWithin G A (insert v (parts γ)) -
       edgeMatrixSumWithin G A (parts γ)) =
      ∑ e ∈ (R ×ˢ Finset.univ).biUnion (fun p : V × Fin r => E p.1 p.2), A e := by
    simp_rw [hB_eq]
    rw [← Finset.sum_product' R Finset.univ (fun v γ => ∑ e ∈ E v γ, A e),
        ← Finset.sum_biUnion hE_disj]
  rw [hsum_eq]
  exact sum_posSemidef_le_sum
    (Finset.biUnion_subset.mpr fun ⟨v, γ⟩ hvγ =>
      hE_sub v ((Finset.mem_product.mp hvγ).1) γ)
    A hA_psd

set_option maxHeartbeats 1600000 in
/-- One step of the BSS iteration: given a coloring satisfying the barrier invariant
at time `t`, extend it by one vertex to obtain the invariant at time `t + 1`.

Uses the averaging argument (average barrier expression < 1 over all vertex-color
choices) combined with `barrier_lemma` from `BarrierLemma.lean`. -/
private lemma bss_one_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d)
    (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V)
    {t : ℕ} (htk : t < Fintype.card V / 4)
    {parts : Fin ⌈16 / ε⌉₊ → Finset V}
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hcard : (Finset.biUnion Finset.univ parts).card = t)
    (hpd : ((ε / 2 + ↑t * (ε / ↑(Fintype.card V))) •
            (1 : Matrix (Fin d) (Fin d) ℝ) -
            ∑ γ, edgeMatrixSumWithin G A (parts γ)).PosDef)
    (hpot : barrierPotential (ε / 2 + ↑t * (ε / ↑(Fintype.card V)))
            (∑ γ, edgeMatrixSumWithin G A (parts γ)) ≤ ↑d / (ε / 2)) :
    ∃ (parts' : Fin ⌈16 / ε⌉₊ → Finset V),
      (∀ i j, i ≠ j → Disjoint (parts' i) (parts' j)) ∧
      (Finset.biUnion Finset.univ parts').card = t + 1 ∧
      ((ε / 2 + ↑(t + 1) * (ε / ↑(Fintype.card V))) •
        (1 : Matrix (Fin d) (Fin d) ℝ) -
        ∑ γ, edgeMatrixSumWithin G A (parts' γ)).PosDef ∧
      barrierPotential (ε / 2 + ↑(t + 1) * (ε / ↑(Fintype.card V)))
        (∑ γ, edgeMatrixSumWithin G A (parts' γ)) ≤ ↑d / (ε / 2) := by
  -- Setup notation
  set n := Fintype.card V with hn_def
  set M := ∑ γ, edgeMatrixSumWithin G A (parts γ) with hM_def
  set u := ε / 2 + ↑t * (ε / ↑n) with hu_def
  set δ := ε / ↑n with hδ_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hδ_pos : 0 < δ := div_pos hε hn_pos
  -- u' = u + δ = ε/2 + (t+1)·(ε/n)
  have hu'_eq : ε / 2 + ↑(t + 1) * (ε / ↑n) = u + δ := by
    simp only [hu_def, hδ_def, Nat.cast_succ]; ring
  -- M is Hermitian
  have hM_herm : M.IsHermitian := isHermitian_color_sum G A hA_psd parts
  -- ((u + δ) • I - M).PosDef
  have hpd' : ((u + δ) • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosDef := by
    have heq : (u + δ) • (1 : Matrix (Fin d) (Fin d) ℝ) - M =
        (u • 1 - M) + δ • 1 := by simp [add_smul]; abel
    rw [heq]; exact PosDef.add_posSemidef hpd (PosSemidef.one.smul hδ_pos.le)
  -- U and gap
  set U := ((u + δ) • (1 : Matrix (Fin d) (Fin d) ℝ) - M)⁻¹ with hU_def
  set gap := barrierPotential u M - barrierPotential (u + δ) M with hgap_def
  have hU_pd : U.PosDef := hpd'.inv
  -- gap > 0 via barrierPotential_drop: δ * tr(U²) ≤ gap, and tr(U²) > 0
  have hdrop : δ * trace (U * U) ≤ gap := barrierPotential_drop hM_herm hpd hδ_pos
  have hgap_pos : 0 < gap := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hUU_pd : (U * U).PosDef := by
      rw [show U * U = Uᴴ * U from by rw [hU_pd.isHermitian.eq]]
      exact Matrix.PosDef.conjTranspose_mul_self U
        (mulVec_injective_of_isUnit hU_pd.isUnit)
    linarith [mul_pos hδ_pos hUU_pd.trace_pos]
  -- tr(U) bound
  have htrU_bound : trace U ≤ ↑d / (ε / 2) :=
    le_trans (barrierPotential_anti hM_herm hpd (by linarith : u ≤ u + δ)) hpot
  -- R = uncolored vertices
  set R := (Finset.univ : Finset V) \ Finset.biUnion Finset.univ parts with hR_def
  have hR_card : R.card = n - t := by
    rw [hR_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard]
  -- v₀ not in any color class
  have hv₀_not_part : ∀ v ∈ R, ∀ i, v ∉ parts i := by
    intro v hv i hi
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
  -- Key claim: ∃ good (v₀, γ₀) with barrier expression ≤ 1
  obtain ⟨v₀, hv₀R, γ₀, hbarrier_le⟩ : ∃ v₀ ∈ R, ∃ γ₀ : Fin ⌈16 / ε⌉₊,
      trace ((edgeMatrixSumWithin G A (insert v₀ (parts γ₀)) -
              edgeMatrixSumWithin G A (parts γ₀)) * U) +
      trace ((edgeMatrixSumWithin G A (insert v₀ (parts γ₀)) -
              edgeMatrixSumWithin G A (parts γ₀)) * (U * U)) / gap ≤ 1 := by
    by_contra hall; push_neg at hall
    have hr_pos : 0 < ⌈16 / ε⌉₊ := by
      rw [Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
      exact div_pos (by norm_num) hε
    have hR_ne : R.Nonempty := Finset.card_pos.mp (by rw [hR_card]; omega)
    -- Upper bound: ∑∑ f ≤ tr(U) + tr(U²)/gap (Loewner + trace monotonicity)
    have hUB : ∑ v ∈ R, ∑ γ : Fin ⌈16 / ε⌉₊,
      (((edgeMatrixSumWithin G A (insert v (parts γ)) -
         edgeMatrixSumWithin G A (parts γ)) * U).trace +
       ((edgeMatrixSumWithin G A (insert v (parts γ)) -
         edgeMatrixSumWithin G A (parts γ)) * (U * U)).trace / gap) ≤
      U.trace + (U * U).trace / gap := by
      -- Loewner bound: ∑∑B ≤ I (key fact about disjoint edge sums)
      have hLoewner : (1 - ∑ v ∈ R, ∑ γ : Fin ⌈16 / ε⌉₊,
        (edgeMatrixSumWithin G A (insert v (parts γ)) -
         edgeMatrixSumWithin G A (parts γ))).PosSemidef :=
        disjoint_cross_edge_sum_le_identity G A hA_psd hA_sum parts hdisjoint R hv₀_not_part
      -- Trace linearity: ∑∑ tr(B*C) = tr((∑∑B)*C)
      have hlin : ∀ C : Matrix (Fin d) (Fin d) ℝ,
          ∑ v ∈ R, ∑ γ : Fin ⌈16 / ε⌉₊,
            ((edgeMatrixSumWithin G A (insert v (parts γ)) -
              edgeMatrixSumWithin G A (parts γ)) * C).trace =
          ((∑ v ∈ R, ∑ γ : Fin ⌈16 / ε⌉₊,
            (edgeMatrixSumWithin G A (insert v (parts γ)) -
             edgeMatrixSumWithin G A (parts γ))) * C).trace := by
        intro C; simp only [← Matrix.trace_sum, ← Finset.sum_mul]
      -- Rewrite using linearity
      simp_rw [Finset.sum_add_distrib, ← Finset.sum_div, hlin]
      -- Trace monotonicity from Loewner bound
      have htr1 := trace_mul_le_of_loewner_le hLoewner hU_pd.posSemidef
      rw [Matrix.one_mul] at htr1
      have hUU_psd : (U * U).PosSemidef := by
        rw [show U * U = Uᴴ * U from by rw [hU_pd.isHermitian.eq]]
        exact Matrix.posSemidef_conjTranspose_mul_self U
      have htr2 := trace_mul_le_of_loewner_le hLoewner hUU_psd
      rw [Matrix.one_mul] at htr2
      linarith [div_le_div_of_nonneg_right htr2 hgap_pos.le]
    -- Arithmetic: tr(U) + tr(U²)/gap < R.card * ⌈16/ε⌉₊
    have hArith : U.trace + (U * U).trace / gap <
      (↑R.card : ℝ) * (↑(⌈16 / ε⌉₊) : ℝ) := by
      have htn_le : t ≤ n := by omega
      have h4tp4 : 4 * t + 4 ≤ n := by omega
      have h4t_r : 4 * (↑t : ℝ) + 4 ≤ ↑n := by exact_mod_cast h4tp4
      have hRcard_r : (↑R.card : ℝ) = ↑n - ↑t := by
        simp only [hR_card, Nat.cast_sub htn_le]
      have hceil : 16 / ε ≤ (↑⌈16 / ε⌉₊ : ℝ) := Nat.le_ceil (16 / ε)
      have hdn_r : (↑d : ℝ) ≤ ↑n := Nat.cast_le.mpr hdn
      have hUU_bound : (U * U).trace / gap ≤ ↑n / ε := by
        have h1 : (U * U).trace * δ ≤ 1 * gap := by linarith [hdrop]
        have h2 : (U * U).trace / gap ≤ 1 / δ :=
          (div_le_div_iff₀ hgap_pos hδ_pos).mpr h1
        have h3 : (1 : ℝ) / δ = ↑n / ε := by rw [hδ_def]; field_simp
        linarith
      have hU_bound : U.trace ≤ 2 * ↑d / ε := by
        linarith [htrU_bound, show ↑d / (ε / 2) = 2 * ↑d / ε from by field_simp]
      -- Combine via explicit multiplication by ε⁻¹
      rw [hRcard_r]
      have hnt_pos : (0 : ℝ) < ↑n - ↑t := by linarith
      suffices hsuff : U.trace + (U * U).trace / gap < (↑n - ↑t) * (16 / ε) by
        linarith [mul_le_mul_of_nonneg_left hceil hnt_pos.le]
      -- LHS ≤ (2d + n)/ε ≤ 3n/ε < 12n/ε < (n-t)*16/ε = RHS
      have h_lhs : U.trace + (U * U).trace / gap ≤ (2 * ↑d + ↑n) / ε := by
        have : U.trace + (U * U).trace / gap ≤ 2 * ↑d / ε + ↑n / ε :=
          add_le_add hU_bound hUU_bound
        linarith [show 2 * (↑d : ℝ) / ε + ↑n / ε = (2 * ↑d + ↑n) / ε from by ring]
      have h_rhs : (2 * (↑d : ℝ) + ↑n) / ε < (↑n - ↑t) * (16 / ε) := by
        rw [show (↑n - ↑t) * (16 / ε) = ((↑n - ↑t) * 16) / ε from by ring]
        rw [show (2 * (↑d : ℝ) + ↑n) / ε < ((↑n - ↑t) * 16) / ε ↔
              2 * (↑d : ℝ) + ↑n < (↑n - ↑t) * 16 from
            div_lt_div_iff_of_pos_right hε]
        nlinarith
      linarith
    -- Lower bound: each term > 1, so sum > R.card * ⌈16/ε⌉₊
    have hLB : (↑R.card : ℝ) * (↑(⌈16 / ε⌉₊) : ℝ) <
      ∑ v ∈ R, ∑ γ : Fin ⌈16 / ε⌉₊,
      (((edgeMatrixSumWithin G A (insert v (parts γ)) -
         edgeMatrixSumWithin G A (parts γ)) * U).trace +
       ((edgeMatrixSumWithin G A (insert v (parts γ)) -
         edgeMatrixSumWithin G A (parts γ)) * (U * U)).trace / gap) := by
      conv_lhs => rw [show (↑R.card : ℝ) * ↑(⌈16 / ε⌉₊) =
        ∑ _v ∈ R, ∑ _γ : Fin ⌈16 / ε⌉₊, (1 : ℝ) from by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]]
      apply Finset.sum_lt_sum
      · intro v hv; exact Finset.sum_le_sum (fun γ _ => le_of_lt (hall v hv γ))
      · obtain ⟨v₀, hv₀⟩ := hR_ne
        exact ⟨v₀, hv₀, Finset.sum_lt_sum
          (fun γ _ => le_of_lt (hall v₀ hv₀ γ))
          ⟨⟨0, hr_pos⟩, Finset.mem_univ _, hall v₀ hv₀ ⟨0, hr_pos⟩⟩⟩
    linarith
  have hv₀_not : v₀ ∉ Finset.biUnion Finset.univ parts :=
    (Finset.mem_sdiff.mp hv₀R).2
  -- B is PSD
  set B := edgeMatrixSumWithin G A (insert v₀ (parts γ₀)) -
           edgeMatrixSumWithin G A (parts γ₀) with hB_def
  have hB_psd : B.PosSemidef :=
    edgeMatrixSumWithin_mono G A hA_psd (Finset.subset_insert v₀ (parts γ₀))
  -- Apply barrier_lemma
  obtain ⟨hpd_new, hpot_new⟩ :=
    barrier_lemma hM_herm hB_psd hpd (by linarith : u < u + δ) hpd' hgap_pos hbarrier_le
  -- Key: ∑ γ, edgeMatrixSumWithin(parts' γ) = M + B
  have hsum_eq : ∀ (f : Fin ⌈16 / ε⌉₊ → Finset V),
      f = Function.update parts γ₀ (insert v₀ (parts γ₀)) →
      ∑ γ, edgeMatrixSumWithin G A (f γ) = M + B := by
    intro f hf; subst hf
    have : ∑ γ, edgeMatrixSumWithin G A (Function.update parts γ₀
              (insert v₀ (parts γ₀)) γ) =
           edgeMatrixSumWithin G A (insert v₀ (parts γ₀)) +
           ∑ γ ∈ Finset.univ.erase γ₀, edgeMatrixSumWithin G A (parts γ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ₀)]
      congr 1
      · simp [Function.update_self]
      · apply Finset.sum_congr rfl; intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [this]
    have hM_eq : M = edgeMatrixSumWithin G A (parts γ₀) +
      ∑ γ ∈ Finset.univ.erase γ₀, edgeMatrixSumWithin G A (parts γ) := by
      rw [hM_def]; exact (Finset.add_sum_erase _ _ (Finset.mem_univ γ₀)).symm
    rw [hM_eq, hB_def]; abel
  -- Construct parts'
  refine ⟨Function.update parts γ₀ (insert v₀ (parts γ₀)), ?_, ?_, ?_, ?_⟩
  -- Disjointness
  · intro i j hij
    by_cases hiγ : i = γ₀ <;> by_cases hjγ : j = γ₀
    · exact absurd (hiγ.trans hjγ.symm) hij
    · subst hiγ; rw [Function.update_self, Function.update_of_ne hjγ]
      exact Finset.disjoint_insert_left.mpr
        ⟨hv₀_not_part v₀ hv₀R j, hdisjoint _ _ hij⟩
    · subst hjγ; rw [Function.update_of_ne hiγ, Function.update_self]
      exact Finset.disjoint_insert_right.mpr
        ⟨hv₀_not_part v₀ hv₀R i, hdisjoint _ _ hij⟩
    · rw [Function.update_of_ne hiγ, Function.update_of_ne hjγ]
      exact hdisjoint _ _ hij
  -- Card = t + 1
  · suffices h : univ.biUnion (Function.update parts γ₀ (insert v₀ (parts γ₀))) =
        insert v₀ (univ.biUnion parts) by
      rw [h, Finset.card_insert_of_notMem hv₀_not, hcard]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Function.update_apply]
    constructor
    · rintro ⟨γ, hx⟩
      split_ifs at hx with h
      · exact (Finset.mem_insert.mp hx).elim Or.inl (fun hm => Or.inr ⟨γ₀, hm⟩)
      · exact Or.inr ⟨γ, hx⟩
    · rintro (rfl | ⟨γ, hx⟩)
      · exact ⟨γ₀, by simp⟩
      · refine ⟨γ, ?_⟩
        split_ifs with h
        · subst h; exact Finset.mem_insert_of_mem hx
        · exact hx
  -- PosDef
  · rw [hu'_eq, hsum_eq _ rfl]; exact hpd_new
  -- Potential bound
  · rw [hu'_eq, hsum_eq _ rfl]; exact le_trans hpot_new hpot

/-! ### BSS Iteration Core -/

set_option maxHeartbeats 800000 in
/-- **Core matrix iteration**: The BSS barrier method produces a PSD matrix `M`
dominated by `u·I` together with a coloring of `k` vertices into `r` colors,
such that the monochromatic edge matrices sum to at most `M`.

Proved by induction on the number of colored vertices using `bss_one_step`. -/
private lemma matrix_iteration_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d)
    (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (hdn : d ≤ Fintype.card V) :
    let n := Fintype.card V
    let k := n / 4
    let r := ⌈16 / ε⌉₊
    let u₀ := ε / 2
    let δ := ε / (n : ℝ)
    ∃ (parts : Fin r → Finset V),
      (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
      (Finset.biUnion Finset.univ parts).card = k ∧
      ((u₀ + ↑k * δ) • (1 : Matrix (Fin d) (Fin d) ℝ) -
        ∑ γ, edgeMatrixSumWithin G A (parts γ)).PosSemidef := by
  intro n k r u₀ δ
  -- Reduce to stronger inductive invariant: PosDef + potential bound
  suffices h : ∀ t, t ≤ k → ∃ (parts : Fin r → Finset V),
      (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
      (Finset.biUnion Finset.univ parts).card = t ∧
      ((u₀ + ↑t * δ) • (1 : Matrix (Fin d) (Fin d) ℝ) -
        ∑ γ, edgeMatrixSumWithin G A (parts γ)).PosDef ∧
      barrierPotential (u₀ + ↑t * δ)
        (∑ γ, edgeMatrixSumWithin G A (parts γ)) ≤ ↑d / u₀ by
    obtain ⟨parts, hdisj, hcard, hpd, _⟩ := h k le_rfl
    exact ⟨parts, hdisj, hcard, hpd.posSemidef⟩
  intro t ht
  induction t with
  | zero =>
    refine ⟨fun _ => ∅, fun _ _ _ => Finset.disjoint_empty_right _, ?_, ?_, ?_⟩
    · apply Finset.card_eq_zero.mpr; ext x; simp [Finset.mem_biUnion]
    · -- (u₀ • I - 0).PosDef since u₀ = ε/2 > 0
      simp only [Nat.cast_zero, zero_mul, add_zero, edgeMatrixSumWithin_empty,
        Finset.sum_const_zero, sub_zero]
      exact Matrix.PosDef.one.smul (half_pos hε)
    · -- barrierPotential u₀ 0 = d/u₀
      simp only [Nat.cast_zero, zero_mul, add_zero, edgeMatrixSumWithin_empty,
        Finset.sum_const_zero]
      exact le_of_eq (barrierPotential_zero u₀ (half_pos hε))
  | succ t ih =>
    have ht' : t ≤ k := Nat.le_of_succ_le ht
    obtain ⟨parts, hdisjoint, hcard, hpd, hpot⟩ := ih ht'
    exact bss_one_step G hd A hA_psd hA_sum ε hε hε1 hn hdn
      (Nat.lt_of_succ_le ht) hdisjoint hcard hpd hpot

/-- Assembly lemma: sum of monochromatic edge matrices dominates each color class. -/
private lemma edgeMatrixSumWithin_le_color_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    {r : ℕ} (parts : Fin r → Finset V)
    (γ : Fin r) :
    (∑ i, edgeMatrixSumWithin G A (parts i) -
      edgeMatrixSumWithin G A (parts γ)).PosSemidef := by
  rw [← Finset.sum_erase_eq_sub (f := fun i => edgeMatrixSumWithin G A (parts i))
      (Finset.mem_univ γ)]
  exact Matrix.posSemidef_sum _ fun i _ =>
    edgeMatrixSumWithin_posSemidef G A hA_psd (parts i)

/-- Loewner transitivity for barrier bounds. -/
private lemma psd_sub_trans {d : ℕ} {M N : Matrix (Fin d) (Fin d) ℝ} {u : ℝ}
    (h1 : (u • (1 : Matrix (Fin d) (Fin d) ℝ) - M).PosSemidef)
    (h2 : (M - N).PosSemidef) :
    (u • (1 : Matrix (Fin d) (Fin d) ℝ) - N).PosSemidef := by
  have : u • (1 : Matrix (Fin d) (Fin d) ℝ) - N = (u • 1 - M) + (M - N) := by
    simp [sub_add_sub_cancel]
  rw [this]
  exact h1.add h2

/-- Abstract barrier iteration: assembles matrix_iteration_exists,
pigeonhole, and edgeMatrixSumWithin_le_color_sum. -/
private lemma bss_barrier_iteration
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d)
    (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (hdn : d ≤ Fintype.card V) :
    let n := Fintype.card V
    let k := n / 4
    let r := ⌈16 / ε⌉₊
    let u₀ := ε / 2
    let δ := ε / (n : ℝ)
    ∃ (S : Finset V),
      ((u₀ + ↑k * δ) • (1 : Matrix (Fin d) (Fin d) ℝ) -
        edgeMatrixSumWithin G A S).PosSemidef ∧
      ε / 256 * (↑n : ℝ) ≤ (S.card : ℝ) := by
  intro n k r u₀ δ
  obtain ⟨parts, hdisjoint, hcard, hbound⟩ :=
    matrix_iteration_exists G hd A hA_psd hA_sum ε hε hε1 hn hdn
  have hr_pos : 0 < r := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
    exact div_pos (by norm_num) hε
  have hr_cast_pos : (0 : ℝ) < ↑r := Nat.cast_pos.mpr hr_pos
  have hk_pos : 0 < k := Nat.div_pos (by omega) (by norm_num)
  -- Real-valued pigeonhole: some color class has ≥ k/r elements (real division)
  have hpigeonhole : ∃ γ : Fin r, (↑k : ℝ) / ↑r ≤ ((parts γ).card : ℝ) := by
    by_contra hall; push_neg at hall
    have hsum_eq : (↑k : ℝ) = ∑ i ∈ (Finset.univ : Finset (Fin r)), ((parts i).card : ℝ) := by
      have hdis : ∀ x ∈ (Finset.univ : Finset (Fin r)),
          ∀ y ∈ (Finset.univ : Finset (Fin r)), x ≠ y → Disjoint (parts x) (parts y) :=
        fun x _ y _ hxy => hdisjoint x y hxy
      have hcb := Finset.card_biUnion hdis
      rw [hcard] at hcb
      exact_mod_cast hcb
    have : (↑k : ℝ) < ∑ _i ∈ (Finset.univ : Finset (Fin r)), (↑k : ℝ) / ↑r :=
      calc (↑k : ℝ) = ∑ i ∈ Finset.univ, ↑(parts i).card := hsum_eq
        _ < ∑ _i ∈ Finset.univ, ↑k / ↑r := Finset.sum_lt_sum
            (fun i _ => le_of_lt (hall i))
            ⟨⟨0, hr_pos⟩, Finset.mem_univ _, hall ⟨0, hr_pos⟩⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ (ne_of_gt hr_cast_pos)] at this
    linarith
  obtain ⟨γ, hγ⟩ := hpigeonhole
  refine ⟨parts γ, ?_, ?_⟩
  · exact psd_sub_trans hbound (edgeMatrixSumWithin_le_color_sum G A hA_psd parts γ)
  · -- Size bound: εn/256 ≤ |parts γ|
    -- |parts γ| ≥ 1 since k/r > 0
    have hS_pos : 0 < (parts γ).card := by
      by_contra h; push_neg at h; interval_cases (parts γ).card
      simp at hγ; linarith [div_pos (Nat.cast_pos.mpr hk_pos) hr_cast_pos]
    -- Ceiling bound: r ≤ 32/ε
    have hceil_le_32 : (↑r : ℝ) ≤ 32 / ε := by
      have h1 : (⌈16 / ε⌉₊ : ℝ) ≤ 16 / ε + 1 := by
        have := Nat.ceil_le_floor_add_one (16 / ε)
        have hfl : (⌊16 / ε⌋₊ : ℝ) ≤ 16 / ε := Nat.floor_le (div_nonneg (by norm_num) hε.le)
        calc (⌈16 / ε⌉₊ : ℝ) ≤ ↑(⌊16 / ε⌋₊ + 1) := by exact_mod_cast this
          _ = ↑⌊16 / ε⌋₊ + 1 := by push_cast; ring
          _ ≤ 16 / ε + 1 := by linarith
      calc (⌈16 / ε⌉₊ : ℝ) ≤ 16 / ε + 1 := h1
        _ ≤ 16 / ε + 16 / ε := by gcongr; rw [le_div_iff₀ hε]; linarith
        _ = 32 / ε := by ring
    -- Nat div bound: k ≥ (n-3)/4
    have hk_bound : (↑n - 3 : ℝ) / 4 ≤ ↑k := by
      have key : n - 3 ≤ n / 4 * 4 := by omega
      have hcast : (↑(n - 3) : ℝ) ≤ (↑(n / 4 * 4) : ℝ) := Nat.cast_le.mpr key
      rw [Nat.cast_mul, Nat.cast_sub (by omega)] at hcast; linarith
    by_cases hn6 : 6 ≤ n
    · -- n ≥ 6: k/r ≥ ε(n-3)/128 ≥ εn/256
      suffices h : ε / 256 * ↑n ≤ (↑k : ℝ) / ↑r from le_trans h hγ
      rw [show ε / 256 * (↑n : ℝ) = (ε * ↑n) / 256 from by ring]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 256) hr_cast_pos]
      have h_er : ε * ↑r ≤ 32 := by
        calc ε * ↑r ≤ ε * (32 / ε) := mul_le_mul_of_nonneg_left hceil_le_32 hε.le
          _ = 32 := by field_simp
      have h_k : (↑n : ℝ) - 3 ≤ 4 * ↑k := by linarith
      nlinarith [show (6 : ℝ) ≤ ↑n from by exact_mod_cast hn6]
    · -- n < 6, n ∈ {4, 5}: εn/256 < 1 ≤ |S|
      have hn5 : (↑n : ℝ) ≤ 5 := by exact_mod_cast (show n ≤ 5 by omega)
      have hS1 : (1 : ℝ) ≤ ↑(parts γ).card := by exact_mod_cast hS_pos
      nlinarith

/-! ### BSS Iteration Result -/

/-- BSS iteration core: assembles barrier iteration with u-bound arithmetic. -/
lemma bss_iteration_result
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d)
    (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (hdn : d ≤ Fintype.card V) :
    ∃ (S : Finset V) (u : ℝ),
      u ≤ ε ∧
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) - edgeMatrixSumWithin G A S).PosSemidef ∧
      ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  set n := Fintype.card V with hn_def
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  set k := n / 4
  set u₀ := ε / 2
  set δ := ε / (↑n : ℝ)
  have hu_final : u₀ + (↑k : ℝ) * δ ≤ ε := u_final_le_eps hn hε
  obtain ⟨S, hbound, hsize⟩ := bss_barrier_iteration G hd A hA_psd hA_sum ε hε hε1 hn hdn
  exact ⟨S, u₀ + ↑k * δ, hu_final, hbound, hsize⟩

set_option maxHeartbeats 800000 in
/-- **BSS Coloring Theorem** (Theorem 5 from the paper). -/
theorem bss_coloring
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d)
    (A : Sym2 V → Matrix (Fin d) (Fin d) ℝ)
    (hA_psd : ∀ e ∈ G.edgeFinset, (A e).PosSemidef)
    (hA_sum : ∑ e ∈ G.edgeFinset, A e = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (hdn : d ≤ Fintype.card V) :
    ∃ S : Finset V,
      (ε • (1 : Matrix (Fin d) (Fin d) ℝ) - edgeMatrixSumWithin G A S).PosSemidef ∧
      ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨S, u, huε, hMu, hsize⟩ :=
    bss_iteration_result G hd A hA_psd hA_sum ε hε hε1 hn hdn
  exact ⟨S, psd_smul_sub_mono huε hMu, hsize⟩

end ClaudeFormalizer
