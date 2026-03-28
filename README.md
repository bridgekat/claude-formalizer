# Claude Formalizer Workspace

Autoformalization of informal proofs for the [First Proof challenge](https://arxiv.org/abs/2602.05192/) using [Claude Opus 4.6](https://www.anthropic.com/claude/opus/).

## Problems

### Problem 6 — Large ε-Light Vertex Subsets

**Source:** [Informal proof by OpenAI](https://openai.com/index/first-proof-submissions/), replicated as [LaTeX](Problems/6.tex) by Claude Sonnet 4.6.

**Result:** Fully formalized. The main theorem is stated in [`ClaudeFormalizer/Problem6/Main.lean`](ClaudeFormalizer/Problem6/Main.lean) and its proof is complete in 1800 lines of Lean code (excluding whitespace and comments). The main theorem statement depends on definitions in [`ClaudeFormalizer/Problem6/Defs.lean`](ClaudeFormalizer/Problem6/Defs.lean), and the proof verifies with no extra axioms.

**Note that the agent was not instructed to produce high-quality code, and there has been no refactoring or simplifications made.** The proof may not be easily readable.

### Problem 5 — O-Slice Connectivity via Geometric Fixed Points

**Source:** [LaTeX](Problems/5.tex) — defines the slice filtration on the G-equivariant stable category adapted to an incomplete transfer system O, and proves a characterization of O-slice connectivity in terms of geometric fixed points.

**Result:** Partially formalized. The combinatorial content (transfer systems, O-index, orbit counting lemma) is fully formalized with no extra axioms. The equivariant stable homotopy theory (genuine G-spectra, geometric fixed points, slice filtration) is axiomatized via a `SliceFramework` class, since these objects do not exist in Mathlib.

#### What is fully formalized

- **Transfer systems** ([`Defs.lean`](ClaudeFormalizer/Problem5/Defs.lean)): The definition of a transfer system on a finite group G (Balchin–Barnes–Roitzheim), the minimal admissible subgroup H_O, and the O-index ‖J‖_O = [J : J_O]. All properties (closure under intersection, conjugation invariance, positivity) are proved from the axioms of transfer systems using Mathlib's finite group theory.

- **Orbit counting lemma** ([`OrbitBound.lean`](ClaudeFormalizer/Problem5/OrbitBound.lean)): The key combinatorial result — if K is O-admissible in H and J ≤ H, then every J-orbit on the coset space H/K has size at most ‖J‖_O. The proof uses the stabilizer admissibility lemma (J ∩ gKg⁻¹ is O-admissible in J) and the orbit-stabilizer theorem. This is the mathematical heart of the proof and is fully formal.

- **Necessity direction** ([`Main.lean`](ClaudeFormalizer/Problem5/Main.lean)): The forward direction of the main theorem (X ∈ Σ≥n^O implies the geometric fixed point bounds) is a genuine proof combining the axiomatized Mackey formula with the formalized orbit counting lemma via ceiling division monotonicity.

#### What is axiomatized

The [`SliceFramework`](ClaudeFormalizer/Problem5/Framework.lean) class axiomatizes the equivariant stable homotopy category with five property axioms:

| Axiom | Mathematical content | Role |
|-------|---------------------|------|
| `geomConn_mono` | Connectivity is downward-closed | Background (definitional) |
| `cell_inOSlice` | Slice cells of dimension ≥ n are in Σ≥n^O | Background (definition of Σ≥n^O) |
| `cell_conn_bound` | Mackey formula: Φ^J(cell) is ⌈[H:K]/‖J‖_O⌉-connective | Bridges categorical and combinatorial worlds |
| `slice_geomConn_of_cell_geomConn` | Connectivity bounds propagate from generators | Standard categorical property |
| `conn_implies_slice` | Connectivity bounds imply slice membership | **Encodes the entire sufficiency direction** |

The sufficiency direction (the hard direction, involving isotropy separation, induction on |G|, and geometric localization) is axiomatized rather than proved. This is the main limitation of the formalization.

#### Files

| File | Lines | Sorries | Content |
|------|-------|---------|---------|
| [`Defs.lean`](ClaudeFormalizer/Problem5/Defs.lean) | ~180 | 0 | Transfer systems, minimal admissible subgroup, O-index |
| [`OrbitBound.lean`](ClaudeFormalizer/Problem5/OrbitBound.lean) | ~150 | 0 | Stabilizer admissibility, orbit counting theorem |
| [`Framework.lean`](ClaudeFormalizer/Problem5/Framework.lean) | ~105 | 0 | Axiomatized equivariant homotopical framework |
| [`Main.lean`](ClaudeFormalizer/Problem5/Main.lean) | ~100 | 0 | Main theorem: necessity (proved), sufficiency (from axiom), iff |

All declarations use only the standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).

#### Verification

The formalization has been verified at multiple levels:

| Verification Layer | Tool | Result |
|---|---|---|
| Compilation | `lake build` | ✅ 0 errors |
| Sorry check | `sorry_analyzer.py` | ✅ 0 sorries across 4 files |
| Axiom check | `check_axioms_inline.sh` | ✅ Standard axioms only |
| Per-theorem axioms | `lean_verify` (7 key theorems) | ✅ `{propext, Classical.choice, Quot.sound}` only |
| Kernel replay | [`lean4checker`](https://github.com/leanprover/lean4checker) | ✅ 4/4 modules replayed |

The kernel replay via `lean4checker` independently replays every declaration through the Lean kernel without trusting `.olean` files, providing the strongest available guarantee of proof validity.

For adversarial verification (e.g., judging untrusted submissions), the [`comparator`](https://github.com/leanprover/comparator) tool adds sandboxed builds via [`landrun`](https://github.com/Zouuup/landrun) (Linux only) and statement-equivalence checking between challenge and solution modules.

## Experimental Setup

- **Model:** [Claude Opus 4.6](https://www.anthropic.com/claude/opus/)
- **Agent:** [Claude Code CLI](https://claude.com/product/claude-code/) (with `--dangerously-skip-permissions`)
- **Tools:**
    - [Lean Theorem Prover MCP](https://github.com/oOo0oOo/lean-lsp-mcp/) (modified to fix encoding issues on Windows)
- **Contexts:**
    - [Lean 4 Skills](https://github.com/cameronfreer/lean4-skills/)
    - [`AGENTS.md`](AGENTS.md)
    - Initial prompt: ``Read `Problems/<N>.tex` and formalize it in Lean according to instructions in `AGENTS.md`.``
    - Resume prompt (existing context): `Proceed.`
    - Resume prompt (new context): ``Read `Problems/<N>.tex` and formalize it in Lean according to instructions in `AGENTS.md`. Check the current state for any existing work, evaluate it and then build on it.``
