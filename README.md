# Claude Formalizer Workspace

## Task

Autoformalization of the [informal proof by OpenAI](https://openai.com/index/first-proof-submissions/) for the [First Proof challenge](https://arxiv.org/abs/2602.05192/), Question 6.

[Claude Sonnet 4.6](https://www.anthropic.com/claude/sonnet/) has generated [LaTeX source code](Problems/6.tex) that replicates the published problem and informal solution.

## Experimental Setup

- **Model:** [Claude Opus 4.6](https://www.anthropic.com/claude/opus/) (with `/effort max`)
- **Agent:** [Claude Code CLI 2.1.85](https://claude.com/product/claude-code/) (with `--dangerously-skip-permissions`)
- **Tools:**
    - [Lean Theorem Prover MCP](https://github.com/oOo0oOo/lean-lsp-mcp/) (modified to fix encoding issues on Windows)
- **Contexts:**
    - [Lean 4 Skills](https://github.com/cameronfreer/lean4-skills/)
    - [`AGENTS.md`](AGENTS.md)
    - Initial prompt: ``Read `Problems/6.tex` and formalize it in Lean according to instructions in `AGENTS.md`.``
    - Resume prompt (existing context): `Proceed.`
    - Resume prompt (new context): ``Read `Problems/6.tex` and formalize it in Lean according to instructions in `AGENTS.md`. Check the current state for any existing work, evaluate it and then build on it.``

## Results

The main theorem is stated in [`ClaudeFormalizer/Main.lean`](ClaudeFormalizer/Main.lean) and its proof is complete in 1800 lines of Lean code (excluding whitespace and comments). The main theorem statement depends on definitions in [`ClaudeFormalizer/Defs.lean`](ClaudeFormalizer/Defs.lean), and the proof verifies with no extra axioms.

**Note that the agent was not instructed to produce high-quality code, and there has been no refactoring or simplifications made.** The proof may not be easily readable.
