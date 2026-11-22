# asene-lean

Lean 4 formalization of "A sum of exponentials is not an exponential."

**Paper:** Cohler, J. and Soon, W. *Bomb-Radiocarbon Decay Falsifies the IPCC (Part II).*
Science of Climate Change. Theorem and both proofs: Appendix A.1.
The version matching this repository state is
[`paper/bomb14c-scc-part2.pdf`](paper/bomb14c-scc-part2.pdf).

![Lean build](https://github.com/cohler/asene-lean/actions/workflows/lean_action_ci.yml/badge.svg)

## What is verified

The files under [`Asene/`](Asene) contain the Lean 4 formalization of the theorem
and both of its proofs. The Lean kernel accepts every proof. Verified items:

| Paper (Appendix A.1)                                             | Lean name                     |
|------------------------------------------------------------------|-------------------------------|
| Theorem (A sum of exponentials is not an exponential)            | `sum_exp_ne_exp`              |
| Proof: `Vc = 0` with `V` Vandermonde, `det V ≠ 0`, so `c = 0`    | `sum_exp_ne_exp_of_ne_zero`   |
| Curvature proof: `y′ = −Σ λ_k w_k`, `y″ = Σ λ_k² w_k`, eq. (65)  | `log_second_deriv`            |
| Eq. (66), strict Cauchy–Schwarz                                  | `cauchy_schwarz_strict`       |
| `(ln y)″ > 0`: upward curvature on the semi-log plot             | `log_curvature_pos`           |
| Zero curvature for a single exponential                          | `log_curvature_single_exp`    |
| Curvature proof of the Theorem                                   | `sum_exp_ne_exp_curvature`    |

Full paper-to-Lean mapping with line numbers and notation notes:
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

## Axioms

`#print axioms` in [`Asene.lean`](Asene.lean) reports:

```
'ASENE.sum_exp_ne_exp'            depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.log_curvature_pos'         depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.log_curvature_single_exp'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.sum_exp_ne_exp_curvature'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext` is propositional extensionality. `Classical.choice` is classical
choice. `Quot.sound` is the soundness of quotient types. These are the
standard foundations of classical mathematics in Lean 4.

## Scope

The theorem is pure mathematics with no physical premises. Lean certifies
the full statement and both proofs. See [`CORRESPONDENCE.md`](CORRESPONDENCE.md)
for notation and for what each proof uses.

## Reproducing the verification

Install the Lean toolchain manager, clone this repository, pull the
Mathlib build cache, and run `lake build`:

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env
git clone https://github.com/cohler/asene-lean.git
cd asene-lean
lake exe cache get
lake build
```

Expected final line: `Build completed successfully`.

Every push to `main` also re-runs this build on a fresh GitHub Actions
Ubuntu runner with no cached state from the authors. The badge at the top
reports the current status.

## Versioning

Each tag freezes the Lean source, this documentation, and the matching
paper PDF (`paper/bomb14c-scc-part2.pdf`) together. Tags are never
moved; a new paper version gets a new tag.

| Tag    | Paper version | Date          |
|--------|---------------|---------------|
| `v1.0` | Manuscript    | November 2026 |

To build the version matching a given paper, run `git checkout <tag>`
before `lake build`.

## Toolchain

- Lean 4 (version pinned in [`lean-toolchain`](lean-toolchain))
- Mathlib (revision pinned in [`lake-manifest.json`](lake-manifest.json))
