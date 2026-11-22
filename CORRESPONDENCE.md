# Paper ↔ Lean Correspondence

**Paper:** Cohler, J. and Soon, W. *Bomb-Radiocarbon Decay Falsifies the IPCC (Part II).*
Appendix A.1. The exact version this file documents is
[`paper/bomb14c-scc-part2.pdf`](paper/bomb14c-scc-part2.pdf) in this repository.
**Formalization:** this repository, files `Asene/SumOfExponentials.lean` and `Asene/LogCurvature.lean`.

Each item in Appendix A.1 maps to the Lean declaration named below.
Line links open the Lean source in the same version of this repository
you are viewing.

## Theorem and Vandermonde proof (`Asene/SumOfExponentials.lean`)

| Paper                                                        | Lean declaration             | Line |
|--------------------------------------------------------------|------------------------------|------|
| A sum of exponentials `Σ_k c_k e^{l_k t}`                    | `expSum`                     | [18](Asene/SumOfExponentials.lean#L18) |
| Derivative of a sum of exponentials                          | `hasDerivAt_expSum`          | [24](Asene/SumOfExponentials.lean#L24) |
| Proof: "Differentiating `j` times"                           | `iteratedDeriv_expSum`       | [38](Asene/SumOfExponentials.lean#L38) |
| Proof: `λ₀ := μ`, `c₀ := −d`, `Vc = 0`, `det V ≠ 0`, `c = 0`  | `sum_exp_ne_exp_of_ne_zero`  | [56](Asene/SumOfExponentials.lean#L56) |
| Theorem (A sum of exponentials is not an exponential)        | `sum_exp_ne_exp`             | [92](Asene/SumOfExponentials.lean#L92) |

## Curvature proof (`Asene/LogCurvature.lean`)

| Paper                                                        | Lean declaration             | Line |
|--------------------------------------------------------------|------------------------------|------|
| `y > 0` for `c_k > 0`                                        | `expSum_pos`                 | [16](Asene/LogCurvature.lean#L16) |
| `y′`, `y″`, and eq. (65), `(ln y)″ = (y″ y − (y′)²) / y²`     | `log_second_deriv`           | [22](Asene/LogCurvature.lean#L22) |
| Equality form of eq. (66) (Lagrange's identity)              | `lagrange_identity`          | [42](Asene/LogCurvature.lean#L42) |
| Eq. (66), strict Cauchy–Schwarz                              | `cauchy_schwarz_strict`      | [55](Asene/LogCurvature.lean#L55) |
| "Hence `(ln y)″ > 0`"                                         | `log_curvature_pos`          | [72](Asene/LogCurvature.lean#L72) |
| Zero curvature for a single exponential                      | `log_curvature_single_exp`   | [102](Asene/LogCurvature.lean#L102) |
| The curvature proof of the Theorem                           | `sum_exp_ne_exp_curvature`   | [116](Asene/LogCurvature.lean#L116) |

**Reading notes.**

- "`μ, λ₁, …, λₙ` all different from one another" is encoded as injectivity
  of the `(n+1)`-tuple `(μ, λ₁, …, λₙ)`, written `Fin.cons μ lam`.
- The Theorem's conclusion `Σ c_k e^{λ_k t} ≢ d e^{μ t}` is a statement
  about functions of `t`, so Lean states it as inequality of functions.
- The Vandermonde proof uses only that `μ, λ₁, …, λₙ` are all different and
  that `d ≠ 0`. `sum_exp_ne_exp_of_ne_zero` proves it under exactly those
  hypotheses. `sum_exp_ne_exp` states the Theorem as written in the paper
  (positive `d` and `c_k`, `n > 1`) and derives it from the general version.
- Eq. (64) writes the exponent as `e^{−λ_i t}` inside a sum over `k`. The
  intended exponent is `e^{−λ_k t}`, which is what Lean uses.
- The curvature proof follows the paper's sign convention `y(t) = Σ c_k e^{−λ_k t}`.
  The strict inequality in (66) needs the vectors `a_k = √w_k` and
  `b_k = λ_k √w_k` not to be proportional. That holds exactly when two of the
  `λ_k` differ, which the Theorem's hypotheses supply (`λ_k` all different,
  `n > 1`). `cauchy_schwarz_strict` takes two indices with different `λ`.
- Lean proves (66) through Lagrange's identity,
  `(Σa²)(Σb²) − (Σab)² = ½ Σ_i Σ_j (a_i b_j − a_j b_i)²`, which in the
  paper's variables is `½ Σ_i Σ_j w_i w_j (λ_i − λ_j)²`. Every term is `≥ 0`,
  and a term with `λ_i ≠ λ_j` is `> 0`.
- The curvature proof of the Theorem holds for every `μ`. It does not need
  `μ` to differ from the `λ_k`.

## Axioms

```
'ASENE.sum_exp_ne_exp'            depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.log_curvature_pos'         depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.log_curvature_single_exp'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ASENE.sum_exp_ne_exp_curvature'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard Lean kernel axioms. Nothing beyond classical
mathematics.

## Reproducing the verification

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env
git clone https://github.com/cohler/asene-lean.git
cd asene-lean
lake exe cache get
lake build
```

Expected final line: `Build completed successfully`.

## Continuous verification

Every push to `main` re-runs `lake build` on a fresh GitHub Actions
Ubuntu runner with no cached state from this repository's authors. Status:

![Lean build](https://github.com/cohler/asene-lean/actions/workflows/lean_action_ci.yml/badge.svg)
