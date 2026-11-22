import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

namespace ASENE

open Real
open scoped Matrix

/-! ## Sums of exponentials -/

/-- A finite sum of exponentials `t ↦ Σ_k c_k e^{l_k t}`. -/
noncomputable def expSum {ι : Type*} [Fintype ι] (c l : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, c k * exp (l k * t)

variable {ι : Type*} [Fintype ι]

/-- `d/dt Σ_k c_k e^{l_k t} = Σ_k c_k l_k e^{l_k t}`. -/
theorem hasDerivAt_expSum (c l : ι → ℝ) (t : ℝ) :
    HasDerivAt (expSum c l) (expSum (fun k => c k * l k) l t) t := by
  change HasDerivAt (fun s => ∑ k, c k * exp (l k * s)) (∑ k, c k * l k * exp (l k * t)) t
  have h : ∀ k ∈ Finset.univ, HasDerivAt (fun s => c k * exp (l k * s))
      (c k * l k * exp (l k * t)) t := by
    intro k _
    have h1 : HasDerivAt (fun s => l k * s) (l k) t := by
      simpa using (hasDerivAt_id t).const_mul (l k)
    have h2 := h1.exp.const_mul (c k)
    convert h2 using 1
    ring
  exact HasDerivAt.fun_sum h

/-- The `j`-th derivative: `dʲ/dtʲ Σ_k c_k e^{l_k t} = Σ_k c_k l_kʲ e^{l_k t}`. -/
theorem iteratedDeriv_expSum (c l : ι → ℝ) (j : ℕ) :
    iteratedDeriv j (expSum c l) = expSum (fun k => c k * l k ^ j) l := by
  induction j with
  | zero =>
    rw [iteratedDeriv_zero]
    funext t
    simp [expSum]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_expSum _ l t).deriv]
    unfold expSum
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## Appendix A.1: A sum of exponentials is not an exponential -/

/-- The Vandermonde argument, with the hypotheses it uses: `μ, λ₁, …, λₙ` all
different and `d ≠ 0`. Positivity of the coefficients and `n > 1` are not used. -/
theorem sum_exp_ne_exp_of_ne_zero {n : ℕ} (μ : ℝ) (lam : Fin n → ℝ) (d : ℝ)
    (c : Fin n → ℝ) (hdist : Function.Injective (Fin.cons μ lam : Fin (n + 1) → ℝ))
    (hd : d ≠ 0) :
    (fun t => ∑ k, c k * exp (lam k * t)) ≠ (fun t => d * exp (μ * t)) := by
  intro heq
  -- Set `λ₀ := μ`, `c₀ := −d`, so `Σ_{k=0}^n c_k e^{λ_k t} ≡ 0`.
  have hzero : expSum (Fin.cons (-d) c : Fin (n + 1) → ℝ) (Fin.cons μ lam) = fun _ => 0 := by
    funext t
    have h : ∑ k, c k * exp (lam k * t) = d * exp (μ * t) := congrFun heq t
    simp only [expSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    linear_combination h
  -- Differentiating `j` times at `t = 0` gives `Σ_k c_k λ_kʲ = 0`.
  have hmom : ∀ j : ℕ, ∑ k, (Fin.cons (-d) c : Fin (n + 1) → ℝ) k *
      (Fin.cons μ lam : Fin (n + 1) → ℝ) k ^ j = 0 := by
    intro j
    have h := congrFun (iteratedDeriv_expSum (Fin.cons (-d) c : Fin (n + 1) → ℝ)
      (Fin.cons μ lam) j) 0
    rw [hzero, iteratedDeriv_fun_const_zero] at h
    simpa [expSum] using h.symm
  -- That is `V c = 0` with `V` the `(n+1) × (n+1)` Vandermonde matrix.
  have hvec : (Fin.cons (-d) c : Fin (n + 1) → ℝ) ᵥ*
      Matrix.vandermonde (Fin.cons μ lam : Fin (n + 1) → ℝ) = 0 := by
    funext j
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] using hmom j
  -- `det V = Π_{i<k} (λ_k − λ_i) ≠ 0`, so `c = 0`, contradicting `c₀ = −d ≠ 0`.
  have hdet : (Matrix.vandermonde (Fin.cons μ lam : Fin (n + 1) → ℝ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.2 hdist
  have hc0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hvec) 0
  simp only [Fin.cons_zero, Pi.zero_apply, neg_eq_zero] at hc0
  exact hd hc0

set_option linter.unusedVariables false in
/-- **Theorem (A sum of exponentials is not an exponential).** Let
`μ, λ₁, …, λₙ` be real numbers, all different from one another, and let
`d, c₁, …, cₙ` be positive numbers with `n > 1`. Then
`Σ_{k=1}^n c_k e^{λ_k t} ≢ d e^{μ t}`. -/
theorem sum_exp_ne_exp {n : ℕ} (hn : 1 < n) (μ : ℝ) (lam : Fin n → ℝ) (d : ℝ)
    (c : Fin n → ℝ) (hdist : Function.Injective (Fin.cons μ lam : Fin (n + 1) → ℝ))
    (hd : 0 < d) (hc : ∀ k, 0 < c k) :
    (fun t => ∑ k, c k * exp (lam k * t)) ≠ (fun t => d * exp (μ * t)) :=
  sum_exp_ne_exp_of_ne_zero μ lam d c hdist hd.ne'

end ASENE
