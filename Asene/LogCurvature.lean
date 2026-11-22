import Asene.SumOfExponentials
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option linter.style.header false

namespace ASENE

open Real

variable {ι : Type*} [Fintype ι]

/-! ## Appendix A.1: the curvature proof -/

/-- A sum of exponentials with positive coefficients is positive. -/
theorem expSum_pos [Nonempty ι] (c l : ι → ℝ) (hc : ∀ k, 0 < c k) (t : ℝ) :
    0 < expSum c l t :=
  Finset.sum_pos (fun k _ => mul_pos (hc k) (exp_pos _)) Finset.univ_nonempty

/-- `(ln y)'' = (y'' y − (y')²) / y²` for `y = Σ_k c_k e^{l_k t}`, with
`y' = Σ_k c_k l_k e^{l_k t}` and `y'' = Σ_k c_k l_k² e^{l_k t}`. -/
theorem log_second_deriv [Nonempty ι] (c l : ι → ℝ) (hc : ∀ k, 0 < c k) (t : ℝ) :
    deriv (deriv (fun s => log (expSum c l s))) t =
      (expSum (fun k => c k * l k ^ 2) l t * expSum c l t -
        expSum (fun k => c k * l k) l t ^ 2) / expSum c l t ^ 2 := by
  have h1 : deriv (fun s => log (expSum c l s)) =
      fun s => expSum (fun k => c k * l k) l s / expSum c l s :=
    funext fun s => ((hasDerivAt_expSum c l s).log (expSum_pos c l hc s).ne').deriv
  have hdiv := (hasDerivAt_expSum (fun k => c k * l k) l t).div (hasDerivAt_expSum c l t)
    (expSum_pos c l hc t).ne'
  rw [h1]
  change deriv (expSum (fun k => c k * l k) l / expSum c l) t = _
  rw [hdiv.deriv]
  have h2 : expSum (fun k => c k * l k * l k) l t = expSum (fun k => c k * l k ^ 2) l t := by
    unfold expSum
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h2]
  ring

/-- Lagrange's identity, the equality form of Cauchy–Schwarz used in (66):
`2 ((Σ l² w)(Σ w) − (Σ l w)²) = Σ_i Σ_j w_i w_j (l_i − l_j)²`. -/
theorem lagrange_identity (w l : ι → ℝ) :
    2 * ((∑ k, l k ^ 2 * w k) * (∑ k, w k) - (∑ k, l k * w k) ^ 2) =
      ∑ i, ∑ j, w i * w j * (l i - l j) ^ 2 := by
  have e : ∀ i j, w i * w j * (l i - l j) ^ 2 =
      l i ^ 2 * w i * w j + w i * (l j ^ 2 * w j) - 2 * (l i * w i) * (l j * w j) := by
    intro i j
    ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

/-- Strict Cauchy–Schwarz, (66): with all `w_k > 0` and two different `l_i ≠ l_j`,
`(Σ l² w)(Σ w) > (Σ l w)²`. -/
theorem cauchy_schwarz_strict (w l : ι → ℝ) (hw : ∀ k, 0 < w k) (i₀ j₀ : ι)
    (hne : l i₀ ≠ l j₀) :
    (∑ k, l k * w k) ^ 2 < (∑ k, l k ^ 2 * w k) * (∑ k, w k) := by
  have hpos : 0 < ∑ i, ∑ j, w i * w j * (l i - l j) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hw i).le (hw j).le) (sq_nonneg _)))
    refine ⟨i₀, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ =>
      mul_nonneg (mul_nonneg (hw i₀).le (hw j).le) (sq_nonneg _))
    exact ⟨j₀, Finset.mem_univ _,
      mul_pos (mul_pos (hw i₀) (hw j₀)) (sq_pos_of_ne_zero (sub_ne_zero.2 hne))⟩
  have h := lagrange_identity w l
  linarith

/-- **Curvature proof.** For `y(t) = Σ_k c_k e^{−λ_k t}` with all `c_k > 0`,
`n > 1`, and the `λ_k` all different, `(ln y)'' > 0` at every `t`: every such
sum has upward curvature on the semi-log plot. -/
theorem log_curvature_pos {n : ℕ} (hn : 1 < n) (c lam : Fin n → ℝ) (hc : ∀ k, 0 < c k)
    (hlam : Function.Injective lam) (t : ℝ) :
    0 < deriv (deriv (fun s => log (expSum c (fun k => -lam k) s))) t := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [log_second_deriv c _ hc t]
  refine div_pos ?_ (pow_pos (expSum_pos c _ hc t) 2)
  -- the numerator is `(Σ w)(Σ λ² w) − (Σ λ w)²` with `w_k = c_k e^{−λ_k t}`
  set w : Fin n → ℝ := fun k => c k * exp (-lam k * t) with hw_def
  have hw : ∀ k, 0 < w k := fun k => mul_pos (hc k) (exp_pos _)
  have hne : -lam (⟨0, by omega⟩ : Fin n) ≠ -lam ⟨1, hn⟩ := by
    intro h
    have h' := hlam (neg_inj.1 h)
    exact absurd (congrArg Fin.val h') (by simp)
  have hcs := cauchy_schwarz_strict w (fun k => -lam k) hw ⟨0, by omega⟩ ⟨1, hn⟩ hne
  have e2 : expSum (fun k => c k * (-lam k) ^ 2) (fun k => -lam k) t =
      ∑ k, (-lam k) ^ 2 * w k := by
    unfold expSum
    exact Finset.sum_congr rfl (fun k _ => by simp only [hw_def]; ring)
  have e1 : expSum (fun k => c k * -lam k) (fun k => -lam k) t =
      ∑ k, -lam k * w k := by
    unfold expSum
    exact Finset.sum_congr rfl (fun k _ => by simp only [hw_def]; ring)
  have e0 : expSum c (fun k => -lam k) t = ∑ k, w k := by
    unfold expSum
    exact Finset.sum_congr rfl (fun k _ => rfl)
  rw [e2, e1, e0]
  linarith

/-- A single exponential `d e^{−μ t}` with `d > 0` has zero curvature on the
semi-log plot: `(ln y)'' = 0`. -/
theorem log_curvature_single_exp (d μ : ℝ) (hd : 0 < d) (t : ℝ) :
    deriv (deriv (fun s => log (d * exp (-μ * s)))) t = 0 := by
  have h1 : (fun s => log (d * exp (-μ * s))) = fun s => log d + -μ * s := by
    funext s
    rw [log_mul hd.ne' (exp_pos _).ne', log_exp]
  have h2 : deriv (fun s => log d + -μ * s) = fun _ => -μ := by
    funext s
    simp
  rw [h1, h2, deriv_const]

/-- **Curvature proof of the Theorem.** A sum `Σ_k c_k e^{−λ_k t}` with all
`c_k > 0`, `n > 1`, and the `λ_k` all different is not a single exponential
`d e^{−μ t}` with `d > 0`, for any `μ`: the first has `(ln y)'' > 0`, the second
has `(ln y)'' = 0`. -/
theorem sum_exp_ne_exp_curvature {n : ℕ} (hn : 1 < n) (c lam : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (hlam : Function.Injective lam) (d μ : ℝ) (hd : 0 < d) :
    expSum c (fun k => -lam k) ≠ fun t => d * exp (-μ * t) := by
  intro h
  have hpos := log_curvature_pos hn c lam hc hlam 0
  have hfun : (fun s => log (expSum c (fun k => -lam k) s)) =
      fun s => log (d * exp (-μ * s)) := by
    funext s
    rw [show expSum c (fun k => -lam k) s = d * exp (-μ * s) from congrFun h s]
  rw [hfun, log_curvature_single_exp d μ hd 0] at hpos
  exact lt_irrefl 0 hpos

end ASENE
