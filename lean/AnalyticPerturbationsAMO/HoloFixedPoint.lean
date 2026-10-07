/-
# Holomorphic dependence of fixed points on a parameter

If `Φ_E` is a uniform contraction of the closed `ρ`-ball of a complex Banach space for `E` in an
open set `U`, and `E ↦ Φ_E(g(E))` is holomorphic whenever `g` is holomorphic with values in the
ball, then the fixed point `z(E)` is holomorphic on `U`: it is the uniform limit of the
holomorphic Picard iterates `Φ_E^n(0)`, with `‖Φ_E^n(0) - z(E)‖ ≤ kⁿ ρ / (1 - k)`.

This is the abstract step behind "carry out the preparation for complex `E`" in the paper; with
`EnergyDerivatives.lean` it turns uniform fixed-point bounds into `C²_E` bounds.
Everything here is proved.
-/
import Mathlib

noncomputable section

open Filter Topology Metric

namespace AMO

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Holomorphic fixed points of holomorphic uniform contractions.** -/
theorem holo_fixed_point {U : Set ℂ} (hU : IsOpen U) {Φ : ℂ → X → X} {ρ k : ℝ} (hρ : 0 ≤ ρ)
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hmaps : ∀ E ∈ U, ∀ x, ‖x‖ ≤ ρ → ‖Φ E x‖ ≤ ρ)
    (hlip : ∀ E ∈ U, ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ → ‖Φ E x - Φ E y‖ ≤ k * ‖x - y‖)
    (hholo : ∀ g : ℂ → X, DifferentiableOn ℂ g U → (∀ E ∈ U, ‖g E‖ ≤ ρ) →
      DifferentiableOn ℂ (fun E => Φ E (g E)) U) :
    ∃ z : ℂ → X, DifferentiableOn ℂ z U ∧ ∀ E ∈ U, ‖z E‖ ≤ ρ ∧ Φ E (z E) = z E ∧
      ∀ n : ℕ, ‖(Φ E)^[n] 0 - z E‖ ≤ k ^ n * ρ / (1 - k) := by
  set g : ℕ → ℂ → X := fun n E => (Φ E)^[n] 0 with hg
  have hsucc : ∀ n E, g (n + 1) E = Φ E (g n E) := fun n E => by
    simp only [hg]; exact Function.iterate_succ_apply' _ _ _
  have hbd : ∀ n, ∀ E ∈ U, ‖g n E‖ ≤ ρ := by
    intro n
    induction n with
    | zero => intro E _; simpa [hg] using hρ
    | succ n ih => intro E hE; rw [hsucc]; exact hmaps E hE _ (ih E hE)
  have hdiff : ∀ n, DifferentiableOn ℂ (g n) U := by
    intro n
    induction n with
    | zero => simpa [hg] using differentiableOn_const (0 : X)
    | succ n ih =>
      have hfun : g (n + 1) = fun E => Φ E (g n E) := funext (hsucc n)
      rw [hfun]
      exact hholo (g n) ih (hbd n)
  -- geometric control of consecutive iterates
  have hstep : ∀ E ∈ U, ∀ n, dist (g n E) (g (n + 1) E) ≤ ρ * k ^ n := by
    intro E hE n
    induction n with
    | zero =>
      simp only [hg, Function.iterate_zero, id, pow_zero, mul_one,
        dist_eq_norm, zero_sub, norm_neg]
      exact hmaps E hE 0 (by simpa using hρ)
    | succ n ih =>
      rw [dist_eq_norm, hsucc (n + 1) E]
      nth_rewrite 1 [hsucc n E]
      calc ‖Φ E (g n E) - Φ E (g (n + 1) E)‖ ≤ k * ‖g n E - g (n + 1) E‖ :=
            hlip E hE _ _ (hbd n E hE) (hbd (n + 1) E hE)
        _ ≤ k * (ρ * k ^ n) := by rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left ih hk0
        _ = ρ * k ^ (n + 1) := by ring
  have hcauchy : ∀ E ∈ U, CauchySeq fun n => g n E := fun E hE =>
    cauchySeq_of_le_geometric k ρ hk1 (hstep E hE)
  set z : ℂ → X := fun E => limUnder atTop fun n => g n E with hz
  have hlim : ∀ E ∈ U, Tendsto (fun n => g n E) atTop (𝓝 (z E)) := fun E hE =>
    (hcauchy E hE).tendsto_limUnder
  have hrate : ∀ E ∈ U, ∀ n, ‖g n E - z E‖ ≤ k ^ n * ρ / (1 - k) := fun E hE n => by
    have := dist_le_of_le_geometric_of_tendsto k ρ hk1 (hstep E hE) (hlim E hE) n
    rw [dist_eq_norm] at this
    calc ‖g n E - z E‖ ≤ ρ * k ^ n / (1 - k) := this
      _ = k ^ n * ρ / (1 - k) := by ring
  have hzbd : ∀ E ∈ U, ‖z E‖ ≤ ρ := fun E hE =>
    le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim E hE)) fun n => hbd n E hE
  -- uniform convergence of the iterates
  have hunif : TendstoUniformlyOn g z atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : Tendsto (fun n : ℕ => k ^ n * ρ / (1 - k)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const (ρ / (1 - k))
      simpa [mul_div_assoc] using this
    filter_upwards [hk.eventually (gt_mem_nhds hε)] with n hn E hE
    rw [dist_comm, dist_eq_norm]
    exact (hrate E hE n).trans_lt hn
  have hzdiff : DifferentiableOn ℂ z U :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hdiff) hU
  refine ⟨z, hzdiff, fun E hE => ⟨hzbd E hE, ?_, hrate E hE⟩⟩
  -- the limit is a fixed point
  have h1 : Tendsto (fun n => g (n + 1) E) atTop (𝓝 (z E)) :=
    (hlim E hE).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => g (n + 1) E) atTop (𝓝 (Φ E (z E))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 (hlim E hE)).const_mul k))
    rw [hsucc]
    exact hlip E hE _ _ (hbd n E hE) (hzbd E hE)
  exact tendsto_nhds_unique h2 h1

end AMO
