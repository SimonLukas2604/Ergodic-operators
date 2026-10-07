/-
# Energy derivatives: `C²_E` bounds from holomorphy

The paper obtains all energy-derivative bounds (`‖∂_E^j f_E‖ ≤ j! 4^j C ε`, `j = 0, 1, 2`, in
`d-eq:C1`, and `j! d_𝒪^{-j} C ‖R‖` in the second preparation) the same way: the construction is
carried out for complex `E` in a neighbourhood of the real energy interval, it depends
holomorphically on `E` with a uniform bound, and Cauchy's estimate on a circle around each real
`E` bounds the real derivatives.  This file proves that mechanism in a Banach space:

* `cauchy_bound`: Cauchy's estimate for `iteratedDeriv`;
* `iteratedDeriv_ofReal`: real derivatives of the restriction to `ℝ` are complex derivatives;
* `real_deriv_bound`: the combined `C^k_E` bound on real energies;
* `CkE`/`cke_of_holo`: the paper's norm `‖f‖_{C^k_E}` and the bound `‖f‖_{C^2_E} ≤ 2·16·M`
  for the `1/4`-neighbourhood used in `d-eq:C1`.

Everything here is proved.
-/
import Mathlib

noncomputable section

open Complex Metric

namespace AMO

namespace Energy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Cauchy's estimate**: a function holomorphic on a neighbourhood of `closedBall c ρ` and
bounded by `M` on the circle has `‖f^{(n)}(c)‖ ≤ n! M / ρⁿ`. -/
theorem cauchy_bound {f : ℂ → X} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hcl : closedBall c ρ ⊆ U)
    (hM : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * M / ρ ^ n :=
  norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ
    ((hf.mono (by rw [closure_ball c hρ.ne']; exact hcl)).diffContOnCl) hM

/-- The restriction of `f : ℂ → X` to the real line. -/
def realRes (f : ℂ → X) : ℝ → X := fun t => f t

lemma differentiableOn_iteratedDeriv {f : ℂ → X} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- Real derivatives of the restriction of a holomorphic function are its complex derivatives. -/
theorem iteratedDeriv_ofReal {f : ℂ → X} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    ∀ t : ℝ, (t : ℂ) ∈ U → iteratedDeriv n (realRes f) t = iteratedDeriv n f t := by
  have hV : IsOpen {t : ℝ | (t : ℂ) ∈ U} := hU.preimage continuous_ofReal
  induction n with
  | zero => intro t _; simp [realRes]
  | succ n ih =>
    intro t ht
    have heq : iteratedDeriv n (realRes f) =ᶠ[nhds t] fun t' : ℝ => iteratedDeriv n f t' :=
      Filter.eventually_of_mem (hV.mem_nhds ht) fun t' ht' => ih t' ht'
    rw [iteratedDeriv_succ, iteratedDeriv_succ, heq.deriv_eq]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) t :=
      ((differentiableOn_iteratedDeriv hU hf n) t ht).differentiableAt (hU.mem_nhds ht)
    have h := (hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ofRealCLM.hasDerivAt
    have h' : HasDerivAt (fun t' : ℝ => iteratedDeriv n f t') (deriv (iteratedDeriv n f) t) t := by
      simpa [Function.comp_def] using h
    exact h'.deriv

/-- **Real-energy derivative bounds.**  If `f` is holomorphic on `U` with `‖f‖ ≤ M` on `U`, and
the closed `ρ`-disc around the real point `t` lies in `U`, then `‖∂_t^n f(t)‖ ≤ n! M / ρⁿ`. -/
theorem real_deriv_bound {f : ℂ → X} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {M ρ : ℝ} (hM : ∀ z ∈ U, ‖f z‖ ≤ M) (hρ : 0 < ρ) {t : ℝ}
    (ht : closedBall (t : ℂ) ρ ⊆ U) (n : ℕ) :
    ‖iteratedDeriv n (realRes f) t‖ ≤ n.factorial * M / ρ ^ n := by
  rw [iteratedDeriv_ofReal hU hf n t (ht (mem_closedBall_self hρ.le))]
  exact cauchy_bound hf hρ ht (fun z hz => hM z (ht (sphere_subset_closedBall hz))) n

/-- The complex `1/2`-neighbourhood of a real interval `[e₁, e₂]`, as in `d-eq:C1`. -/
def nbhd (e₁ e₂ : ℝ) : Set ℂ := {z | ∃ t ∈ Set.Icc e₁ e₂, ‖z - t‖ < 1 / 2}

lemma isOpen_nbhd (e₁ e₂ : ℝ) : IsOpen (nbhd e₁ e₂) := by
  have : nbhd e₁ e₂ = ⋃ t ∈ Set.Icc e₁ e₂, ball (t : ℂ) (1 / 2) := by
    ext z; simp [nbhd, dist_eq_norm]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

lemma closedBall_subset_nbhd {e₁ e₂ t : ℝ} (ht : t ∈ Set.Icc e₁ e₂) :
    closedBall (t : ℂ) (1 / 4) ⊆ nbhd e₁ e₂ := fun z hz =>
  ⟨t, ht, by rw [mem_closedBall, dist_eq_norm] at hz; linarith⟩

/-- The paper's `C^k_E` bound: `‖∂_E^j f_E‖ ≤ B` for all real `E ∈ [e₁, e₂]` and `j ≤ k`. -/
def CkE (k : ℕ) (e₁ e₂ : ℝ) (f : ℝ → X) (B : ℝ) : Prop :=
  ∀ j ≤ k, ∀ t ∈ Set.Icc e₁ e₂, ‖iteratedDeriv j f t‖ ≤ B

/-- **`d-eq:C1` mechanism.**  If the coefficient is holomorphic on the `1/2`-neighbourhood of
`[e₁, e₂]` with norm `≤ M` there, then `‖∂_E^j f‖ ≤ j! 4^j M` for `j = 0, 1, 2` on `[e₁, e₂]`;
in particular `‖f‖_{C^2_E} ≤ 32 M`. -/
theorem deriv_bound_nbhd {f : ℂ → X} {e₁ e₂ M : ℝ}
    (hf : DifferentiableOn ℂ f (nbhd e₁ e₂)) (hM : ∀ z ∈ nbhd e₁ e₂, ‖f z‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc e₁ e₂) (n : ℕ) :
    ‖iteratedDeriv n (realRes f) t‖ ≤ n.factorial * 4 ^ n * M := by
  have h := real_deriv_bound (isOpen_nbhd e₁ e₂) hf hM (by norm_num : (0 : ℝ) < 1 / 4)
    (closedBall_subset_nbhd ht) n
  calc _ ≤ _ := h
    _ = n.factorial * 4 ^ n * M := by
      rw [one_div, inv_pow, div_inv_eq_mul]; ring

theorem cke_of_holo {f : ℂ → X} {e₁ e₂ M : ℝ}
    (hf : DifferentiableOn ℂ f (nbhd e₁ e₂)) (hM : ∀ z ∈ nbhd e₁ e₂, ‖f z‖ ≤ M) (hM0 : 0 ≤ M) :
    CkE 2 e₁ e₂ (realRes f) (32 * M) := by
  intro j hj t ht
  refine (deriv_bound_nbhd hf hM ht j).trans ?_
  interval_cases j <;> norm_num [Nat.factorial] <;> nlinarith

end Energy

end AMO
