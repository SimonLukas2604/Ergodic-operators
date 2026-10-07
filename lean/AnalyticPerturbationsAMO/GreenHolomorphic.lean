/-
# Holomorphic dependence of the Green series on the energy

If the coefficients `β_j(E)`, `d_j(E)` of the tail recurrence depend holomorphically on `E` in an
open set `U`, the transfer products obey `‖P_{j,m}(E)‖ ≤ C e^{γ m}` uniformly on `U`, and the
sources are dominated uniformly, `‖d_r(E)‖ ≤ δ_r` with `∑ e^{s r} δ_r < ∞`, then each Green
vector `E ↦ v_j(E)` is holomorphic on `U` and uniformly bounded there.  Combined with
`EnergyDerivatives.lean` this gives the `C²_E` bounds of the tail inverse.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.TailInverse
import AnalyticPerturbationsAMO.EnergyDerivatives

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace AMO

namespace Tail

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
variable {U : Set ℂ} {β d : ℂ → ℕ → B}

lemma P_entry_holo (hβ : ∀ j, DifferentiableOn ℂ (fun z => β z j) U) (m : ℕ) :
    ∀ j i k, DifferentiableOn ℂ (fun z => P (β z) j m i k) U := by
  induction m with
  | zero => intro j i k; simp only [P]; exact differentiableOn_const _
  | succ m ih =>
    intro j i k
    simp only [P, Matrix.mul_apply, Fin.sum_univ_two]
    refine DifferentiableOn.add (DifferentiableOn.mul ?_ (ih _ _ _))
      (DifferentiableOn.mul ?_ (ih _ _ _)) <;>
    fin_cases i <;> simp [tm, hβ j, differentiableOn_const]

lemma gterm_holo (hβ : ∀ j, DifferentiableOn ℂ (fun z => β z j) U)
    (hd : ∀ r, DifferentiableOn ℂ (fun z => d z r) U) (j m : ℕ) :
    DifferentiableOn ℂ (fun z => gterm (β z) (d z) j m) U := by
  refine differentiableOn_pi.2 fun i => ?_
  simp only [gterm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
  exact (P_entry_holo hβ m j i 0).mul (hd _)

variable {C γ s : ℝ} {δ : ℕ → ℝ}

/-- **The Green vectors depend holomorphically on the energy**, with a uniform bound. -/
theorem green_holo (hU : IsOpen U) (hβ : ∀ j, DifferentiableOn ℂ (fun z => β z j) U)
    (hd : ∀ r, DifferentiableOn ℂ (fun z => d z r) U) (hC : 0 ≤ C)
    (hP : ∀ z ∈ U, ∀ j m, ‖P (β z) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < s)
    (hδ : ∀ z ∈ U, ∀ r, ‖d z r‖ ≤ δ r) (hδs : Summable fun r : ℕ => Real.exp (s * r) * δ r)
    (j : ℕ) :
    DifferentiableOn ℂ (fun z => green (β z) (d z) j) U ∧
      ∀ z ∈ U, ‖green (β z) (d z) j‖ ≤
        C * Real.exp (-s * j) * ∑' m : ℕ, Real.exp (s * (j + m : ℕ)) * δ (j + m) := by
  have hsh : Summable fun m : ℕ => Real.exp (s * (j + m : ℕ)) * δ (j + m) :=
    hδs.comp_injective (add_right_injective j)
  have hdz : ∀ z ∈ U, Summable fun r : ℕ => Real.exp (s * r) * ‖d z r‖ := fun z hz =>
    hδs.of_nonneg_of_le (fun r => by positivity)
      fun r => mul_le_mul_of_nonneg_left (hδ z hz r) (Real.exp_pos _).le
  have hle : ∀ z ∈ U, ∀ m, ‖gterm (β z) (d z) j m‖ ≤
      C * Real.exp (-s * j) * (Real.exp (s * (j + m : ℕ)) * δ (j + m)) := fun z hz m => by
    refine (norm_gterm_le hC (hP z hz) hγs (hdz z hz) j m).trans ?_
    have h1 : Real.exp ((γ - s) * m) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg m))
    have h2 : Real.exp (s * (j + m : ℕ)) * ‖d z (j + m)‖ ≤
        Real.exp (s * (j + m : ℕ)) * δ (j + m) :=
      mul_le_mul_of_nonneg_left (hδ z hz _) (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (s * (j + m : ℕ)) * ‖d z (j + m)‖ := by positivity
    have h4 : 0 ≤ C * Real.exp (-s * j) := by positivity
    calc C * Real.exp (-s * j) * (Real.exp ((γ - s) * m) *
          (Real.exp (s * (j + m : ℕ)) * ‖d z (j + m)‖))
        ≤ C * Real.exp (-s * j) * (1 * (Real.exp (s * (j + m : ℕ)) * δ (j + m))) := by
          gcongr
      _ = _ := by rw [one_mul]
  refine ⟨?_, fun z hz => ?_⟩
  · exact Complex.differentiableOn_tsum_of_summable_norm (hsh.mul_left (C * Real.exp (-s * j)))
      (fun m => gterm_holo hβ hd j m) hU (fun m z hz => hle z hz m)
  · rw [← tsum_mul_left]
    exact norm_tsum_le_tsum_norm (summable_gterm_norm hC (hP z hz) hγs (hdz z hz) j) |>.trans
      (Summable.tsum_le_tsum (hle z hz) (summable_gterm_norm hC (hP z hz) hγs (hdz z hz) j)
        (hsh.mul_left _))

/-- The scalar Green solution `l_j(E) = v_j(E)₀` is holomorphic in `E`. -/
theorem green0_holo (hU : IsOpen U) (hβ : ∀ j, DifferentiableOn ℂ (fun z => β z j) U)
    (hd : ∀ r, DifferentiableOn ℂ (fun z => d z r) U) (hC : 0 ≤ C)
    (hP : ∀ z ∈ U, ∀ j m, ‖P (β z) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < s)
    (hδ : ∀ z ∈ U, ∀ r, ‖d z r‖ ≤ δ r) (hδs : Summable fun r : ℕ => Real.exp (s * r) * δ r)
    (j : ℕ) : DifferentiableOn ℂ (fun z => green (β z) (d z) j 0) U :=
  (differentiableOn_pi.1 (green_holo hU hβ hd hC hP hγs hδ hδs j).1) 0

/-- **`C²_E` bound for the Green solution** on a real energy interval `[e₁, e₂]`, from
holomorphy on its `1/2`-neighbourhood: `‖∂_E^n l_j(E)‖ ≤ n! 4ⁿ M_j` for every `n`, with
`M_j = C e^{-s j} ∑_m e^{s(j+m)} δ_{j+m}`. -/
theorem green0_deriv_bound {e₁ e₂ : ℝ}
    (hβ : ∀ j, DifferentiableOn ℂ (fun z => β z j) (Energy.nbhd e₁ e₂))
    (hd : ∀ r, DifferentiableOn ℂ (fun z => d z r) (Energy.nbhd e₁ e₂)) (hC : 0 ≤ C)
    (hP : ∀ z ∈ Energy.nbhd e₁ e₂, ∀ j m, ‖P (β z) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < s)
    (hδ : ∀ z ∈ Energy.nbhd e₁ e₂, ∀ r, ‖d z r‖ ≤ δ r)
    (hδs : Summable fun r : ℕ => Real.exp (s * r) * δ r) (j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc e₁ e₂) (n : ℕ) :
    ‖iteratedDeriv n (Energy.realRes fun z => green (β z) (d z) j 0) t‖ ≤
      n.factorial * 4 ^ n *
        (C * Real.exp (-s * j) * ∑' m : ℕ, Real.exp (s * (j + m : ℕ)) * δ (j + m)) := by
  have hU := Energy.isOpen_nbhd e₁ e₂
  refine Energy.deriv_bound_nbhd (green0_holo hU hβ hd hC hP hγs hδ hδs j) (fun z hz => ?_) ht n
  exact (norm_le_pi_norm _ 0).trans ((green_holo hU hβ hd hC hP hγs hδ hδs j).2 z hz)

end Tail

end AMO
