/-
# Lemma 2.4 for symbols: holomorphic and `C²_E` dependence on the energy

Let the phase coefficient `w_E` and the source `D_E` of the tail problem
`Π_{≥2}(J₀(E) K) = D_E`, `J₀(E) = a(U + U^{-1}) + w_E`, depend holomorphically on the energy `E`
in the complex `1/2`-neighbourhood of a real interval `[e₁, e₂]`.  Assume that the transfer
products satisfy `‖P_{j,m}(E)‖ ≤ C e^{γ m}` uniformly there, `γ < s`, and that the rows of `D_E`
are dominated uniformly: `ρ_{j+2}(D_E) ≤ Δ_j` with `∑ e^{s j} Δ_j < ∞`.  Then each row
`L_j(E) = l_{j+1}(E)` of the solution `K(E)` is holomorphic, and on the real interval
  `‖∂_E^n L_j(E)‖ ≤ n! 4ⁿ C e^{-sj} ∑_m e^{s(j+m)} |a|^{-1} Δ_{j+m}`,   `n = 0, 1, 2, …`.
This is the `C²_E` statement used for the second preparation, obtained exactly as in the paper
(holomorphy in a complex neighbourhood plus Cauchy).  Everything here is proved.
-/
import AnalyticPerturbationsAMO.TailSymbol
import AnalyticPerturbationsAMO.GreenHolomorphic

noncomputable section

open scoped Matrix.Norms.Operator

namespace AMO

section Rows

variable {α : ℝ}

/-! ### Linearity of the row operations -/

lemma wtr_add (w w' : Symbol) (r : ℤ) : wtr α (w + w') r = wtr α w r + wtr α w' r := by
  funext p; simp only [wtr, Pi.add_apply]; split_ifs <;> ring

lemma wtr_smul (c : ℂ) (w : Symbol) (r : ℤ) : wtr α (c • w) r = c • wtr α w r := by
  funext p; simp only [wtr, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

lemma lrow_add (K K' : Symbol) (r : ℤ) : lrow α (K + K') r = lrow α K r + lrow α K' r := by
  funext p; simp only [lrow, Pi.add_apply]; split_ifs <;> ring

lemma lrow_smul (c : ℂ) (K : Symbol) (r : ℤ) : lrow α (c • K) r = c • lrow α K r := by
  funext p; simp only [lrow, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

lemma norm_wtr_term_le (w : Symbol) (r : ℤ) (p : ℤ × ℤ) : ‖wtr α w r p‖ ≤ ‖w p‖ := by
  obtain ⟨a, b⟩ := p
  simp only [wtr]
  split_ifs with h
  · obtain rfl : a = 0 := h
    simp
  · simp

lemma wtr_wsum' {s ℓ : ℝ} {w : Symbol} (hW : WSum s ℓ w) (r : ℤ) : WSum s ℓ (wtr α w r) :=
  hW.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    fun p => mul_le_mul_of_nonneg_right (norm_wtr_term_le w r p) (wt_pos p).le

lemma wnorm_wtr_le {s ℓ : ℝ} {w : Symbol} (hW : WSum s ℓ w) (r : ℤ) :
    wnorm s ℓ (wtr α w r) ≤ wnorm s ℓ w :=
  Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_right (norm_wtr_term_le w r p)
    (wt_pos p).le) (wtr_wsum' hW r) hW

lemma wnorm_lrow_le {s ℓ : ℝ} (hs : 0 ≤ s) {K : Symbol} (hK : WSum s ℓ K) (r : ℤ) :
    wnorm s ℓ (lrow α K r) ≤ wnorm s ℓ K := by
  rw [(lrow_wsum hs hK r).2]
  have h := hK.rows
  calc ∑' q : ℤ, ‖K (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) = rowSum ℓ K r := rfl
    _ ≤ Real.exp (s * |(r : ℝ)|) * rowSum ℓ K r :=
        le_mul_of_one_le_left (rowSum_nonneg _ _ _)
          (Real.one_le_exp_iff.2 (mul_nonneg hs (abs_nonneg _)))
    _ ≤ wnorm s ℓ K := by
        rw [h.2]
        exact h.1.le_tsum r fun r' _ => mul_nonneg (Real.exp_pos _).le (rowSum_nonneg _ _ _)

end Rows

namespace TailSym

variable (ω : Weights) (α : ℝ)

lemma symW (f : WAlg ω α) : WSum ω.s ω.ℓ (WAlg.sym ω α f) := ω.toS_wsum f

lemma sym_mk_wtr (r : ℤ) (f : WAlg ω α) :
    WAlg.sym ω α (mk ω α (wtr α (WAlg.sym ω α f) r)) = wtr α (WAlg.sym ω α f) r :=
  sym_mk ω α (wtr_wsum' (symW ω α f) r)

lemma sym_mk_lrow (r : ℤ) (f : WAlg ω α) :
    WAlg.sym ω α (mk ω α (lrow α (WAlg.sym ω α f) r)) = lrow α (WAlg.sym ω α f) r :=
  sym_mk ω α (lrow_wsum ω.hs (symW ω α f) r).1

/-- `f ↦ τ_{-rα}(f)₀` as a bounded linear operator on `𝒲_{s,ℓ}`. -/
def wtrCLM (r : ℤ) : WAlg ω α →L[ℂ] WAlg ω α :=
  LinearMap.mkContinuous
    { toFun := fun f => mk ω α (wtr α (WAlg.sym ω α f) r)
      map_add' := fun f g => by
        apply WAlg.sym_injective ω α
        rw [sym_mk_wtr, WAlg.sym_add, WAlg.sym_add, sym_mk_wtr, sym_mk_wtr, wtr_add]
      map_smul' := fun c f => by
        apply WAlg.sym_injective ω α
        rw [RingHom.id_apply, sym_mk_wtr, WAlg.sym_smul, WAlg.sym_smul, sym_mk_wtr, wtr_smul] }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [norm_mk ω α (wtr_wsum' (symW ω α f) r), WAlg.norm_eq_wnorm ω α f]
      exact wnorm_wtr_le (symW ω α f) r

lemma sym_wtrCLM (r : ℤ) (f : WAlg ω α) :
    WAlg.sym ω α (wtrCLM ω α r f) = wtr α (WAlg.sym ω α f) r :=
  sym_mk_wtr ω α r f

/-- `f ↦ l_r(f)` (row `r` moved to row `0` with the gauge phase) as a bounded linear operator. -/
def lrowCLM (r : ℤ) : WAlg ω α →L[ℂ] WAlg ω α :=
  LinearMap.mkContinuous
    { toFun := fun f => mk ω α (lrow α (WAlg.sym ω α f) r)
      map_add' := fun f g => by
        apply WAlg.sym_injective ω α
        rw [sym_mk_lrow, WAlg.sym_add, WAlg.sym_add, sym_mk_lrow, sym_mk_lrow, lrow_add]
      map_smul' := fun c f => by
        apply WAlg.sym_injective ω α
        rw [RingHom.id_apply, sym_mk_lrow, WAlg.sym_smul, WAlg.sym_smul, sym_mk_lrow, lrow_smul] }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [norm_mk ω α (lrow_wsum ω.hs (symW ω α f) r).1, WAlg.norm_eq_wnorm ω α f]
      exact wnorm_lrow_le ω.hs (symW ω α f) r

lemma sym_lrowCLM (r : ℤ) (f : WAlg ω α) :
    WAlg.sym ω α (lrowCLM ω α r f) = lrow α (WAlg.sym ω α f) r :=
  sym_mk_lrow ω α r f

variable {ω α} {a : ℝ}

lemma beta_eq (f : WAlg ω α) (j : ℕ) :
    beta ω α a (WAlg.sym ω α f) j = (-(a : ℂ)⁻¹) • wtrCLM ω α ((j : ℤ) + 2) f := by
  apply WAlg.sym_injective ω α
  rw [WAlg.sym_smul, sym_wtrCLM, beta, sym_mk ω α ((wtr_wsum' (symW ω α f) _).csmul _)]

lemma dsrc_eq (f : WAlg ω α) (j : ℕ) :
    dsrc ω α a (WAlg.sym ω α f) j = ((a : ℂ)⁻¹) • lrowCLM ω α ((j : ℤ) + 2) f := by
  apply WAlg.sym_injective ω α
  rw [WAlg.sym_smul, sym_lrowCLM, dsrc,
    sym_mk ω α ((lrow_wsum ω.hs (symW ω α f) _).1.csmul _)]

/-- **Lemma 2.4, energy dependence.**  For holomorphic families `w_E`, `D_E` on the complex
`1/2`-neighbourhood of `[e₁, e₂]` with uniform transfer and row bounds, each row `L_j(E)` of the
tail-inverse solution has `‖∂_E^n L_j(E)‖ ≤ n! 4ⁿ M_j` on `[e₁, e₂]`. -/
theorem tail_rows_deriv_bound {e₁ e₂ : ℝ} {w D : ℂ → WAlg ω α}
    (hw : DifferentiableOn ℂ w (Energy.nbhd e₁ e₂))
    (hD : DifferentiableOn ℂ D (Energy.nbhd e₁ e₂)) {C γ : ℝ} (hC : 0 ≤ C)
    (hP : ∀ z ∈ Energy.nbhd e₁ e₂, ∀ j m,
      ‖Tail.P (beta ω α a (WAlg.sym ω α (w z))) j m‖ ≤ C * Real.exp (γ * m))
    (hγs : γ < ω.s) {Δ : ℕ → ℝ}
    (hΔ : ∀ z ∈ Energy.nbhd e₁ e₂, ∀ j : ℕ, rowSum ω.ℓ (WAlg.sym ω α (D z)) ((j : ℤ) + 2) ≤ Δ j)
    (hΔs : Summable fun j : ℕ => Real.exp (ω.s * j) * Δ j) (j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc e₁ e₂) (n : ℕ) :
    ‖iteratedDeriv n (Energy.realRes fun z =>
        L ω α a (WAlg.sym ω α (w z)) (WAlg.sym ω α (D z)) j) t‖ ≤
      n.factorial * 4 ^ n * (C * Real.exp (-ω.s * j) *
        ∑' m : ℕ, Real.exp (ω.s * (j + m : ℕ)) * (|a|⁻¹ * Δ (j + m))) := by
  have hβ : ∀ j, DifferentiableOn ℂ (fun z => beta ω α a (WAlg.sym ω α (w z)) j)
      (Energy.nbhd e₁ e₂) := fun j => by
    simp only [beta_eq]
    exact fun z hz =>
      (((wtrCLM ω α ((j : ℤ) + 2)).differentiable.comp_differentiableOn hw) z hz).const_smul
        (-(a : ℂ)⁻¹)
  have hd : ∀ r, DifferentiableOn ℂ (fun z => dsrc ω α a (WAlg.sym ω α (D z)) r)
      (Energy.nbhd e₁ e₂) := fun r => by
    simp only [dsrc_eq]
    exact fun z hz =>
      (((lrowCLM ω α ((r : ℤ) + 2)).differentiable.comp_differentiableOn hD) z hz).const_smul
        ((a : ℂ)⁻¹)
  have hδ : ∀ z ∈ Energy.nbhd e₁ e₂, ∀ r,
      ‖dsrc ω α a (WAlg.sym ω α (D z)) r‖ ≤ |a|⁻¹ * Δ r := fun z hz r => by
    rw [norm_dsrc (symW ω α (D z))]
    exact mul_le_mul_of_nonneg_left (hΔ z hz r) (by positivity)
  have hδs : Summable fun r : ℕ => Real.exp (ω.s * r) * (|a|⁻¹ * Δ r) :=
    (hΔs.mul_left |a|⁻¹).congr fun r => by ring
  exact Tail.green0_deriv_bound (β := fun z => beta ω α a (WAlg.sym ω α (w z)))
    (d := fun z => dsrc ω α a (WAlg.sym ω α (D z))) hβ hd hC hP hγs hδ hδs j ht n

end TailSym

end AMO
