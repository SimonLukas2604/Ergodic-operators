/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.6: the Thouless formula

## Main results
* `E.lyap_eq_integral_log` — the Thouless formula off the real axis:
  `L(z) = ∫ log |z - x| dk(x)` for `Im z ≠ 0`;
* `E.thouless` — **Theorem 4.6.1 (Thouless formula)**: `L(z) = -Φ_{dk}(z)` for every `z ∈ ℂ`,
  where `Φ_{dk}` is the logarithmic potential of the density of states measure.

## Proof
For `Im z ≠ 0`, the entries of the transfer matrix `A_z(N)` are (up to sign) the determinants
`det(z - H_Λ)` of Dirichlet truncations to intervals `Λ` of length `N`, `N - 1`, `N - 2`
(Proposition 2.2.5), and `N⁻¹ log |det(z - H_{ω,N})| = ∫ log |z - x| dk^T_{ω,N}(x)` converges to
`∫ log |z - x| dk(x)` by Theorem 4.3.8.  Since the norm of a `2 × 2` matrix is comparable to its
largest entry, `N⁻¹ log ‖A_z(N)‖ → ∫ log |z - x| dk(x)`, which identifies `L(z)`.  Both sides
of the Thouless formula are subharmonic (Theorem 4.5.3 and Proposition A.2.2), so equality off
the real axis implies equality everywhere (`DF.Subharmonic.eq_of_eq_off_real`).
-/
import DamanikFillman.Ch4.IDSTruncation
import DamanikFillman.Ch4.LyapunovSubharmonic
import DamanikFillman.Ch4.ThoulessPotential
import DamanikFillman.Ch3.Ruelle

noncomputable section

open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter Matrix

namespace DF

/-- If `a_N / N → I`, then `a_{m+j} / (m + 2) → I`. -/
lemma tendsto_shift_div {a : ℕ → ℝ} {I : ℝ} (h : Tendsto (fun N : ℕ => a N / N) atTop (𝓝 I))
    (j : ℕ) : Tendsto (fun m : ℕ => a (m + j) / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 I) := by
  have h1 := h.comp (tendsto_add_atTop_nat j)
  have h2 : Tendsto (fun m : ℕ => ((2 : ℝ) - j) / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((2 : ℝ) - j)).comp (tendsto_add_atTop_nat 2)
  have h3 := h1.sub (h1.mul h2)
  rw [mul_zero, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  simp only [Function.comp_apply]
  have hj : ((m + j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2' : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  push_cast at hj h2' ⊢
  field_simp
  ring

lemma log_max4_le (a b c d : ℝ) :
    Real.log (max (max a b) (max c d)) ≤
      max (max (Real.log a) (Real.log b)) (max (Real.log c) (Real.log d)) := by
  rcases max_choice (max a b) (max c d) with h | h
  · rw [h]
    rcases max_choice a b with h' | h' <;> rw [h']
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  · rw [h]
    rcases max_choice c d with h' | h' <;> rw [h']
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-- `D(ω, N) = |det(z - H_{ω,N})|`. -/
def detN (z : ℂ) (ω : Ω) (N : ℕ) : ℝ :=
  ‖(z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat (E.V ω) 0 N).det‖

lemma detN_pos {z : ℂ} (hz : z.im ≠ 0) (ω : Ω) (N : ℕ) : 0 < E.detN z ω N := by
  unfold detN
  rw [det_sub_eq_prod_eigenvalues (truncMat_isHermitian _ 0 N), norm_prod]
  refine Finset.prod_pos fun i _ => norm_pos_iff.2 (sub_ne_zero.2 fun h => hz ?_)
  rw [h, Complex.ofReal_im]

lemma truncMat_one_eq (ω : Ω) (N : ℕ) :
    truncMat (E.V ω) 1 N = truncMat (E.V (E.T ω)) 0 N := by
  ext i j
  rw [truncMat_apply, truncMat_apply, E.V_T,
    show (1 : ℤ) + 1 + ((i : ℕ) : ℤ) = 0 + 1 + ((i : ℕ) : ℤ) + 1 by ring]

lemma norm_transferProd_entries (z : ℂ) (ω : Ω) (m : ℕ) :
    ‖transferProd (E.V ω) z (m + 2) 0 0‖ = E.detN z ω (m + 2) ∧
    ‖transferProd (E.V ω) z (m + 2) 0 1‖ = E.detN z (E.T ω) (m + 1) ∧
    ‖transferProd (E.V ω) z (m + 2) 1 0‖ = E.detN z ω (m + 1) ∧
    ‖transferProd (E.V ω) z (m + 2) 1 1‖ = E.detN z (E.T ω) m := by
  have h := transferZ_eq_det (E.V ω) z m
  rw [show (m : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring, transferZ_natCast] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h, detN, E.truncMat_one_eq]

/-- The Thouless formula off the real axis: `L(z) = ∫ log |z - x| dk(x)` for `Im z ≠ 0`. -/
theorem lyap_eq_integral_log {z : ℂ} (hz : z.im ≠ 0) :
    E.lyap z = ∫ x, Real.log ‖z - x‖ ∂E.dosm := by
  set I := ∫ x, Real.log ‖z - x‖ ∂E.dosm with hI
  have hne : ∀ x : ℝ, ‖z - x‖ ≠ 0 := fun x =>
    norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => hz (by rw [h, Complex.ofReal_im]))
  have hg : Continuous fun x : ℝ => Real.log ‖z - x‖ :=
    Continuous.log (continuous_const.sub Complex.continuous_ofReal).norm hne
  have hconv : ∀ᵐ ω ∂E.μ, Tendsto (fun N : ℕ => Real.log (E.detN z ω N) / N) atTop (𝓝 I) := by
    filter_upwards [E.ae_tendsto_dkT] with ω hω
    refine (hω _ hg).congr fun N => ?_
    rw [E.integral_log_dkT ω N hz, detN, div_eq_inv_mul]
  have hconvT : ∀ᵐ ω ∂E.μ,
      Tendsto (fun N : ℕ => Real.log (E.detN z (E.T ω) N) / N) atTop (𝓝 I) :=
    E.measurePreserving_T.quasiMeasurePreserving.ae hconv
  have hL := E.ae_tendsto_log_norm_transferProd z
  have : (ae E.μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, h1, h2, h3⟩ := (hconv.and (hconvT.and hL)).exists
  have hA : Tendsto (fun m : ℕ => Real.log ‖transferProd (E.V ω) z (m + 2)‖ /
      ((m + 2 : ℕ) : ℝ)) atTop (𝓝 (E.lyap z)) := h3.comp (tendsto_add_atTop_nat 2)
  have s1 := tendsto_shift_div h1 2
  have s2 := tendsto_shift_div h2 1
  have s3 := tendsto_shift_div h1 1
  have s4 := tendsto_shift_div h2 0
  have hup : Tendsto (fun m : ℕ => Real.log 2 / ((m + 2 : ℕ) : ℝ) +
      max (max (Real.log (E.detN z ω (m + 2)) / ((m + 2 : ℕ) : ℝ))
        (Real.log (E.detN z (E.T ω) (m + 1)) / ((m + 2 : ℕ) : ℝ)))
        (max (Real.log (E.detN z ω (m + 1)) / ((m + 2 : ℕ) : ℝ))
          (Real.log (E.detN z (E.T ω) (m + 0)) / ((m + 2 : ℕ) : ℝ)))) atTop (𝓝 I) := by
    have h0 : Tendsto (fun m : ℕ => Real.log 2 / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).comp (tendsto_add_atTop_nat 2)
    have := h0.add ((s1.max s2).max (s3.max s4))
    simpa using this
  have hsq : Tendsto (fun m : ℕ => Real.log ‖transferProd (E.V ω) z (m + 2)‖ /
      ((m + 2 : ℕ) : ℝ)) atTop (𝓝 I) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le s1 hup (fun m => ?_) (fun m => ?_)
    · obtain ⟨e1, -, -, -⟩ := E.norm_transferProd_entries z ω m
      have hpos := E.detN_pos hz ω (m + 2)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      refine Real.log_le_log hpos ?_
      rw [← e1]
      exact Cocycle.norm_entry_le _ 0 0
    · obtain ⟨e1, e2, e3, e4⟩ := E.norm_transferProd_entries z ω m
      have p1 := E.detN_pos hz ω (m + 2)
      have p2 := E.detN_pos hz (E.T ω) (m + 1)
      have p3 := E.detN_pos hz ω (m + 1)
      have p4 := E.detN_pos hz (E.T ω) m
      set c := max (max (E.detN z ω (m + 2)) (E.detN z (E.T ω) (m + 1)))
        (max (E.detN z ω (m + 1)) (E.detN z (E.T ω) m)) with hc
      have hcpos : 0 < c := lt_of_lt_of_le p1 ((le_max_left _ _).trans (le_max_left _ _))
      have hnorm : ‖transferProd (E.V ω) z (m + 2)‖ ≤ 2 * c := by
        refine Cocycle.norm_le_of_entries _ hcpos.le fun i j => ?_
        fin_cases i <;> fin_cases j
        · simp only [Fin.zero_eta]; rw [e1]
          exact (le_max_left _ _).trans (le_max_left _ _)
        · simp only [Fin.zero_eta, Fin.mk_one]; rw [e2]
          exact (le_max_right _ _).trans (le_max_left _ _)
        · simp only [Fin.zero_eta, Fin.mk_one]; rw [e3]
          exact (le_max_left _ _).trans (le_max_right _ _)
        · simp only [Fin.mk_one]; rw [e4]
          exact (le_max_right _ _).trans (le_max_right _ _)
      have hApos : 0 < ‖transferProd (E.V ω) z (m + 2)‖ := by
        rw [← e1] at p1
        exact lt_of_lt_of_le p1 (Cocycle.norm_entry_le _ 0 0)
      have hlog : Real.log ‖transferProd (E.V ω) z (m + 2)‖ ≤ Real.log 2 +
          max (max (Real.log (E.detN z ω (m + 2))) (Real.log (E.detN z (E.T ω) (m + 1))))
            (max (Real.log (E.detN z ω (m + 1))) (Real.log (E.detN z (E.T ω) m))) := by
        calc Real.log ‖transferProd (E.V ω) z (m + 2)‖ ≤ Real.log (2 * c) :=
              Real.log_le_log hApos hnorm
          _ = Real.log 2 + Real.log c := Real.log_mul two_ne_zero hcpos.ne'
          _ ≤ _ := by gcongr; exact log_max4_le _ _ _ _
      have hpos2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      rw [max_div_div_right hpos2.le, max_div_div_right hpos2.le, max_div_div_right hpos2.le,
        ← add_div, add_zero]
      exact div_le_div_of_nonneg_right hlog hpos2.le
  exact tendsto_nhds_unique hA hsq

/-- **Theorem 4.6.1 (Thouless formula)**: `L(z) = -Φ_{dk}(z) = ∫ log |z - x| dk(x)` for every
`z ∈ ℂ`, with `Φ_{dk}` the logarithmic potential of the density of states measure. -/
theorem thouless (z : ℂ) : ((E.lyap z : ℝ) : EReal) = -logPotential (toC E.dosm) z := by
  set R := 2 + E.fBound
  have hK : E.dosm (Icc (-R) R)ᶜ = 0 := ae_iff.1 E.ae_mem_Icc_dosm
  have hint := integrable_norm_toC isCompact_Icc hK
  have hS : Subharmonic (fun z => -logPotential (toC E.dosm) z) :=
    subharmonic_neg_logPotential hint
  refine congrFun (Subharmonic.eq_of_eq_off_real E.subharmonic_lyap hS fun w hw => ?_) z
  show ((E.lyap w : ℝ) : EReal) = -logPotential (toC E.dosm) w
  have hδ : 0 < |w.im| := abs_pos.2 hw
  have hzK : ∀ u ∈ (fun x : ℝ => (x : ℂ)) '' Icc (-R) R, |w.im| ≤ ‖w - u‖ := by
    rintro u ⟨x, -, rfl⟩
    calc |w.im| = |(w - (x : ℂ)).im| := by simp
      _ ≤ ‖w - (x : ℂ)‖ := Complex.abs_im_le_norm _
  rw [E.lyap_eq_integral_log hw, logPotential_eq_integral_of_dist hint
    (toC_compl_image isCompact_Icc hK) hδ hzK, integral_neg, EReal.coe_neg, neg_neg, toC,
    integral_map measurable_ofReal'.aemeasurable
      ((by fun_prop : Measurable fun u : ℂ => ‖w - u‖).log).aestronglyMeasurable]

end ErgodicFamily

end DF
