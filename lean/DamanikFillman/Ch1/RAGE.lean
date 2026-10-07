/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Quantum dynamics and the RAGE theorem  (book §1.6.2, Theorem 1.6.7, Lemma 1.6.9, pp. 50–53)

* `DF.evol A hA t = e^{-itA}` (1.6.17), defined through the Borel functional calculus; it is
  unitary (`DF.norm_evol`, `DF.adjoint_evol_mul_evol`) and leaves the spectral subspaces
  invariant.
* `DF.tendsto_timeAvg_inner_evol` — the key consequence of Wiener's theorem (the estimate
  (1.6.27) in the proof of Lemma 1.6.9): for `φ ∈ H_c` and any `ψ`,
  `(1/2T) ∫_{-T}^{T} |⟪ψ, e^{-itA} φ⟫|² dt → 0`.
* `DF.tendsto_inner_evol_of_mem_acSubspace` — the Riemann–Lebesgue analogue for `φ ∈ H_ac`.
* **RAGE theorem** (Theorem 1.6.7) on `ℓ²(ℤ)`:
  - (a) `DF.rage_pp`: `φ ∈ H_pp` iff `sup_t ∑_{|n|>N} |φ(t)(n)|² → 0` as `N → ∞`;
  - (b) `DF.rage_c`: `φ ∈ H_c` iff the time averages of `∑_{|n|≤N} |φ(t)(n)|²` tend to `0`;
  - (c) `DF.rage_ac`: if `φ ∈ H_ac` then `∑_{|n|≤N} |φ(t)(n)|² → 0` as `|t| → ∞`.

Deviations
* Lemma 1.6.9 itself (the double-limit formula for `⟪ψ, P_pp φ⟫`) is not stated; the proofs of
  (a) and (b) given here avoid it (the converse of (b) uses an eigenvector component directly).
* Proposition 1.6.10 is not formalized.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.SpectralDecomposition
import DamanikFillman.Ch1.Wiener

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology FourierTransform
open MeasureTheory Set Filter Complex

namespace DF

/-! ### Time averages -/

section TimeAvg

lemma timeAvg_le {T : ℝ} (hT : 0 < T) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, f t ≤ g t) : timeAvg f T ≤ timeAvg g T := by
  unfold timeAvg
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) fun t _ => h t

lemma timeAvg_const {T : ℝ} (hT : 0 < T) (c : ℝ) : timeAvg (fun _ => c) T = c := by
  unfold timeAvg
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma timeAvg_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i, Continuous (f i))
    (T : ℝ) : timeAvg (fun t => ∑ i ∈ s, f i t) T = ∑ i ∈ s, timeAvg (f i) T := by
  unfold timeAvg
  rw [intervalIntegral.integral_finset_sum fun i _ => (hf i).intervalIntegrable _ _,
    Finset.mul_sum]

lemma timeAvg_const_mul (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    timeAvg (fun t => c * f t) T = c * timeAvg f T := by
  unfold timeAvg
  rw [intervalIntegral.integral_const_mul]; ring

/-- Squeeze for time averages. -/
lemma tendsto_timeAvg_of_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ t, 0 ≤ f t) (h : ∀ t, f t ≤ g t)
    (hlim : Tendsto (timeAvg g) atTop (𝓝 0)) : Tendsto (timeAvg f) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have := timeAvg_le hT continuous_const hf h0
    rwa [timeAvg_const hT] at this
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact timeAvg_le hT hf hg h

end TimeAvg

/-! ### Riemann–Lebesgue for absolutely continuous measures -/

/-- **Riemann–Lebesgue lemma** (Exercise 1.6.1): the Fourier transform of a finite absolutely
continuous measure vanishes at infinity. -/
theorem tendsto_measFourier_of_ac (μ : Measure ℝ) [IsFiniteMeasure μ] (h : μ ≪ volume) :
    Tendsto (measFourier μ) (cocompact ℝ) (𝓝 0) := by
  set g : ℝ → ℂ := fun x => ((μ.rnDeriv volume x).toReal : ℂ)
  have hRL := Real.tendsto_integral_exp_smul_cocompact g
  have hscale := Filter.tendsto_cocompact_mul_right₀ (K := ℝ) (a := (2 * Real.pi)⁻¹)
    (by positivity)
  refine (hRL.comp hscale).congr fun t => ?_
  simp only [Function.comp_apply]
  have e := Measure.withDensity_rnDeriv_eq μ volume h
  calc ∫ v, 𝐞 (-(v * (t * (2 * Real.pi)⁻¹))) • g v
      = ∫ x, (μ.rnDeriv volume x).toReal • exp (-((x * t : ℝ) : ℂ) * I) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [g, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, real_smul]
        rw [mul_comm]
        congr 2
        push_cast
        field_simp
    _ = measFourier (volume.withDensity (μ.rnDeriv volume)) t := by
        rw [measFourier, integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
          (Measure.rnDeriv_lt_top _ _)]
    _ = measFourier μ t := by rw [e]

/-! ### The unitary group -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

/-- The phase `x ↦ e^{-ixt}`. -/
def expPhase (t x : ℝ) : ℂ := exp (-((x * t : ℝ) : ℂ) * I)

lemma continuous_expPhase (t : ℝ) : Continuous (expPhase t) := by unfold expPhase; fun_prop

lemma norm_expPhase (t x : ℝ) : ‖expPhase t x‖ = 1 := norm_exp_neg_mul_I _

lemma isBddBorel_expPhase (t : ℝ) : IsBddBorel (expPhase t) :=
  ⟨(continuous_expPhase t).measurable, 1, fun x => (norm_expPhase t x).le⟩

lemma conj_expPhase (t x : ℝ) : conj (expPhase t x) = expPhase (-t) x := by
  simp only [expPhase, ← exp_conj, map_mul, map_neg, conj_ofReal, conj_I]
  congr 1; push_cast; ring

variable (A hA) in
/-- The Schrödinger evolution `e^{-itA}` (1.6.17). -/
def evol (t : ℝ) : H →L[ℂ] H := borelCalc A hA (expPhase t)

/-- `⟪v, e^{-itA} v⟫ = μ̂_v(t)`. -/
lemma inner_evol_self (t : ℝ) (v : H) :
    ⟪v, evol A hA t v⟫_ℂ = measFourier (spectralMeasure A hA v) t :=
  inner_borelCalc_self (isBddBorel_expPhase t) v

lemma continuous_measFourier (μ : Measure ℝ) [IsFiniteMeasure μ] : Continuous (measFourier μ) :=
  continuous_of_dominated (bound := fun _ => 1)
    (fun t => (by fun_prop : Continuous fun x : ℝ => exp (-((x * t : ℝ) : ℂ) * I)).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun x => (norm_exp_neg_mul_I _).le) (integrable_const _)
    (Eventually.of_forall fun x => by fun_prop)

/-- Polarization: matrix elements of `e^{-itA}` are combinations of Fourier transforms of
spectral measures. -/
lemma inner_evol_eq_sum (t : ℝ) (ψ φ : H) :
    ⟪ψ, evol A hA t φ⟫_ℂ = ∑ k, polC k * measFourier (spectralMeasure A hA (polV ψ φ k)) t := by
  rw [evol, inner_borelCalc (isBddBorel_expPhase t), sform_eq_sum]
  rfl

lemma continuous_inner_evol (ψ φ : H) : Continuous fun t => ⟪ψ, evol A hA t φ⟫_ℂ := by
  simp_rw [inner_evol_eq_sum]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_measFourier _)

/-- `e^{-itA}` preserves spectral measures. -/
lemma spectralMeasure_evol (t : ℝ) (φ : H) :
    spectralMeasure A hA (evol A hA t φ) = spectralMeasure A hA φ := by
  rw [evol, spectralMeasure_borelCalc (isBddBorel_expPhase t)]
  have : (fun x => ((‖expPhase t x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) = fun _ => 1 := by
    funext x
    have : ‖expPhase t x‖₊ = 1 := NNReal.eq (by simpa using norm_expPhase t x)
    simp [this]
  rw [this]
  exact withDensity_one

/-- `e^{-itA}` is an isometry. -/
lemma norm_evol (t : ℝ) (φ : H) : ‖evol A hA t φ‖ = ‖φ‖ := by
  have h1 := spectralMeasure_real_univ A hA (evol A hA t φ)
  rw [spectralMeasure_evol, spectralMeasure_real_univ A hA φ] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1.symm

lemma adjoint_evol (t : ℝ) : ContinuousLinearMap.adjoint (evol A hA t) = evol A hA (-t) := by
  rw [evol, evol, ← borelCalc_conj (isBddBorel_expPhase t)]
  simp_rw [conj_expPhase]

lemma adjoint_evol_mul_evol (t : ℝ) :
    ContinuousLinearMap.adjoint (evol A hA t) * evol A hA t = 1 := by
  rw [evol, ← borelCalc_conj (isBddBorel_expPhase t), ← borelCalc_mul
    (isBddBorel_expPhase t).conj (isBddBorel_expPhase t), ← borelCalc_one (A := A) (hA := hA)]
  congr 1; funext x
  simp only [Pi.mul_apply]
  rw [Complex.conj_mul', norm_expPhase]; simp

lemma inner_evol_evol (t : ℝ) (φ ψ : H) : ⟪evol A hA t φ, evol A hA t ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
    adjoint_evol_mul_evol, ContinuousLinearMap.one_apply]

lemma evol_mem_cSubspace {φ : H} (hφ : φ ∈ cSubspace A hA) (t : ℝ) :
    evol A hA t φ ∈ cSubspace A hA := by
  intro E; rw [spectralMeasure_evol]; exact hφ E

lemma evol_mem_acSubspace {φ : H} (hφ : φ ∈ acSubspace A hA) (t : ℝ) :
    evol A hA t φ ∈ acSubspace A hA := by
  intro N hN hN0; rw [spectralMeasure_evol]; exact hφ N hN hN0

/-- `f(A) ψ = f(E) ψ` for an eigenvector `Aψ = Eψ`. -/
lemma borelCalc_apply_eigenvector {f : ℝ → ℂ} (hf : IsBddBorel f) {ψ : H} {E : ℝ}
    (h : A ψ = (E : ℂ) • ψ) : borelCalc A hA f ψ = f E • ψ := by
  set c : ℝ → ℂ := fun x => (-f E) * (fun _ : ℝ => (1 : ℂ)) x with hc
  have hcB : IsBddBorel c := (isBddBorel_const 1).const_mul _
  have hg : IsBddBorel (f + c) := hf.add hcB
  have h1 := norm_borelCalc_apply_sq (A := A) (hA := hA) hg ψ
  have h0 : ∫ x, ‖(f + c) x‖ ^ 2 ∂(spectralMeasure A hA ψ) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have := spectralMeasure_eigenvector (hA := hA) h
    rw [← mem_ae_iff] at this
    filter_upwards [this] with x hx
    rw [mem_singleton_iff] at hx
    simp [hx, c]
  rw [h0, sq_eq_zero_iff, norm_eq_zero, borelCalc_add hf hcB, hc,
    borelCalc_const_mul (isBddBorel_const 1), borelCalc_one] at h1
  have := sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1)
  exact this

lemma evol_eigenvector {ψ : H} {E : ℝ} (h : A ψ = (E : ℂ) • ψ) (t : ℝ) :
    evol A hA t ψ = expPhase t E • ψ :=
  borelCalc_apply_eigenvector (isBddBorel_expPhase t) h

/-! ### Consequence of Wiener's theorem -/

lemma polV_mem {S : Submodule ℂ H} {u w : H} (hu : u ∈ S) (hw : w ∈ S) (k : Fin 4) :
    polV u w k ∈ S := by
  fin_cases k <;> simp only [polV, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk]
  · exact S.add_mem hu hw
  · exact S.sub_mem hu hw
  · exact S.add_mem hu (S.smul_mem _ hw)
  · exact S.sub_mem hu (S.smul_mem _ hw)

lemma norm_sum_polC_sq_le (z : Fin 4 → ℂ) :
    ‖∑ k, polC k * z k‖ ^ 2 ≤ (1 / 4) * ∑ k, ‖z k‖ ^ 2 := by
  have hn : ∀ k, ‖polC k‖ = 1 / 4 := by
    intro k; fin_cases k <;> simp [polC, norm_div]
  have h1 : ‖∑ k, polC k * z k‖ ≤ (1 / 4) * ∑ k, ‖z k‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by rw [norm_mul, hn]
  have h2 : 0 ≤ ‖∑ k, polC k * z k‖ := norm_nonneg _
  refine (pow_le_pow_left₀ h2 h1 2).trans ?_
  simp only [Fin.sum_univ_four]
  have := norm_nonneg (z 0); have := norm_nonneg (z 1); have := norm_nonneg (z 2)
  have := norm_nonneg (z 3)
  nlinarith [sq_nonneg (‖z 0‖ - ‖z 1‖), sq_nonneg (‖z 0‖ - ‖z 2‖), sq_nonneg (‖z 0‖ - ‖z 3‖),
    sq_nonneg (‖z 1‖ - ‖z 2‖), sq_nonneg (‖z 1‖ - ‖z 3‖), sq_nonneg (‖z 2‖ - ‖z 3‖)]

/-- The decomposition `ψ = ψ_c + ψ_pp`. -/
lemma exists_c_pp_decomposition (ψ : H) :
    ∃ c ∈ cSubspace A hA, ∃ p ∈ ppSubspace A hA, ψ = c + p := by
  obtain ⟨a, ha, s, hs, p, hp, rfl⟩ := exists_decomposition (A := A) (hA := hA) ψ
  exact ⟨a + s, add_mem (acSubspace_le_cSubspace ha) (scSubspace_le_cSubspace hs), p, hp, rfl⟩

/-- **Key estimate** (cf. (1.6.27)): for `φ ∈ H_c` and every `ψ`, the time averages of
`|⟪ψ, e^{-itA} φ⟫|²` tend to zero. -/
theorem tendsto_timeAvg_inner_evol {φ : H} (hφ : φ ∈ cSubspace A hA) (ψ : H) :
    Tendsto (timeAvg fun t => ‖⟪ψ, evol A hA t φ⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨c, hc, p, hp, rfl⟩ := exists_c_pp_decomposition (A := A) (hA := hA) ψ
  have hred : ∀ t, ⟪c + p, evol A hA t φ⟫_ℂ = ⟪c, evol A hA t φ⟫_ℂ := by
    intro t
    rw [inner_add_left, inner_eq_zero_symm.1 (cSubspace_orthogonal_ppSubspace
      (evol_mem_cSubspace hφ t) hp), add_zero]
  simp_rw [hred]
  have hv := fun k => polV_mem (S := cSubspace A hA) hc hφ k
  have hlim : ∀ k, Tendsto (timeAvg fun t =>
      ‖measFourier (spectralMeasure A hA (polV c φ k)) t‖ ^ 2) atTop (𝓝 0) :=
    fun k => (wiener_continuous_iff _).1 (hv k)
  have hcont : ∀ k, Continuous fun t => ‖measFourier (spectralMeasure A hA (polV c φ k)) t‖ ^ 2 :=
    fun k => (continuous_measFourier _).norm.pow 2
  refine tendsto_timeAvg_of_le (g := fun t => (1 / 4 : ℝ) *
      ∑ k, ‖measFourier (spectralMeasure A hA (polV c φ k)) t‖ ^ 2)
    ((continuous_inner_evol c φ).norm.pow 2)
    (continuous_const.mul (continuous_finsetSum _ fun k _ => hcont k))
    (fun t => sq_nonneg _) (fun t => ?_) ?_
  · rw [inner_evol_eq_sum]; exact norm_sum_polC_sq_le _
  · have : Tendsto (fun T => (1 / 4 : ℝ) * ∑ k, timeAvg (fun t =>
        ‖measFourier (spectralMeasure A hA (polV c φ k)) t‖ ^ 2) T) atTop (𝓝 0) := by
      have := (tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun k _ => hlim k).const_mul
        (1 / 4 : ℝ)
      simpa using this
    refine this.congr fun T => ?_
    rw [timeAvg_const_mul _ (continuous_finsetSum _ fun k _ => hcont k),
      timeAvg_sum _ hcont]

/-- Riemann–Lebesgue for the dynamics: for `φ ∈ H_ac` and every `ψ`,
`⟪ψ, e^{-itA} φ⟫ → 0` as `|t| → ∞`. -/
theorem tendsto_inner_evol_of_mem_acSubspace {φ : H} (hφ : φ ∈ acSubspace A hA) (ψ : H) :
    Tendsto (fun t => ⟪ψ, evol A hA t φ⟫_ℂ) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨a, ha, s, hs, p, hp, rfl⟩ := exists_decomposition (A := A) (hA := hA) ψ
  have hred : ∀ t, ⟪a + s + p, evol A hA t φ⟫_ℂ = ⟪a, evol A hA t φ⟫_ℂ := by
    intro t
    have hsing : s + p ∈ sSubspace A hA := add_mem (scSubspace_le_sSubspace hs)
      (ppSubspace_le_sSubspace hp)
    rw [add_assoc, inner_add_left, inner_eq_zero_symm.1 (acSubspace_orthogonal_sSubspace
      (evol_mem_acSubspace hφ t) hsing), add_zero]
  simp_rw [hred, inner_evol_eq_sum]
  rw [show (0 : ℂ) = ∑ k : Fin 4, polC k * 0 by simp]
  refine tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul ?_
  have hk := polV_mem (S := acSubspace A hA) ha hφ k
  exact tendsto_measFourier_of_ac _ ((mem_acSubspace_iff _).1 hk)

end Hilbert

/-! ### Local projections on `ℓ²(ℤ)` -/

section L2Z

open L2

/-- Indicator of `{|n| ≤ N}`. -/
def cutIn (N : ℕ) (n : ℤ) : ℂ := if |n| ≤ (N : ℤ) then 1 else 0

lemma bdd_cutIn (N : ℕ) : Bdd (cutIn N) := ⟨1, fun n => by unfold cutIn; split_ifs <;> simp⟩

/-- `P_N`: projection onto the sites `|n| ≤ N`. -/
def Pin (N : ℕ) : L2 ℤ →L[ℂ] L2 ℤ := weightedShift (cutIn N) (Equiv.refl ℤ)

/-- `I - P_N`. -/
def Pout (N : ℕ) : L2 ℤ →L[ℂ] L2 ℤ := 1 - Pin N

lemma Pin_apply (N : ℕ) (v : L2 ℤ) (n : ℤ) : Pin N v n = cutIn N n * v n := by
  rw [Pin, weightedShift_apply (bdd_cutIn N)]; rfl

lemma Pout_apply (N : ℕ) (v : L2 ℤ) (n : ℤ) : Pout N v n = (1 - cutIn N n) * v n := by
  rw [Pout, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, lp.coeFn_sub,
    Pi.sub_apply, Pin_apply]; ring

lemma Pin_add_Pout (N : ℕ) (v : L2 ℤ) : Pin N v + Pout N v = v := by
  simp [Pout]

lemma mem_Icc_iff_abs_le (N : ℕ) (n : ℤ) : n ∈ Finset.Icc (-(N : ℤ)) N ↔ |n| ≤ N := by
  rw [Finset.mem_Icc, abs_le]

lemma norm_Pin_sq (N : ℕ) (v : L2 ℤ) :
    ‖Pin N v‖ ^ 2 = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖v n‖ ^ 2 := by
  rw [norm_sq_eq_tsum, tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Pin_apply, cutIn, if_pos ((mem_Icc_iff_abs_le N n).1 hn), one_mul]
  · intro n hn
    rw [Pin_apply, cutIn, if_neg (fun h => hn ((mem_Icc_iff_abs_le N n).2 h))]
    simp

lemma norm_Pout_sq (N : ℕ) (v : L2 ℤ) :
    ‖Pout N v‖ ^ 2 = ∑' n, if (N : ℤ) < |n| then ‖v n‖ ^ 2 else 0 := by
  rw [norm_sq_eq_tsum]
  congr 1; funext n
  rw [Pout_apply, cutIn]
  split_ifs with h1 h2 h2
  · exact absurd h1 (not_le.2 h2)
  · simp
  · simp
  · exact absurd (le_of_not_gt h2) h1

lemma norm_Pout_le (N : ℕ) (v : L2 ℤ) : ‖Pout N v‖ ≤ ‖v‖ := by
  have h : ‖Pout N v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_Pout_sq, norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ (summable_norm_sq v)
    · split_ifs <;> simp
    · exact (summable_norm_sq v).of_nonneg_of_le (fun n => by split_ifs <;> simp)
        (fun n => by split_ifs <;> simp)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma tendsto_Pout (v : L2 ℤ) : Tendsto (fun N => ‖Pout N v‖) atTop (𝓝 0) := by
  have h2 : Tendsto (fun N => ‖Pout N v‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [norm_Pout_sq]
    have h := tendsto_tsum_of_dominated_convergence (bound := fun n => ‖v n‖ ^ 2)
      (f := fun (N : ℕ) (n : ℤ) => if (N : ℤ) < |n| then ‖v n‖ ^ 2 else 0) (g := fun _ => 0)
      (summable_norm_sq v) (fun n => ?_) (Eventually.of_forall (f := (atTop : Filter ℕ)) fun N n => ?_)
    · simpa using h
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n.natAbs] with N hN
      rw [if_neg]
      rw [not_lt, Int.abs_eq_natAbs]; exact_mod_cast hN
    · split_ifs <;> simp
  have := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_zero] at this
  refine this.congr fun N => ?_
  exact Real.sqrt_sq (norm_nonneg _)

lemma inner_Pin (N : ℕ) (u w : L2 ℤ) : ⟪Pin N u, w⟫_ℂ = ⟪u, Pin N w⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; funext n
  rw [Pin_apply, Pin_apply]
  unfold cutIn; split_ifs <;> simp

lemma apply_eq_inner_single (v : L2 ℤ) (n : ℤ) : v n = ⟪lp.single 2 n (1 : ℂ), v⟫_ℂ := by
  rw [lp.inner_single_left]; simp

variable {A : L2 ℤ →L[ℂ] L2 ℤ} {hA : IsSelfAdjoint A}

lemma continuous_evol_apply (φ : L2 ℤ) (n : ℤ) : Continuous fun t => evol A hA t φ n := by
  simp_rw [apply_eq_inner_single _ n]
  exact continuous_inner_evol _ _

lemma continuous_norm_Pin_evol_sq (N : ℕ) (φ : L2 ℤ) :
    Continuous fun t => ‖Pin N (evol A hA t φ)‖ ^ 2 := by
  simp_rw [norm_Pin_sq]
  exact continuous_finsetSum _ fun n _ => (continuous_evol_apply φ n).norm.pow 2

/-- **RAGE theorem (b), "only if"**: for `φ ∈ H_c` the time averages of
`∑_{|n|≤N} |φ(t)(n)|²` tend to zero. -/
theorem rage_c_of_mem {φ : L2 ℤ} (hφ : φ ∈ cSubspace A hA) (N : ℕ) :
    Tendsto (timeAvg fun t => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖evol A hA t φ n‖ ^ 2) atTop
      (𝓝 0) := by
  have hc : ∀ n, Continuous fun t => ‖evol A hA t φ n‖ ^ 2 :=
    fun n => (continuous_evol_apply φ n).norm.pow 2
  have := tendsto_finsetSum (Finset.Icc (-(N : ℤ)) N) fun n _ =>
    tendsto_timeAvg_inner_evol (A := A) (hA := hA) hφ (lp.single 2 n (1 : ℂ))
  simp only [Finset.sum_const_zero] at this
  refine this.congr fun T => ?_
  rw [timeAvg_sum _ hc]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp_rw [← apply_eq_inner_single]

lemma timeAvg_ge_of_forall {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (h : ∀ t, c ≤ f t)
    (hlim : Tendsto (timeAvg f) atTop (𝓝 0)) : c ≤ 0 := by
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have := timeAvg_le hT continuous_const hf h
  rwa [timeAvg_const hT] at this

/-- **RAGE theorem (b)** (Theorem 1.6.7(b)): `μ_φ` is continuous iff for every `N` the time
averages of `∑_{|n|≤N} |⟨δ_n, φ(t)⟩|²` tend to zero. -/
theorem rage_c (φ : L2 ℤ) :
    φ ∈ cSubspace A hA ↔ ∀ N : ℕ,
      Tendsto (timeAvg fun t => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖evol A hA t φ n‖ ^ 2) atTop
        (𝓝 0) := by
  refine ⟨fun hφ N => rage_c_of_mem hφ N, fun h => ?_⟩
  intro E
  by_contra hE
  set η := specProj A hA {E} φ
  set m := ‖η‖ ^ 2
  have hm : m = (spectralMeasure A hA φ).real {E} := norm_specProj_apply_sq
    (measurableSet_singleton E) φ
  have hmpos : 0 < m := by
    rw [hm]; exact ENNReal.toReal_pos hE (measure_ne_top _ _)
  have hη0 : 0 < ‖η‖ := by
    by_contra h0; push Not at h0
    have : ‖η‖ = 0 := le_antisymm h0 (norm_nonneg _)
    simp [m, this] at hmpos
  have heig : A η = (E : ℂ) • η := apply_specProj_singleton E φ
  -- `|⟪η, φ(t)⟫| = m`
  have hinner : ∀ t, ‖⟪η, evol A hA t φ⟫_ℂ‖ = m := by
    intro t
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_evol, evol_eigenvector heig,
      inner_smul_left, norm_mul, RCLike.norm_conj, norm_expPhase, one_mul]
    have h1 : ⟪η, φ⟫_ℂ = ⟪φ, specProj A hA {E} φ⟫_ℂ := by
      have := (isSelfAdjoint_specProj (A := A) (hA := hA) (measurableSet_singleton E)).isSymmetric
        φ φ
      exact this
    rw [h1, inner_specProj_self (measurableSet_singleton E), ← hm, Complex.norm_real,
      Real.norm_of_nonneg hmpos.le]
  -- choose `N` with a small tail of `η`
  have hev : ∀ᶠ N in atTop, ‖Pout N η‖ * (‖φ‖ + 1) < m / 2 := by
    have := (tendsto_Pout η).mul_const (‖φ‖ + 1)
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := hev.exists
  have hlow : ∀ t, (m / (2 * ‖η‖)) ^ 2 ≤ ‖Pin N (evol A hA t φ)‖ ^ 2 := by
    intro t
    have hsplit : ⟪η, evol A hA t φ⟫_ℂ =
        ⟪η, Pin N (evol A hA t φ)⟫_ℂ + ⟪Pout N η, evol A hA t φ⟫_ℂ := by
      conv_lhs => rw [← Pin_add_Pout N η]
      rw [inner_add_left, inner_Pin]
    have h1 : ‖⟪η, Pin N (evol A hA t φ)⟫_ℂ‖ ≤ ‖η‖ * ‖Pin N (evol A hA t φ)‖ :=
      norm_inner_le_norm _ _
    have h2 : ‖⟪Pout N η, evol A hA t φ⟫_ℂ‖ ≤ ‖Pout N η‖ * ‖φ‖ := by
      refine (norm_inner_le_norm _ _).trans ?_; rw [norm_evol]
    have h3 : ‖Pout N η‖ * ‖φ‖ ≤ ‖Pout N η‖ * (‖φ‖ + 1) := by
      have := norm_nonneg (Pout N η); nlinarith
    have h4 : ‖⟪η, evol A hA t φ⟫_ℂ‖ ≤ ‖η‖ * ‖Pin N (evol A hA t φ)‖ + m / 2 := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      linarith
    rw [hinner t] at h4
    have h5 : m / (2 * ‖η‖) ≤ ‖Pin N (evol A hA t φ)‖ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact pow_le_pow_left₀ (by positivity) h5 2
  have hc := timeAvg_ge_of_forall (continuous_norm_Pin_evol_sq N φ) hlow (by
    refine (h N).congr fun T => ?_
    simp_rw [norm_Pin_sq])
  have : 0 < (m / (2 * ‖η‖)) ^ 2 := by positivity
  linarith

/-- The tightness property of the orbit `{e^{-itA} φ}` (cf. (1.6.18)). -/
def IsTightOrbit (A : L2 ℤ →L[ℂ] L2 ℤ) (hA : IsSelfAdjoint A) (φ : L2 ℤ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t, ‖Pout N (evol A hA t φ)‖ ≤ ε

variable (A hA) in
/-- Tight orbits form a closed subspace. -/
def tightSubmodule : Submodule ℂ (L2 ℤ) where
  carrier := {φ | IsTightOrbit A hA φ}
  add_mem' := by
    intro φ ψ hφ hψ ε hε
    obtain ⟨N₁, h₁⟩ := hφ (ε / 2) (by positivity)
    obtain ⟨N₂, h₂⟩ := hψ (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun N hN t => ?_⟩
    rw [map_add, map_add]
    calc ‖Pout N (evol A hA t φ) + Pout N (evol A hA t ψ)‖
        ≤ ‖Pout N (evol A hA t φ)‖ + ‖Pout N (evol A hA t ψ)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (h₁ N (le_of_max_le_left hN) t)
          (h₂ N (le_of_max_le_right hN) t)
      _ = ε := by ring
  zero_mem' := fun ε hε => ⟨0, fun N _ t => by simp [hε.le]⟩
  smul_mem' := by
    intro c φ hφ ε hε
    obtain ⟨N₀, h₀⟩ := hφ (ε / (‖c‖ + 1)) (by positivity)
    refine ⟨N₀, fun N hN t => ?_⟩
    rw [map_smul, map_smul, norm_smul]
    calc ‖c‖ * ‖Pout N (evol A hA t φ)‖ ≤ ‖c‖ * (ε / (‖c‖ + 1)) :=
          mul_le_mul_of_nonneg_left (h₀ N hN t) (norm_nonneg _)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg c]

lemma isClosed_tightSubmodule : IsClosed (tightSubmodule A hA : Set (L2 ℤ)) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim ε hε => ?_
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hlim (ε / 2) (by positivity))
  obtain ⟨N₀, h₀⟩ := hφ k (ε / 2) (by positivity)
  refine ⟨N₀, fun N hN t => ?_⟩
  have hk' : ‖ψ - φ k‖ ≤ ε / 2 := by
    rw [← dist_eq_norm, dist_comm]; exact (hk k le_rfl).le
  calc ‖Pout N (evol A hA t ψ)‖
      = ‖Pout N (evol A hA t (φ k)) + Pout N (evol A hA t (ψ - φ k))‖ := by
        rw [← map_add, ← map_add, add_sub_cancel]
    _ ≤ ‖Pout N (evol A hA t (φ k))‖ + ‖Pout N (evol A hA t (ψ - φ k))‖ := norm_add_le _ _
    _ ≤ ε / 2 + ‖ψ - φ k‖ := add_le_add (h₀ N hN t)
        ((norm_Pout_le _ _).trans (norm_evol t _).le)
    _ ≤ ε := by linarith

lemma eigenvector_mem_tightSubmodule {v : L2 ℤ} {E : ℝ} (h : A v = (E : ℂ) • v) :
    v ∈ tightSubmodule A hA := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_Pout v).eventually (ge_mem_nhds hε))
  refine ⟨N₀, fun N hN t => ?_⟩
  rw [evol_eigenvector h, map_smul, norm_smul, norm_expPhase, one_mul]
  exact hN₀ N hN

lemma ppSubspace_le_tightSubmodule : ppSubspace A hA ≤ tightSubmodule A hA := by
  refine ppSubspace_le_closure_span_eigenvectors.trans ?_
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_tightSubmodule
  rw [Submodule.span_le]
  rintro v ⟨E, hE⟩
  exact eigenvector_mem_tightSubmodule hE

/-- **RAGE theorem (a)** (Theorem 1.6.7(a)): `μ_φ` is pure point iff for every `ε > 0` there
is `N` with `∑_{|n|>N} |⟨δ_n, φ(t)⟩|² < ε` for all `t`. -/
theorem rage_pp (φ : L2 ℤ) :
    φ ∈ ppSubspace A hA ↔ ∀ ε > 0, ∃ N : ℕ, ∀ t,
      (∑' n, if (N : ℤ) < |n| then ‖evol A hA t φ n‖ ^ 2 else 0) < ε := by
  constructor
  · intro hφ ε hε
    obtain ⟨N₀, h₀⟩ := ppSubspace_le_tightSubmodule hφ (Real.sqrt ε / 2) (by positivity)
    refine ⟨N₀, fun t => ?_⟩
    rw [← norm_Pout_sq]
    have h1 := h₀ N₀ le_rfl t
    have h2 : ‖Pout N₀ (evol A hA t φ)‖ ^ 2 ≤ (Real.sqrt ε / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [div_pow, Real.sq_sqrt hε.le] at h2
    linarith
  · intro h
    obtain ⟨c, hc, p, hp, rfl⟩ := exists_c_pp_decomposition (A := A) (hA := hA) φ
    suffices hc0 : c = 0 by rw [hc0, zero_add]; exact hp
    by_contra hc0
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    set ε := ‖c‖ / 2
    obtain ⟨N, hN⟩ := h (ε ^ 2) (by positivity)
    have htail : ∀ t, ‖Pout N (evol A hA t (c + p))‖ < ε := by
      intro t
      have := hN t
      rw [← norm_Pout_sq] at this
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
    have hcp : ⟪c, c + p⟫_ℂ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_add_right, cSubspace_orthogonal_ppSubspace hc hp, add_zero,
        inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have hlow : ∀ t, (‖c‖ ^ 2 / 2) ^ 2 ≤ ‖c + p‖ ^ 2 * ‖Pin N (evol A hA t c)‖ ^ 2 := by
      intro t
      have hsplit : ⟪c, c + p⟫_ℂ = ⟪Pin N (evol A hA t c), evol A hA t (c + p)⟫_ℂ +
          ⟪evol A hA t c, Pout N (evol A hA t (c + p))⟫_ℂ := by
        rw [← inner_evol_evol t c (c + p), inner_Pin]
        conv_lhs => rw [← Pin_add_Pout N (evol A hA t (c + p))]
        rw [inner_add_right]
      have h1 : ‖⟪Pin N (evol A hA t c), evol A hA t (c + p)⟫_ℂ‖ ≤
          ‖Pin N (evol A hA t c)‖ * ‖c + p‖ := by
        refine (norm_inner_le_norm _ _).trans ?_; rw [norm_evol]
      have h2 : ‖⟪evol A hA t c, Pout N (evol A hA t (c + p))⟫_ℂ‖ ≤ ‖c‖ * ε := by
        refine (norm_inner_le_norm _ _).trans ?_
        rw [norm_evol]
        exact mul_le_mul_of_nonneg_left (htail t).le (norm_nonneg _)
      have h3 : ‖c‖ ^ 2 ≤ ‖Pin N (evol A hA t c)‖ * ‖c + p‖ + ‖c‖ * ε := by
        have : ‖⟪c, c + p⟫_ℂ‖ = ‖c‖ ^ 2 := by
          rw [hcp, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [← this, hsplit]
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      have h4 : ‖c‖ ^ 2 / 2 ≤ ‖c + p‖ * ‖Pin N (evol A hA t c)‖ := by
        simp only [ε] at h3; nlinarith
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h4 2
    have hlim := (rage_c_of_mem (A := A) (hA := hA) hc N).const_mul (‖c + p‖ ^ 2)
    rw [mul_zero] at hlim
    have hle := timeAvg_ge_of_forall
      (f := fun t => ‖c + p‖ ^ 2 * ‖Pin N (evol A hA t c)‖ ^ 2)
      (continuous_const.mul (continuous_norm_Pin_evol_sq N c)) hlow (by
        refine hlim.congr fun T => ?_
        rw [timeAvg_const_mul _ (continuous_norm_Pin_evol_sq N c)]
        simp_rw [norm_Pin_sq])
    have : 0 < (‖c‖ ^ 2 / 2) ^ 2 := by positivity
    linarith

/-- **RAGE theorem (c)** (Theorem 1.6.7(c)): if `μ_φ` is absolutely continuous then
`∑_{|n|≤N} |⟨δ_n, φ(t)⟩|² → 0` as `|t| → ∞`. -/
theorem rage_ac {φ : L2 ℤ} (hφ : φ ∈ acSubspace A hA) (N : ℕ) :
    Tendsto (fun t => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖evol A hA t φ n‖ ^ 2) (cocompact ℝ)
      (𝓝 0) := by
  have := tendsto_finsetSum (Finset.Icc (-(N : ℤ)) N) fun n _ =>
    ((tendsto_inner_evol_of_mem_acSubspace (A := A) (hA := hA) hφ
      (lp.single 2 n (1 : ℂ))).norm.pow 2)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at this
  refine this.congr fun t => ?_
  simp_rw [← apply_eq_inner_single]

end L2Z

end DF
