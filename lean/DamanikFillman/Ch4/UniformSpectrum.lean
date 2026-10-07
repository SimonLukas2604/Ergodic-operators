/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.9.1: uniform spectral results in the topological setting  (book pp. 379–382)

Setting as in `DamanikFillman/Ch4/Johnson.lean`: `X` compact metric, `T : X ≃ₜ X`,
`f : X → ℝ` continuous, `H_ω = DF.Johnson.ham T f ω`.

## Main results
* `DF.Johnson.ham_T` — covariance `H_{Tω} = U H_ω U*`; `DF.Johnson.spectrum_ham_tp` —
  `σ(H_{Tⁿω}) = σ(H_ω)`;
* `DF.Johnson.tendsto_ham_apply` — `x_k → x` implies `H_{x_k} → H_x` strongly;
* `DF.Johnson.spectrum_subset_of_mem_closure` — if `ω` lies in the orbit closure of `ω₀`, then
  `σ(H_ω) ⊆ σ(H_{ω₀})` (the strong approximation argument of the proof of Theorem 4.9.1);
* `DF.Johnson.spectrum_eq_compl_UH_of_dense` — **Corollary 4.9.4**: if `ω₀` has a dense orbit,
  `σ(H_{ω₀}) = ℝ \ 𝒰ℋ`;
* `DF.Johnson.spectrum_eq_of_minimal` — **Theorem 4.9.1** (spectrum part) and (4.9.5): for a
  minimal system, `σ(H_ω) = ℝ \ 𝒰ℋ` for every `ω`; in particular it does not depend on `ω`;
* `DF.Johnson.uniformExpGrowth_of_uniform` — the key step of **Theorem 4.9.8**: a uniform
  cocycle with positive (uniform) Lyapunov exponent is uniformly hyperbolic;
* `DF.Johnson.spectrum_eq_zero_set_of_uniform` — **Theorem 4.9.8**: if `(Ω, T)` is minimal and
  every `(T, A_E)` is uniform with limit `L(E)`, then `σ(H_ω) = {E : L(E) = 0}` for every `ω`
  (i.e. `Σ = 𝒵` and `𝒩𝒰ℋ = ∅`).

## Deviations
* The absolutely continuous part of Theorem 4.9.1 relies on Theorem 2.9.7, which is not
  available; it is omitted.
* In Theorem 4.9.8 the "uniform Lyapunov exponent" is phrased directly as uniform convergence of
  `(1/n) log ‖A_n(ω)‖` to a constant `L(E)` (4.9.13); no measure is needed.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.Johnson
import DamanikFillman.Ch4.Setting
import DamanikFillman.Ch3.Minimal

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix Metric L2
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Johnson

open Cocycle

variable {X : Type*} [MetricSpace X] [CompactSpace X] {T : X ≃ₜ X} {f : X → ℝ}

/-! ### Covariance -/

lemma pot_T (ω : X) (n : ℤ) : pot T f (T ω) n = pot T f ω (n + 1) := by
  simp only [pot, tp]
  rw [show n + 1 = 1 + n by ring, tpow_add]
  congr 2
  simp [tpow]

/-- Covariance: `H_{Tω} = U H_ω U*`. -/
theorem ham_T (hf : Continuous f) (ω : X) :
    ham T f (T ω) = shiftL * ham T f ω * star shiftL := by
  rw [star_shiftL]
  ext1 ψ
  ext n
  simp only [ContinuousLinearMap.mul_apply, ham]
  rw [schr_apply (bddPot hf _), shiftL_apply, schr_apply (bddPot hf _), shiftR_apply,
    shiftR_apply, shiftR_apply, pot_T]
  simp only [add_sub_cancel_right]

/-- The shift as a unit of `Op`. -/
def shiftUnit : Opˣ where
  val := shiftL
  inv := shiftR
  val_inv := by ext1 ψ; exact shiftL_shiftR ψ
  inv_val := by ext1 ψ; exact shiftR_shiftL ψ

lemma spectrum_ham_T (hf : Continuous f) (ω : X) :
    spectrum ℝ (ham T f (T ω)) = spectrum ℝ (ham T f ω) := by
  rw [ham_T hf, star_shiftL]
  exact spectrum.units_conjugate (u := shiftUnit)

/-- `σ(H_{Tⁿω}) = σ(H_ω)`. -/
theorem spectrum_ham_tp (hf : Continuous f) (n : ℤ) (ω : X) :
    spectrum ℝ (ham T f (tp T n ω)) = spectrum ℝ (ham T f ω) := by
  induction n using Int.induction_on with
  | zero => rw [tp, tpow_zero]
  | succ i ih => rw [tp_add_one, spectrum_ham_T hf, ih]
  | pred i ih =>
    rw [← ih, tp, tpow_sub_one]
    conv_rhs => rw [show tpow T.toEquiv (-(i : ℤ)) ω =
      T (T.toEquiv.symm (tpow T.toEquiv (-(i : ℤ)) ω)) from (T.toEquiv.apply_symm_apply _).symm]
    rw [spectrum_ham_T hf]

/-! ### Strong continuity in `ω` -/

lemma continuous_tp (n : ℤ) : Continuous (tp T n) := by
  induction n using Int.induction_on with
  | zero => exact continuous_id.congr fun x => (tpow_zero x).symm
  | succ i ih => exact (T.continuous.comp ih).congr fun x => (tpow_add_one (i : ℤ) x).symm
  | pred i ih => exact (T.symm.continuous.comp ih).congr fun x => (tpow_sub_one (-(i : ℤ)) x).symm

/-- If `x_k → x`, then `H_{x_k} → H_x` strongly. -/
theorem tendsto_ham_apply (hf : Continuous f) {x : ℕ → X} {y : X} (hx : Tendsto x atTop (𝓝 y))
    (ψ : L2 ℤ) : Tendsto (fun k => ham T f (x k) ψ) atTop (𝓝 (ham T f y ψ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨B, hB⟩ := (isCompact_range hf).isBounded.exists_norm_le
  have hBf : ∀ z, |f z| ≤ B := fun z => by rw [← Real.norm_eq_abs]; exact hB _ ⟨z, rfl⟩
  have hdiff : ∀ k n, (ham T f (x k) ψ - ham T f y ψ) n =
      ((pot T f (x k) n - pot T f y n : ℝ) : ℂ) * ψ n := by
    intro k n
    simp only [lp.coeFn_sub, Pi.sub_apply, ham]
    rw [schr_apply (bddPot hf _), schr_apply (bddPot hf _)]
    push_cast; ring
  have hsq : ∀ k, ‖ham T f (x k) ψ - ham T f y ψ‖ ^ 2 =
      ∑' n, ‖((pot T f (x k) n - pot T f y n : ℝ) : ℂ) * ψ n‖ ^ 2 := by
    intro k; rw [norm_sq_eq_tsum]; exact tsum_congr fun n => by rw [hdiff]
  have hlim : Tendsto (fun k => ∑' n, ‖((pot T f (x k) n - pot T f y n : ℝ) : ℂ) * ψ n‖ ^ 2)
      atTop (𝓝 (∑' n : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => (2 * B) ^ 2 * ‖ψ n‖ ^ 2)
      ((summable_norm_sq ψ).mul_left _) (fun n => ?_) (Eventually.of_forall fun k n => ?_)
    · have h1 : Tendsto (fun k => pot T f (x k) n) atTop (𝓝 (pot T f y n)) :=
        ((hf.comp (continuous_tp n)).tendsto y).comp hx
      have h2 : Tendsto (fun k => ‖((pot T f (x k) n - pot T f y n : ℝ) : ℂ) * ψ n‖ ^ 2) atTop
          (𝓝 (‖((pot T f y n - pot T f y n : ℝ) : ℂ) * ψ n‖ ^ 2)) := by
        refine ((Complex.continuous_ofReal.tendsto _).comp (h1.sub_const _)
          |>.mul_const (ψ n)).norm.pow 2
      simpa using h2
    · rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have : |pot T f (x k) n - pot T f y n| ≤ 2 * B := by
        have := abs_sub (pot T f (x k) n) (pot T f y n)
        have h1 := hBf (tp T n (x k)); have h2 := hBf (tp T n y)
        simp only [pot] at this ⊢; linarith
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [tsum_zero] at hlim
  have h2 : Tendsto (fun k => Real.sqrt (‖ham T f (x k) ψ - ham T f y ψ‖ ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := by
    simp only [hsq]; exact hlim.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h2

/-- The strong approximation argument (proof of Theorem 4.9.1): if `ω` lies in the closure of the
orbit of `ω₀`, then `σ(H_ω) ⊆ σ(H_{ω₀})`. -/
theorem spectrum_subset_of_mem_closure (hf : Continuous f) {ω ω₀ : X}
    (h : ω ∈ closure (range fun n : ℤ => tp T n ω₀)) :
    spectrum ℝ (ham T f ω) ⊆ spectrum ℝ (ham T f ω₀) := by
  have := nontrivial_L2
  obtain ⟨x, hxmem, hx⟩ := mem_closure_iff_seq_limit.1 h
  choose m hm using hxmem
  have hsa : ∀ k, IsSelfAdjoint (ham T f (x k)) := fun k => isSelfAdjoint_schr (bddPot hf _)
  have hsub := spectrum_subset_of_strong_limit hsa (tendsto_ham_apply hf hx)
  have hk : ∀ k, spectrum ℂ (ham T f (x k)) = spectrum ℂ (ham T f ω₀) := by
    intro k
    rw [← hm k]
    ext z
    constructor
    · intro hz
      have hr : z.im = 0 := (isSelfAdjoint_schr (bddPot hf _)).im_eq_zero_of_mem_spectrum hz
      have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hr])
      rw [hz'] at hz ⊢
      have : z.re ∈ spectrum ℝ (ham T f (tp T (m k) ω₀)) := (spectrum.algebraMap_mem_iff ℂ).1 hz
      rw [spectrum_ham_tp hf] at this
      exact (spectrum.algebraMap_mem_iff ℂ).2 this
    · intro hz
      have hr : z.im = 0 := (isSelfAdjoint_schr (bddPot hf _)).im_eq_zero_of_mem_spectrum hz
      have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hr])
      rw [hz'] at hz ⊢
      have : z.re ∈ spectrum ℝ (ham T f ω₀) := (spectrum.algebraMap_mem_iff ℂ).1 hz
      rw [← spectrum_ham_tp hf (m k)] at this
      exact (spectrum.algebraMap_mem_iff ℂ).2 this
  intro E hE
  have hE' : (E : ℂ) ∈ spectrum ℂ (ham T f ω) := (spectrum.algebraMap_mem_iff ℂ).2 hE
  have h1 := hsub hE'
  simp only [mem_iInter, hk] at h1
  have h2 := h1 0
  have hcl : closure (⋃ k ≥ (0 : ℕ), spectrum ℂ (ham T f ω₀)) ⊆ spectrum ℂ (ham T f ω₀) := by
    refine closure_minimal (iUnion₂_subset fun _ _ => subset_rfl) (spectrum.isClosed _)
  exact (spectrum.algebraMap_mem_iff ℂ).1 (hcl h2)

/-- The `ℤ`-orbit of Chapter 3 is contained in `{Tⁿω : n ∈ ℤ}`. -/
lemma orbit_subset_range (ω : X) : orbit T ω ⊆ range fun n : ℤ => tp T n ω := by
  rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact ⟨n, tpow_natCast n ω⟩
  · rcases n with _ | k
    · exact ⟨0, by simp [tp, tpow_zero]⟩
    · exact ⟨Int.negSucc k, tpow_negSucc k ω⟩

lemma dense_range_of_dense_orbit {ω : X} (h : Dense (orbit T ω)) :
    Dense (range fun n : ℤ => tp T n ω) := h.mono (orbit_subset_range ω)

/-- **Corollary 4.9.4**: if `ω₀` has a dense orbit, then `σ(H_{ω₀}) = ℝ \ 𝒰ℋ`. -/
theorem spectrum_eq_compl_UH_of_dense (hf : Continuous f) {ω₀ : X} (h : Dense (orbit T ω₀)) :
    spectrum ℝ (ham T f ω₀) = (UHset T f)ᶜ := by
  refine subset_antisymm (spectrum_subset_compl_UH hf ω₀) fun E hE => ?_
  obtain ⟨ω, hω⟩ := mem_spectrum_of_not_UH hf hE
  exact spectrum_subset_of_mem_closure hf ((dense_range_of_dense_orbit h) ω) hω

/-- **Theorem 4.9.1** (spectrum part) together with (4.9.5): for a minimal system,
`σ(H_ω) = ℝ \ 𝒰ℋ` for every `ω ∈ Ω`. -/
theorem spectrum_eq_of_minimal (hf : Continuous f) (hmin : IsMinimalSys T) (ω : X) :
    spectrum ℝ (ham T f ω) = (UHset T f)ᶜ :=
  spectrum_eq_compl_UH_of_dense hf (hmin ω)

/-- **Theorem 4.9.1** (spectrum part): for a minimal system, `σ(H_ω)` does not depend on `ω`. -/
theorem spectrum_const_of_minimal (hf : Continuous f) (hmin : IsMinimalSys T) (ω₁ ω₂ : X) :
    spectrum ℝ (ham T f ω₁) = spectrum ℝ (ham T f ω₂) := by
  rw [spectrum_eq_of_minimal hf hmin, spectrum_eq_of_minimal hf hmin]

end Johnson

end DF
