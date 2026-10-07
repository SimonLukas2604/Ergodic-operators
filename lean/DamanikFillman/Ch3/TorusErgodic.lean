/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Theorem 3.2.14: ergodicity of torus translations  (book §3.2)

Main result:
* `DF.torusTranslationErgodic` — proof of `DF.TorusTranslationErgodicStatement`: Lebesgue
  measure on `𝕋^d` is ergodic for `ω ↦ ω + α` iff `1, α₁, …, α_d` are rationally independent.

Proof (Fourier series on `𝕋^d`, Mathlib's `UnitAddTorus.mFourier`):
* translating a function by `a` multiplies its `n`-th Fourier coefficient by `e_n(a)`
  (`DF.mFourierCoeff_comp_add`);
* `e_n(α) = 1` iff `∑ nᵢαᵢ ∈ ℤ` (`DF.mFourier_coe_eq_one_iff`);
* (⇐) the indicator of an invariant set has `ĝ(n) = e_n(α) ĝ(n)`, so `ĝ(n) = 0` for `n ≠ 0` under
  independence; by completeness of the Fourier basis in `L²` the indicator is a.e. constant;
* (⇒) if `k₀ = ∑ kᵢαᵢ` with `k ≠ 0`, the character `e_k` is invariant, hence a.e. constant by
  ergodicity, contradicting `∫ ē_k e_k = 1` and `∫ e_k = 0`.
-/
import DamanikFillman.Ch3.Examples
import Mathlib.Analysis.Fourier.AddCircleMulti

noncomputable section

open MeasureTheory Filter Set Function Topology UnitAddTorus
open scoped ComplexConjugate

namespace DF

variable {d : ℕ}

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The translation vector as a point of `𝕋^d`. -/
def torusVec (α : Fin d → ℝ) : UnitAddTorus (Fin d) := fun i => (α i : UnitAddCircle)

lemma torusTranslation_eq (α : Fin d → ℝ) (x : UnitAddTorus (Fin d)) :
    torusTranslation α x = x + torusVec α := rfl

lemma mFourier_add_point (n : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

lemma mFourier_neg_point (n : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    mFourier (-n) (-x) = mFourier n x := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, neg_smul, smul_neg,
    neg_neg]

lemma mFourier_mul_neg (n : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    mFourier (-n) x * mFourier n x = 1 := by
  rw [← mFourier_add, neg_add_cancel, mFourier_zero, ContinuousMap.one_apply]

/-- `e_n(α) = exp(2πi ∑ nᵢαᵢ)`. -/
lemma mFourier_torusVec (n : Fin d → ℤ) (α : Fin d → ℝ) :
    mFourier n (torusVec α) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * α i : ℝ) : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, torusVec]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- `e_n(α) = 1` iff `∑ nᵢαᵢ` is an integer. -/
lemma mFourier_torusVec_eq_one_iff (n : Fin d → ℤ) (α : Fin d → ℝ) :
    mFourier n (torusVec α) = 1 ↔ ∃ k₀ : ℤ, (k₀ : ℝ) = ∑ i, (n i : ℝ) * α i := by
  rw [mFourier_torusVec, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((∑ i, (n i : ℝ) * α i : ℝ) : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hk]; ring
    exact_mod_cast this.symm
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; push_cast; ring⟩

/-- The translation is measure preserving. -/
lemma measurePreserving_torusTranslation (α : Fin d → ℝ) :
    MeasurePreserving (torusTranslation α) (volume : Measure (UnitAddTorus (Fin d))) volume := by
  have : torusTranslation α = fun x => x + torusVec α := funext fun x => rfl
  rw [this]
  exact measurePreserving_add_right volume (torusVec α)

/-- Translating a function multiplies its Fourier coefficients by `e_n(a)`. -/
lemma mFourierCoeff_comp_add (g : UnitAddTorus (Fin d) → ℂ) (a : UnitAddTorus (Fin d))
    (n : Fin d → ℤ) :
    mFourierCoeff (fun t => g (t + a)) n = mFourier n a * mFourierCoeff g n := by
  unfold mFourierCoeff
  show ∫ t, mFourier (-n) t • g (t + a) = mFourier n a * ∫ t, mFourier (-n) t • g t
  have h := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus (Fin d))))
    (fun s => mFourier (-n) (s - a) • g s) a
  simp only [add_sub_cancel_right] at h
  rw [h, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [smul_eq_mul, sub_eq_add_neg, mFourier_add_point, mFourier_neg_point]
  ring

/-- `∫ e_n = 0` for `n ≠ 0`. -/
lemma integral_mFourier_eq_zero {n : Fin d → ℤ} (hn : n ≠ 0) :
    ∫ t, mFourier n t ∂(volume : Measure (UnitAddTorus (Fin d))) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h; push Not at h; exact hn (funext h)
  -- the point `b` with `b_i = 1/(2 nᵢ)`, `b_j = 0` has `e_n(b) = -1`
  set b : UnitAddTorus (Fin d) := Pi.single i ((1 / (2 * (n i : ℝ)) : ℝ) : UnitAddCircle) with hb
  have heb : mFourier n b = -1 := by
    have : b = torusVec (Pi.single i (1 / (2 * (n i : ℝ)))) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hb, torusVec]
      · simp [hb, torusVec, Pi.single_eq_of_ne hj]
    rw [this, mFourier_torusVec]
    have hsum : (∑ j, (n j : ℝ) * (Pi.single i (1 / (2 * (n i : ℝ))) : Fin d → ℝ) j) = 1 / 2 := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same]
      have : (n i : ℝ) ≠ 0 := by exact_mod_cast hi
      field_simp
    rw [hsum]
    have : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have h := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus (Fin d))))
    (fun s => mFourier n s) b
  simp only [mFourier_add_point, heb, mul_neg, mul_one, integral_neg] at h
  -- `-I = I`
  have h2 : (2 : ℂ) * ∫ t, mFourier n t ∂(volume : Measure (UnitAddTorus (Fin d))) = 0 := by
    linear_combination -h
  simpa using h2

/-- **Theorem 3.2.14**: Lebesgue measure on `𝕋^d` is ergodic for the translation by `α` iff
`1, α₁, …, α_d` are rationally independent. -/
theorem torusTranslationErgodic : TorusTranslationErgodicStatement := by
  intro d α
  constructor
  · -- ergodic ⇒ independent
    intro hE k₀ k hk
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨by exact_mod_cast (by simpa using hk : (k₀ : ℝ) = 0), fun i => rfl⟩
    exfalso
    -- the character `e_k` is invariant
    have hinv : (fun x => mFourier k x) ∘ torusTranslation α =ᵐ[volume] fun x => mFourier k x := by
      refine Eventually.of_forall fun x => ?_
      simp only [comp_apply, torusTranslation_eq, mFourier_add_point]
      rw [(mFourier_torusVec_eq_one_iff k α).2 ⟨k₀, hk⟩, mul_one]
    obtain ⟨c, hc⟩ := hE.ae_eq_const_of_ae_eq_comp_ae
      (mFourier k).continuous.aestronglyMeasurable hinv
    -- compute `∫ ē_k e_k` in two ways
    have h1 : ∫ t, mFourier (-k) t * mFourier k t ∂(volume : Measure (UnitAddTorus (Fin d))) = 1 := by
      simp only [mFourier_mul_neg, integral_const, smul_eq_mul, mul_one]
      simp
    have h2 : ∫ t, mFourier (-k) t * mFourier k t ∂(volume : Measure (UnitAddTorus (Fin d))) =
        0 := by
      have hae : (fun t => mFourier (-k) t * mFourier k t) =ᵐ[volume]
          fun t => mFourier (-k) t * c := by
        filter_upwards [hc] with t ht
        simp only [Function.const_apply] at ht
        rw [ht]
      rw [integral_congr_ae hae, integral_mul_const,
        integral_mFourier_eq_zero (neg_ne_zero.2 hk0), zero_mul]
    rw [h1] at h2
    exact one_ne_zero h2
  · -- independent ⇒ ergodic
    intro hind
    refine Ergodic.of_preimage_eq (measurePreserving_torusTranslation α) fun s hs hinv => ?_
    rw [eventuallyEmptyOrUniv_iff]
    set g : UnitAddTorus (Fin d) → ℂ := s.indicator 1 with hg
    have hτ : (fun t => g (t + torusVec α)) = g := by
      funext t
      have : (t + torusVec α ∈ s) ↔ t ∈ s := by
        rw [← torusTranslation_eq, ← mem_preimage, hinv]
      by_cases ht : t ∈ s
      · rw [hg, indicator_of_mem ht, indicator_of_mem (this.2 ht)]
      · rw [hg, indicator_of_notMem ht, indicator_of_notMem (fun h => ht (this.1 h))]
    -- `ĝ(n) = 0` for `n ≠ 0`
    have hcoef : ∀ n : Fin d → ℤ, n ≠ 0 → mFourierCoeff g n = 0 := by
      intro n hn
      have h := mFourierCoeff_comp_add g (torusVec α) n
      rw [hτ] at h
      have hne : mFourier n (torusVec α) ≠ 1 := by
        intro h1
        obtain ⟨k₀, hk₀⟩ := (mFourier_torusVec_eq_one_iff n α).1 h1
        exact hn (funext (hind k₀ n hk₀).2)
      have : (1 - mFourier n (torusVec α)) * mFourierCoeff g n = 0 := by
        linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd (sub_eq_zero.1 h').symm hne
      · exact h'
    -- `g` as an `L²` function
    set G := indicatorConstLp 2 hs (measure_ne_top volume s) (1 : ℂ) with hG
    have hGg : (G : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] g := by
      rw [hG]
      exact indicatorConstLp_coeFn
    have hGcoef : ∀ n, mFourierCoeff (G : UnitAddTorus (Fin d) → ℂ) n = mFourierCoeff g n :=
      fun n => integral_congr_ae (by filter_upwards [hGg] with t ht; rw [ht])
    have hsum := hasSum_mFourier_series_L2 G
    have hsum' : HasSum (fun n => mFourierCoeff (G : UnitAddTorus (Fin d) → ℂ) n • mFourierLp 2 n)
        (mFourierCoeff (G : UnitAddTorus (Fin d) → ℂ) 0 • mFourierLp 2 (0 : Fin d → ℤ)) := by
      apply hasSum_single
      intro n hn
      rw [hGcoef, hcoef n hn, zero_smul]
    have hGeq := hsum.unique hsum'
    -- hence `g = c` a.e.
    set c := mFourierCoeff (G : UnitAddTorus (Fin d) → ℂ) 0
    have hgc : ∀ᵐ t ∂(volume : Measure (UnitAddTorus (Fin d))), g t = c := by
      have h1 := coeFn_mFourierLp (d := Fin d) 2 (0 : Fin d → ℤ)
      have h2 := Lp.coeFn_smul c (mFourierLp (d := Fin d) 2 (0 : Fin d → ℤ))
      rw [← hGeq] at h2
      filter_upwards [hGg, h1, h2] with t ht1 ht2 ht3
      rw [← ht1, ht3, Pi.smul_apply, ht2, mFourier_zero, ContinuousMap.one_apply, smul_eq_mul,
        mul_one]
    by_cases hμ : volume s = 0
    · right
      exact measure_eq_zero_iff_ae_notMem.1 hμ
    · left
      obtain ⟨x, hx, hgx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμ (ae_restrict_of_ae hgc)
      have hc1 : c = 1 := by rw [← hgx, hg, indicator_of_mem hx, Pi.one_apply]
      filter_upwards [hgc] with t ht
      by_contra hts
      rw [hg, indicator_of_notMem hts, hc1] at ht
      exact zero_ne_one ht

end DF
