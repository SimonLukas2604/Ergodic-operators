/-
# The density of states is carried by the spectrum  (paper §1.2, consequence of Thm 1.4(iii))

For a covariant family `x ↦ H_x` of self-adjoint operators whose spectra all lie in a closed
set `Σ`, every density of states measure `ν` satisfies `ν(Σᶜ) = 0`.  Consequently, if `ν` is
absolutely continuous then `|Σ| > 0` and `dim_H Σ = 1`, which is the "in particular" of
Theorem 1.4(iii).  Everything here is proved.
-/
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open scoped ENNReal InnerProductSpace
open MeasureTheory Set Filter Metric BoundedContinuousFunction L2

namespace AMO

/-- `f(T) = 0` when `f` vanishes on a set containing the real spectrum of a self-adjoint `T`. -/
lemma cfc_re_eq_zero {T : Op ℤ} (hT : IsSelfAdjoint T) {S : Set ℝ}
    (hS : spectrum ℝ T ⊆ S) {f : ℝ → ℝ} (hf : ∀ t ∈ S, f t = 0) :
    cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T = 0 := by
  have : IsStarNormal T := hT.isStarNormal
  rw [cfc_congr (g := fun _ => (0 : ℂ))]
  · exact cfc_const_zero ℂ T
  intro z hz
  have hre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  have hmem : z.re ∈ spectrum ℝ T := by
    rw [← spectrum.preimage_algebraMap ℂ]
    simp only [mem_preimage, Complex.coe_algebraMap]
    rwa [← hre]
  simp [hf _ (hS hmem)]

/-- The truncated distance function `t ↦ min 1 (k · d(t, Σ))` as a bounded continuous map. -/
def distCutoff (S : Set ℝ) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => min 1 ((k : ℝ) * infDist t S))
    (continuous_const.min (continuous_const.mul (continuous_infDist_pt S))) 1
    (fun t => by
      have h0 : 0 ≤ (k : ℝ) * infDist t S := mul_nonneg (Nat.cast_nonneg k) infDist_nonneg
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · exact le_trans (by norm_num) (le_min zero_le_one h0)
      · exact min_le_left _ _)

lemma distCutoff_apply (S : Set ℝ) (k : ℕ) (t : ℝ) :
    distCutoff S k t = min 1 ((k : ℝ) * infDist t S) := rfl

/-- **The DOS measure is carried by the common spectrum.** -/
theorem dos_compl_eq_zero {Hx : ℝ → Op ℤ} {ν : Measure ℝ} (hν : IsDOSMeasure Hx ν)
    {S : Set ℝ} (hSc : IsClosed S) (hSne : S.Nonempty)
    (hsa : ∀ x, IsSelfAdjoint (Hx x)) (hspec : ∀ x, spectrum ℝ (Hx x) ⊆ S) :
    ν Sᶜ = 0 := by
  have hprob := hν.1
  -- `∫ f dν = 0` for bounded continuous `f` vanishing on `S`
  have hzero : ∀ f : ℝ →ᵇ ℝ, (∀ t ∈ S, f t = 0) → ∫ t, f t ∂ν = 0 := by
    intro f hf
    rw [hν.2 f]
    have : ∀ x : ℝ, RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (Hx x)
        (delta 0)⟫_ℂ = 0 := by
      intro x
      rw [cfc_re_eq_zero (hsa x) (hspec x) hf]
      simp
    simp [this]
  -- the sets `{t | 1/k < d(t,S)}` are null
  have hk : ∀ k : ℕ, ν {t | 1 ≤ distCutoff S k t} = 0 := by
    intro k
    have hnn : 0 ≤ᵐ[ν] fun t => distCutoff S k t := Eventually.of_forall fun t => by
      show (0 : ℝ) ≤ distCutoff S k t
      rw [distCutoff_apply]
      exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg k) infDist_nonneg)
    have hint : Integrable (fun t => distCutoff S k t) ν := (distCutoff S k).integrable ν
    have h := mul_meas_ge_le_integral_of_nonneg hnn hint 1
    rw [hzero _ (fun t ht => by simp [distCutoff_apply, infDist_zero_of_mem ht]), one_mul] at h
    have h' : (ν {t | 1 ≤ distCutoff S k t}).toReal = 0 :=
      le_antisymm h ENNReal.toReal_nonneg
    rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h'
  -- `Sᶜ` is the union of these sets
  have hcover : Sᶜ ⊆ ⋃ k : ℕ, {t | 1 ≤ distCutoff S k t} := by
    intro t ht
    have hpos : 0 < infDist t S := (hSc.notMem_iff_infDist_pos hSne).1 ht
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / infDist t S)
    refine mem_iUnion.2 ⟨k, ?_⟩
    simp only [mem_ofPred_eq, distCutoff_apply, le_min_iff, le_refl, true_and]
    rw [div_lt_iff₀ hpos] at hk
    exact hk.le
  exact measure_mono_null hcover (measure_iUnion_null hk)

/-- An absolutely continuous probability measure carried by `S` forces `|S| > 0`. -/
theorem volume_pos_of_ac {ν : Measure ℝ} [IsProbabilityMeasure ν] {S : Set ℝ}
    (hac : ν ≪ volume) (hS : ν Sᶜ = 0) : 0 < volume S := by
  rw [pos_iff_ne_zero]
  intro h0
  have h1 : ν S = 0 := hac h0
  have : ν univ ≤ ν S + ν Sᶜ := by
    rw [← union_compl_self S]
    exact measure_union_le _ _
  rw [h1, hS, add_zero, measure_univ] at this
  exact absurd this (by simp)

/-- A subset of `ℝ` of positive Lebesgue measure has Hausdorff dimension `1`. -/
theorem dimH_eq_one_of_volume_pos {S : Set ℝ} (h : 0 < volume S) : dimH S = 1 := by
  refine le_antisymm ?_ ?_
  · calc dimH S ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ S)
      _ = 1 := Real.dimH_univ
  · have := le_dimH_of_hausdorffMeasure_ne_zero (s := S) (d := 1)
      (by simp only [NNReal.coe_one]; rw [hausdorffMeasure_real]; exact h.ne')
    simpa using this

/-- The real spectrum of a self-adjoint operator on `ℓ²(ℤ)` is closed and nonempty. -/
lemma spectrum_real_isClosed (T : Op ℤ) : IsClosed (spectrum ℝ T) := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (spectrum.isClosed (𝕜 := ℂ) T).preimage (by
    simp only [Complex.coe_algebraMap]
    exact Complex.continuous_ofReal)

instance : Nontrivial (L2 ℤ) :=
  ⟨⟨delta 0, 0, fun h => by
    have := congrArg (fun u : L2 ℤ => u 0) h
    simp [delta] at this⟩⟩

lemma spectrum_real_nonempty {T : Op ℤ} (hT : IsSelfAdjoint T) : (spectrum ℝ T).Nonempty := by
  have hne : (spectrum ℂ T).Nonempty := spectrum.nonempty T
  obtain ⟨z, hz⟩ := hne
  refine ⟨z.re, ?_⟩
  rw [← spectrum.preimage_algebraMap ℂ]
  simp only [mem_preimage, Complex.coe_algebraMap]
  rwa [← hT.mem_spectrum_eq_re hz]

/-- **Theorem 1.4(iii), "in particular".**  For the covariant family `H_x` with absolutely
summable self-adjoint perturbation and irrational `α`, an absolutely continuous density of
states forces `|Σ| > 0` and `dim_H Σ = 1`. -/
theorem volume_Sigma_pos_and_dimH {α η : ℝ} {R : Symbol} (hα : Irrational α)
    (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) {ν : Measure ℝ}
    (hν : IsDOSMeasure (H α η R) ν) (hac : ν ≪ volume) :
    0 < volume (Sigma α η R) ∧ dimH (Sigma α η R) = 1 := by
  have hSA : ∀ x, IsSelfAdjoint (H α η R x) := isSelfAdjoint_H α η hR hsa
  have hS : ν (Sigma α η R)ᶜ = 0 :=
    dos_compl_eq_zero hν (spectrum_real_isClosed _) (spectrum_real_nonempty (hSA 0)) hSA
      (fun x => (spectrum_H_eq_Sigma hα hR hsa x).le)
  have := hν.1
  have hpos := volume_pos_of_ac hac hS
  exact ⟨hpos, dimH_eq_one_of_volume_pos hpos⟩

end AMO
