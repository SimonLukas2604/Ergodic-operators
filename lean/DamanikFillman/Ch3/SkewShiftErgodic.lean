/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Theorem 3.2.15: the skew-shift is ergodic  (book §3.2)

Main result:
* `DF.skewShiftErgodic` — proof of `DF.SkewShiftErgodicStatement`: for irrational `α`, Lebesgue
  measure on `𝕋²` is ergodic for `(ω₁, ω₂) ↦ (ω₁ + α, ω₁ + ω₂)`.

Proof (Fourier series, as in the book): on `𝕋² = UnitAddTorus (Fin 2)` the skew-shift is
`S x = (x₀ + α, x₀ + x₁)`. For an invariant set with indicator `h`, the substitution `z = S y`
gives `ĥ(n₀, n₁) = e((n₀ - n₁)α) ĥ(n₀ - n₁, n₁)`. If `n₁ ≠ 0`, then `|ĥ|` is constant along the
injective sequence `k ↦ (n₀ - k n₁, n₁)`, so square-summability (Parseval) forces `ĥ(n) = 0`;
if `n₁ = 0 ≠ n₀`, then `ĥ(n) = e(n₀α) ĥ(n)` with `e(n₀α) ≠ 1`. Hence only `ĥ(0)` survives and
the set is null or conull (`DF.ae_mem_or_ae_notMem_of_mFourierCoeff`). The product `𝕋 × 𝕋` of the
statement is identified with `UnitAddTorus (Fin 2)` by `MeasurableEquiv.piFinTwo`.
-/
import DamanikFillman.Ch3.TorusErgodic

noncomputable section

open MeasureTheory Filter Set Function Topology UnitAddTorus
open scoped ComplexConjugate

namespace DF

/-- Lebesgue measure on `𝕋 × 𝕋` is the product of Haar probability measures. -/
lemma volume_prod_eq_haar :
    (volume : Measure (UnitAddCircle × UnitAddCircle)) =
      (AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle := by
  rw [Measure.volume_eq_prod, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one,
    one_smul]

attribute [local instance] haarMeasureSpace

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The skew-shift on `UnitAddTorus (Fin 2)`. -/
def skewT (α : ℝ) (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 0 + (α : UnitAddCircle), x 0 + x 1]

/-- Its inverse. -/
def skewTinv (α : ℝ) (z : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![z 0 - (α : UnitAddCircle), z 1 - z 0 + (α : UnitAddCircle)]

lemma skewTinv_skewT (α : ℝ) (x : UnitAddTorus (Fin 2)) : skewTinv α (skewT α x) = x := by
  funext i
  fin_cases i <;> simp [skewT, skewTinv] <;> abel

lemma skewT_skewTinv (α : ℝ) (z : UnitAddTorus (Fin 2)) : skewT α (skewTinv α z) = z := by
  funext i
  fin_cases i <;> simp [skewT, skewTinv] <;> abel

lemma continuous_skewT (α : ℝ) : Continuous (skewT α) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply 0).add continuous_const
  · exact (continuous_apply 0).add (continuous_apply 1)

lemma continuous_skewTinv (α : ℝ) : Continuous (skewTinv α) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply 0).sub continuous_const
  · exact ((continuous_apply 1).sub (continuous_apply 0)).add continuous_const

/-- The skew-shift as a measurable equivalence. -/
def skewTEquiv (α : ℝ) : UnitAddTorus (Fin 2) ≃ᵐ UnitAddTorus (Fin 2) where
  toFun := skewT α
  invFun := skewTinv α
  left_inv := skewTinv_skewT α
  right_inv := skewT_skewTinv α
  measurable_toFun := (continuous_skewT α).measurable
  measurable_invFun := (continuous_skewTinv α).measurable

/-- The identification `𝕋^{Fin 2} ≃ 𝕋 × 𝕋`. -/
abbrev e2 : UnitAddTorus (Fin 2) ≃ᵐ UnitAddCircle × UnitAddCircle :=
  MeasurableEquiv.piFinTwo fun _ => UnitAddCircle

lemma e2_preserving :
    MeasurePreserving e2 (volume : Measure (UnitAddTorus (Fin 2)))
      ((volume : Measure UnitAddCircle).prod volume) :=
  measurePreserving_piFinTwo fun _ => (volume : Measure UnitAddCircle)

/-- The skew-shift on `𝕋 × 𝕋` is conjugate to `skewT`. -/
lemma skewShift_eq_conj (α : ℝ) : skewShift α = e2 ∘ skewT α ∘ e2.symm := by
  funext x
  rfl

lemma skewShift_preserving (α : ℝ) :
    MeasurePreserving (skewShift α) ((volume : Measure UnitAddCircle).prod volume)
      ((volume : Measure UnitAddCircle).prod volume) := by
  have h1 := measurePreserving_prod_add (volume : Measure UnitAddCircle) (volume : Measure UnitAddCircle)
  have h2 := measurePreserving_add_right ((volume : Measure UnitAddCircle).prod volume)
    ((α : UnitAddCircle), (0 : UnitAddCircle))
  convert h2.comp h1 using 1
  funext x
  simp [skewShift, Prod.ext_iff]

lemma skewT_preserving (α : ℝ) :
    MeasurePreserving (skewT α) (volume : Measure (UnitAddTorus (Fin 2))) volume := by
  have : skewT α = e2.symm ∘ skewShift α ∘ e2 := by
    rw [skewShift_eq_conj]
    funext x
    simp
  rw [this]
  exact (e2_preserving.symm e2).comp ((skewShift_preserving α).comp e2_preserving)

/-! ### Fourier coefficients -/

/-- `e_m(z) = e_{m₀}(z₀) e_{m₁}(z₁)` on `𝕋²`. -/
lemma mFourier_two (m : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    mFourier m z = fourier (m 0) (z 0) * fourier (m 1) (z 1) := by
  simp [mFourier, Fin.prod_univ_two]

lemma fourier_add_pt (k : ℤ) (a b : UnitAddCircle) :
    fourier k (a + b) = fourier k a * fourier k b := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fourier_neg_pt (k : ℤ) (a : UnitAddCircle) : fourier k (-a) = fourier (-k) a := by
  simp only [fourier_apply, smul_neg, neg_smul]

lemma fourier_mul_same (k l : ℤ) (a : UnitAddCircle) :
    fourier k a * fourier l a = fourier (k + l) a := by
  rw [fourier_add]

/-- The character `e_{-n}` composed with the inverse skew-shift. -/
lemma mFourier_neg_skewTinv (α : ℝ) (n : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    mFourier (-n) (skewTinv α z) =
      fourier (n 0 - n 1) (α : UnitAddCircle) * mFourier (-![n 0 - n 1, n 1]) z := by
  simp only [mFourier_two, skewTinv, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [sub_eq_add_neg, fourier_add_pt, sub_eq_add_neg (z 1), add_assoc, fourier_add_pt,
    fourier_add_pt, fourier_neg_pt, fourier_neg_pt, fourier_neg_pt]
  have h1 : fourier (-n 0) (z 0) * fourier (- -n 1) (z 0) = fourier (-(n 0 - n 1)) (z 0) := by
    rw [fourier_mul_same]; congr 1; ring
  have h2 : fourier (- -n 0) (α : UnitAddCircle) * fourier (-n 1) (α : UnitAddCircle) =
      fourier (n 0 - n 1) (α : UnitAddCircle) := by
    rw [fourier_mul_same]; congr 1; ring
  rw [← h1, ← h2]
  ring

/-- **Coefficient relation for invariant functions.** If `h ∘ S = h`, then
`ĥ(n₀, n₁) = e((n₀ - n₁)α) ĥ(n₀ - n₁, n₁)`. -/
lemma mFourierCoeff_of_skew_invariant (α : ℝ) {h : UnitAddTorus (Fin 2) → ℂ}
    (hinv : ∀ x, h (skewT α x) = h x) (n : Fin 2 → ℤ) :
    mFourierCoeff h n =
      fourier (n 0 - n 1) (α : UnitAddCircle) * mFourierCoeff h ![n 0 - n 1, n 1] := by
  unfold mFourierCoeff
  have key := (skewT_preserving α).integral_comp' (f := skewTEquiv α)
    (fun z => mFourier (-n) (skewTinv α z) • h z)
  have hl : ∀ y, mFourier (-n) (skewTinv α (skewTEquiv α y)) • h (skewTEquiv α y) =
      mFourier (-n) y • h y := fun y => by
    show mFourier (-n) (skewTinv α (skewT α y)) • h (skewT α y) = _
    rw [skewTinv_skewT, hinv]
  simp only [hl] at key
  rw [key, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul, mFourier_neg_skewTinv]
  ring

lemma fourier_coe_ne_one {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    fourier k (α : UnitAddCircle) ≠ 1 := by
  intro h
  rw [fourier_coe_apply, Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((k : ℝ) * α : ℝ) = (m : ℝ) := by
    have : ((k * α : ℝ) : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2
      push_cast
      rw [← hm]
      ring
    exact_mod_cast this
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  apply hα
  refine ⟨(m : ℚ) / k, ?_⟩
  push_cast
  field_simp
  linarith

/-- **Theorem 3.2.15** on `UnitAddTorus (Fin 2)` with Haar measure. -/
theorem skewT_ergodic {α : ℝ} (hα : Irrational α) :
    Ergodic (skewT α) (volume : Measure (UnitAddTorus (Fin 2))) := by
  refine Ergodic.of_preimage_eq (skewT_preserving α) fun s hs hinv => ?_
  rw [eventuallyEmptyOrUniv_iff]
  set h : UnitAddTorus (Fin 2) → ℂ := s.indicator 1 with hh
  have hhinv : ∀ x, h (skewT α x) = h x := by
    intro x
    have : skewT α x ∈ s ↔ x ∈ s := by rw [← mem_preimage, hinv]
    by_cases hx : x ∈ s
    · rw [hh, indicator_of_mem hx, indicator_of_mem (this.2 hx)]; rfl
    · rw [hh, indicator_of_notMem hx, indicator_of_notMem (fun h' => hx (this.1 h'))]
  have hrel := mFourierCoeff_of_skew_invariant α hhinv
  -- square summability of the coefficients (Parseval)
  set H := indicatorConstLp 2 hs (measure_ne_top volume s) (1 : ℂ) with hH
  have hHh : (H : UnitAddTorus (Fin 2) → ℂ) =ᵐ[volume] h := by
    rw [hH]; exact indicatorConstLp_coeFn
  have hHcoef : ∀ n, mFourierCoeff (H : UnitAddTorus (Fin 2) → ℂ) n = mFourierCoeff h n :=
    fun n => integral_congr_ae (by filter_upwards [hHh] with t ht; rw [ht])
  have hsq : Summable fun n : Fin 2 → ℤ => ‖mFourierCoeff h n‖ ^ 2 := by
    have := (hasSum_sq_mFourierCoeff H).summable
    simpa only [hHcoef] using this
  -- `‖ĥ(n₀ - k n₁, n₁)‖ = ‖ĥ(n)‖`
  have hnorm : ∀ (n : Fin 2 → ℤ) (k : ℕ),
      ‖mFourierCoeff h ![n 0 - k * n 1, n 1]‖ = ‖mFourierCoeff h n‖ := by
    intro n k
    induction k with
    | zero =>
      congr 2
      funext i; fin_cases i <;> simp
    | succ k ih =>
      rw [← ih, hrel ![n 0 - k * n 1, n 1], norm_mul]
      have h1 : ‖fourier ((![n 0 - k * n 1, n 1] : Fin 2 → ℤ) 0 - (![n 0 - k * n 1, n 1] :
          Fin 2 → ℤ) 1) (α : UnitAddCircle)‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      rw [h1, one_mul]
      congr 2
      funext i; fin_cases i <;> simp <;> push_cast <;> ring
  have hcoef : ∀ n : Fin 2 → ℤ, n ≠ 0 → mFourierCoeff h n = 0 := by
    intro n hn
    by_cases h1 : n 1 = 0
    · have h0 : n 0 ≠ 0 := by
        intro h0; apply hn; funext i; fin_cases i <;> simp [h0, h1]
      have hr := hrel n
      have hn' : ![n 0 - n 1, n 1] = n := by
        funext i; fin_cases i <;> simp [h1]
      rw [hn', h1, sub_zero] at hr
      have hne := fourier_coe_ne_one hα h0
      have : (1 - fourier (n 0) (α : UnitAddCircle)) * mFourierCoeff h n = 0 := by
        linear_combination hr
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd (sub_eq_zero.1 h').symm hne
      · exact h'
    · -- the indices `(n₀ - k n₁, n₁)` are distinct
      have hinj : Injective fun k : ℕ => (![n 0 - k * n 1, n 1] : Fin 2 → ℤ) := by
        intro k l hkl
        have := congrFun hkl 0
        simp only [Matrix.cons_val_zero] at this
        have : (k : ℤ) * n 1 = l * n 1 := by linarith
        exact_mod_cast mul_right_cancel₀ h1 this
      have hs2 := hsq.comp_injective hinj
      simp only [comp_def, hnorm] at hs2
      have := summable_const_iff.1 hs2
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  exact ae_mem_or_ae_notMem_of_mFourierCoeff hs hcoef

end DF

namespace DF

/-- **Theorem 3.2.15**: for irrational `α`, Lebesgue measure on `𝕋²` is ergodic for the
skew-shift. -/
theorem skewShiftErgodic : SkewShiftErgodicStatement := by
  intro α hα
  rw [volume_prod_eq_haar, skewShift_eq_conj]
  have hp : MeasurePreserving e2 (Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) :=
    measurePreserving_piFinTwo fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle)
  exact (ergodic_conjugate_iff hp).2 (skewT_ergodic hα)

end DF
