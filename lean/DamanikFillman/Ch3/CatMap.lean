/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Theorem 3.2.16: the cat map is ergodic  (book §3.2)

Main result:
* `DF.catMapErgodic` — proof of `DF.CatMapErgodicStatement`: Lebesgue measure on `𝕋²` is ergodic
  for `C(ω₁, ω₂) = (2ω₁ + ω₂, ω₁ + ω₂)`.

Proof (Fourier series): `C` preserves Lebesgue measure (it is the composition of the shears
`(x, y) ↦ (x, x + y)` and `(x, y) ↦ (x + y, y)`). For an invariant set with indicator `h`, the
substitution `z = C y` gives `ĥ(n) = ĥ(M n)` with `M = [[1, -1], [-1, 2]]`. For `n ≠ 0` the orbit
`k ↦ Mᵏ n` is injective: a nonzero fixed vector of `Mᵐ` (`m ≥ 1`) would force `tr Mᵐ = 2`
(Cayley–Hamilton for `det = 1`), but `tr Mᵐ ≥ m + 2`. So `|ĥ|` is constant along an infinite set of
indices, and square-summability (Parseval) gives `ĥ(n) = 0`.
-/
import DamanikFillman.Ch3.SkewShiftErgodic

noncomputable section

open MeasureTheory Filter Set Function Topology UnitAddTorus
open scoped ComplexConjugate

namespace DF

/-! ### The matrix `M` and its orbits -/

/-- `M = C⁻¹ = [[1, -1], [-1, 2]]`, acting on frequencies. -/
def catM : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, 2]

/-- The action of `M` on `ℤ²`. -/
def catMf (n : Fin 2 → ℤ) : Fin 2 → ℤ := ![n 0 - n 1, -n 0 + 2 * n 1]

lemma catMf_eq_mulVec (n : Fin 2 → ℤ) : catMf n = catM.mulVec n := by
  funext i
  fin_cases i <;> simp [catMf, catM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma iterate_catMf (k : ℕ) (n : Fin 2 → ℤ) : catMf^[k] n = (catM ^ k).mulVec n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply, ih, catMf_eq_mulVec, Matrix.mulVec_mulVec, ← pow_succ]

lemma catMf_ne_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) : catMf n ≠ 0 := by
  intro h
  apply hn
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [catMf] at h0 h1
  funext i
  fin_cases i <;> simp <;> omega

lemma iterate_catMf_ne_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) (k : ℕ) : catMf^[k] n ≠ 0 := by
  induction k with
  | zero => simpa using hn
  | succ k ih => rw [iterate_succ_apply']; exact catMf_ne_zero ih

lemma det_catM : catM.det = 1 := by simp [catM, Matrix.det_fin_two]

lemma trace_catM : catM.trace = 3 := by simp [catM, Matrix.trace_fin_two]

lemma catM_sq : catM * catM = (3 : ℤ) • catM - (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [catM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

lemma trace_catM_pow_succ_succ (m : ℕ) :
    (catM ^ (m + 2)).trace = 3 * (catM ^ (m + 1)).trace - (catM ^ m).trace := by
  have : catM ^ (m + 2) = (3 : ℤ) • catM ^ (m + 1) - catM ^ m := by
    rw [pow_add, sq, catM_sq, mul_sub, mul_smul_comm, mul_one, ← pow_succ]
  rw [this, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

lemma trace_catM_pow_ge (m : ℕ) :
    (m : ℤ) + 2 ≤ (catM ^ m).trace ∧ (catM ^ m).trace + 1 ≤ (catM ^ (m + 1)).trace := by
  induction m with
  | zero =>
    refine ⟨by simp, ?_⟩
    norm_num [trace_catM, Matrix.trace_one]
  | succ m ih =>
    refine ⟨by push_cast; linarith [ih.1, ih.2], ?_⟩
    rw [show m + 1 + 1 = m + 2 by ring, trace_catM_pow_succ_succ]
    linarith [ih.1, ih.2]

/-- A `2 × 2` integer matrix of determinant `1` with a nonzero fixed vector has trace `2`. -/
lemma trace_eq_two_of_fixed {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det = 1) {w : Fin 2 → ℤ}
    (hw : w ≠ 0) (hfix : A.mulVec w = w) : A.trace = 2 := by
  have e1 := congrFun hfix 0
  have e2 := congrFun hfix 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2
  rw [Matrix.det_fin_two] at hA
  rw [Matrix.trace_fin_two]
  -- `((a-1)(d-1) - bc) wᵢ = 0`
  have k0 : ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) * w 0 = 0 := by
    linear_combination (A 1 1 - 1) * e1 - A 0 1 * e2
  have k1 : ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) * w 1 = 0 := by
    linear_combination -(A 1 0) * e1 + (A 0 0 - 1) * e2
  have hX : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
    by_contra hX
    apply hw
    funext i
    fin_cases i
    · exact (mul_eq_zero.1 k0).resolve_left hX
    · exact (mul_eq_zero.1 k1).resolve_left hX
  linear_combination -hX + hA

lemma catMf_iterate_injective {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    Injective fun k : ℕ => catMf^[k] n := by
  intro k j hkj
  by_contra hne
  wlog hlt : j < k generalizing k j
  · exact this hkj.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) hne)
  obtain ⟨m, rfl⟩ : ∃ m, k = j + (m + 1) := ⟨k - j - 1, by omega⟩
  have hw := iterate_catMf_ne_zero hn j
  have hfix : (catM ^ (m + 1)).mulVec (catMf^[j] n) = catMf^[j] n := by
    rw [← iterate_catMf]
    have : catMf^[m + 1] (catMf^[j] n) = catMf^[j + (m + 1)] n := by
      rw [← iterate_add_apply, add_comm]
    rw [this]
    exact hkj
  have htr := trace_eq_two_of_fixed (by rw [Matrix.det_pow, det_catM, one_pow]) hw hfix
  have := (trace_catM_pow_ge (m + 1)).1
  push_cast at this
  linarith

/-! ### The cat map on `𝕋²` -/

attribute [local instance] haarMeasureSpace

local instance catIsAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance catIsProb : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The cat map on `UnitAddTorus (Fin 2)`. -/
def catT (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) := ![x 0 + x 0 + x 1, x 0 + x 1]

/-- Its inverse. -/
def catTinv (z : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) := ![z 0 - z 1, z 1 + z 1 - z 0]

lemma catTinv_catT (x : UnitAddTorus (Fin 2)) : catTinv (catT x) = x := by
  funext i
  fin_cases i <;> simp [catT, catTinv] <;> abel

lemma catT_catTinv (z : UnitAddTorus (Fin 2)) : catT (catTinv z) = z := by
  funext i
  fin_cases i <;> simp [catT, catTinv] <;> abel

lemma continuous_catT : Continuous catT := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact ((continuous_apply 0).add (continuous_apply 0)).add (continuous_apply 1)
  · exact (continuous_apply 0).add (continuous_apply 1)

lemma continuous_catTinv : Continuous catTinv := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply 0).sub (continuous_apply 1)
  · exact ((continuous_apply 1).add (continuous_apply 1)).sub (continuous_apply 0)

/-- The cat map as a measurable equivalence. -/
def catTEquiv : UnitAddTorus (Fin 2) ≃ᵐ UnitAddTorus (Fin 2) where
  toFun := catT
  invFun := catTinv
  left_inv := catTinv_catT
  right_inv := catT_catTinv
  measurable_toFun := continuous_catT.measurable
  measurable_invFun := continuous_catTinv.measurable

lemma catMap_eq_conj : catMap = e2 ∘ catT ∘ e2.symm := by
  funext x
  refine Prod.ext ?_ rfl
  show 2 • x.1 + x.2 = x.1 + x.1 + x.2
  rw [two_nsmul]

lemma catMap_preserving :
    MeasurePreserving catMap ((volume : Measure UnitAddCircle).prod volume)
      ((volume : Measure UnitAddCircle).prod volume) := by
  set μ := (volume : Measure UnitAddCircle)
  have hL := measurePreserving_prod_add μ μ
  have hU : MeasurePreserving (fun z : UnitAddCircle × UnitAddCircle => (z.1 + z.2, z.2))
      (μ.prod μ) (μ.prod μ) := by
    have h := (Measure.measurePreserving_swap.comp (measurePreserving_prod_add μ μ)).comp
      (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    convert h using 1
    funext z
    simp [add_comm]
  convert hU.comp hL using 1
  funext x
  simp only [comp_apply, catMap]
  rw [two_nsmul, add_assoc]

lemma catT_preserving :
    MeasurePreserving catT (volume : Measure (UnitAddTorus (Fin 2))) volume := by
  have : catT = e2.symm ∘ catMap ∘ e2 := by
    rw [catMap_eq_conj]
    funext x i
    fin_cases i <;> rfl
  rw [this]
  exact (e2_preserving.symm e2).comp (catMap_preserving.comp e2_preserving)

/-- The character `e_{-n}` composed with the inverse cat map. -/
lemma mFourier_neg_catTinv (n : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    mFourier (-n) (catTinv z) = mFourier (-catMf n) z := by
  have h1 : fourier (-(n 0 - n 1)) (z 0) = fourier (-n 0) (z 0) * fourier (- -n 1) (z 0) := by
    rw [fourier_mul_same, show -n 0 + - -n 1 = -(n 0 - n 1) by ring]
  have h2 : fourier (-(-n 0 + 2 * n 1)) (z 1) =
      fourier (-n 1) (z 1) * fourier (-n 1) (z 1) * fourier (- -n 0) (z 1) := by
    rw [fourier_mul_same, fourier_mul_same, show -n 1 + -n 1 + - -n 0 = -(-n 0 + 2 * n 1) by ring]
  simp only [mFourier_two, catTinv, catMf, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h1, h2]
  simp only [sub_eq_add_neg, fourier_add_pt, fourier_neg_pt]
  ring

/-- **Coefficient relation for invariant functions**: if `h ∘ C = h`, then `ĥ(n) = ĥ(M n)`. -/
lemma mFourierCoeff_of_cat_invariant {h : UnitAddTorus (Fin 2) → ℂ}
    (hinv : ∀ x, h (catT x) = h x) (n : Fin 2 → ℤ) :
    mFourierCoeff h n = mFourierCoeff h (catMf n) := by
  unfold mFourierCoeff
  have key := catT_preserving.integral_comp' (f := catTEquiv)
    (fun z => mFourier (-n) (catTinv z) • h z)
  have hl : ∀ y, mFourier (-n) (catTinv (catTEquiv y)) • h (catTEquiv y) =
      mFourier (-n) y • h y := fun y => by
    show mFourier (-n) (catTinv (catT y)) • h (catT y) = _
    rw [catTinv_catT, hinv]
  simp only [hl] at key
  rw [key]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mFourier_neg_catTinv]

/-- **Theorem 3.2.16** on `UnitAddTorus (Fin 2)` with Haar measure. -/
theorem catT_ergodic : Ergodic catT (volume : Measure (UnitAddTorus (Fin 2))) := by
  refine Ergodic.of_preimage_eq catT_preserving fun s hs hinv => ?_
  rw [eventuallyEmptyOrUniv_iff]
  set h : UnitAddTorus (Fin 2) → ℂ := s.indicator 1 with hh
  have hhinv : ∀ x, h (catT x) = h x := by
    intro x
    have : catT x ∈ s ↔ x ∈ s := by rw [← mem_preimage, hinv]
    by_cases hx : x ∈ s
    · rw [hh, indicator_of_mem hx, indicator_of_mem (this.2 hx)]; rfl
    · rw [hh, indicator_of_notMem hx, indicator_of_notMem (fun h' => hx (this.1 h'))]
  have hrel := mFourierCoeff_of_cat_invariant hhinv
  set H := indicatorConstLp 2 hs (measure_ne_top volume s) (1 : ℂ) with hH
  have hHh : (H : UnitAddTorus (Fin 2) → ℂ) =ᵐ[volume] h := by
    rw [hH]; exact indicatorConstLp_coeFn
  have hHcoef : ∀ n, mFourierCoeff (H : UnitAddTorus (Fin 2) → ℂ) n = mFourierCoeff h n :=
    fun n => integral_congr_ae (by filter_upwards [hHh] with t ht; rw [ht])
  have hsq : Summable fun n : Fin 2 → ℤ => ‖mFourierCoeff h n‖ ^ 2 := by
    have := (hasSum_sq_mFourierCoeff H).summable
    simpa only [hHcoef] using this
  have horbit : ∀ (n : Fin 2 → ℤ) (k : ℕ), mFourierCoeff h (catMf^[k] n) = mFourierCoeff h n := by
    intro n k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply', ← hrel, ih]
  have hcoef : ∀ n : Fin 2 → ℤ, n ≠ 0 → mFourierCoeff h n = 0 := by
    intro n hn
    have hs2 := hsq.comp_injective (catMf_iterate_injective hn)
    simp only [comp_def, horbit] at hs2
    have := (summable_const_iff _).1 hs2
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  exact ae_mem_or_ae_notMem_of_mFourierCoeff hs hcoef

end DF

namespace DF

/-- **Theorem 3.2.16**: Lebesgue measure on `𝕋²` is ergodic for the cat map. -/
theorem catMapErgodic : CatMapErgodicStatement := by
  show Ergodic catMap volume
  rw [volume_prod_eq_haar, catMap_eq_conj]
  have hp : MeasurePreserving e2 (Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) :=
    measurePreserving_piFinTwo fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle)
  exact hp.ergodic_conjugate_iff.2 catT_ergodic

end DF
