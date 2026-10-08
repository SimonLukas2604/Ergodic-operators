/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.1: the Fourier and Hilbert transforms   (book pp. 403–410)

## Main results

* Theorem A.1.1 (Fourier series on `𝕋ᵈ`): `fourier_unitary_torus`, `parseval_torus`,
  `fourier_inversion_torus`, `eq_of_mFourierCoeff_eq` — thin wrappers around Mathlib's
  `UnitAddTorus.mFourierBasis`.
* Hilbert transform on `𝕋`: `hilbertT` and Theorem A.1.2: `fourierCoeff_hilbertT` (A.1.3),
  `hilbertT_hilbertT` (`H² g = -g + ĝ(0)`), `hilbertT_eq_zero_iff` (the kernel consists of the
  constants), `norm_hilbertT_sq` (partial isometry).
* Theorem A.1.3 (Fourier transform on `ℝᵈ`): `fourierL2_norm`, `fourierL2_schwartz`,
  `fourier_inversion_schwartz`, `fourier_convolution_schwartz` — wrappers around Mathlib.
* Hilbert transform on `ℝ`: `truncHilbert` (`H_ε`), `hilbertR` (A.1.5) and
  Proposition A.1.4: `tendsto_truncHilbert` (existence of the principal value at points of
  local Hölder continuity) and `tendstoUniformly_truncHilbert` (uniform convergence for
  uniformly Hölder `g`), together with the explicit formula `hilbertR_eq`.

## Deviations

* On the circle the book defines `Hg = lim_{r↑1} g * Q_r` and then derives (A.1.3).  We take the
  Fourier-multiplier formula (A.1.3) as the definition (on `L²(𝕋)`); the identification with
  the conjugate Poisson integral is `ConjugatePoissonStatement` (it contains the claim
  `H P_r = Q_r` of Theorem A.1.2); it is *proved* in `DamanikFillman/AppA/FourierDecay.lean`
  (`DF.conjugatePoissonStatement_holds`).
* Functions on `ℝ` are complex valued.

## Statements (recorded, not proved)

* `ConjugatePoissonStatement` — Fourier coefficients of the Poisson kernel `P_r` and the
  conjugate kernel `Q_r` (contains `H P_r = Q_r` from Theorem A.1.2); proved in
  `FourierDecay.lean`;
* `HilbertL2Statement` — Proposition A.1.5;
* `HolderHilbertStatement` — Theorem A.1.6 (Plemelj–Privalov); its second sentence (Lipschitz
  `g`) is derived as `holder_hilbertR_of_lipschitz`.  Proved in `HolderHilbert.lean`
  (`holderHilbertStatement_holds`, `holder_hilbertR_of_lipschitz'`).
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Basic.Real.Sign

noncomputable section

open Real Complex Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### Theorem A.1.1: Fourier series on the torus `𝕋ᵈ` -/

section Torus

/-- As in Mathlib's `AddCircleMulti`, `ℝ/ℤ` carries the Haar probability measure. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {d : Type*} [Fintype d]

/-- Theorem A.1.1: the Fourier coefficient map extends to a unitary `L²(𝕋ᵈ) → ℓ²(ℤᵈ)`. -/
theorem fourier_unitary_torus :
    ∃ F : L²(UnitAddTorus d) ≃ₗᵢ[ℂ] lp (fun _ : d → ℤ => ℂ) 2,
      ∀ f k, F f k = UnitAddTorus.mFourierCoeff f k :=
  ⟨UnitAddTorus.mFourierBasis.repr, UnitAddTorus.mFourierBasis_repr⟩

/-- Theorem A.1.1: Parseval's formula (A.1.2). -/
theorem parseval_torus (f : L²(UnitAddTorus d)) :
    HasSum (fun k => ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) (∫ t, ‖f t‖ ^ 2) :=
  UnitAddTorus.hasSum_sq_mFourierCoeff f

/-- Theorem A.1.1: the Fourier series of `f ∈ L²(𝕋ᵈ)` converges to `f` in `L²`. -/
theorem fourier_inversion_torus (f : L²(UnitAddTorus d)) :
    HasSum (fun k => UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourierLp 2 k) f :=
  UnitAddTorus.hasSum_mFourier_series_L2 f

/-- Theorem A.1.1: an `L²` function is determined by its Fourier coefficients. -/
theorem eq_of_mFourierCoeff_eq {f g : L²(UnitAddTorus d)}
    (h : ∀ k, UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k) : f = g := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext k
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr, h]

end Torus

/-! ### The Hilbert transform on the circle (Theorem A.1.2) -/

section HilbertCircle

/-- `L²(𝕋)` with normalized Haar measure. -/
abbrev L2T := Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))

/-- The symbol `-i sgn(k)` of the Hilbert transform (A.1.3). -/
def hilbertSymbol (k : ℤ) : ℂ := -Complex.I * (Int.sign k : ℂ)

lemma norm_hilbertSymbol_le (k : ℤ) : ‖hilbertSymbol k‖ ≤ 1 := by
  unfold hilbertSymbol
  rcases lt_trichotomy k 0 with h | rfl | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp
  · simp [Int.sign_eq_one_of_pos h]

lemma hilbertSymbol_zero : hilbertSymbol 0 = 0 := by simp [hilbertSymbol]

lemma hilbertSymbol_sq {k : ℤ} (hk : k ≠ 0) : hilbertSymbol k * hilbertSymbol k = -1 := by
  unfold hilbertSymbol
  rcases lt_or_gt_of_ne hk with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]

lemma norm_hilbertSymbol {k : ℤ} (hk : k ≠ 0) : ‖hilbertSymbol k‖ = 1 := by
  unfold hilbertSymbol
  rcases lt_or_gt_of_ne hk with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]

/-- Multiplication by a sequence bounded by `1`, as an operator on `ℓ²(ℤ)`. -/
def lpMul (m : ℤ → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨fun k => m k * ψ k, (lp.memℓp ψ).mono' fun k => by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hm k)⟩
      map_add' := fun ψ φ => by
        ext k
        change m k * (ψ + φ) k = m k * ψ k + m k * φ k
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c ψ => by
        ext k; simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        change m k * (c * ψ k) = c * (m k * ψ k); ring }
    1 (fun ψ => by
      rw [one_mul]
      refine lp.norm_mono (by norm_num) fun k => ?_
      change ‖m k * ψ k‖ ≤ ‖ψ k‖
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hm k))

@[simp] lemma lpMul_apply (m : ℤ → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1) (ψ : lp (fun _ : ℤ => ℂ) 2)
    (k : ℤ) : lpMul m hm ψ k = m k * ψ k := rfl

/-- The Hilbert transform on `L²(𝕋)`, defined by the Fourier multiplier `-i sgn(k)` (A.1.3). -/
def hilbertT : L2T →L[ℂ] L2T :=
  (fourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((lpMul hilbertSymbol norm_hilbertSymbol_le).comp
      fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

lemma repr_hilbertT (g : L2T) (k : ℤ) :
    fourierBasis.repr (hilbertT g) k = hilbertSymbol k * fourierBasis.repr g k := by
  simp [hilbertT]

/-- Theorem A.1.2, (A.1.3): `(Hg)^(k) = -i sgn(k) ĝ(k)`. -/
theorem fourierCoeff_hilbertT (g : L2T) (k : ℤ) :
    fourierCoeff (hilbertT g) k = -Complex.I * (Int.sign k : ℂ) * fourierCoeff g k := by
  rw [← fourierBasis_repr, ← fourierBasis_repr, repr_hilbertT]; rfl

/-- The constant function `1 = e₀` in `L²(𝕋)`. -/
abbrev constOne : L2T := fourierLp 2 0

lemma repr_constOne (k : ℤ) :
    fourierBasis.repr constOne k = if k = 0 then 1 else 0 := by
  have : constOne = fourierBasis 0 := by simp [constOne]
  rw [this, HilbertBasis.repr_self, lp.single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

/-- Theorem A.1.2: `H² g = -g + ĝ(0)`. -/
theorem hilbertT_hilbertT (g : L2T) :
    hilbertT (hilbertT g) = -g + fourierCoeff g 0 • constOne := by
  apply fourierBasis.repr.injective
  ext k
  rw [repr_hilbertT, repr_hilbertT, map_add, map_neg, map_smul]
  simp only [lp.coeFn_add, lp.coeFn_neg, lp.coeFn_smul, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, repr_constOne, ← fourierBasis_repr]
  by_cases hk : k = 0
  · subst hk; simp [hilbertSymbol_zero]
  · rw [← mul_assoc, hilbertSymbol_sq hk]; simp [hk]

/-- Theorem A.1.2: the kernel of `H` consists exactly of the constant functions. -/
theorem hilbertT_eq_zero_iff (g : L2T) :
    hilbertT g = 0 ↔ ∃ c : ℂ, g = c • constOne := by
  constructor
  · intro h
    refine ⟨fourierCoeff g 0, ?_⟩
    have := hilbertT_hilbertT g
    rw [h, map_zero] at this
    exact (neg_add_eq_zero.1 this.symm)
  · rintro ⟨c, rfl⟩
    apply fourierBasis.repr.injective
    ext k
    rw [repr_hilbertT, map_smul, map_zero]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, repr_constOne, lp.coeFn_zero,
      Pi.zero_apply]
    by_cases hk : k = 0
    · subst hk; simp [hilbertSymbol_zero]
    · simp [hk]

/-- Theorem A.1.2: `H` is a partial isometry: `‖Hg‖² = ‖g‖² - |ĝ(0)|²`. -/
theorem norm_hilbertT_sq (g : L2T) :
    ‖hilbertT g‖ ^ 2 = ‖g‖ ^ 2 - ‖fourierCoeff g 0‖ ^ 2 := by
  have h1 : HasSum (fun k => ‖fourierBasis.repr (hilbertT g) k‖ ^ 2) (‖hilbertT g‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by norm_num) (fourierBasis.repr (hilbertT g))
    simpa using this
  have h2 : HasSum (fun k => ‖fourierBasis.repr g k‖ ^ 2) (‖g‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by norm_num) (fourierBasis.repr g)
    simpa using this
  have h3 : HasSum (fun k : ℤ => if k = 0 then ‖fourierBasis.repr g 0‖ ^ 2 else 0)
      (‖fourierBasis.repr g 0‖ ^ 2) := hasSum_ite_eq 0 _
  have h4 := h2.sub h3
  rw [← fourierBasis_repr]
  refine h1.unique (h4.congr_fun fun k => ?_)
  rw [repr_hilbertT, norm_mul]
  by_cases hk : k = 0
  · subst hk; simp [hilbertSymbol_zero]
  · simp [hk, norm_hilbertSymbol hk]

/-- The Poisson kernel `P_r(x) = (1 - r²)/(1 - 2r cos 2πx + r²)` on `𝕋 = ℝ/ℤ`
(here `cos 2πx = Re e^{2πix}`, with `e^{2πix} = fourier 1 x`). -/
def circlePoissonKernel (r : ℝ) (x : UnitAddCircle) : ℂ :=
  (((1 - r ^ 2) / (1 - 2 * r * (fourier 1 x).re + r ^ 2) : ℝ) : ℂ)

/-- The conjugate Poisson kernel `Q_r(x) = 2r sin 2πx/(1 - 2r cos 2πx + r²)` on `𝕋`
(here `sin 2πx = Im e^{2πix}`). -/
def conjPoissonKernel (r : ℝ) (x : UnitAddCircle) : ℂ :=
  (((2 * r * (fourier 1 x).im) / (1 - 2 * r * (fourier 1 x).re + r ^ 2) : ℝ) : ℂ)

/-- Fourier coefficients of the Poisson kernel and of the conjugate Poisson kernel:
`P̂_r(k) = r^{|k|}`, `Q̂_r(k) = -i sgn(k) r^{|k|}`; in particular `H P_r = Q_r` (Theorem A.1.2),
and the conjugate Poisson integral `g * Q_r` has Fourier coefficients `-i sgn(k) r^{|k|} ĝ(k)`,
which identifies the book's definition `Hg = lim_{r↑1} g * Q_r` with `hilbertT`. -/
def ConjugatePoissonStatement : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ k : ℤ,
    fourierCoeff (circlePoissonKernel r) k = (r : ℂ) ^ k.natAbs ∧
    fourierCoeff (conjPoissonKernel r) k = hilbertSymbol k * (r : ℂ) ^ k.natAbs

end HilbertCircle

/-! ### Theorem A.1.3: the Fourier transform on `ℝᵈ` (wrappers around Mathlib) -/

section Euclidean

open FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Theorem A.1.3: Plancherel — the Fourier transform is unitary on `L²(V)`. -/
theorem fourierL2_norm (f : Lp (α := V) ℂ 2) : ‖𝓕 f‖ = ‖f‖ := Lp.norm_fourier_eq f

/-- Theorem A.1.3: the `L²` Fourier transform extends the Fourier transform on Schwartz
functions. -/
theorem fourierL2_schwartz (f : 𝓢(V, ℂ)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 :=
  SchwartzMap.toLp_fourier_eq f

/-- Theorem A.1.3: the Fourier inversion formula on Schwartz space. -/
theorem fourier_inversion_schwartz (f : 𝓢(V, ℂ)) : 𝓕⁻ (𝓕 f) = f :=
  fourierInv_fourier_eq f

/-- Theorem A.1.3: the Fourier transform turns convolution of Schwartz functions into
products. -/
theorem fourier_convolution_schwartz (f g : 𝓢(V, ℂ)) (x : V) :
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) x = 𝓕 f x * 𝓕 g x := by
  rw [SchwartzMap.fourier_convolution]
  simp

end Euclidean

/-! ### The Hilbert transform on `ℝ` (Proposition A.1.4) -/

section HilbertLine

/-- The truncated Hilbert transform `H_ε g(t) = π⁻¹ ∫_{|x| > ε} g(t - x)/x dx`. -/
def truncHilbert (ε : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / π : ℝ) • ∫ x in {x : ℝ | ε < |x|}, g (t - x) / (x : ℂ)

/-- The Hilbert transform `Hg(t) = lim_{ε↓0} H_ε g(t)` (A.1.5), defined as `limUnder` (it is
meaningful wherever the limit exists, cf. `tendsto_truncHilbert`). -/
def hilbertR (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => truncHilbert ε g t)

variable {g : ℝ → ℂ}

lemma memLp_comp_sub (hg : MemLp g 2) (t : ℝ) : MemLp (fun x => g (t - x)) 2 :=
  hg.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left t)

lemma memLp_comp_add (hg : MemLp g 2) (t : ℝ) : MemLp (fun x => g (t + x)) 2 :=
  hg.comp_measurePreserving (measurePreserving_add_left volume t)

lemma aestronglyMeasurable_div_id {h : ℝ → ℂ} (hh : AEStronglyMeasurable h volume)
    (μ : Measure ℝ) (hμ : μ ≪ volume) :
    AEStronglyMeasurable (fun x => h x / (x : ℂ)) μ := by
  simp_rw [div_eq_mul_inv]
  exact (hh.mono_ac hμ).mul
    (Complex.measurable_ofReal.inv.aestronglyMeasurable)

/-- The Hilbert kernel is integrable away from the origin, for `L²` functions. -/
lemma integrableOn_div_id {h : ℝ → ℂ} (hh : MemLp h 2) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x => h x / (x : ℂ)) {x : ℝ | ε < |x|} := by
  have h1 : Integrable (fun x => ‖h x‖ ^ (2 : ℝ≥0∞).toReal) :=
    hh.integrable_norm_rpow (by norm_num) (by norm_num)
  have h2 : Integrable (fun x : ℝ => ‖h x‖ ^ (2 : ℝ≥0∞).toReal / 2 +
      (1 + (ε ^ 2)⁻¹) / 2 * (1 + x ^ 2)⁻¹) :=
    (h1.div_const 2).add (integrable_inv_one_add_sq.const_mul _)
  refine h2.integrableOn.mono' (aestronglyMeasurable_div_id hh.aestronglyMeasurable _ Measure.restrict_le_self.absolutelyContinuous)
    ((ae_restrict_iff' (measurableSet_lt measurable_const continuous_abs.measurable)).2
      (Eventually.of_forall fun x hx => ?_))
  simp only [mem_ofPred_eq] at hx
  have hx0 : 0 < |x| := hε.trans hx
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hx2 : 0 < x ^ 2 := by rw [← sq_abs]; positivity
  have hε2 : ε ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hε.le hx.le 2
  have hsq : (x ^ 2)⁻¹ ≤ (1 + (ε ^ 2)⁻¹) * (1 + x ^ 2)⁻¹ := by
    have h1 : 1 ≤ x ^ 2 * (ε ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (by positivity)]; exact hε2
    have key : 1 + x ^ 2 ≤ x ^ 2 * (1 + (ε ^ 2)⁻¹) := by nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ hx2]
    exact key
  have hamgm : ‖h x‖ / |x| ≤ ‖h x‖ ^ 2 / 2 + (x ^ 2)⁻¹ / 2 := by
    have : ‖h x‖ / |x| = ‖h x‖ * |x|⁻¹ := div_eq_mul_inv _ _
    rw [this]
    have h3 : (x ^ 2)⁻¹ = (|x|⁻¹) ^ 2 := by rw [inv_pow, sq_abs]
    rw [h3]
    nlinarith [sq_nonneg (‖h x‖ - |x|⁻¹)]
  linarith

/-- Splitting `{ε < |x|}` into `{1 < |x|}` and the two intervals `(ε, 1]`, `[-1, -ε)`. -/
lemma setOf_lt_abs_eq {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    {x : ℝ | ε < |x|} = {x : ℝ | 1 < |x|} ∪ (Ioc ε 1 ∪ Ico (-1) (-ε)) := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioc, mem_Ico]
  constructor
  · intro h
    by_cases h1 : 1 < |x|
    · exact Or.inl h1
    · right
      push Not at h1
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx] at h h1; exact Or.inl ⟨h, h1⟩
      · rw [abs_of_neg hx] at h h1; exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · rw [abs_of_pos (hε.trans h1)]; exact h1
    · rw [abs_of_neg (by linarith)]; linarith

/-- The principal-value part `∫_ε^1 (g(t-x) - g(t+x))/x dx` of `H_ε g(t)`. -/
lemma truncHilbert_eq (hg : MemLp g 2) (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    truncHilbert ε g t = (1 / π : ℝ) • ((∫ x in {x : ℝ | 1 < |x|}, g (t - x) / (x : ℂ)) +
      ∫ x in ε..1, (g (t - x) - g (t + x)) / (x : ℂ)) := by
  unfold truncHilbert
  congr 1
  have hI := integrableOn_div_id (memLp_comp_sub hg t) hε
  have hI' := integrableOn_div_id (memLp_comp_add hg t) hε
  have hS := setOf_lt_abs_eq hε hε1
  rw [hS] at hI hI'
  have hd1 : Disjoint {x : ℝ | 1 < |x|} (Ioc ε 1 ∪ Ico (-1) (-ε)) := by
    rw [Set.disjoint_left]
    rintro x hx (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · simp only [mem_ofPred_eq] at hx; rw [abs_of_pos (hε.trans h1)] at hx; linarith
    · simp only [mem_ofPred_eq] at hx; rw [abs_of_neg (by linarith)] at hx; linarith
  have hd2 : Disjoint (Ioc ε 1) (Ico (-1) (-ε)) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, _⟩ ⟨_, h2⟩; linarith
  rw [hS, setIntegral_union hd1 (measurableSet_Ioc.union measurableSet_Ico)
    (hI.mono_set subset_union_left) (hI.mono_set subset_union_right),
    setIntegral_union hd2 measurableSet_Ico (hI.mono_set (subset_union_left.trans subset_union_right))
    (hI.mono_set (subset_union_right.trans subset_union_right))]
  congr 1
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε1,
    ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -ε)]
  rw [← intervalIntegral.integral_comp_neg (fun x => g (t - x) / (x : ℂ))]
  have hint1 : IntervalIntegrable (fun x => g (t - x) / (x : ℂ)) volume ε 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).2
      (hI.mono_set (subset_union_left.trans subset_union_right))
  have hint2 : IntervalIntegrable (fun x => g (t + x) / (x : ℂ)) volume ε 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).2
      (hI'.mono_set (subset_union_left.trans subset_union_right))
  simp only [sub_neg_eq_add, Complex.ofReal_neg, div_neg, intervalIntegral.integral_neg]
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub hint1 hint2]
  congr 1; funext x; ring

/-- The integrand `(g(t-x) - g(t+x))/x` is dominated by `2C x^{α-1}` on `(0,1]` under a local
Hölder condition at `t`. -/
lemma norm_hilbertDiff_le {α C t : ℝ}
    (hC : ∀ y, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖(g (t - x) - g (t + x)) / (x : ℂ)‖ ≤ 2 * C * x ^ (α - 1) := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1 := hC (t - x) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hx0]; exact hx1)
  have h2 := hC (t + x) (by rw [add_sub_cancel_left, abs_of_pos hx0]; exact hx1)
  rw [sub_sub_cancel_left, abs_neg, abs_of_pos hx0] at h1
  rw [add_sub_cancel_left, abs_of_pos hx0] at h2
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_sub_one hx0.ne',
    div_le_iff₀ hx0]
  have : ‖g (t - x) - g (t + x)‖ ≤ ‖g (t - x) - g t‖ + ‖g (t + x) - g t‖ := by
    rw [← norm_neg (g (t + x) - g t)]
    refine (norm_add_le _ _).trans_eq' ?_
    congr 1; ring
  have hxpos : 0 < x := hx0
  field_simp
  linarith

lemma intervalIntegrable_hilbertDiff (hg : MemLp g 2) {α C t : ℝ} (hα : 0 < α)
    (hC : ∀ y, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun x => (g (t - x) - g (t + x)) / (x : ℂ)) volume a b := by
  have hbound : IntervalIntegrable (fun x : ℝ => 2 * C * x ^ (α - 1)) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  refine hbound.mono_fun' ?_ ?_
  · exact aestronglyMeasurable_div_id
      ((memLp_comp_sub hg t).aestronglyMeasurable.sub (memLp_comp_add hg t).aestronglyMeasurable) _
      Measure.restrict_le_self.absolutelyContinuous
  · rw [uIoc_of_le hab]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    exact norm_hilbertDiff_le hC ⟨lt_of_le_of_lt ha hx.1, hx.2.trans hb⟩

/-- The explicit value of the principal value integral. -/
def hilbertPV (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / π : ℝ) • ((∫ x in {x : ℝ | 1 < |x|}, g (t - x) / (x : ℂ)) +
      ∫ x in (0 : ℝ)..1, (g (t - x) - g (t + x)) / (x : ℂ))

/-- Quantitative convergence `|H_ε g(t) - Hg(t)| ≤ 2|C| ε^α/(πα)` for `0 < ε ≤ 1`. -/
lemma norm_truncHilbert_sub_le (hg : MemLp g 2) {α C t : ℝ} (hα : 0 < α)
    (hC : ∀ y, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ‖truncHilbert ε g t - hilbertPV g t‖ ≤ (1 / π) * (2 * C * (ε ^ α / α)) := by
  rw [truncHilbert_eq hg t hε hε1, hilbertPV, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  gcongr
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_hilbertDiff hg hα hC le_rfl hε.le hε1)
    (intervalIntegrable_hilbertDiff hg hα hC hε.le hε1 le_rfl)]
  rw [show ∀ a b c : ℂ, (a + b) - (a + (c + b)) = -c from fun a b c => by ring, norm_neg]
  have h1 : ‖∫ x in (0 : ℝ)..ε, (g (t - x) - g (t + x)) / (x : ℂ)‖ ≤
      ∫ x in (0 : ℝ)..ε, 2 * C * x ^ (α - 1) :=
    intervalIntegral.norm_integral_le_of_norm_le hε.le
      (Eventually.of_forall fun x hx => norm_hilbertDiff_le hC ⟨hx.1, hx.2.trans hε1⟩)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
  refine h1.trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  rw [sub_add_cancel, Real.zero_rpow hα.ne', sub_zero]

lemma tendsto_rpow_nhdsGT_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) := by
  have : ContinuousAt (fun ε : ℝ => ε ^ α) 0 :=
    continuousAt_id.rpow_const (Or.inr hα.le)
  have h := this.tendsto
  simp only [Real.zero_rpow hα.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Proposition A.1.4**, first part: if `g ∈ L²(ℝ)` is `α`-Hölder continuous at `t` (for some
`α > 0`), then the principal value `Hg(t) = lim_{ε↓0} H_ε g(t)` exists. -/
theorem tendsto_truncHilbert (hg : MemLp g 2) {α C t : ℝ} (hα : 0 < α)
    (hC : ∀ y, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) :
    Tendsto (fun ε => truncHilbert ε g t) (𝓝[>] 0) (𝓝 (hilbertR g t)) := by
  have key : Tendsto (fun ε => truncHilbert ε g t) (𝓝[>] 0) (𝓝 (hilbertPV g t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun ε : ℝ => (1 / π) * (2 * |C| * (ε ^ α / α))) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_rpow_nhdsGT_zero hα).div_const α).const_mul (2 * |C|) |>.const_mul (1 / π)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_ hlim
    filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    refine (norm_truncHilbert_sub_le hg hα hC hε.1 hε.2).trans ?_
    gcongr
    · exact div_nonneg (Real.rpow_nonneg hε.1.le _) hα.le
    · exact le_abs_self C
  rwa [hilbertR, key.limUnder_eq]

/-- The explicit formula `Hg(t) = π⁻¹ (∫_{|x|>1} g(t-x)/x dx + ∫_0^1 (g(t-x) - g(t+x))/x dx)`. -/
theorem hilbertR_eq (hg : MemLp g 2) {α C t : ℝ} (hα : 0 < α)
    (hC : ∀ y, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) : hilbertR g t = hilbertPV g t := by
  have key : Tendsto (fun ε => truncHilbert ε g t) (𝓝[>] 0) (𝓝 (hilbertPV g t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun ε : ℝ => (1 / π) * (2 * |C| * (ε ^ α / α))) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_rpow_nhdsGT_zero hα).div_const α).const_mul (2 * |C|) |>.const_mul (1 / π)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_ hlim
    filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    refine (norm_truncHilbert_sub_le hg hα hC hε.1 hε.2).trans ?_
    gcongr
    · exact div_nonneg (Real.rpow_nonneg hε.1.le _) hα.le
    · exact le_abs_self C
  rw [hilbertR, key.limUnder_eq]

/-- **Proposition A.1.4**, second part: if `g ∈ L²(ℝ)` is uniformly `α`-Hölder continuous, then
`H_ε g → Hg` uniformly on `ℝ`. -/
theorem tendstoUniformly_truncHilbert (hg : MemLp g 2) {α C : ℝ} (hα : 0 < α)
    (hC : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) :
    TendstoUniformly (fun ε t => truncHilbert ε g t) (hilbertR g) (𝓝[>] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  have hlim : Tendsto (fun ε : ℝ => (1 / π) * (2 * |C| * (ε ^ α / α))) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_rpow_nhdsGT_zero hα).div_const α).const_mul (2 * |C|) |>.const_mul (1 / π)
    simpa using this
  filter_upwards [Ioc_mem_nhdsGT one_pos, hlim.eventually (gt_mem_nhds hδ)] with ε hε hε' t
  rw [hilbertR_eq hg hα (hC · t), dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt ((norm_truncHilbert_sub_le hg hα (hC · t) hε.1 hε.2).trans ?_) hε'
  gcongr
  · exact div_nonneg (Real.rpow_nonneg hε.1.le _) hα.le
  · exact le_abs_self C

end HilbertLine

/-! ### Proposition A.1.5 and Theorem A.1.6 (recorded as statements) -/

section HilbertStatements

open FourierTransform SchwartzMap

/-- **Proposition A.1.5**: the Hilbert transform extends to a unitary operator `U` on `L²(ℝ)`
with `U² = -1`, agreeing with the principal value `hilbertR` on Schwartz functions, and acting
on the Fourier side as multiplication by `-i sgn(ξ)` (cf. (4.6.18); with the book's convention
`ĝ(t) = ∫ e^{-2πixt} g(x) dx` this is the correct sign). -/
def HilbertL2Statement : Prop :=
  ∃ U : Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2,
    (∀ g : 𝓢(ℝ, ℂ), ∀ᵐ t, (U (g.toLp 2)) t = hilbertR g t) ∧
    (∀ f, U (U f) = -f) ∧
    (∀ f : Lp (α := ℝ) ℂ 2, ∀ᵐ ξ,
      ((𝓕 (U f) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) ξ =
        -Complex.I * (Real.sign ξ : ℂ) * ((𝓕 f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) ξ)

/-- **Theorem A.1.6 (Plemelj–Privalov)**: if `g ∈ L²(ℝ)` is uniformly `α`-Hölder continuous
(at scales `≤ 1`) for some `0 < α < 1`, then so is `Hg`.  The book proves it for compactly
supported `g` and leaves the general case as Exercise A.1.3. -/
def HolderHilbertStatement : Prop :=
  ∀ (g : ℝ → ℂ) (α C : ℝ), MemLp g 2 → 0 < α → α < 1 →
    (∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) →
    ∃ C' : ℝ, ∀ s t, |s - t| ≤ 1 → ‖hilbertR g s - hilbertR g t‖ ≤ C' * |s - t| ^ α

/-- Theorem A.1.6, second sentence, deduced from the first: Lipschitz `g ∈ L²(ℝ)` have
`α`-Hölder continuous Hilbert transforms for every `α < 1`. -/
theorem holder_hilbertR_of_lipschitz (hH : HolderHilbertStatement) {g : ℝ → ℂ} (hg : MemLp g 2)
    {L : ℝ} (hL : ∀ y t, ‖g y - g t‖ ≤ L * |y - t|) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C' : ℝ, ∀ s t, |s - t| ≤ 1 → ‖hilbertR g s - hilbertR g t‖ ≤ C' * |s - t| ^ α := by
  refine hH g α |L| hg hα hα1 fun y t hyt => (hL y t).trans ?_
  have h1 : |y - t| ≤ |y - t| ^ α := by
    rcases eq_or_lt_of_le (abs_nonneg (y - t)) with h | h
    · rw [← h, Real.zero_rpow hα.ne']
    · calc |y - t| = |y - t| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |y - t| ^ α := Real.rpow_le_rpow_of_exponent_ge h hyt hα1.le
  calc L * |y - t| ≤ |L| * |y - t| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
    _ ≤ |L| * |y - t| ^ α := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)

end HilbertStatements

end DF
