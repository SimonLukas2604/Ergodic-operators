/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.7 (third part)  Gilbert–Pearson subordinacy theory  (book pp. 180–193)

## Main definitions
* `DF.schrDecT V t = schrDec V - t ⟨δ₁, ·⟩ δ₁` — the half-line operator `H⁺_θ` of (2.7.34) with
  `t = tan θ` (realized, like `DF.schrDec`, as `H⁺_θ ⊕ H⁻` on `ℓ²(ℤ)`), and its canonical
  spectral measure `DF.muTheta V hV t` (the spectral measure of `δ₁`).
* `DF.muPlus V hV` (`t = 0`) and `DF.muMinus V hV = muPlus (reflV V)`: canonical spectral measures
  of the right and (via the reflection `n ↦ 1 - n`) left half-line operators.
* `DF.subSet V E`, `DF.NPlus V`, `DF.NMinus V`: the sets `S`, `N₊`, `N₋` of Theorems 2.7.10–2.7.11.
* `DF.acPart μ = Leb.withDensity (dμ/dLeb)` and `DF.IsEssSupport ν S` (essential supports).

## Main results
* **Lemma 2.7.1**: `DF.M0_eq` (`M₀ = m₋ / (1 - m₊ m₋)`), `DF.M1_eq` (`M₁ = m₊ / (1 - m₊ m₋)`),
  `DF.borelTransform_canonical` ((2.7.5): `M = (m₊ + m₋)/(1 - m₊ m₋)`), and the algebraic
  identity (2.7.4) for the imaginary part, `DF.im_M_formula`.
* (2.7.35): `DF.borelTransform_muTheta` — `F_θ = m₊ / (1 - tan θ · m₊)`.
* **Theorem 2.7.10**: `DF.singularPart_muTheta_compl` ((a)) and `DF.isEssSupport_NPlus_muTheta`
  ((b)).
* **Theorem 2.7.11(b)** and **Corollary 2.7.12(c)**: `DF.isEssSupport_N_canonical` —
  `N = N₊ ∪ N₋` is an essential support of `μ_ac`.
* **Proposition 2.9.1**, (2.9.2): `DF.ess_support_union` — `Σ_ac(H) = Σ_ac(H₊) ∪ Σ_ac(H₋)` up to
  Lebesgue-null sets.

## Deviations
* Lebesgue-a.e. existence of boundary values of `m±` and `M` comes from Theorem 1.9.4 (a), (d)
  (`DF.ae_tendsto_im_volume`, `DF.reBoundaryValueStatement_holds`).
* The left half-line operator `H₋` is represented through the reflected potential: `μ₋` is the
  canonical spectral measure of the right half-line operator of `n ↦ V(1 - n)` (unitarily
  equivalent to `H₋` with cyclic vector `δ₀`); its Borel transform is `m₋`
  (`DF.mMinus_eq_mPlus_reflV`).
-/
import DamanikFillman.Ch2.Subordinacy
import DamanikFillman.Ch2.GenEigenSupport
import DamanikFillman.Ch1.BorelHerglotz

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 MeasureTheory Filter Topology Complex Set

namespace DF

variable {V : ℤ → ℝ}

/-! ### Essential supports -/

/-- The absolutely continuous part `μ_ac = (dμ/dE) dE` (Lebesgue decomposition). -/
def acPart (μ : Measure ℝ) : Measure ℝ := volume.withDensity (μ.rnDeriv volume)

/-- `S` is a (Lebesgue) essential support of the measure `ν`: `ν(ℝ \ S) = 0` and
`Leb(S \ A) = 0` for every support `A` of `ν`. -/
def IsEssSupport (ν : Measure ℝ) (S : Set ℝ) : Prop :=
  ν Sᶜ = 0 ∧ ∀ A : Set ℝ, ν Aᶜ = 0 → volume (S \ A) = 0

/-- Two essential supports of the same measure agree up to Lebesgue-null sets. -/
lemma IsEssSupport.volume_diff {ν : Measure ℝ} {S T : Set ℝ} (hS : IsEssSupport ν S)
    (hT : IsEssSupport ν T) : volume (S \ T) = 0 :=
  hS.2 T hT.1

/-- Theorem 1.9.4(b) in the language of essential supports. -/
lemma isEssSupport_imBoundaryPosSet (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsEssSupport (acPart μ) (imBoundaryPosSet μ) :=
  ⟨acPart_compl_imBoundaryPosSet μ, fun _ hA => volume_imBoundaryPosSet_diff μ hA⟩

/-- Transfer of an essential support along a set agreeing a.e. on a conull set `G`. -/
lemma isEssSupport_of_eqOn (μ : Measure ℝ) [IsFiniteMeasure μ] {S G : Set ℝ}
    (hG : volume Gᶜ = 0) (h : ∀ E ∈ G, E ∈ S ↔ E ∈ imBoundaryPosSet μ) :
    IsEssSupport (acPart μ) S := by
  have hac : acPart μ Gᶜ = 0 := withDensity_absolutelyContinuous _ _ hG
  obtain ⟨h1, h2⟩ := isEssSupport_imBoundaryPosSet μ
  refine ⟨measure_mono_null ?_ (measure_union_null hac h1), fun A hA => ?_⟩
  · intro E hE
    by_cases hEG : E ∈ G
    · exact Or.inr fun hc => hE ((h E hEG).2 hc)
    · exact Or.inl hEG
  · refine measure_mono_null ?_ (measure_union_null hG (h2 A hA))
    rintro E ⟨hES, hEA⟩
    by_cases hEG : E ∈ G
    · exact Or.inr ⟨(h E hEG).1 hES, hEA⟩
    · exact Or.inl hEG

/-! ### Boundary values of Borel transforms -/

/-- Theorem 1.9.4(a), (d): for Lebesgue-a.e. `E`, `F_μ(E + iε)` has a finite limit. -/
theorem ae_tendsto_borelTransform (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ (E : ℝ) ∂volume, ∃ w : ℂ,
      Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w) := by
  filter_upwards [ae_tendsto_im_volume μ, reBoundaryValueStatement_holds μ inferInstance]
    with E him ⟨y, hre⟩
  refine ⟨y + (Real.pi * (μ.rnDeriv volume E).toReal : ℝ) * I, ?_⟩
  have h1 := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const I)
  refine h1.congr fun ε => ?_
  simp only [Function.comp_apply]
  exact Complex.re_add_im _

lemma volume_not_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] :
    volume {E : ℝ | ¬ ∃ w : ℂ,
      Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w)} = 0 := by
  have := ae_tendsto_borelTransform μ
  rwa [ae_iff] at this

lemma im_nonneg_of_tendsto {f : ℝ → ℂ} {w : ℂ} (hf : Tendsto f (𝓝[>] 0) (𝓝 w))
    (hpos : ∀ ε : ℝ, 0 < ε → 0 < (f ε).im) : 0 ≤ w.im := by
  have := (Complex.continuous_im.tendsto w).comp hf
  refine ge_of_tendsto this ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (hpos ε hε).le

/-- If `m(E + iε)` has a finite limit `w`, then (2.7.10) has no solution subordinate at `+∞`
iff `Im w > 0` (Corollary 2.7.9(c)). -/
lemma notMem_subordinate_iff (hV : BddPot V) {E : ℝ} {w : ℂ}
    (hw : Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 w)) :
    (¬ ∃ u, IsSubordinate V E u) ↔ 0 < w.im := by
  have hw0 : 0 ≤ w.im := im_nonneg_of_tendsto hw fun ε hε => im_mPlus_pos hV hε
  rw [exists_subordinate_iff hV E]
  constructor
  · intro h
    rcases hw0.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply h; right
      refine ⟨w.re, ?_⟩
      have : (w.re : ℂ) = w := Complex.ext (by simp) (by simp [h'])
      rwa [this]
  · rintro hpos (h | ⟨x, hx⟩)
    · exact not_tendsto_atTop_of_tendsto_nhds hw.norm h
    · have := tendsto_nhds_unique hw hx
      rw [this] at hpos; simp at hpos

/-! ### Lemma 2.7.1 -/

/-- **Lemma 2.7.1**, (2.7.3): `M₀(z) = ⟨δ₀, (H - z)⁻¹ δ₀⟩ = m₋ / (1 - m₊ m₋)`. -/
theorem M0_eq (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪dlt 0, res (schr V) z (dlt 0)⟫_ℂ = mMinus V z / (1 - mPlus V z * mMinus V z) := by
  have hzr := mem_resolventSet_of_im hV hz
  obtain ⟨um, hum, hum0, hum2⟩ := exists_weyl_bot hV hzr
  obtain ⟨up, hup, hup0, hup2⟩ := exists_weyl_top hV hzr
  have hW := wronskian_weyl_ne_zero hV hzr hum hup hum0 hup0 hum2 hup2
  simp only [wronskian, zero_add] at hW
  obtain ⟨hu0, hmp, -⟩ := mPlus_eq hz hup hup0 hup2
  obtain ⟨hu1, hmm, -⟩ := mMinus_eq hz hum hum0 hum2
  rw [green_eq hV hzr hum hup hum0 hup0 hum2 hup2, hmp, hmm]
  simp only [min_self, max_self]
  have hden : (1 - -up 1 / up 0 * (-um 0 / um 1)) = (up 0 * um 1 - um 0 * up 1) / (up 0 * um 1) := by
    field_simp; try ring
  have h2 : up 0 * um 1 - um 0 * up 1 ≠ 0 := by
    intro h; apply hW; linear_combination -h
  have hne : (1 - -up 1 / up 0 * (-um 0 / um 1)) ≠ 0 := by
    rw [hden]; exact div_ne_zero h2 (mul_ne_zero hu0 hu1)
  have h3 : up 1 * um 0 - um 1 * up 0 ≠ 0 := by
    intro h; apply hW; linear_combination h
  rw [eq_div_iff hne]
  field_simp
  try ring

/-- **Lemma 2.7.1**, (2.7.3): `M₁(z) = ⟨δ₁, (H - z)⁻¹ δ₁⟩ = m₊ / (1 - m₊ m₋)`. -/
theorem M1_eq (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪dlt 1, res (schr V) z (dlt 1)⟫_ℂ = mPlus V z / (1 - mPlus V z * mMinus V z) := by
  have hzr := mem_resolventSet_of_im hV hz
  obtain ⟨um, hum, hum0, hum2⟩ := exists_weyl_bot hV hzr
  obtain ⟨up, hup, hup0, hup2⟩ := exists_weyl_top hV hzr
  have hW := wronskian_weyl_ne_zero hV hzr hum hup hum0 hup0 hum2 hup2
  simp only [wronskian, zero_add] at hW
  obtain ⟨hu0, hmp, -⟩ := mPlus_eq hz hup hup0 hup2
  obtain ⟨hu1, hmm, -⟩ := mMinus_eq hz hum hum0 hum2
  rw [green_eq hV hzr hum hup hum0 hup0 hum2 hup2, hmp, hmm]
  simp only [min_self, max_self]
  have hden : (1 - -up 1 / up 0 * (-um 0 / um 1)) = (up 0 * um 1 - um 0 * up 1) / (up 0 * um 1) := by
    field_simp; try ring
  have h2 : up 0 * um 1 - um 0 * up 1 ≠ 0 := by
    intro h; apply hW; linear_combination -h
  have hne : (1 - -up 1 / up 0 * (-um 0 / um 1)) ≠ 0 := by
    rw [hden]; exact div_ne_zero h2 (mul_ne_zero hu0 hu1)
  have h3 : up 1 * um 0 - um 1 * up 0 ≠ 0 := by
    intro h; apply hW; linear_combination h
  rw [eq_div_iff hne]
  field_simp
  try ring

/-- `1 - m₊ m₋ ≠ 0` off the real axis. -/
lemma one_sub_mPlus_mMinus_ne_zero (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    1 - mPlus V z * mMinus V z ≠ 0 := by
  have hzr := mem_resolventSet_of_im hV hz
  obtain ⟨um, hum, hum0, hum2⟩ := exists_weyl_bot hV hzr
  obtain ⟨up, hup, hup0, hup2⟩ := exists_weyl_top hV hzr
  have hW := wronskian_weyl_ne_zero hV hzr hum hup hum0 hup0 hum2 hup2
  simp only [wronskian, zero_add] at hW
  obtain ⟨hu0, hmp, -⟩ := mPlus_eq hz hup hup0 hup2
  obtain ⟨hu1, hmm, -⟩ := mMinus_eq hz hum hum0 hum2
  rw [hmp, hmm]
  intro h
  apply hW
  field_simp at h
  linear_combination -h

/-- (2.7.4)/(2.7.5): `Im((p + q)/(1 - p q)) = (Im p (1 + |q|²) + Im q (1 + |p|²)) / |1 - p q|²`. -/
lemma im_M_formula (p q : ℂ) :
    ((p + q) / (1 - p * q)).im =
      (p.im * (1 + normSq q) + q.im * (1 + normSq p)) / normSq (1 - p * q) := by
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp only [Complex.add_im, Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- The canonical spectral measure is finite. -/
instance (hV : BddPot V) : IsFiniteMeasure (canonicalMeasure V hV) := by
  unfold canonicalMeasure; infer_instance

/-- (2.7.5): `M(z) = (m₊(z) + m₋(z)) / (1 - m₊(z) m₋(z))`, `M` the Borel transform of the
canonical spectral measure. -/
theorem borelTransform_canonical (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    borelTransform (canonicalMeasure V hV) z =
      (mPlus V z + mMinus V z) / (1 - mPlus V z * mMinus V z) := by
  rw [canonicalMeasure, borelTransform_add _ _ hz, borelTransform, borelTransform,
    ← inner_resolvent_eq_integral _ _ _ hz, ← inner_resolvent_eq_integral _ _ _ hz]
  have h0 := M0_eq hV hz
  have h1 := M1_eq hV hz
  rw [res] at h0 h1
  rw [h0, h1, ← add_div, add_comm]

/-! ### Half-line operators with boundary condition `θ` -/

lemma isSelfAdjoint_rankOne_dlt (n : ℤ) : IsSelfAdjoint (rankOneOp (dlt n)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, rankOneOp_apply, inner_smul_left, inner_smul_right,
    inner_dlt]
  have r : ⟪x, dlt n⟫_ℂ = conj (x n) := by rw [← inner_conj_symm, inner_dlt]
  rw [r]; ring

/-- `H⁺_θ ⊕ H⁻ = H₊ ⊕ H₋ - t ⟨δ₁, ·⟩ δ₁` with `t = tan θ` (2.7.34). -/
def schrDecT (V : ℤ → ℝ) (t : ℝ) : Op := schrDec V - ((t : ℝ) : ℂ) • rankOneOp (dlt 1)

lemma isSelfAdjoint_schrDecT (hV : BddPot V) (t : ℝ) : IsSelfAdjoint (schrDecT V t) := by
  have hR : IsSelfAdjoint (((t : ℝ) : ℂ) • rankOneOp (dlt 1)) := by
    have h := isSelfAdjoint_rankOne_dlt 1
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h ⊢
    intro x y
    simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    rw [h x y]
  exact (isSelfAdjoint_schrDec hV).sub hR

/-- The canonical spectral measure `μ⁺_θ` of `H⁺_θ` (spectral measure of `δ₁`), `t = tan θ`. -/
def muTheta (V : ℤ → ℝ) (hV : BddPot V) (t : ℝ) : Measure ℝ :=
  spectralMeasure (schrDecT V t) (isSelfAdjoint_schrDecT hV t) (dlt 1)

instance (hV : BddPot V) (t : ℝ) : IsFiniteMeasure (muTheta V hV t) := by
  unfold muTheta; infer_instance

/-- The canonical spectral measure of the right half-line operator `H₊` (Dirichlet). -/
def muPlus (V : ℤ → ℝ) (hV : BddPot V) : Measure ℝ :=
  spectralMeasure (schrDec V) (isSelfAdjoint_schrDec hV) (dlt 1)

instance (hV : BddPot V) : IsFiniteMeasure (muPlus V hV) := by
  unfold muPlus; infer_instance

/-- The canonical spectral measure of the left half-line operator `H₋`, through reflection. -/
def muMinus (V : ℤ → ℝ) (hV : BddPot V) : Measure ℝ := muPlus (reflV V) (bddPot_reflV hV)

instance (hV : BddPot V) : IsFiniteMeasure (muMinus V hV) := by
  unfold muMinus; infer_instance

lemma mPlus_eq_borelTransform (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    mPlus V z = borelTransform (muPlus V hV) z := by
  rw [← mHalf_eq_mPlus hV hz, mHalf_eq_integral hV hz]; rfl

lemma mMinus_eq_borelTransform (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    mMinus V z = borelTransform (muMinus V hV) z := by
  rw [mMinus_eq_mPlus_reflV hV hz, mPlus_eq_borelTransform (bddPot_reflV hV) hz]; rfl

lemma mem_resolventSet_of_sa {A : Op} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ A := by
  rw [mem_resolventSet_iff_notMem]
  intro h
  have := hA.mem_spectrum_eq_re h
  apply hz; rw [this]; simp

/-- (2.7.35) (Lemma 1.9.8): `F_θ(z) = m₊(z) / (1 - tan θ · m₊(z))`. -/
theorem borelTransform_muTheta (hV : BddPot V) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    borelTransform (muTheta V hV t) z = mPlus V z / (1 - t * mPlus V z) := by
  have hA := isSelfAdjoint_schrDec hV
  have hAt := isSelfAdjoint_schrDecT hV t
  have h1 := mem_resolventSet_of_sa hA hz
  have h2 := mem_resolventSet_of_sa hAt hz
  have hal : algebraMap ℂ Op z = z • (1 : Op) := Algebra.algebraMap_eq_smul_one z
  have hR : res (schrDec V) z ∘L (schrDec V - z • (1 : Op)) = 1 := by
    have := res_mul_sub h1; rw [hal] at this; exact this
  have hT : schrDecT V t = schrDec V + ((-t : ℝ) : ℂ) • rankOneOp (dlt 1) := by
    rw [schrDecT]; push_cast; rw [neg_smul, sub_eq_add_neg]
  have hRl : (schrDec V + ((-t : ℝ) : ℂ) • rankOneOp (dlt 1) - z • (1 : Op)) ∘L
      res (schrDecT V t) z = 1 := by
    have := sub_mul_res h2; rw [hal] at this; rw [← hT]; exact this
  have key := rankOne_borel (schrDec V) (dlt 1) (-t) z _ _ hR hRl
  unfold muTheta borelTransform
  rw [← inner_resolvent_eq_integral _ _ _ hz]
  change ⟪dlt 1, res (schrDecT V t) z (dlt 1)⟫_ℂ = _
  rw [key, ← mHalf_eq_mPlus hV hz, mHalf]
  push_cast; ring_nf

/-! ### Theorem 2.7.10 -/

/-- The set `Sp,θ` of Theorem 2.7.10(a): energies at which `u_{1,θ}` is subordinate at `+∞`. -/
def subSetTheta (V : ℤ → ℝ) (θ : ℝ) : Set ℝ :=
  {E | IsSubordinate V E (solAB V E (Real.cos θ) (-Real.sin θ))}

/-- `N₊`: energies at which (2.7.10) has no solution subordinate at `+∞`. -/
def NPlus (V : ℤ → ℝ) : Set ℝ := {E | ¬ ∃ u, IsSubordinate V E u}

/-- `N₋`: energies at which (2.7.10) has no solution subordinate at `-∞`. -/
def NMinus (V : ℤ → ℝ) : Set ℝ := {E | ¬ ∃ u, IsSubordinateBot V E u}

lemma NMinus_eq (V : ℤ → ℝ) : NMinus V = NPlus (reflV V) := by
  ext E; simp only [NMinus, NPlus, mem_ofPred_eq, exists_subordinateBot_iff']

lemma hz_of_pos {E ε : ℝ} (hε : 0 < ε) : (E + ε * I : ℂ).im ≠ 0 := by simp [hε.ne']

lemma mPlus_ne_zero (hV : BddPot V) {E ε : ℝ} (hε : 0 < ε) : mPlus V (E + ε * I) ≠ 0 := by
  intro h; have := im_mPlus_pos hV (E := E) hε; rw [h] at this; simp at this

lemma one_sub_mul_mPlus_ne_zero (hV : BddPot V) (t : ℝ) {E ε : ℝ} (hε : 0 < ε) :
    1 - (t : ℂ) * mPlus V (E + ε * I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_sub, Complex.zero_im, neg_eq_zero] at him
  have hpos := im_mPlus_pos hV (E := E) hε
  have ht : t = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · linarith
  subst ht; simp at h

lemma alg_mTheta (m c s : ℂ) (hm : m ≠ 0) (hc : c ≠ 0) (hd : 1 - s / c * m ≠ 0)
    (hd2 : c - s * m ≠ 0) :
    m / (1 - s / c * m) * (1 + s / c * m⁻¹) = (c * m + s) / (c - s * m) := by
  field_simp
  ring

/-- **Theorem 2.7.10(a)**: for `θ ∈ (-π/2, π/2)`, the singular part of `μ⁺_θ` is supported by
`Sp,θ = {E : u_{1,θ} is subordinate at +∞}`. -/
theorem singularPart_muTheta_compl (hV : BddPot V) {θ : ℝ}
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (muTheta V hV (Real.tan θ)).singularPart volume (subSetTheta V θ)ᶜ = 0 := by
  refine measure_mono_null ?_ (singularPart_not_tendsto_atTop (muTheta V hV (Real.tan θ)))
  intro E hE hF
  apply hE
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hab : Real.cos θ ^ 2 + (-Real.sin θ) ^ 2 = 1 := by
    rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ
  rw [subSetTheta, mem_ofPred_eq, isSubordinate_solAB_iff hV hab E]
  set t := Real.tan θ
  set μ := muTheta V hV t
  have hFn : Tendsto (fun ε : ℝ => ‖borelTransform μ (E + ε * I)‖) (𝓝[>] 0) atTop :=
    tendsto_atTop_mono (fun ε => (le_abs_self _).trans (Complex.abs_im_le_norm _)) hF
  have hFinv : Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hFn.inv_tendsto_atTop.congr fun ε => ?_
    simp [norm_inv]
  have hminv : Tendsto (fun ε : ℝ => (mPlus V (E + ε * I))⁻¹) (𝓝[>] 0) (𝓝 (0 + t)) := by
    refine (hFinv.add_const (t : ℂ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [borelTransform_muTheta hV t (hz_of_pos hε)]
    have hm0 := mPlus_ne_zero hV (E := E) hε
    have hd := one_sub_mul_mPlus_ne_zero hV t (E := E) hε
    rw [inv_div]; field_simp; try ring
  have hfac : Tendsto (fun ε : ℝ => ‖1 + (t : ℂ) * (mPlus V (E + ε * I))⁻¹‖) (𝓝[>] 0)
      (𝓝 ‖1 + (t : ℂ) * (0 + t)‖) := ((hminv.const_mul _).const_add 1).norm
  have hpos : 0 < ‖1 + (t : ℂ) * (0 + t)‖ := by
    rw [zero_add, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real]
    have : 0 < 1 + t * t := by nlinarith [mul_self_nonneg t]
    rw [Real.norm_eq_abs, abs_of_pos this]; exact this
  have := hFn.atTop_mul_pos hpos hfac
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← norm_mul, borelTransform_muTheta hV t (hz_of_pos hε)]
  congr 1
  have hm0 := mPlus_ne_zero hV (E := E) hε
  have hd := one_sub_mul_mPlus_ne_zero hV t (E := E) hε
  have hd2 := add_mul_mPlus_ne_zero hV hab (E := E) hε
  have hc' : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht : (t : ℂ) = Real.sin θ / Real.cos θ := by
    simp only [t, Real.tan_eq_sin_div_cos]; push_cast; rfl
  rw [ht] at hd ⊢
  rw [alg_mTheta _ _ _ hm0 hc' hd (by rw [Complex.ofReal_neg] at hd2; intro h; apply hd2; linear_combination h)]
  unfold mAB
  rw [Complex.ofReal_neg]
  congr 1 <;> ring

lemma mem_imBoundaryPosSet_iff {μ : Measure ℝ} {E : ℝ} {W : ℂ}
    (hW : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 W)) :
    E ∈ imBoundaryPosSet μ ↔ 0 < W.im := by
  have h := (Complex.continuous_im.tendsto W).comp hW
  constructor
  · rintro ⟨y, hy, hEy⟩
    rw [tendsto_nhds_unique h hEy]; exact hy
  · intro hpos; exact ⟨W.im, hpos, h⟩

/-- Theorem 2.7.10(b), abstract form: if `F_ν = m₊ / (1 - t m₊)` on the upper half-plane, then
`N₊` is an essential support of `ν_ac`. -/
theorem isEssSupport_NPlus_of_borel (hV : BddPot V) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (t : ℝ) (hν : ∀ (E ε : ℝ), 0 < ε →
      borelTransform ν (E + ε * I) = mPlus V (E + ε * I) / (1 - t * mPlus V (E + ε * I))) :
    IsEssSupport (acPart ν) (NPlus V) := by
  set G : Set ℝ := {E | (∃ w : ℂ, Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 w)) ∧
    ∃ W : ℂ, Tendsto (fun ε : ℝ => borelTransform ν (E + ε * I)) (𝓝[>] 0) (𝓝 W)}
  have hG : volume Gᶜ = 0 := by
    refine measure_mono_null ?_ (measure_union_null (volume_not_tendsto (muPlus V hV))
      (volume_not_tendsto ν))
    intro E hE
    simp only [G, mem_compl_iff, mem_ofPred_eq, not_and_or] at hE
    rcases hE with h | h
    · left; intro ⟨w, hw⟩; apply h; refine ⟨w, hw.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (mPlus_eq_borelTransform hV (hz_of_pos hε)).symm
    · right; exact h
  refine isEssSupport_of_eqOn ν hG fun E ⟨⟨w, hw⟩, ⟨W, hW⟩⟩ => ?_
  rw [mem_imBoundaryPosSet_iff hW]
  change (¬ ∃ u, IsSubordinate V E u) ↔ _
  rw [notMem_subordinate_iff hV hw]
  -- `m = F (1 - t m)` gives `1 - t w ≠ 0` and `W = w / (1 - t w)`
  have hlim : Tendsto (fun ε : ℝ => borelTransform ν (E + ε * I) * (1 - t * mPlus V (E + ε * I)))
      (𝓝[>] 0) (𝓝 (W * (1 - t * w))) := hW.mul (tendsto_const_nhds.sub (hw.const_mul _))
  have hlim' : Tendsto (fun ε : ℝ => borelTransform ν (E + ε * I) * (1 - t * mPlus V (E + ε * I)))
      (𝓝[>] 0) (𝓝 w) := by
    refine hw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [hν E ε hε, div_mul_cancel₀ _ (one_sub_mul_mPlus_ne_zero hV t hε)]
  have hwW := tendsto_nhds_unique hlim' hlim
  have hd : 1 - (t : ℂ) * w ≠ 0 := by
    intro h; rw [h, mul_zero] at hwW; rw [hwW, mul_zero, sub_zero] at h; exact one_ne_zero h
  have hd' : 1 + ((-t : ℝ) : ℂ) * w ≠ 0 := by push_cast; rwa [neg_mul, ← sub_eq_add_neg]
  have hW' : W = w / (1 + ((-t : ℝ) : ℂ) * w) := by
    rw [eq_div_iff hd']; push_cast; linear_combination -hwW
  rw [hW', im_div_one_add_mul]
  have hns : 0 < Complex.normSq (1 + ((-t : ℝ) : ℂ) * w) := by
    apply Complex.normSq_pos.2; push_cast; rwa [neg_mul, ← sub_eq_add_neg]
  exact (div_pos_iff_of_pos_right hns).symm

/-- **Theorem 2.7.10(b)**: `N₊` is an essential support of `(μ⁺_θ)_ac` (`t = tan θ`; in fact
for every real `t`). -/
theorem isEssSupport_NPlus_muTheta (hV : BddPot V) (t : ℝ) :
    IsEssSupport (acPart (muTheta V hV t)) (NPlus V) :=
  isEssSupport_NPlus_of_borel hV _ t fun _ _ hε => borelTransform_muTheta hV t (hz_of_pos hε)

/-- `N₊` is an essential support of `(μ₊)_ac` (Dirichlet half-line). -/
theorem isEssSupport_NPlus_muPlus (hV : BddPot V) :
    IsEssSupport (acPart (muPlus V hV)) (NPlus V) :=
  isEssSupport_NPlus_of_borel hV _ 0 fun _ _ hε => by
    rw [← mPlus_eq_borelTransform hV (hz_of_pos hε)]; simp

/-- `N₋` is an essential support of `(μ₋)_ac` (left half-line). -/
theorem isEssSupport_NMinus_muMinus (hV : BddPot V) :
    IsEssSupport (acPart (muMinus V hV)) (NMinus V) := by
  rw [NMinus_eq]; exact isEssSupport_NPlus_muPlus (bddPot_reflV hV)

/-! ### Theorem 2.7.11(b) -/

lemma notMem_subordinateBot_iff (hV : BddPot V) {E : ℝ} {w : ℂ}
    (hw : Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 w)) :
    (¬ ∃ u, IsSubordinateBot V E u) ↔ 0 < w.im := by
  rw [exists_subordinateBot_iff']
  exact notMem_subordinate_iff (bddPot_reflV hV)
    ((tendsto_congr' (mMinus_eventuallyEq hV E)).2 hw)

lemma im_mMinus_pos (hV : BddPot V) {E ε : ℝ} (hε : 0 < ε) :
    0 < (mMinus V (E + ε * I)).im := by
  rw [mMinus_eq_mPlus_reflV hV (hz_of_pos hε)]; exact im_mPlus_pos (bddPot_reflV hV) hε

/-- **Theorem 2.7.11(b)** (and Corollary 2.7.12(c)): `N = N₊ ∪ N₋` is an essential support of the
absolutely continuous part of the canonical spectral measure `μ` of `H`. -/
theorem isEssSupport_N_canonical (hV : BddPot V) :
    IsEssSupport (acPart (canonicalMeasure V hV)) (NPlus V ∪ NMinus V) := by
  set μ := canonicalMeasure V hV
  set G : Set ℝ := {E | (∃ w : ℂ, Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 w)) ∧
    (∃ w : ℂ, Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 w)) ∧
    ∃ W : ℂ, Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 W)}
  have hG : volume Gᶜ = 0 := by
    refine measure_mono_null ?_ (measure_union_null (volume_not_tendsto (muPlus V hV))
      (measure_union_null (volume_not_tendsto (muMinus V hV)) (volume_not_tendsto μ)))
    intro E hE
    simp only [G, mem_compl_iff, mem_ofPred_eq, not_and_or] at hE
    rcases hE with h | h | h
    · left; intro ⟨w, hw⟩; apply h; refine ⟨w, hw.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (mPlus_eq_borelTransform hV (hz_of_pos hε)).symm
    · right; left; intro ⟨w, hw⟩; apply h; refine ⟨w, hw.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (mMinus_eq_borelTransform hV (hz_of_pos hε)).symm
    · right; right; exact h
  refine isEssSupport_of_eqOn μ hG fun E ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, ⟨W, hW⟩⟩ => ?_
  rw [mem_imBoundaryPosSet_iff hW]
  change ((¬ ∃ u, IsSubordinate V E u) ∨ (¬ ∃ u, IsSubordinateBot V E u)) ↔ _
  rw [notMem_subordinate_iff hV hw₁, notMem_subordinateBot_iff hV hw₂]
  have h1 : 0 ≤ w₁.im := im_nonneg_of_tendsto hw₁ fun ε hε => im_mPlus_pos hV hε
  have h2 : 0 ≤ w₂.im := im_nonneg_of_tendsto hw₂ fun ε hε => im_mMinus_pos hV hε
  -- `M (1 - m₊ m₋) = m₊ + m₋`
  have hlim : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I) *
      (1 - mPlus V (E + ε * I) * mMinus V (E + ε * I))) (𝓝[>] 0) (𝓝 (W * (1 - w₁ * w₂))) :=
    hW.mul (tendsto_const_nhds.sub (hw₁.mul hw₂))
  have hlim' : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I) *
      (1 - mPlus V (E + ε * I) * mMinus V (E + ε * I))) (𝓝[>] 0) (𝓝 (w₁ + w₂)) := by
    refine (hw₁.add hw₂).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [borelTransform_canonical hV (hz_of_pos hε),
      div_mul_cancel₀ _ (one_sub_mPlus_mMinus_ne_zero hV (hz_of_pos hε))]
  have hwW := tendsto_nhds_unique hlim' hlim
  have hd : 1 - w₁ * w₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hwW
    have h2' : w₂ = -w₁ := by linear_combination hwW
    have him : w₁.im = 0 := by
      have := congrArg Complex.im h2'; simp at this; linarith
    have hre : w₁ = (w₁.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [h2', hre] at h
    have : (1 + (w₁.re : ℂ) ^ 2) = 0 := by linear_combination h
    have : (1 + w₁.re ^ 2 : ℝ) = 0 := by exact_mod_cast this
    nlinarith [sq_nonneg w₁.re]
  have hW' : W = (w₁ + w₂) / (1 - w₁ * w₂) := by rw [eq_div_iff hd, hwW]
  rw [hW', im_M_formula]
  have hns : 0 < Complex.normSq (1 - w₁ * w₂) := Complex.normSq_pos.2 hd
  rw [div_pos_iff_of_pos_right hns]
  have hq1 : 0 ≤ Complex.normSq w₁ := Complex.normSq_nonneg _
  have hq2 : 0 ≤ Complex.normSq w₂ := Complex.normSq_nonneg _
  constructor
  · rintro (h | h)
    · nlinarith
    · nlinarith
  · intro h
    by_contra hcon
    push Not at hcon
    have e1 : w₁.im = 0 := le_antisymm hcon.1 h1
    have e2 : w₂.im = 0 := le_antisymm hcon.2 h2
    rw [e1, e2] at h; simp at h

/-! ### Proposition 2.9.1 -/

/-- **Proposition 2.9.1**, (2.9.2): if `Σ`, `Σ₊`, `Σ₋` are essential supports of the absolutely
continuous parts of the canonical spectral measures of `H`, `H₊`, `H₋`, then
`Σ = Σ₊ ∪ Σ₋` up to Lebesgue-null sets. -/
theorem ess_support_union (hV : BddPot V) {S Sp Sm : Set ℝ}
    (hS : IsEssSupport (acPart (canonicalMeasure V hV)) S)
    (hSp : IsEssSupport (acPart (muPlus V hV)) Sp)
    (hSm : IsEssSupport (acPart (muMinus V hV)) Sm) :
    volume (S \ (Sp ∪ Sm)) = 0 ∧ volume ((Sp ∪ Sm) \ S) = 0 := by
  have hN := isEssSupport_N_canonical hV
  have hNp := isEssSupport_NPlus_muPlus hV
  have hNm := isEssSupport_NMinus_muMinus hV
  have a1 := hS.volume_diff hN
  have a2 := hNp.volume_diff hSp
  have a3 := hNm.volume_diff hSm
  have b1 := hN.volume_diff hS
  have b2 := hSp.volume_diff hNp
  have b3 := hSm.volume_diff hNm
  constructor
  · refine measure_mono_null ?_ (measure_union_null a1 (measure_union_null a2 a3))
    rintro E ⟨hE, hE'⟩
    simp only [mem_union, not_or] at hE'
    by_cases h : E ∈ NPlus V ∪ NMinus V
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨h, hE'.1⟩)
      · exact Or.inr (Or.inr ⟨h, hE'.2⟩)
    · exact Or.inl ⟨hE, h⟩
  · refine measure_mono_null ?_ (measure_union_null b1 (measure_union_null b2 b3))
    rintro E ⟨hE, hE'⟩
    rcases hE with h | h
    · by_cases h' : E ∈ NPlus V
      · exact Or.inl ⟨Or.inl h', hE'⟩
      · exact Or.inr (Or.inl ⟨h, h'⟩)
    · by_cases h' : E ∈ NMinus V
      · exact Or.inl ⟨Or.inr h', hE'⟩
      · exact Or.inr (Or.inr ⟨h, h'⟩)

end DF
