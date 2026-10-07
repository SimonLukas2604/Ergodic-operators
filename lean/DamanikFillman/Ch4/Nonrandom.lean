/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.2 Nonrandomness of the spectrum   (book pp. 309–314)

## Main definitions
* `DF.opTrace P = ∑ₙ ⟨δₙ, P δₙ⟩ ∈ [0, ∞]` — the trace of a (positive) operator on `ℓ²(ℤ)` in the
  standard basis (for orthogonal projections this is `dim Ran P`, Theorem 1.4.8);
* `DF.discreteSpectrum A` — the isolated points of `σ(A)` (for self-adjoint `A` these are the
  isolated eigenvalues; the book's `σ_disc` additionally requires finite multiplicity, so our
  set contains the book's);
* `E.asSpectrum` — the almost sure spectrum `Σ` (Theorem 4.2.4), defined explicitly through the
  rational intervals `J` with `P_ω(J) = 0` almost surely;
* `E.tr ω S = Tr P_ω(S) = ∑ₙ η_{ω,n}(S)`.

## Main results
* `E.ae_mem_iff_ae`, `E.ae_forall_mem_iff_ae` — the zero-one law for `T`-invariant events,
  in the form used throughout §4.2;
* `E.trace_dichotomy` — **Lemma 4.2.3**: for a weakly measurable covariant family `P_ω`
  (`P_{Tω} = U P_ω U*`), either `Tr P_ω = 0` a.s. or `Tr P_ω = ∞` a.s.  (No projection
  hypothesis is needed for this formulation in terms of the trace.)
* `E.ae_spectrum_eq` — **Theorem 4.2.4** (first part): `σ(H_ω) = Σ` for `μ`-a.e. `ω`;
* `E.ae_discreteSpectrum_eq_empty` — **Theorem 4.2.4** (second part): `σ_disc(H_ω) = ∅` a.s.;
* `E.measure_eigenvalue_eq_zero` — **(4.2.18)**: every fixed `E ∈ ℝ` is a.s. not an eigenvalue;
* generic spectral facts: `DF.mem_spectrum_iff_rat` (rational intervals suffice),
  `DF.specProj_eq_zero_of_subset`.

The ac/sc/pp parts (Theorem 4.2.6) are treated in `DamanikFillman/Ch4/SpectralTypes.lean`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.Setting

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology
open MeasureTheory Set Filter L2

namespace DF

/-! ### Generic facts on spectral projections -/

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

lemma specProj_eq_zero_of_subset {S S' : Set ℝ} (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (h : S' ⊆ S) (h0 : specProj A hA S = 0) : specProj A hA S' = 0 :=
  (specProj_eq_zero_iff hS').2 fun φ => measure_mono_null h ((specProj_eq_zero_iff hS).1 h0 φ)

/-- `x ∈ σ(A)` iff `P(a, b) ≠ 0` for all rational `a < x < b`. -/
theorem mem_spectrum_iff_rat (x : ℝ) :
    x ∈ spectrum ℝ A ↔ ∀ a b : ℚ, (a : ℝ) < x → x < b → specProj A hA (Ioo a b) ≠ 0 := by
  rw [mem_spectrum_iff_specProj (hA := hA)]
  constructor
  · intro h a b ha hb h0
    set ε := min (x - a) (b - x)
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    refine h ε hε (specProj_eq_zero_of_subset measurableSet_Ioo measurableSet_Ioo ?_ h0)
    intro y hy
    exact ⟨by linarith [hy.1, min_le_left (x - a) (b - x)],
      by linarith [hy.2, min_le_right (x - a) (b - x)]⟩
  · intro h ε hε h0
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    refine h a b ha2 hb1 (specProj_eq_zero_of_subset measurableSet_Ioo measurableSet_Ioo ?_ h0)
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The discrete spectrum, here: the isolated points of `σ(A)`. -/
def discreteSpectrum (A : H →L[ℂ] H) : Set ℝ :=
  {x ∈ spectrum ℝ A | ∃ ε > 0, spectrum ℝ A ∩ Ioo (x - ε) (x + ε) = {x}}

end Generic

/-! ### Operators on `ℓ²(ℤ)` -/

/-- A self-adjoint operator on `ℓ²(ℤ)` vanishing on all `δₙ` vanishes. -/
lemma op_eq_zero_of_dlt {P : Op} (hP : IsSelfAdjoint P) (h : ∀ n, P (dlt n) = 0) : P = 0 := by
  ext1 φ
  ext n
  rw [ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply, ← inner_dlt,
    ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hP.star_eq,
    h n, inner_zero_left]

/-- The trace `∑ₙ ⟨δₙ, P δₙ⟩` (truncated at `0`) of an operator on `ℓ²(ℤ)`. -/
def opTrace (P : Op) : ℝ≥0∞ := ∑' n : ℤ, ENNReal.ofReal (RCLike.re ⟪dlt n, P (dlt n)⟫_ℂ)

lemma inner_dlt_conj (P : Op) (m : ℤ) :
    ⟪dlt m, (shiftL * P * star shiftL) (dlt m)⟫_ℂ = ⟪dlt (m + 1), P (dlt (m + 1))⟫_ℂ := by
  rw [star_shiftL, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, shiftR_dlt,
    inner_dlt, inner_dlt, shiftL_apply]

lemma opTrace_conj (P : Op) : opTrace (shiftL * P * star shiftL) = opTrace P := by
  unfold opTrace
  simp_rw [inner_dlt_conj]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n => ENNReal.ofReal (RCLike.re ⟪dlt n, P (dlt n)⟫_ℂ))

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-! ### Zero-one law for invariant events -/

/-- A `T`-invariant measurable event has probability `0` or `1`. -/
lemma ae_or_ae_not {S : Set Ω} (hS : MeasurableSet S) (hinv : ∀ ω, E.T ω ∈ S ↔ ω ∈ S) :
    (∀ᵐ ω ∂E.μ, ω ∈ S) ∨ (∀ᵐ ω ∂E.μ, ω ∉ S) :=
  E.ergodic.toPreErgodic.ae_mem_or_ae_notMem hS.nullMeasurableSet
    (Eq.eventuallyEq (by ext ω; exact hinv ω))

/-- For a `T`-invariant measurable event `S`: for a.e. `ω`, `ω ∈ S` iff `S` holds a.s. -/
lemma ae_mem_iff_ae {S : Set Ω} (hS : MeasurableSet S) (hinv : ∀ ω, E.T ω ∈ S ↔ ω ∈ S) :
    ∀ᵐ ω ∂E.μ, (ω ∈ S ↔ ∀ᵐ ω' ∂E.μ, ω' ∈ S) := by
  rcases E.ae_or_ae_not hS hinv with h | h
  · filter_upwards [h] with ω hω
    exact ⟨fun _ => h, fun _ => hω⟩
  · filter_upwards [h] with ω hω
    refine ⟨fun h' => absurd h' hω, fun h' => ?_⟩
    obtain ⟨ω', h1, h2⟩ := (h.and h').exists
    exact absurd h2 h1

/-- Countable version of `ae_mem_iff_ae`. -/
lemma ae_forall_mem_iff_ae {ι : Type*} [Countable ι] (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hinv : ∀ i ω, E.T ω ∈ S i ↔ ω ∈ S i) :
    ∀ᵐ ω ∂E.μ, ∀ i, (ω ∈ S i ↔ ∀ᵐ ω' ∂E.μ, ω' ∈ S i) :=
  ae_all_iff.2 fun i => E.ae_mem_iff_ae (hS i) (hinv i)

/-! ### Spectral projections of `H_ω` -/

lemma proj_T {S : Set ℝ} (hS : MeasurableSet S) (ω : Ω) :
    E.proj (E.T ω) S = shiftL * E.proj ω S * star shiftL :=
  E.fc_T (isBddBorel_indicator hS) ω

lemma conj_eq_zero_iff (P : Op) : shiftL * P * star shiftL = 0 ↔ P = 0 := by
  have hu := shiftL_mem_unitary
  constructor
  · intro h
    have : star shiftL * (shiftL * P * star shiftL) * shiftL = P := by
      rw [← mul_assoc, ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul, mul_assoc,
        Unitary.star_mul_self_of_mem hu, mul_one]
    rw [← this, h, mul_zero, zero_mul]
  · rintro rfl; simp

lemma proj_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) (ω : Ω) :
    E.proj ω S = 0 ↔ ∀ n, E.spec ω (dlt n) S = 0 := by
  constructor
  · intro h n
    exact (specProj_eq_zero_iff hS).1 h _
  · intro h
    refine op_eq_zero_of_dlt (isSelfAdjoint_specProj hS) fun n => ?_
    exact (specProj_apply_eq_zero_iff hS _).2 (h n)

lemma proj_T_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) (ω : Ω) :
    E.proj (E.T ω) S = 0 ↔ E.proj ω S = 0 := by
  rw [E.proj_T hS, conj_eq_zero_iff]

lemma measurableSet_proj_eq_zero {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {ω | E.proj ω S = 0} := by
  simp_rw [E.proj_eq_zero_iff hS, setOf_forall]
  exact MeasurableSet.iInter fun n =>
    (E.measurable_spec_apply (dlt n) hS) (measurableSet_singleton 0)

/-! ### Theorem 4.2.4: the almost sure spectrum -/

/-- The **almost sure spectrum** `Σ` (Theorem 4.2.4): the set of `x` such that for all rational
`a < x < b`, the spectral projection `P_ω(a, b)` is not almost surely zero. -/
def asSpectrum : Set ℝ :=
  {x | ∀ a b : ℚ, (a : ℝ) < x → x < b → ¬ ∀ᵐ ω ∂E.μ, E.proj ω (Ioo a b) = 0}

/-- **Theorem 4.2.4** (first part): `σ(H_ω) = Σ` for `μ`-a.e. `ω`. -/
theorem ae_spectrum_eq : ∀ᵐ ω ∂E.μ, spectrum ℝ (E.H ω) = E.asSpectrum := by
  have h := E.ae_forall_mem_iff_ae (ι := ℚ × ℚ)
    (fun p => {ω | E.proj ω (Ioo p.1 p.2) = 0})
    (fun p => E.measurableSet_proj_eq_zero measurableSet_Ioo)
    (fun p ω => E.proj_T_eq_zero_iff measurableSet_Ioo ω)
  filter_upwards [h] with ω hω
  ext x
  refine (mem_spectrum_iff_rat (hA := E.isSelfAdjoint_H ω) x).trans ?_
  simp only [asSpectrum, mem_setOf_eq]
  refine forall₂_congr fun a b => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact not_congr (hω (a, b))

/-- `Σ` is the spectrum of `H_ω` for some (indeed almost every) `ω`; in particular it is a
compact subset of `[-2 - ‖f‖_∞, 2 + ‖f‖_∞]`. -/
lemma exists_spectrum_eq : ∃ ω, spectrum ℝ (E.H ω) = E.asSpectrum := E.ae_spectrum_eq.exists

lemma isCompact_asSpectrum : IsCompact E.asSpectrum := by
  obtain ⟨ω, hω⟩ := E.exists_spectrum_eq
  rw [← hω]; exact isCompact_spectrum_real _

lemma asSpectrum_subset : E.asSpectrum ⊆ Icc (-(2 + E.fBound)) (2 + E.fBound) := by
  obtain ⟨ω, hω⟩ := E.exists_spectrum_eq
  rw [← hω]
  intro x hx
  exact abs_le.1 ((abs_le_norm_of_mem_spectrum hx).trans (E.norm_H_le ω))

/-! ### Lemma 4.2.3: the trace dichotomy -/

/-- `⟨δₘ, P_{Tⁿω} δₘ⟩ = ⟨δₘ₊ₙ, P_ω δₘ₊ₙ⟩` for a covariant family. -/
lemma inner_dlt_Tz (P : Ω → Op) (hcov : ∀ ω, P (E.T ω) = shiftL * P ω * star shiftL)
    (ω : Ω) (n m : ℤ) :
    ⟪dlt m, P (E.Tz n ω) (dlt m)⟫_ℂ = ⟪dlt (m + n), P ω (dlt (m + n))⟫_ℂ := by
  induction n using Int.induction_on generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Tz_succ, hcov, inner_dlt_conj, ih, show m + 1 + (n : ℤ) = m + (↑n + 1) by ring]
  | pred n ih =>
    have h := ih (m - 1)
    rw [show -(n : ℤ) = (-n - 1) + 1 by ring, Tz_succ, hcov, inner_dlt_conj,
      sub_add_cancel] at h
    rw [h, show m - 1 + (-(n : ℤ) - 1 + 1) = m + (-↑n - 1) by ring]

/-- **Lemma 4.2.3.** Let `P_ω` be a weakly measurable family of operators with
`P_{Tω} = U P_ω U*` (4.2.17).  Then either `Tr P_ω = 0` for a.e. `ω` or `Tr P_ω = ∞` for a.e. `ω`.
(For orthogonal projections `Tr P_ω = dim Ran P_ω`.) -/
theorem trace_dichotomy (P : Ω → Op) (hcov : ∀ ω, P (E.T ω) = shiftL * P ω * star shiftL)
    (hmeas : ∀ n, Measurable fun ω => ⟪dlt n, P ω (dlt n)⟫_ℂ) :
    (∀ᵐ ω ∂E.μ, opTrace (P ω) = 0) ∨ (∀ᵐ ω ∂E.μ, opTrace (P ω) = ⊤) := by
  set g : ℤ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (RCLike.re ⟪dlt n, P ω (dlt n)⟫_ℂ)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (RCLike.continuous_re.measurable.comp (hmeas n))
  have htm : Measurable fun ω => opTrace (P ω) := Measurable.ennreal_tsum hgm
  have hinv : (fun ω => opTrace (P ω)) ∘ E.T = fun ω => opTrace (P ω) := by
    funext ω; simp only [Function.comp, hcov, opTrace_conj]
  obtain ⟨c, hc⟩ := E.ergodic.toPreErgodic.ae_eq_const_of_ae_eq_comp htm hinv
  -- the expectation of the trace
  set a := ∫⁻ ω, g 0 ω ∂E.μ
  have hgn : ∀ n, ∫⁻ ω, g n ω ∂E.μ = a := by
    intro n
    have h1 : ∀ ω, g n ω = g 0 (E.Tz n ω) := by
      intro ω; simp only [g]; rw [E.inner_dlt_Tz P hcov ω n 0, zero_add]
    simp_rw [h1]
    exact (E.measurePreserving_Tz n).lintegral_comp (hgm 0)
  have hint : ∫⁻ ω, opTrace (P ω) ∂E.μ = ∑' _ : ℤ, a := by
    rw [show (fun ω => opTrace (P ω)) = fun ω => ∑' n, g n ω from rfl,
      lintegral_tsum fun n => (hgm n).aemeasurable]
    simp_rw [hgn]
  have hc' : ∫⁻ ω, opTrace (P ω) ∂E.μ = c := by
    rw [lintegral_congr_ae hc]; simp
  by_cases ha : a = 0
  · left
    have : c = 0 := by rw [← hc', hint, ha, tsum_zero]
    filter_upwards [hc] with ω hω; rw [hω, this]; rfl
  · right
    have : c = ⊤ := by rw [← hc', hint]; exact ENNReal.tsum_const_eq_top_of_ne_zero ha
    filter_upwards [hc] with ω hω; rw [hω, this]; rfl

/-! ### Traces of spectral projections -/

/-- `Tr P_ω(S) = ∑ₙ η_{ω,n}(S)`. -/
def tr (ω : Ω) (S : Set ℝ) : ℝ≥0∞ := ∑' n : ℤ, E.spec ω (dlt n) S

lemma opTrace_proj {S : Set ℝ} (hS : MeasurableSet S) (ω : Ω) :
    opTrace (E.proj ω S) = E.tr ω S := by
  unfold opTrace tr
  refine tsum_congr fun n => ?_
  rw [proj, inner_specProj_self hS, RCLike.re_to_complex, Complex.ofReal_re, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

lemma tr_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) (ω : Ω) :
    E.tr ω S = 0 ↔ E.proj ω S = 0 := by
  rw [tr, ENNReal.tsum_eq_zero, E.proj_eq_zero_iff hS]

lemma measurable_inner_proj {S : Set ℝ} (hS : MeasurableSet S) (n : ℤ) :
    Measurable fun ω => ⟪dlt n, E.proj ω S (dlt n)⟫_ℂ :=
  E.measurable_inner_fc (isBddBorel_indicator hS) _ _

/-- Lemma 4.2.3 for the spectral projections `P_ω(S)`. -/
theorem tr_dichotomy {S : Set ℝ} (hS : MeasurableSet S) :
    (∀ᵐ ω ∂E.μ, E.tr ω S = 0) ∨ (∀ᵐ ω ∂E.μ, E.tr ω S = ⊤) := by
  have := E.trace_dichotomy (fun ω => E.proj ω S) (E.proj_T hS) (E.measurable_inner_proj hS)
  simp_rw [E.opTrace_proj hS] at this
  exact this

/-- The spectral projection onto a single energy has trace at most one (eigenvalues of `H_ω`
are simple, Corollary 2.2.3). -/
theorem tr_singleton_le_one (ω : Ω) (x : ℝ) : E.tr ω {x} ≤ 1 := by
  have hS : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
  set P := E.proj ω {x} with hPdef
  by_cases hP : P = 0
  · rw [(E.tr_eq_zero_iff hS ω).2 hP]; exact zero_le
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀, P φ₀ ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hP (ContinuousLinearMap.ext hcon)
  have hn : 0 < ‖P φ₀‖ := norm_pos_iff.2 hφ₀
  set ψ := P (((‖P φ₀‖ : ℝ) : ℂ)⁻¹ • φ₀) with hψdef
  have hψ' : ψ = (((‖P φ₀‖ : ℝ) : ℂ)⁻¹) • P φ₀ := by rw [hψdef, map_smul]
  have hψn : ‖ψ‖ = 1 := by
    rw [hψ', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']
  have hidem : ∀ v, P (P v) = P v := fun v => by
    have := congrArg (fun T : Op => T v) (specProj_idem (A := E.H ω) (hA := E.isSelfAdjoint_H ω) hS)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this
  have hPψ : P ψ = ψ := hidem _
  have heig : ∀ v, E.H ω (P v) = (x : ℂ) • P v := fun v => apply_specProj_singleton x v
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_specProj hS
  -- every `P φ` is a multiple of `ψ`
  have hrank : ∀ φ, P φ = ⟪ψ, φ⟫_ℂ • ψ := by
    intro φ
    obtain ⟨a, b, hab, h0⟩ := eigen_simple (E.bddPot ω) (heig _) (heig φ)
    have hb : b ≠ 0 := by
      rintro rfl
      have ha : a ≠ 0 := hab.resolve_right (fun h => h rfl)
      rw [zero_smul, add_zero, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact ha h0
      · rw [← hψdef] at h0; rw [h0, norm_zero] at hψn; exact zero_ne_one hψn
    rw [← hψdef] at h0
    have hPφ : P φ = (-(a / b)) • ψ := by
      have : b • P φ = -(a • ψ) := eq_neg_of_add_eq_zero_right h0
      rw [neg_smul, div_eq_inv_mul, mul_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ hb,
        one_smul]
    have hc : ⟪ψ, P φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hPsa.star_eq, hPψ]
    rw [hPφ] at hc ⊢
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψn] at hc
    simp only [RCLike.ofReal_one, one_pow, mul_one] at hc
    rw [hc]
  -- compute the trace
  have hterm : ∀ n, E.spec ω (dlt n) {x} = ENNReal.ofReal (‖ψ n‖ ^ 2) := by
    intro n
    have h1 := norm_specProj_apply_sq (A := E.H ω) (hA := E.isSelfAdjoint_H ω) hS (dlt n)
    change ‖P (dlt n)‖ ^ 2 = _ at h1
    rw [hrank, norm_smul, mul_pow, hψn, one_pow, mul_one] at h1
    have h2 : ‖⟪ψ, dlt n⟫_ℂ‖ = ‖ψ n‖ := by rw [← inner_conj_symm, inner_dlt, RCLike.norm_conj]
    rw [h2] at h1
    rw [h1, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  rw [tr]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (L2.summable_norm_sq ψ),
    ← L2.norm_sq_eq_tsum, hψn]
  simp

/-- For fixed `x`, almost surely `P_ω({x}) = 0` (trace version). -/
theorem ae_tr_singleton_eq_zero (x : ℝ) : ∀ᵐ ω ∂E.μ, E.tr ω {x} = 0 := by
  rcases E.tr_dichotomy (measurableSet_singleton x) with h | h
  · exact h
  · exfalso
    obtain ⟨ω, hω⟩ := h.exists
    have := E.tr_singleton_le_one ω x
    rw [hω] at this
    exact absurd this (by simp)

/-- **Theorem 4.2.4**, (4.2.18): every fixed energy is almost surely not an eigenvalue. -/
theorem measure_eigenvalue_eq_zero (x : ℝ) :
    E.μ {ω | ∃ ψ : L2 ℤ, ψ ≠ 0 ∧ E.H ω ψ = (x : ℂ) • ψ} = 0 := by
  have hS : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
  have h0 := E.ae_tr_singleton_eq_zero x
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h0] with ω hω
  rintro ⟨ψ, hψ, hH⟩
  rw [E.tr_eq_zero_iff hS] at hω
  have := (eigen_iff_specProj_singleton (hA := E.isSelfAdjoint_H ω) ψ x).1 hH
  rw [← proj, hω, ContinuousLinearMap.zero_apply] at this
  exact hψ this.symm

/-- **Theorem 4.2.4** (second part): `σ_disc(H_ω) = ∅` for `μ`-a.e. `ω`. -/
theorem ae_discreteSpectrum_eq_empty : ∀ᵐ ω ∂E.μ, discreteSpectrum (E.H ω) = ∅ := by
  have hdich : ∀ᵐ ω ∂E.μ, ∀ p : ℚ × ℚ,
      E.tr ω (Ioo p.1 p.2) = 0 ∨ E.tr ω (Ioo p.1 p.2) = ⊤ := by
    refine ae_all_iff.2 fun p => ?_
    rcases E.tr_dichotomy (measurableSet_Ioo (a := (p.1 : ℝ)) (b := p.2)) with h | h
    · filter_upwards [h] with ω hω; exact Or.inl hω
    · filter_upwards [h] with ω hω; exact Or.inr hω
  filter_upwards [hdich] with ω hω
  refine eq_empty_iff_forall_notMem.2 fun x ⟨hx, ε, hε, hiso⟩ => ?_
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + ε by linarith)
  set J := Ioo (a : ℝ) b
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hxJ : x ∈ J := ⟨ha2, hb1⟩
  -- `J \ {x}` misses the spectrum
  have hdisj : Disjoint (J \ {x}) (spectrum ℝ (E.H ω)) := by
    rw [Set.disjoint_left]
    intro y hy hys
    have h' : y ∈ spectrum ℝ (E.H ω) ∩ Ioo (x - ε) (x + ε) :=
      ⟨hys, by linarith [hy.1.1], by linarith [hy.1.2]⟩
    have h2 : y ∈ ({x} : Set ℝ) := hiso.subset h'
    exact hy.2 h2
  have hnull : ∀ n, E.spec ω (dlt n) (J \ {x}) = 0 := fun n =>
    measure_mono_null (fun y hy hys => Set.disjoint_left.1 hdisj hy hys)
      (spectralMeasure_compl_spectrum _ _ _)
  have heq : E.tr ω J = E.tr ω {x} := by
    unfold tr
    refine tsum_congr fun n => ?_
    have := measure_union (μ := E.spec ω (dlt n)) (s₁ := {x}) (s₂ := J \ {x})
      Set.disjoint_sdiff_right (hJm.diff (measurableSet_singleton x))
    rw [Set.union_diff_cancel (singleton_subset_iff.2 hxJ), hnull n, add_zero] at this
    exact this
  have hne : E.tr ω J ≠ 0 := by
    rw [Ne, E.tr_eq_zero_iff hJm]
    exact (mem_spectrum_iff_rat (hA := E.isSelfAdjoint_H ω) x).1 hx a b ha2 hb1
  have hle := E.tr_singleton_le_one ω x
  rw [← heq] at hle
  rcases hω (a, b) with h | h
  · exact hne h
  · exact absurd (h ▸ hle) (by simp)

end ErgodicFamily

end DF
