import AvilaGlobal.UniformHyperbolicity

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-!
# Regular cocycles with positive exponent are uniformly hyperbolic (paper §3)

`regularPosUH_proof`: the statement of `Hypotheses.regularPosUH`, proved from the statement of
`Hypotheses.jks` only.  `per_proof`: `PerClaim` (Lemma `per`), from the same input.

Route (a variant of the paper's): the trace estimate of Lemma `per` (`perCore`, from
`rational_estimate` + JKS) and its neighbourhood form (`robustPer`); the expanding spectral
projections `Π_n` of the period products (`specProj`, via the Joukowski inverse `jk`); a
pointwise log-derivative bound (Borel–Carathéodory, `logDeriv_bound`) giving the Fourier decay of
Lemma `gam` (`derivBound`), hence uniform bounds on `Π_n` on a band; Cauchy estimates +
Arzelà–Ascoli (`exists_uniform_subseq`) give a continuous invariant rank-one projection field in
the limit; continuous sections (`exists_section`) and Weyl equidistribution with `L > 0` give
uniform hyperbolicity (`isUH_of_proj`).
-/
/-! ### The Joukowski inverse and spectral projections -/

/-- The inverse of the Joukowski map on `{‖τ‖ > 2}`: the root of `λ² - τλ + 1` of modulus `> 1`. -/
def jk (τ : ℂ) : ℂ := τ / 2 * (1 + (1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ))

/-- The companion root. -/
def jkc (τ : ℂ) : ℂ := τ / 2 * (1 - (1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ))

lemma jk_re_pos {τ : ℂ} (hτ : 2 < ‖τ‖) : 0 < (1 - 4 / τ ^ 2).re := by
  have h1 : ‖4 / τ ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    have : ‖(4 : ℂ)‖ = 4 := by simp
    rw [this]; nlinarith
  have h2 := Complex.abs_re_le_norm (4 / τ ^ 2)
  have h3 := le_abs_self (4 / τ ^ 2).re
  simp only [sub_re, one_re]
  linarith

lemma jk_sqrt_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (2⁻¹ : ℂ)).re := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have ha := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have him : (Complex.log w * 2⁻¹).im = w.arg / 2 := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, Complex.log_im]
    ring
  rw [him]
  rw [abs_lt] at ha
  constructor <;> linarith [Real.pi_pos]

lemma jk_mul_jkc {τ : ℂ} (hτ : 2 < ‖τ‖) : jk τ * jkc τ = 1 := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ; linarith
  have hs : ((1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = 1 - 4 / τ ^ 2 := by
    have := Complex.cpow_ofNat_inv_pow (1 - 4 / τ ^ 2) 2
    simpa using this
  unfold jk jkc
  have e : τ / 2 * (1 + (1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ)) * (τ / 2 * (1 - (1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ)))
      = τ ^ 2 / 4 * (1 - ((1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ)) ^ 2) := by ring
  rw [e, hs]
  field_simp
  ring

lemma jk_add_jkc (τ : ℂ) : jk τ + jkc τ = τ := by unfold jk jkc; ring

lemma norm_jkc_lt_norm_jk {τ : ℂ} (hτ : 2 < ‖τ‖) : ‖jkc τ‖ < ‖jk τ‖ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ; linarith
  set s := (1 - 4 / τ ^ 2) ^ (2⁻¹ : ℂ) with hs
  have hre : 0 < s.re := jk_sqrt_re_pos (jk_re_pos hτ)
  have h1 : ‖1 - s‖ < ‖1 + s‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, add_re, add_im]
    nlinarith
  unfold jk jkc
  rw [← hs, norm_mul, norm_mul]
  exact mul_lt_mul_of_pos_left h1 (by simpa using hτ0)

lemma one_lt_norm_jk {τ : ℂ} (hτ : 2 < ‖τ‖) : 1 < ‖jk τ‖ := by
  have h := jk_mul_jkc hτ
  have h1 : ‖jk τ‖ * ‖jkc τ‖ = 1 := by rw [← norm_mul, h, norm_one]
  have h2 := norm_jkc_lt_norm_jk hτ
  nlinarith [norm_nonneg (jkc τ), norm_nonneg (jk τ)]

lemma norm_jkc_lt_one {τ : ℂ} (hτ : 2 < ‖τ‖) : ‖jkc τ‖ < 1 := by
  have h := jk_mul_jkc hτ
  have h1 : ‖jk τ‖ * ‖jkc τ‖ = 1 := by rw [← norm_mul, h, norm_one]
  have h2 := one_lt_norm_jk hτ
  nlinarith [norm_nonneg (jkc τ), norm_nonneg (jk τ)]

lemma jk_ne_zero {τ : ℂ} (hτ : 2 < ‖τ‖) : jk τ ≠ 0 := by
  intro h; have := one_lt_norm_jk hτ; rw [h, norm_zero] at this; linarith

lemma jkc_eq_inv {τ : ℂ} (hτ : 2 < ‖τ‖) : jkc τ = (jk τ)⁻¹ :=
  eq_inv_of_mul_eq_one_right (jk_mul_jkc hτ)

lemma jk_sub_jkc_ne_zero {τ : ℂ} (hτ : 2 < ‖τ‖) : jk τ - jkc τ ≠ 0 := by
  intro h
  have := norm_jkc_lt_norm_jk hτ
  rw [sub_eq_zero.1 h] at this
  exact lt_irrefl _ this

lemma norm_jk_le {τ : ℂ} (hτ : 2 < ‖τ‖) : ‖jk τ‖ ≤ ‖τ‖ + 1 := by
  have h : jk τ = τ - jkc τ := by rw [eq_sub_iff_add_eq]; exact jk_add_jkc τ
  rw [h]
  linarith [norm_sub_le τ (jkc τ), norm_jkc_lt_one hτ]

lemma differentiableAt_jk {τ : ℂ} (hτ : 2 < ‖τ‖) : DifferentiableAt ℂ jk τ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ; linarith
  have hsl : (1 - 4 / τ ^ 2) ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl (jk_re_pos hτ))
  have hd : DifferentiableAt ℂ (fun τ : ℂ => 1 - 4 / τ ^ 2) τ :=
    (differentiableAt_const _).sub ((differentiableAt_const _).div (differentiableAt_id.pow 2)
      (pow_ne_zero 2 hτ0))
  unfold jk
  exact (differentiableAt_id.div_const 2).mul
    ((differentiableAt_const _).add (hd.cpow_const hsl))

lemma differentiableAt_jkc {τ : ℂ} (hτ : 2 < ‖τ‖) : DifferentiableAt ℂ jkc τ := by
  have h : jkc = fun τ => τ - jk τ := by
    funext σ; rw [eq_sub_iff_add_eq, add_comm]; exact jk_add_jkc σ
  rw [h]
  exact differentiableAt_id.sub (differentiableAt_jk hτ)

lemma isOpen_norm_gt_two : IsOpen {τ : ℂ | 2 < ‖τ‖} := isOpen_lt continuous_const continuous_norm

/-- The spectral projection onto the expanding eigendirection of `P ∈ SL(2,ℂ)` (when
`‖tr P‖ > 2`). -/
def specProj (P : M2) : M2 :=
  (jk P.trace - jkc P.trace)⁻¹ • (P - jkc P.trace • (1 : M2))

/-- Cayley–Hamilton-type identities for the unnormalized projection `X = P - μ`. -/
lemma specX_identities {P : M2} (hP : P.det = 1) {l m : ℂ} (hsum : l + m = P.trace)
    (hprod : l * m = 1) :
    (P - m • (1 : M2)) * (P - m • (1 : M2)) = (l - m) • (P - m • (1 : M2)) ∧
    P * (P - m • (1 : M2)) = l • (P - m • (1 : M2)) ∧
    (P - m • (1 : M2)) * P = l • (P - m • (1 : M2)) ∧
    (P - m • (1 : M2)).trace = l - m ∧ (P - m • (1 : M2)).det = 0 := by
  rw [Matrix.det_fin_two] at hP
  rw [Matrix.trace_fin_two] at hsum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first
      | linear_combination (-1 : ℂ) * hP + (-(P 0 0)) * hsum + hprod
      | linear_combination (-(P 0 1)) * hsum
      | linear_combination (-(P 1 0)) * hsum
      | linear_combination (-1 : ℂ) * hP + (-(P 1 1)) * hsum + hprod
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first
      | linear_combination (-1 : ℂ) * hP + (-(P 0 0)) * hsum + hprod
      | linear_combination (-(P 0 1)) * hsum
      | linear_combination (-(P 1 0)) * hsum
      | linear_combination (-1 : ℂ) * hP + (-(P 1 1)) * hsum + hprod
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first
      | linear_combination (-1 : ℂ) * hP + (-(P 0 0)) * hsum + hprod
      | linear_combination (-(P 0 1)) * hsum
      | linear_combination (-(P 1 0)) * hsum
      | linear_combination (-1 : ℂ) * hP + (-(P 1 1)) * hsum + hprod
  · rw [Matrix.trace_fin_two]
    simp
    linear_combination (-1 : ℂ) * hsum
  · rw [Matrix.det_fin_two]
    simp
    linear_combination hP + m * hsum - hprod

section specProj

variable {P : M2} (hP : P.det = 1) (hτ : 2 < ‖P.trace‖)
include hP hτ

lemma specProj_idem : specProj P * specProj P = specProj P := by
  obtain ⟨h1, -, -, -, -⟩ := specX_identities hP (jk_add_jkc P.trace) (jk_mul_jkc hτ)
  have hne := jk_sub_jkc_ne_zero hτ
  unfold specProj
  rw [smul_mul_smul_comm, h1, smul_smul]
  congr 1
  field_simp

lemma mul_specProj : P * specProj P = jk P.trace • specProj P := by
  obtain ⟨-, h2, -, -, -⟩ := specX_identities hP (jk_add_jkc P.trace) (jk_mul_jkc hτ)
  unfold specProj
  rw [mul_smul_comm, h2, smul_comm]

lemma specProj_mul : specProj P * P = jk P.trace • specProj P := by
  obtain ⟨-, -, h3, -, -⟩ := specX_identities hP (jk_add_jkc P.trace) (jk_mul_jkc hτ)
  unfold specProj
  rw [smul_mul_assoc, h3, smul_comm]

lemma trace_specProj : (specProj P).trace = 1 := by
  obtain ⟨-, -, -, h4, -⟩ := specX_identities hP (jk_add_jkc P.trace) (jk_mul_jkc hτ)
  have hne := jk_sub_jkc_ne_zero hτ
  unfold specProj
  rw [Matrix.trace_smul, h4, smul_eq_mul, inv_mul_cancel₀ hne]

lemma det_specProj : (specProj P).det = 0 := by
  obtain ⟨-, -, -, -, h5⟩ := specX_identities hP (jk_add_jkc P.trace) (jk_mul_jkc hτ)
  unfold specProj
  rw [Matrix.det_smul, h5, mul_zero]

end specProj

/-- `P = μ + (λ - μ) Π`. -/
lemma eq_specProj_decomp {P : M2} (hτ : 2 < ‖P.trace‖) :
    P = jkc P.trace • (1 : M2) + (jk P.trace - jkc P.trace) • specProj P := by
  have hne := jk_sub_jkc_ne_zero hτ
  unfold specProj
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  abel

/-- Conjugation invariance of `specProj`. -/
lemma specProj_conj {P Q B : M2} (hB : B.det ≠ 0) (hQ : B * P = Q * B) :
    B * specProj P = specProj Q * B := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hQ' : Q = B * P * B⁻¹ := by
    rw [hQ, mul_assoc, mul_nonsing_inv _ hu, mul_one]
  have htr : Q.trace = P.trace := by
    rw [hQ', Matrix.trace_mul_comm, ← mul_assoc, nonsing_inv_mul _ hu, one_mul]
  unfold specProj
  rw [htr, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hQ, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul]

/-! ### Rank-one projections, continuous sections, and uniform hyperbolicity from a splitting -/

/-- Two vectors of `ℂ²` with vanishing cross product are parallel. -/
lemma parallel_of_cross {v w : Fin 2 → ℂ} (key : v 0 * w 1 - v 1 * w 0 = 0) (hw0 : w ≠ 0) :
    ∃ c : ℂ, v = c • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw0; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨v 1 / w 1, ?_⟩
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      have : v 0 * w 1 = 0 := by rw [h0] at key; simpa using key
      exact (mul_eq_zero.1 this).resolve_right h1
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨v 0 / w 0, ?_⟩
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination -key

lemma mulVec_fin_two_0 (M : M2) (v : Fin 2 → ℂ) : (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mulVec_fin_two_1 (M : M2) (v : Fin 2 → ℂ) : (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Cross product of images. -/
lemma cross_mulVec (M : M2) (v w : Fin 2 → ℂ) :
    (M *ᵥ v) 0 * (M *ᵥ w) 1 - (M *ᵥ v) 1 * (M *ᵥ w) 0 = M.det * (v 0 * w 1 - v 1 * w 0) := by
  rw [mulVec_fin_two_0, mulVec_fin_two_1, mulVec_fin_two_0, mulVec_fin_two_1, Matrix.det_fin_two]
  ring

/-- In the range of a determinant-zero `2 × 2` matrix, any two vectors are parallel. -/
lemma parallel_of_det_zero' {M : M2} (hM : M.det = 0) {v w : Fin 2 → ℂ} (hv : M *ᵥ v = v)
    (hw : M *ᵥ w = w) (hw0 : w ≠ 0) : ∃ c : ℂ, v = c • w := by
  refine parallel_of_cross ?_ hw0
  have := cross_mulVec M v w
  rw [hv, hw, hM, zero_mul] at this
  exact this

lemma mulVec_ne_zero_of_det {M : M2} (hM : M.det = 1) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    M *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
  have : M⁻¹ *ᵥ (M *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

/-- Near-injectivity of a projection on the range of a nearby projection. -/
lemma norm_mulVec_ge_half {M N : M2} {v : Fin 2 → ℂ} (hv : N *ᵥ v = v) (hMN : ‖M - N‖ ≤ 1 / 2) :
    ‖v‖ / 2 ≤ ‖M *ᵥ v‖ := by
  have h1 : v = M *ᵥ v - (M - N) *ᵥ v := by rw [Matrix.sub_mulVec, hv]; abel
  have h2 := Matrix.linfty_opNorm_mulVec (M - N) v
  have h3 : ‖v‖ ≤ ‖M *ᵥ v‖ + ‖(M - N) *ᵥ v‖ := by
    conv_lhs => rw [h1]
    exact norm_sub_le _ _
  have h4 : ‖M - N‖ * ‖v‖ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hMN (norm_nonneg _)
  linarith

lemma periodic_fract_eq {β : Type*} {f : ℝ → β} (hp : Function.Periodic f 1) (x : ℝ) :
    f (Int.fract x) = f x := by
  have := hp.sub_int_mul_eq ⌊x⌋ (x := x)
  rwa [mul_one, Int.self_sub_floor] at this

lemma periodic_bounds {g : ℝ → ℝ} (hc : Continuous g) (hp : Function.Periodic g 1) :
    ∃ m M : ℝ, ∀ x, m ≤ g x ∧ g x ≤ M := by
  obtain ⟨a, -, hamin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    hc.continuousOn
  obtain ⟨b, -, hbmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
    hc.continuousOn
  refine ⟨g a, g b, fun x => ?_⟩
  have hm : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← periodic_fract_eq hp x]
  exact ⟨isMinOn_iff.1 hamin _ hm, isMaxOn_iff.1 hbmax _ hm⟩

lemma norm_bounds_of_ne_zero {u : ℝ → (Fin 2 → ℂ)} (hc : Continuous u)
    (hp : Function.Periodic u 1) (h0 : ∀ x, u x ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ ‖u x‖ ∧ ‖u x‖ ≤ M := by
  obtain ⟨a, -, hamin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (hc.norm.continuousOn : ContinuousOn (fun x => ‖u x‖) (Icc (0 : ℝ) 1))
  obtain ⟨_, M, hM⟩ := periodic_bounds hc.norm (fun x => by simp only [hp x])
  refine ⟨‖u a‖, M, norm_pos_iff.2 (h0 a), fun x => ⟨?_, (hM x).2⟩⟩
  have hm : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← periodic_fract_eq hp x]
  exact isMinOn_iff.1 hamin _ hm

lemma exists_unif {F : ℝ → M2} (hc : Continuous F) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ 1 / N →
      ‖F x - F y‖ ≤ 1 / 2 := by
  have hu : UniformContinuousOn F (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  refine ⟨N, by exact_mod_cast hNpos, fun x hx y hy hxy => ?_⟩
  have h1 : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have := h x hx y hy (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at this
  linarith

/-- Chained products of projections along a partition. -/
def chainProd (F : ℝ → M2) (N : ℕ) : ℕ → ℝ → M2
  | 0, _ => 1
  | k + 1, x => F (min x ((k : ℝ) / N)) * chainProd F N k x

lemma continuous_chainProd {F : ℝ → M2} (hc : Continuous F) (N : ℕ) (k : ℕ) :
    Continuous (chainProd F N k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    change Continuous fun x => F (min x ((k : ℝ) / N)) * chainProd F N k x
    exact (hc.comp (continuous_id.min continuous_const)).mul ih

/-- **Continuous sections of a rank-one projection field over the circle.** -/
theorem exists_section {F : ℝ → M2} (hc : Continuous F) (hp : Function.Periodic F 1)
    (hidem : ∀ x, F x * F x = F x) (hdet : ∀ x, (F x).det = 0)
    (htr : ∀ x, (F x).trace = 1) :
    ∃ u : ℝ → (Fin 2 → ℂ), Continuous u ∧ Function.Periodic u 1 ∧ (∀ x, u x ≠ 0) ∧
      ∀ x, F x *ᵥ u x = u x := by
  obtain ⟨N, hN0, hN⟩ := exists_unif hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 2 → ℂ, w ≠ 0 ∧ F 0 *ᵥ w = w := by
    have hF0 : F 0 ≠ 0 := by
      intro h; have := htr 0; rw [h, Matrix.trace_zero] at this; exact zero_ne_one this
    have : ∃ j : Fin 2, F 0 *ᵥ Pi.single j 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hF0
      ext i j
      have := congrFun (h j) i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    obtain ⟨j, hj⟩ := this
    refine ⟨_, hj, ?_⟩
    rw [Matrix.mulVec_mulVec, hidem]
  have hmin_mem : ∀ x ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ N → min x ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    intro x hx k hk
    have hk' : (k : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hk
    exact ⟨le_min hx.1 (by positivity), (min_le_right _ _).trans hk'⟩
  have hchain : ∀ x ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ N →
      chainProd F N (k + 1) x *ᵥ w ≠ 0 ∧
        F (min x ((k : ℝ) / N)) *ᵥ (chainProd F N (k + 1) x *ᵥ w) =
          chainProd F N (k + 1) x *ᵥ w := by
    intro x hx k hk
    induction k with
    | zero =>
      have hm : min x (((0 : ℕ) : ℝ) / N) = 0 := by simp [hx.1]
      have e : chainProd F N 1 x *ᵥ w = w := by
        change (F (min x (((0 : ℕ) : ℝ) / N)) * 1) *ᵥ w = w
        rw [hm, mul_one, hw]
      rw [e, hm]
      exact ⟨hw0, hw⟩
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      set V := chainProd F N (k + 1) x *ᵥ w with hV
      have e : chainProd F N (k + 1 + 1) x *ᵥ w = F (min x (((k + 1 : ℕ) : ℝ) / N)) *ᵥ V := by
        change (F (min x (((k + 1 : ℕ) : ℝ) / N)) * chainProd F N (k + 1) x) *ᵥ w = _
        rw [← Matrix.mulVec_mulVec]
      rw [e]
      refine ⟨?_, ?_⟩
      · have hdist : |min x (((k + 1 : ℕ) : ℝ) / N) - min x ((k : ℝ) / N)| ≤ 1 / N := by
          have e1 : ((k + 1 : ℕ) : ℝ) / N = (k : ℝ) / N + 1 / N := by push_cast; ring
          rw [e1]
          have h1N : (0 : ℝ) ≤ 1 / N := by positivity
          rcases le_total x ((k : ℝ) / N) with h | h
          · rw [min_eq_left h, min_eq_left (by linarith)]; simp
          · rw [min_eq_right h]
            rcases le_total x ((k : ℝ) / N + 1 / N) with h' | h'
            · rw [min_eq_left h', abs_le]; constructor <;> linarith
            · rw [min_eq_right h', abs_le]; constructor <;> linarith
        have hn := norm_mulVec_ge_half ih2
          (hN _ (hmin_mem x hx _ hk) _ (hmin_mem x hx k (by omega)) hdist)
        intro h0
        rw [h0, norm_zero] at hn
        have : 0 < ‖V‖ := norm_pos_iff.2 ih1
        linarith
      · rw [Matrix.mulVec_mulVec, hidem]
  set u0 : ℝ → (Fin 2 → ℂ) := fun x => chainProd F N (N + 1) x *ᵥ w with hu0
  have hu0c : Continuous u0 := (continuous_chainProd hc N (N + 1)).matrix_mulVec continuous_const
  have hu0x : ∀ x ∈ Icc (0 : ℝ) 1, u0 x ≠ 0 ∧ F x *ᵥ u0 x = u0 x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hchain x hx N le_rfl
    have hm : min x ((N : ℝ) / N) = x := by rw [div_self hNpos.ne']; exact min_eq_left hx.2
    rw [hm] at h2
    exact ⟨h1, h2⟩
  have hu00 : u0 0 = w := by
    have : ∀ k, chainProd F N k 0 *ᵥ w = w := by
      intro k
      induction k with
      | zero => exact Matrix.one_mulVec w
      | succ k ih =>
        change (F (min 0 ((k : ℝ) / N)) * chainProd F N k 0) *ᵥ w = w
        rw [min_eq_left (by positivity), ← Matrix.mulVec_mulVec, ih, hw]
    exact this _
  have hF1 : F 1 = F 0 := by simpa using hp 0
  obtain ⟨c, hc1⟩ : ∃ c : ℂ, u0 1 = c • w := by
    have h := (hu0x 1 ⟨zero_le_one, le_rfl⟩).2
    rw [hF1] at h
    exact parallel_of_det_zero' (hdet 0) h hw hw0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc1
    exact (hu0x 1 ⟨zero_le_one, le_rfl⟩).1 hc1
  set f : ℝ → (Fin 2 → ℂ) := fun t => Complex.exp (-(t : ℂ) * Complex.log c) • u0 t with hf
  have hfc : Continuous f := by
    show Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.log c) • u0 t
    exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.neg).mul
      continuous_const)).smul hu0c
  have hf01 : f 0 = f 1 := by
    simp only [hf, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_smul,
      Complex.ofReal_one, neg_one_mul, hu00, hc1, smul_smul]
    rw [Complex.exp_neg, Complex.exp_log hc0, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨f ∘ Int.fract, ContinuousOn.comp_fract'' hfc.continuousOn hf01, ?_, ?_, ?_⟩
  · intro x; simp [Int.fract_add_one]
  · intro x
    have hm : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    simp only [Function.comp, hf]
    exact smul_ne_zero (Complex.exp_ne_zero _) (hu0x _ hm).1
  · intro x
    have hm : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    simp only [Function.comp, hf]
    rw [← periodic_fract_eq hp x, Matrix.mulVec_smul, (hu0x _ hm).2]

section Splitting

variable {α : ℝ} {A : ℝ → M2}

/-- The logarithmic growth along an invariant section. -/
def lgrowth (α : ℝ) (A : ℝ → M2) (v : ℝ → (Fin 2 → ℂ)) (x : ℝ) : ℝ :=
  Real.log ‖A x *ᵥ v x‖ - Real.log ‖v (x + α)‖

lemma iter_section {v : ℝ → (Fin 2 → ℂ)} (hA : IsSLCocycle A) (h0 : ∀ x, v x ≠ 0)
    (hstep : ∀ x, ∃ c : ℂ, A x *ᵥ v x = c • v (x + α)) (n : ℕ) (x : ℝ) :
    (∃ C : ℂ, iter α A n x *ᵥ v x = C • v (x + n * α)) ∧
      ‖iter α A n x *ᵥ v x‖ =
        Real.exp (∑ j ∈ Finset.range n, lgrowth α A v (x + j * α)) * ‖v (x + n * α)‖ := by
  induction n with
  | zero =>
    refine ⟨⟨1, by simp [iter]⟩, ?_⟩
    simp [iter]
  | succ n ih =>
    obtain ⟨⟨C, hC⟩, hn⟩ := ih
    obtain ⟨c, hc⟩ := hstep (x + n * α)
    have e : x + n * α + α = x + ((n + 1 : ℕ) : ℝ) * α := by push_cast; ring
    have hit : iter α A (n + 1) x *ᵥ v x = C • (A (x + n * α) *ᵥ v (x + n * α)) := by
      change (A (x + n * α) * iter α A n x) *ᵥ v x = _
      rw [← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul]
    refine ⟨⟨C * c, ?_⟩, ?_⟩
    · rw [hit, hc, smul_smul, e]
    · have hvpos : 0 < ‖v (x + n * α)‖ := norm_pos_iff.2 (h0 _)
      have hCn : ‖C‖ = Real.exp (∑ j ∈ Finset.range n, lgrowth α A v (x + j * α)) := by
        rw [hC, norm_smul] at hn
        exact mul_right_cancel₀ hvpos.ne' hn
      have hApos : 0 < ‖A (x + n * α) *ᵥ v (x + n * α)‖ :=
        norm_pos_iff.2 (mulVec_ne_zero_of_det (hA.det_eq_one _) (h0 _))
      have hv2pos : 0 < ‖v (x + n * α + α)‖ := norm_pos_iff.2 (h0 _)
      have hg : Real.exp (lgrowth α A v (x + n * α)) * ‖v (x + n * α + α)‖ =
          ‖A (x + n * α) *ᵥ v (x + n * α)‖ := by
        rw [lgrowth, Real.exp_sub, Real.exp_log hApos, Real.exp_log hv2pos]
        field_simp
      rw [hit, norm_smul, hCn, Finset.sum_range_succ, Real.exp_add, ← hg, e]
      ring

lemma continuous_lgrowth {v : ℝ → (Fin 2 → ℂ)} (hA : IsSLCocycle A) (hc : Continuous v)
    (h0 : ∀ x, v x ≠ 0) : Continuous (lgrowth α A v) := by
  unfold lgrowth
  refine Continuous.sub ?_ ?_
  · exact (hA.continuous.matrix_mulVec hc).norm.log
      (fun x => (norm_pos_iff.2 (mulVec_ne_zero_of_det (hA.det_eq_one _) (h0 _))).ne')
  · exact (hc.comp (continuous_id.add continuous_const)).norm.log
      (fun x => (norm_pos_iff.2 (h0 _)).ne')

lemma periodic_lgrowth {v : ℝ → (Fin 2 → ℂ)} (hA : IsSLCocycle A) (hp : Function.Periodic v 1) :
    Function.Periodic (lgrowth α A v) 1 := by
  intro x
  simp only [lgrowth, hA.periodic x, hp x, add_right_comm x 1 α, hp (x + α)]

/-- Growth along a section, with uniform constants. -/
lemma growth_section {v : ℝ → (Fin 2 → ℂ)} (hα : Irrational α) (hA : IsSLCocycle A)
    (hc : Continuous v) (hp : Function.Periodic v 1) (h0 : ∀ x, v x ≠ 0)
    (hstep : ∀ x, ∃ c : ℂ, A x *ᵥ v x = c • v (x + α)) {e : ℝ} (he : 0 < e) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x,
      Real.exp (n * ((∫ y in (0 : ℝ)..1, lgrowth α A v y) - e)) * ‖v (x + n * α)‖ ≤
        ‖iter α A n x *ᵥ v x‖ ∧
      ‖iter α A n x *ᵥ v x‖ ≤
        Real.exp (n * ((∫ y in (0 : ℝ)..1, lgrowth α A v y) + e)) * ‖v (x + n * α)‖ := by
  obtain ⟨n₀, hn₀⟩ := weyl_uniform_real hα (continuous_lgrowth hA hc h0) (periodic_lgrowth hA hp) he
  refine ⟨n₀ + 1, fun n hn x => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := hn₀ n (by omega) x
  rw [abs_le] at h
  set S := ∑ k ∈ Finset.range n, lgrowth α A v (x + k * α) with hS
  set μ := ∫ y in (0 : ℝ)..1, lgrowth α A v y
  have h1 : n * (μ - e) ≤ S := by
    have := mul_le_mul_of_nonneg_left h.1 hnpos.le
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at this
    linarith
  have h2 : S ≤ n * (μ + e) := by
    have := mul_le_mul_of_nonneg_left h.2 hnpos.le
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at this
    linarith
  rw [(iter_section hA h0 hstep n x).2]
  constructor
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h2) (norm_nonneg _)

/-- The two growth rates of an invariant splitting add up to zero. -/
lemma integral_lgrowth_add {u s : ℝ → (Fin 2 → ℂ)} (hA : IsSLCocycle A)
    (huc : Continuous u) (hsc : Continuous s) (hup : Function.Periodic u 1)
    (hsp : Function.Periodic s 1) (hu0 : ∀ x, u x ≠ 0) (hs0 : ∀ x, s x ≠ 0)
    (hus : ∀ x, u x 0 * s x 1 - u x 1 * s x 0 ≠ 0)
    (hustep : ∀ x, ∃ c : ℂ, A x *ᵥ u x = c • u (x + α))
    (hsstep : ∀ x, ∃ c : ℂ, A x *ᵥ s x = c • s (x + α)) :
    (∫ y in (0 : ℝ)..1, lgrowth α A u y) + (∫ y in (0 : ℝ)..1, lgrowth α A s y) = 0 := by
  set D : ℝ → ℂ := fun x => u x 0 * s x 1 - u x 1 * s x 0 with hD
  set k : ℝ → ℝ := fun x => Real.log ‖D x‖ with hk
  have hkc : Continuous k := by
    have : Continuous D := by
      simp only [hD]
      have h0 : Continuous fun x => u x 0 := (continuous_apply 0).comp huc
      have h1 : Continuous fun x => u x 1 := (continuous_apply 1).comp huc
      have h2 : Continuous fun x => s x 0 := (continuous_apply 0).comp hsc
      have h3 : Continuous fun x => s x 1 := (continuous_apply 1).comp hsc
      exact (h0.mul h3).sub (h1.mul h2)
    exact this.norm.log (fun x => norm_ne_zero_iff.2 (hus x))
  have hkp : Function.Periodic k 1 := fun x => by simp only [hk, hD, hup x, hsp x]
  have hpt : ∀ x, lgrowth α A u x + lgrowth α A s x = k x - k (x + α) := by
    intro x
    obtain ⟨cu, hcu⟩ := hustep x
    obtain ⟨cs, hcs⟩ := hsstep x
    have hcr := cross_mulVec (A x) (u x) (s x)
    rw [hA.det_eq_one, one_mul, hcu, hcs] at hcr
    simp only [Pi.smul_apply, smul_eq_mul] at hcr
    have hcr' : cu * cs * D (x + α) = D x := by rw [hD]; linear_combination hcr
    have hcu0 : cu ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hcu
      exact mulVec_ne_zero_of_det (hA.det_eq_one x) (hu0 x) hcu
    have hcs0 : cs ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hcs
      exact mulVec_ne_zero_of_det (hA.det_eq_one x) (hs0 x) hcs
    have hu' : 0 < ‖u (x + α)‖ := norm_pos_iff.2 (hu0 _)
    have hs' : 0 < ‖s (x + α)‖ := norm_pos_iff.2 (hs0 _)
    simp only [lgrowth, hk, hcu, hcs, norm_smul]
    rw [Real.log_mul (norm_ne_zero_iff.2 hcu0) hu'.ne',
      Real.log_mul (norm_ne_zero_iff.2 hcs0) hs'.ne', ← hcr', norm_mul, norm_mul,
      Real.log_mul (by simp [hcu0, hcs0]) (norm_ne_zero_iff.2 (hus _)),
      Real.log_mul (norm_ne_zero_iff.2 hcu0) (norm_ne_zero_iff.2 hcs0)]
    ring
  have hk2 : Continuous fun x => k (x + α) := hkc.comp (continuous_id.add continuous_const)
  have hi1 := (continuous_lgrowth (α := α) hA huc hu0).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have hi2 := (continuous_lgrowth (α := α) hA hsc hs0).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  rw [← intervalIntegral.integral_add hi1 hi2]
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (hkc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    (hk2.intervalIntegrable (μ := MeasureTheory.volume) 0 1),
    intervalIntegral.integral_comp_add_right, zero_add,
    show (1 : ℝ) + α = α + 1 by ring, hkp.intervalIntegral_add_eq α 0, zero_add, sub_self]

/-- The matrix with columns `v, w`. -/
def colM (v w : Fin 2 → ℂ) : M2 := !![v 0, w 0; v 1, w 1]

lemma norm_colM_le (v w : Fin 2 → ℂ) : ‖colM v w‖ ≤ ‖v‖ + ‖w‖ := by
  obtain ⟨i, hi⟩ := exists_row_norm_eq (colM v w)
  rw [hi]
  fin_cases i
  · simp only [colM, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact add_le_add (norm_le_pi_norm v 0) (norm_le_pi_norm w 0)
  · simp only [colM, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact add_le_add (norm_le_pi_norm v 1) (norm_le_pi_norm w 1)

/-- The inverse of `colM u s`. -/
def colMinv (v w : Fin 2 → ℂ) : M2 :=
  (v 0 * w 1 - v 1 * w 0)⁻¹ • !![w 1, -w 0; -v 1, v 0]

lemma eq_colM_mul_colMinv (M : M2) {v w : Fin 2 → ℂ} (h : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    M = colM (M *ᵥ v) (M *ᵥ w) * colMinv v w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colM, colMinv, Matrix.mul_apply, Fin.sum_univ_two, mulVec_fin_two_0,
      mulVec_fin_two_1] <;> field_simp <;> ring

/-- **Uniform hyperbolicity from a continuous invariant rank-one projection field**, for
irrational frequency and positive Lyapunov exponent. -/
theorem isUH_of_proj (hα : Irrational α) (hA : IsSLCocycle A) (hL : 0 < lyapunov α A)
    {F : ℝ → M2} (hc : Continuous F) (hp : Function.Periodic F 1)
    (hidem : ∀ x, F x * F x = F x) (hdet : ∀ x, (F x).det = 0)
    (htr : ∀ x, (F x).trace = 1) (hinv : ∀ x, A x * F x = F (x + α) * A x) : IsUH α A := by
  set G : ℝ → M2 := fun x => 1 - F x with hG
  have hGc : Continuous G := continuous_const.sub hc
  have hGp : Function.Periodic G 1 := fun x => by simp only [hG, hp x]
  have hGidem : ∀ x, G x * G x = G x := fun x => by
    simp only [hG, sub_mul, mul_sub, one_mul, mul_one, hidem]; abel
  have hGtr : ∀ x, (G x).trace = 1 := fun x => by
    have := htr x
    simp only [hG, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, this]
    norm_num
  have hGdet : ∀ x, (G x).det = 0 := fun x => by
    have h1 := hdet x
    have h2 := htr x
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [Matrix.trace_fin_two] at h2
    simp only [hG, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
      (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    linear_combination h1 - h2
  have hGinv : ∀ x, A x * G x = G (x + α) * A x := fun x => by
    simp only [hG, mul_sub, sub_mul, mul_one, one_mul, hinv]
  obtain ⟨u, huc, hup, hu0, huF⟩ := exists_section hc hp hidem hdet htr
  obtain ⟨s, hsc, hsp, hs0, hsG⟩ := exists_section hGc hGp hGidem hGdet hGtr
  have step : ∀ {E : ℝ → M2} {v : ℝ → (Fin 2 → ℂ)}, (∀ x, (E x).det = 0) → (∀ x, v x ≠ 0) →
      (∀ x, E x *ᵥ v x = v x) → (∀ x, A x * E x = E (x + α) * A x) →
      ∀ x, ∃ c : ℂ, A x *ᵥ v x = c • v (x + α) := by
    intro E v hEd hv0 hvE hEinv x
    refine parallel_of_det_zero' (hEd (x + α)) ?_ (hvE (x + α)) (hv0 (x + α))
    rw [Matrix.mulVec_mulVec, ← hEinv, ← Matrix.mulVec_mulVec, hvE]
  have hustep := step hdet hu0 huF hinv
  have hsstep := step hGdet hs0 hsG hGinv
  have hus : ∀ x, u x 0 * s x 1 - u x 1 * s x 0 ≠ 0 := by
    intro x h
    obtain ⟨c, hc'⟩ := parallel_of_cross (v := s x) (w := u x)
      (by linear_combination -h) (hu0 x)
    apply hs0 x
    have h1 : F x *ᵥ s x = s x := by rw [hc', Matrix.mulVec_smul, huF]
    have h2 : F x *ᵥ s x = 0 := by
      rw [← hsG x, Matrix.mulVec_mulVec]
      simp only [hG, mul_sub, mul_one, hidem, sub_self, Matrix.zero_mulVec]
    rw [← h1, h2]
  have hsum := integral_lgrowth_add hA huc hsc hup hsp hu0 hs0 hus hustep hsstep
  set μ := ∫ y in (0 : ℝ)..1, lgrowth α A u y with hμ
  have hμ0 : μ ≠ 0 := by
    intro hμz
    have hν : (∫ y in (0 : ℝ)..1, lgrowth α A s y) = 0 := by linarith
    set e := lyapunov α A / 4 with he
    have he0 : 0 < e := by positivity
    obtain ⟨n₁, hn₁⟩ := growth_section hα hA huc hup hu0 hustep he0
    obtain ⟨n₂, hn₂⟩ := growth_section hα hA hsc hsp hs0 hsstep he0
    obtain ⟨_, Mu, -, hMu⟩ := norm_bounds_of_ne_zero huc hup hu0
    obtain ⟨_, Ms, -, hMs⟩ := norm_bounds_of_ne_zero hsc hsp hs0
    have hinvc : Continuous fun x => ‖colMinv (u x) (s x)‖ := by
      refine Continuous.norm ?_
      unfold colMinv
      have h0 : Continuous fun x => u x 0 := (continuous_apply 0).comp huc
      have h1 : Continuous fun x => u x 1 := (continuous_apply 1).comp huc
      have h2 : Continuous fun x => s x 0 := (continuous_apply 0).comp hsc
      have h3 : Continuous fun x => s x 1 := (continuous_apply 1).comp hsc
      refine Continuous.smul (((h0.mul h3).sub (h1.mul h2)).inv₀ hus) ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    obtain ⟨_, Ki, hKi⟩ := periodic_bounds hinvc (fun x => by simp only [hup x, hsp x])
    have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0).2
    have hMs0 : 0 ≤ Ms := (norm_nonneg _).trans (hMs 0).2
    have hKi0 : 0 ≤ Ki := (norm_nonneg _).trans (hKi 0).2
    set K := (Mu + Ms) * Ki + 1 with hK
    have hK1 : 1 ≤ K := by rw [hK]; nlinarith
    have hbound : ∀ n ≥ max n₁ n₂, ∀ x, ‖iter α A n x‖ ≤ K * Real.exp (n * e) := by
      intro n hn x
      have hu := (hn₁ n (le_of_max_le_left hn) x).2
      have hs := (hn₂ n (le_of_max_le_right hn) x).2
      rw [← hμ, hμz, zero_add] at hu
      rw [hν, zero_add] at hs
      have heq := eq_colM_mul_colMinv (iter α A n x) (hus x)
      have hE : 1 ≤ Real.exp (n * e) := Real.one_le_exp (by positivity)
      calc ‖iter α A n x‖ ≤ ‖colM (iter α A n x *ᵥ u x) (iter α A n x *ᵥ s x)‖ *
            ‖colMinv (u x) (s x)‖ := by
            conv_lhs => rw [heq]
            exact norm_mul_le _ _
        _ ≤ (Real.exp (n * e) * Mu + Real.exp (n * e) * Ms) * Ki := by
            refine mul_le_mul ((norm_colM_le _ _).trans (add_le_add ?_ ?_)) (hKi x).2
              (norm_nonneg _) (by positivity)
            · exact hu.trans (mul_le_mul_of_nonneg_left (hMu _).2 (Real.exp_pos _).le)
            · exact hs.trans (mul_le_mul_of_nonneg_left (hMs _).2 (Real.exp_pos _).le)
        _ ≤ K * Real.exp (n * e) := by rw [hK]; nlinarith [Real.exp_pos (n * e)]
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, max n₁ n₂ + 1 ≤ n ∧ Real.log K / e ≤ n := by
      obtain ⟨m, hm⟩ := exists_nat_ge (Real.log K / e)
      exact ⟨max (max n₁ n₂ + 1) m, le_max_left _ _,
        hm.trans (by exact_mod_cast le_max_right _ _)⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : ∀ x, Real.log ‖iter α A n x‖ ≤ Real.log K + n * e := by
      intro x
      have hpos : 0 < ‖iter α A n x‖ := zero_lt_one.trans_le (hA.one_le_norm_iter n x)
      calc Real.log ‖iter α A n x‖ ≤ Real.log (K * Real.exp (n * e)) :=
            Real.log_le_log hpos (hbound n (by omega) x)
        _ = Real.log K + n * e := by
            rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hseq : lyapSeq α A n ≤ Real.log K + n * e := by
      unfold lyapSeq
      have := intervalIntegral.integral_mono_on zero_le_one
        ((hA.continuous_log_norm_iter n).intervalIntegrable (μ := MeasureTheory.volume) 0 1)
        intervalIntegrable_const
        (fun x _ => hlog x)
      simpa using this
    have hly := hA.lyapunov_le (α := α) n (by omega)
    have h1 : lyapSeq α A n / n ≤ Real.log K / n + e := by
      rw [div_add' _ _ _ hnpos.ne', div_le_div_iff_of_pos_right hnpos]
      linarith
    have h2 : Real.log K / n ≤ e := by
      rw [div_le_iff₀ hnpos]
      rw [div_le_iff₀ he0] at hn2
      linarith
    rw [he] at h1 h2
    linarith
  have key : ∀ {U S : ℝ → (Fin 2 → ℂ)}, Continuous U → Continuous S → Function.Periodic U 1 →
      Function.Periodic S 1 → (∀ x, U x ≠ 0) → (∀ x, S x ≠ 0) →
      (∀ x, ∃ c : ℂ, A x *ᵥ U x = c • U (x + α)) →
      (∀ x, ∃ c : ℂ, A x *ᵥ S x = c • S (x + α)) →
      0 < (∫ y in (0 : ℝ)..1, lgrowth α A U y) →
      (∫ y in (0 : ℝ)..1, lgrowth α A U y) + (∫ y in (0 : ℝ)..1, lgrowth α A S y) = 0 →
      IsUH α A := by
    intro U S hUc hSc hUp hSp hU0 hS0 hUs hSs hpos hsum'
    set m := ∫ y in (0 : ℝ)..1, lgrowth α A U y with hm
    have hm2 : 0 < m / 2 := by positivity
    obtain ⟨n₁, hn₁⟩ := growth_section hα hA hUc hUp hU0 hUs hm2
    obtain ⟨n₂, hn₂⟩ := growth_section hα hA hSc hSp hS0 hSs hm2
    obtain ⟨mu, Mu, hmu, hMu⟩ := norm_bounds_of_ne_zero hUc hUp hU0
    obtain ⟨ms, Ms, hms, hMs⟩ := norm_bounds_of_ne_zero hSc hSp hS0
    have hMu0 : 0 < Mu := hmu.trans_le ((hMu 0).1.trans (hMu 0).2)
    have hMs0 : 0 < Ms := hms.trans_le ((hMs 0).1.trans (hMs 0).2)
    obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n : ℕ, max n₁ n₂ + 1 ≤ n ∧
        Real.log (Mu / mu) < n * (m / 2) ∧ Real.log (Ms / ms) < n * (m / 2) := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((|Real.log (Mu / mu)| + |Real.log (Ms / ms)|) / (m / 2))
      have hk' : (k : ℝ) ≤ max (max n₁ n₂ + 1) k := by exact_mod_cast le_max_right _ _
      rw [div_lt_iff₀ hm2] at hk
      have hkm := mul_le_mul_of_nonneg_right hk' hm2.le
      refine ⟨max (max n₁ n₂ + 1) k, le_max_left _ _, ?_, ?_⟩
      · have := le_abs_self (Real.log (Mu / mu))
        have := abs_nonneg (Real.log (Ms / ms))
        push_cast at hkm ⊢
        linarith
      · have := le_abs_self (Real.log (Ms / ms))
        have := abs_nonneg (Real.log (Mu / mu))
        push_cast at hkm ⊢
        linarith
    refine ⟨U, S, hUc, hSc, hUp, hSp, hU0, hS0, hUs, hSs, n, by omega, fun x => ⟨?_, ?_⟩⟩
    · have h := (hn₂ n (by omega) x).2
      have hS : (∫ y in (0 : ℝ)..1, lgrowth α A S y) + m / 2 = -(m / 2) := by linarith
      rw [hS] at h
      have h3 : Real.exp (n * -(m / 2)) * Ms < ms := by
        have : Real.exp (n * (m / 2)) > Ms / ms := by
          rw [gt_iff_lt, ← Real.exp_log (by positivity : 0 < Ms / ms)]
          exact Real.exp_lt_exp.2 hn3
        rw [mul_neg, Real.exp_neg]
        rw [gt_iff_lt, div_lt_iff₀ hms] at this
        rw [inv_mul_lt_iff₀ (Real.exp_pos _)]
        linarith
      calc ‖iter α A n x *ᵥ S x‖ ≤ Real.exp (n * -(m / 2)) * ‖S (x + n * α)‖ := h
        _ ≤ Real.exp (n * -(m / 2)) * Ms :=
            mul_le_mul_of_nonneg_left (hMs _).2 (Real.exp_pos _).le
        _ < ms := h3
        _ ≤ ‖S x‖ := (hMs x).1
    · have h := (hn₁ n (by omega) x).1
      have hU : m - m / 2 = m / 2 := by ring
      rw [← hm, hU] at h
      have h3 : Mu < Real.exp (n * (m / 2)) * mu := by
        have : Mu / mu < Real.exp (n * (m / 2)) := by
          rw [← Real.exp_log (by positivity : 0 < Mu / mu)]
          exact Real.exp_lt_exp.2 hn2
        rwa [div_lt_iff₀ hmu] at this
      calc ‖U x‖ ≤ Mu := (hMu x).2
        _ < Real.exp (n * (m / 2)) * mu := h3
        _ ≤ Real.exp (n * (m / 2)) * ‖U (x + n * α)‖ :=
            mul_le_mul_of_nonneg_left (hMu _).1 (Real.exp_pos _).le
        _ ≤ ‖iter α A n x *ᵥ U x‖ := h
  rcases lt_or_gt_of_ne hμ0 with hneg | hpos
  · exact key hsc huc hsp hup hs0 hu0 hsstep hustep (by linarith) (by linarith)
  · exact key huc hsc hup hsp hu0 hs0 hustep hsstep hpos hsum

end Splitting

/-! ### Lemma `per`: the trace estimate -/

/-- The statement of **Theorem [JKS]** (the field `Hypotheses.jks`). -/
def JKSHyp : Prop :=
  ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α →
    ∀ {αs : ℕ → ℝ} {As : ℕ → ℂ → M2}, (∀ n, IsAnalyticCocycle δ (As n)) →
      Tendsto αs atTop (𝓝 α) → TendstoUniformlyOn As A atTop (strip δ) →
        Tendsto (fun n => L (αs n) (As n) 0) atTop (𝓝 (L α A 0))

lemma tendstoUniformlyOn_cshift {δ : ℝ} {As : ℕ → ℂ → M2} {A : ℂ → M2}
    (h : TendstoUniformlyOn As A atTop (strip δ)) (t : ℝ) :
    TendstoUniformlyOn (fun n => cshift (As n) t) (cshift A t) atTop (strip (δ - |t|)) := by
  have h2 : TendstoUniformlyOn (fun n => cshift (As n) t) (cshift A t) atTop
      ((fun z : ℂ => z + t * I) ⁻¹' strip δ) := h.comp _
  refine h2.mono ?_
  intro z hz
  simp only [strip, mem_preimage, Set.mem_ofPred_eq] at hz ⊢
  simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  calc |z.im + t| ≤ |z.im| + |t| := abs_add_le _ _
    _ < δ := by linarith

lemma L_tendsto_shift (hJKS : JKSHyp) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    {α : ℝ} (hα : Irrational α) {rs : ℕ → ℝ} (hrs : Tendsto rs atTop (𝓝 α))
    {As : ℕ → ℂ → M2} (hAs : ∀ n, IsAnalyticCocycle δ (As n))
    (hconv : TendstoUniformlyOn As A atTop (strip δ)) {t : ℝ} (ht : |t| < δ) :
    Tendsto (fun n => L (rs n) (As n) t) atTop (𝓝 (L α A t)) := by
  have h := hJKS (hA.cshift ht) hα (fun n => (hAs n).cshift ht) hrs
    (tendstoUniformlyOn_cshift hconv t)
  simpa [L_cshift] using h

lemma rat_coprime (r : ℚ) : IsCoprime r.num (r.den : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  simpa using r.reduced

set_option maxHeartbeats 1000000 in
/-- **Lemma `per`, core estimate** (estimate (201) at the real line): if `(α, A)` is regular
with positive exponent, `p_n/q_n → α` and `A_n → A` on the strip, then the traces of the period
products of `A_n` are large on the real line. -/
theorem perCore (hJKS : JKSHyp) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) {η0 a b : ℝ} (hη0 : 0 < η0)
    (haff : ∀ t, |t| < η0 → L α A t = a + b * t) (ha : 0 < a)
    {rs : ℕ → ℚ} (hrs : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α))
    {As : ℕ → ℂ → M2} (hAs : ∀ n, IsAnalyticCocycle δ (As n))
    (hconv : TendstoUniformlyOn As A atTop (strip δ)) :
    ∀ᶠ n in atTop, ∀ x : ℝ, 2 < ‖(perIter (As n) (rs n).num (rs n).den x).trace‖ := by
  have hδ := hA.pos
  have hpi := Real.pi_pos
  set ε' := min η0 δ / 2 with hε'
  have hmin := lt_min hη0 hδ
  have hε'0 : 0 < ε' := by positivity
  have hε'η : ε' < η0 := by have := min_le_left η0 δ; linarith
  have hε'δ : ε' < δ := by have := min_le_right η0 δ; linarith
  set η := (δ - ε') / 4 with hη
  have hη0' : 0 < η := by rw [hη]; linarith
  obtain ⟨C0, hC01, hC0⟩ := exists_bound_strip hA (ε := ε' + 2 * η) (by rw [hη]; linarith)
  set C := C0 + 1 with hCdef
  have hC1 : 1 ≤ C := by linarith
  obtain ⟨k0, hk0⟩ := exists_nat_ge (Real.log C / (Real.pi * η))
  have hpe : 0 < Real.pi * η := by positivity
  have hk0' : Real.log C ≤ Real.pi * η * (k0 + 1) := by
    rw [div_le_iff₀ hpe] at hk0
    nlinarith
  set e := min a (Real.pi * ε') / 8 with he
  have he0 : 0 < e := by have := lt_min ha (by positivity : 0 < Real.pi * ε'); positivity
  have hea : e ≤ a / 8 := by have := min_le_left a (Real.pi * ε'); rw [he]; linarith
  have heπ : e ≤ Real.pi * ε' / 8 := by
    have := min_le_right a (Real.pi * ε'); rw [he]; linarith
  set Ncard : ℝ := ((Finset.Icc (-(k0 : ℤ)) k0).card : ℝ) with hNcard
  have hNc0 : 0 ≤ Ncard := Nat.cast_nonneg _
  have hK0 := tailC_nonneg η
  have hE0 := errC_nonneg k0 η
  set Q0 : ℝ := 2 * errC k0 η / e + 2 * Ncard / (Real.pi * ε') +
    2 * (2 + tailC η) / (a - e) + 1 with hQ0
  have ev1 : ∀ᶠ n in atTop, ∀ z ∈ strip δ, ‖As n z - A z‖ < 1 := by
    have := Metric.tendstoUniformlyOn_iff.1 hconv 1 one_pos
    filter_upwards [this] with n hn z hz
    rw [← dist_eq_norm, dist_comm]; exact hn z hz
  have ev2 : ∀ t, |t| ≤ ε' → ∀ᶠ n in atTop, |L (rs n) (As n) t - (a + b * t)| < e / 2 := by
    intro t ht
    have hT := L_tendsto_shift hJKS hA hα hrs hAs hconv (t := t) (by linarith)
    rw [haff t (by linarith)] at hT
    have := (Metric.tendsto_nhds.1 hT) (e / 2) (by positivity)
    filter_upwards [this] with n hn
    rwa [Real.dist_eq] at hn
  have ev3 : ∀ᶠ n in atTop, Q0 ≤ ((rs n).den : ℝ) := by
    have hden := tendsto_den_of_irrational hα hrs
    filter_upwards [hden.eventually_ge_atTop ⌈Q0⌉₊] with n hn
    exact (Nat.le_ceil Q0).trans (by exact_mod_cast hn)
  filter_upwards [ev1, ev2 0 (by simp; linarith), ev2 ε' (by rw [abs_of_pos hε'0]),
    ev2 (-ε') (by rw [abs_neg, abs_of_pos hε'0]), ev3] with n h1 h20 h2p h2m h3 x
  set p := (rs n).num
  set q := (rs n).den
  have hq : 0 < q := (rs n).den_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hcop := rat_coprime (rs n)
  have hrsq : ((rs n : ℚ) : ℝ) = (p : ℝ) / q := by rw [Rat.cast_def]
  have hCn : ∀ z : ℂ, |z.im| ≤ ε' + 2 * η → ‖As n z‖ ≤ C := by
    intro z hz
    have hzs : z ∈ strip δ := by
      show |z.im| < δ
      rw [hη] at hz; linarith
    have := norm_le_norm_sub_add (As n z) (A z)
    have := h1 z hzs
    have := hC0 z hz
    rw [hCdef]; linarith
  set c := cfun (As n) k0 ε' p q with hc
  have hest : ∀ t ∈ Icc (-ε') ε', |L (rs n) (As n) t - plModel k0 c t| ≤ errC k0 η / q := by
    intro t ht
    rw [hrsq]
    exact rational_estimate (hAs n) hε'0 hη0' (by rw [hη]; linarith) hC1 hCn hk0' p hq hcop ht
  have herr : errC k0 η / q < e / 2 := by
    rw [div_lt_iff₀ hqpos]
    have h2 : 2 * errC k0 η / e + 1 ≤ Q0 := by
      rw [hQ0]
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * Ncard) (by positivity : (0 : ℝ) ≤ Real.pi * ε')
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * (2 + tailC η)) (by linarith : (0 : ℝ) ≤ a - e)
      linarith
    have h4 : 2 * errC k0 η / e < q := by linarith
    rw [div_lt_iff₀ he0] at h4
    linarith
  have hM : ∀ t, |t| ≤ ε' → |L (rs n) (As n) t - (a + b * t)| < e / 2 →
      |plModel k0 c t - (a + b * t)| < e := by
    intro t ht hL
    have := hest t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    rw [abs_lt] at hL ⊢
    rw [abs_le] at this
    constructor <;> linarith
  have hM0 := hM 0 (by simp; linarith) h20
  have hMp := hM ε' (by rw [abs_of_pos hε'0]) h2p
  have hMm := hM (-ε') (by rw [abs_neg, abs_of_pos hε'0]) h2m
  rw [abs_lt] at hM0 hMp hMm
  set S : Finset ℤ := Finset.Icc (-(k0 : ℤ)) k0 with hS
  have hSne : S.Nonempty := ⟨0, by simp [hS]⟩
  have hup : ∀ t, ∀ j ∈ S, c j - 2 * Real.pi * j * t ≤ plModel k0 c t := fun t j hj =>
    (Finset.le_sup' (fun k => c k - 2 * Real.pi * k * t) hj).trans (le_max_right _ _)
  obtain ⟨k, hkS, hk⟩ : ∃ k ∈ S, a - e < c k := by
    have hpos : 0 < plModel k0 c 0 := by linarith
    have hsup : plModel k0 c 0 = S.sup' hSne (fun k => c k - 2 * Real.pi * k * 0) := by
      unfold plModel
      refine max_eq_right ?_
      by_contra hneg
      push Not at hneg
      have : plModel k0 c 0 = 0 := max_eq_left hneg.le
      linarith
    obtain ⟨k, hkS, hk⟩ := Finset.exists_mem_eq_sup' hSne (fun k => c k - 2 * Real.pi * k * 0)
    refine ⟨k, hkS, ?_⟩
    have : plModel k0 c 0 = c k := by rw [hsup, hk]; ring
    linarith
  have hkp := hup ε' k hkS
  have hkm := hup (-ε') k hkS
  have hgap : ∀ j ∈ S, j ≠ k → c j ≤ c k - Real.pi * ε' := by
    intro j hj hjk
    have hjp := hup ε' j hj
    have hjm := hup (-ε') j hj
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_left hjk' (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ε')
      linarith [hjp, hkm, hMp.2, hMm.2, hk, heπ]
    · have hjk' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hgt
      have := mul_le_mul_of_nonneg_left hjk' (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ε')
      linarith [hjm, hkp, hMp.2, hMm.2, hk, heπ]
  set g := trPer (As n) p q with hg
  set fa : ℤ → ℂ := fun j => fcoef g (j * q) 0 with hfa
  have hfa_le : ∀ j, ‖fa j‖ ≤ Real.exp (q * c j) := by
    intro j
    by_cases h0 : fa j = 0
    · rw [h0, norm_zero]; positivity
    · have hcj : c j = (1 / (q : ℝ)) * Real.log ‖fa j‖ := by
        simp only [hc, cfun]; rw [if_neg h0]
      rw [hcj, ← mul_assoc, mul_one_div_cancel hqpos.ne', one_mul,
        Real.exp_log (norm_pos_iff.2 h0)]
  have hfa_k : ‖fa k‖ = Real.exp (q * c k) := by
    have h0 : fa k ≠ 0 := by
      intro h0
      have : c k = -(2 * Real.pi * k0 * ε' + 1) := by
        simp only [hc, cfun]; rw [if_pos h0]
      have : 0 ≤ 2 * Real.pi * k0 * ε' := by positivity
      linarith
    have hcj : c k = (1 / (q : ℝ)) * Real.log ‖fa k‖ := by
      simp only [hc, cfun]; rw [if_neg h0]
    rw [hcj, ← mul_assoc, mul_one_div_cancel hqpos.ne', one_mul,
      Real.exp_log (norm_pos_iff.2 h0)]
  have hstrip : strip (ε' + 2 * η) ⊆ strip δ := fun z hz => by
    show |z.im| < δ
    have : |z.im| < ε' + 2 * η := hz
    rw [hη] at this; linarith
  have hgd : DifferentiableOn ℂ g (strip (ε' + 2 * η)) :=
    (differentiableOn_trace (differentiableOn_citer (hAs n) _ q)).mono hstrip
  have hgper : ∀ z, g (z + 1) = g z := fun z => by
    simp only [hg, trPer, perIter, citer_periodic (hAs n).periodic]
  have hgperq : ∀ x : ℝ, g (x + 1 / q) = g x := fun x =>
    trace_perIter_periodic (hAs n).periodic hq hcop x (fun w hw => (hAs n).det_eq_one w (by
      show |w.im| < δ
      rw [hw, Complex.ofReal_im, abs_zero]; exact hδ))
  have hgb : ∀ z ∈ strip (ε' + 2 * η), ‖g z‖ ≤ 2 * C ^ q := fun z hz => by
    refine (norm_trace_le _).trans ?_
    have := norm_citer_le (A := As n) (α := (p : ℝ) / q) (by linarith : (0 : ℝ) ≤ C)
      (y := z.im) (fun w hw => hCn w (by rw [hw]; exact le_of_lt hz)) q rfl
    simp only [perIter]
    linarith
  have htail := tail_bound (t := 0) hq hgd hgper hgperq hgb hC1 hη0' hk0'
    (by linarith : ε' + η < ε' + 2 * η) (by simp; linarith) x
  have e0 : ∀ j : ℤ, eC (j * q * (((0 : ℝ) : ℂ) * I)) = 1 := fun j => by simp [eC]
  simp only [e0, mul_one] at htail
  have hgx : g (x + ((0 : ℝ) : ℂ) * I) = (perIter (As n) p q x).trace := by simp [hg, trPer]
  rw [hgx] at htail
  set T := trigP k0 q (fun j => fcoef g (j * q) 0) x with hT
  have hTsplit : T = fa k * eC (k * q * x) +
      ∑ j ∈ S.erase k, fa j * eC (j * q * x) := by
    rw [hT, trigP, ← Finset.add_sum_erase _ _ hkS]
  have hrest : ‖∑ j ∈ S.erase k, fa j * eC (j * q * x)‖ ≤
      Ncard * (Real.exp (q * c k) * Real.exp (-(q * (Real.pi * ε')))) := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ j ∈ S.erase k, ‖fa j * eC (j * q * x)‖ ≤
        Real.exp (q * c k) * Real.exp (-(q * (Real.pi * ε'))) := by
      intro j hj
      rw [norm_mul, norm_eC]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
        Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
        add_zero, Real.exp_zero, mul_one]
      rw [← Real.exp_add]
      refine (hfa_le j).trans (Real.exp_le_exp.2 ?_)
      have := hgap j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
      have := mul_le_mul_of_nonneg_left this hqpos.le
      linarith
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hNcard]
    exact_mod_cast Finset.card_erase_le
  have hmain : ‖fa k * eC (k * q * x)‖ = Real.exp (q * c k) := by
    rw [norm_mul, norm_eC, hfa_k]
    simp
  have hsmall : Ncard * Real.exp (-(q * (Real.pi * ε'))) ≤ 1 / 2 := by
    have hq2 : 2 * Ncard / (Real.pi * ε') ≤ q := by
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * errC k0 η) he0.le
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * (2 + tailC η)) (by linarith : (0 : ℝ) ≤ a - e)
      rw [hQ0] at h3; linarith
    rw [div_le_iff₀ (by positivity)] at hq2
    have hexp := Real.add_one_le_exp (q * (Real.pi * ε'))
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have hT_ge : Real.exp (q * c k) / 2 ≤ ‖T‖ := by
    rw [hTsplit]
    have := norm_sub_norm_le (fa k * eC (k * q * x)) (-(∑ j ∈ S.erase k, fa j * eC (j * q * x)))
    rw [sub_neg_eq_add, norm_neg, hmain] at this
    have h5 : Ncard * (Real.exp (q * c k) * Real.exp (-(q * (Real.pi * ε')))) ≤
        Real.exp (q * c k) / 2 := by
      have := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (q * c k)).le
      nlinarith
    linarith
  have hbig : 2 + tailC η < Real.exp (q * c k) / 2 := by
    have hq3 : 2 * (2 + tailC η) / (a - e) ≤ q := by
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * errC k0 η) he0.le
      have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * Ncard) (by positivity : (0 : ℝ) ≤ Real.pi * ε')
      rw [hQ0] at h3; linarith
    rw [div_le_iff₀ (by linarith)] at hq3
    have h6 : q * (a - e) ≤ q * c k := mul_le_mul_of_nonneg_left hk.le hqpos.le
    have h7 := Real.add_one_le_exp (q * c k)
    have h8 : (0 : ℝ) ≤ 1 := zero_le_one
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have := norm_sub_norm_le T ((perIter (As n) p q x).trace)
  rw [norm_sub_rev] at htail
  have htail' : ‖T - (perIter (As n) p q x).trace‖ ≤ tailC η := by
    simpa [hT] using htail
  linarith

/-! ### Logarithmic derivative bound (harmonicity of `log |g|`) -/

/-- If `g` is holomorphic on a disc of radius `R` with `1 ≤ |g| ≤ M`, then
`|g'(0)| ≤ 4 (log M + 1)/R · |g(0)|`. -/
theorem logDeriv_bound {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R))
    (h1 : ∀ s ∈ Metric.ball (0 : ℂ) R, 1 ≤ ‖g s‖) (hM : ∀ s ∈ Metric.ball (0 : ℂ) R, ‖g s‖ ≤ M) :
    ‖deriv g 0‖ ≤ 4 * (Real.log M + 1) / R * ‖g 0‖ := by
  set B := Metric.ball (0 : ℂ) R with hBdef
  have hB : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self hR
  have hne : ∀ s ∈ B, g s ≠ 0 := fun s hs h => by
    have := h1 s hs; rw [h, norm_zero] at this; linarith
  have hM1 : 1 ≤ M := (h1 0 h0B).trans (hM 0 h0B)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  set f : ℂ → ℂ := fun s => deriv g s / g s with hfdef
  have hf : DifferentiableOn ℂ f B := (hg.deriv hB).div hg hne
  obtain ⟨ℓ, hℓ⟩ := hf.isExactOn_ball
  set h : ℂ → ℂ := fun s => g s * Complex.exp (-(ℓ s - ℓ 0)) with hhdef
  have hderiv : ∀ s ∈ B, HasDerivAt h 0 s := by
    intro s hs
    have hgd : HasDerivAt g (deriv g s) s := (hg.differentiableAt (hB.mem_nhds hs)).hasDerivAt
    have hl := (((hℓ s hs).sub_const (ℓ 0)).neg).cexp
    have := hgd.mul hl
    convert this using 1
    have hgs := hne s hs
    simp only [hfdef]
    field_simp
    ring
  have hconst : ∀ s ∈ B, h s = h 0 := fun s hs =>
    hB.is_const_of_deriv_eq_zero (convex_ball 0 R).isPreconnected
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).deriv) hs h0B
  set F : ℂ → ℂ := fun s => ℓ s - ℓ 0 with hFdef
  have hFexp : ∀ s ∈ B, g s = g 0 * Complex.exp (F s) := by
    intro s hs
    have e := hconst s hs
    simp only [hhdef, sub_self, neg_zero, Complex.exp_zero, mul_one] at e
    rw [← e, mul_assoc, ← Complex.exp_add]
    simp [hFdef]
  have hReF : ∀ s ∈ B, (F s).re ≤ Real.log M + 1 := by
    intro s hs
    have e := congrArg norm (hFexp s hs)
    rw [norm_mul, Complex.norm_exp] at e
    have hg0 := h1 0 h0B
    have hexp : Real.exp (F s).re ≤ M := by
      have := hM s hs
      rw [e] at this
      nlinarith [Real.exp_pos (F s).re]
    have := (Real.le_log_iff_exp_le (by linarith)).2 hexp
    linarith
  have hFd : DifferentiableOn ℂ F B := fun s hs =>
    ((hℓ s hs).differentiableAt.sub_const _).differentiableWithinAt
  have hBC : ∀ s ∈ B, ‖F s‖ ≤ 2 * (Real.log M + 1) * ‖s‖ / (R - ‖s‖) := fun s hs =>
    Complex.borelCaratheodory_zero (by positivity) hFd (fun t ht => hReF t ht) hR hs
      (by simp [hFdef])
  have hcl : DiffContOnCl ℂ F (Metric.ball 0 (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    refine hFd.mono ?_
    rw [closure_ball _ (by positivity : R / 2 ≠ 0)]
    exact Metric.closedBall_subset_ball (by linarith)
  have hsph : ∀ s ∈ Metric.sphere (0 : ℂ) (R / 2), ‖F s‖ ≤ 2 * (Real.log M + 1) := by
    intro s hs
    have hn : ‖s‖ = R / 2 := by simpa using hs
    have hsB : s ∈ B := by rw [hBdef, Metric.mem_ball, dist_zero_right, hn]; linarith
    have := hBC s hsB
    rw [hn] at this
    have e : 2 * (Real.log M + 1) * (R / 2) / (R - R / 2) = 2 * (Real.log M + 1) := by
      field_simp; ring
    linarith
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hcl hsph
  have hF0 : deriv F 0 = f 0 := ((hℓ 0 h0B).sub_const (ℓ 0)).deriv
  rw [hF0] at hd
  have hg0 : g 0 ≠ 0 := hne 0 h0B
  have e1 : deriv g 0 = f 0 * g 0 := by simp only [hfdef]; field_simp
  rw [e1, norm_mul]
  have e2 : 2 * (Real.log M + 1) / (R / 2) = 4 * (Real.log M + 1) / R := by field_simp; ring
  rw [e2] at hd
  exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)

/-! ### Derivative of a perturbed period product -/

lemma citer_add (α : ℝ) (A : ℂ → M2) (m n : ℕ) (z : ℂ) :
    citer α A (n + m) z = citer α A m (z + n * α) * citer α A n z := by
  induction m with
  | zero => simp [citer]
  | succ m ih =>
    rw [← add_assoc, citer, ih, citer, mul_assoc]
    congr 2
    push_cast; ring

/-- The derivative of the perturbed product (explicit sum). -/
def dSum (β : ℝ) (A W : ℂ → M2) (n : ℕ) (z : ℂ) : M2 :=
  ∑ j ∈ Finset.range n, citer β A (n - (j + 1)) (z + ((j + 1 : ℕ) : ℂ) * β) *
    (A (z + (j : ℂ) * β) * W (z + (j : ℂ) * β)) * citer β A j z

lemma dSum_succ (β : ℝ) (A W : ℂ → M2) (n : ℕ) (z : ℂ) :
    dSum β A W (n + 1) z = A (z + (n : ℂ) * β) * W (z + (n : ℂ) * β) * citer β A n z +
      A (z + (n : ℂ) * β) * dSum β A W n z := by
  unfold dSum
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp [citer]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have e : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
    rw [e, citer]
    have e2 : z + ((j + 1 : ℕ) : ℂ) * β + ((n - (j + 1) : ℕ) : ℂ) * β = z + (n : ℂ) * β := by
      rw [Nat.cast_sub hj']; push_cast; ring
    rw [e2]
    simp only [mul_assoc]

lemma hasDerivAt_citer_pert (β : ℝ) (A W : ℂ → M2) (n : ℕ) (z : ℂ) :
    HasDerivAt (fun s : ℂ => citer β (fun w => A w * (1 + s • W w)) n z) (dSum β A W n z) 0 := by
  induction n with
  | zero =>
    have e : dSum β A W 0 z = 0 := by simp [dSum]
    rw [e]
    exact hasDerivAt_const _ _
  | succ n ih =>
    set w0 := z + (n : ℂ) * β with hw0
    have h1 : HasDerivAt (fun s : ℂ => (1 : M2) + s • W w0) (W w0) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).smul_const (W w0)).const_add (1 : M2)
      simp only [id, one_smul] at this
      exact this
    have hB : HasDerivAt (fun s : ℂ => A w0 * (1 + s • W w0)) (A w0 * W w0) 0 :=
      h1.const_mul (A w0)
    have e : (fun s : ℂ => citer β (fun w => A w * (1 + s • W w)) (n + 1) z) =
        fun s => (A w0 * (1 + s • W w0)) * citer β (fun w => A w * (1 + s • W w)) n z := rfl
    rw [e, dSum_succ]
    have key := hB.mul ih
    simp only [zero_smul, add_zero, mul_one] at key
    exact key

lemma citer_int_periodic {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (β : ℝ) (n : ℕ) (m : ℤ)
    (z : ℂ) : citer β A n (z + m) = citer β A n z := by
  have h : Function.Periodic (citer β A n) 1 := fun w => citer_periodic hper β n w
  simpa using (h.int_mul m) z

lemma perIter_rotate {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (p : ℤ) {q : ℕ} (hq : 0 < q)
    (z : ℂ) {j : ℕ} (hj : j < q) :
    perIter A p q (z + (j : ℂ) * ((p : ℝ) / q : ℝ)) =
      citer ((p : ℝ) / q) A j z *
        citer ((p : ℝ) / q) A (q - (j + 1)) (z + ((j + 1 : ℕ) : ℂ) * ((p : ℝ) / q : ℝ)) *
          A (z + (j : ℂ) * ((p : ℝ) / q : ℝ)) := by
  unfold perIter
  set β : ℝ := (p : ℝ) / q with hβ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 := citer_add β A j (q - j) (z + (j : ℂ) * β)
  rw [Nat.sub_add_cancel hj.le] at h1
  rw [h1]
  have e2 : z + (j : ℂ) * β + ((q - j : ℕ) : ℂ) * β = z + (p : ℤ) := by
    rw [Nat.cast_sub hj.le, hβ]; push_cast; field_simp; ring
  rw [e2, citer_int_periodic hper]
  have e3 : q - j = (q - (j + 1)) + 1 := by omega
  rw [e3, citer_succ']
  have e4 : z + (j : ℂ) * β + (β : ℂ) = z + ((j + 1 : ℕ) : ℂ) * β := by push_cast; ring
  rw [e4, mul_assoc]

lemma trace_dSum {A W : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (p : ℤ) {q : ℕ} (hq : 0 < q)
    (z : ℂ) :
    (dSum ((p : ℝ) / q) A W q z).trace = ∑ j ∈ Finset.range q,
      (perIter A p q (z + (j : ℂ) * ((p : ℝ) / q : ℝ)) *
        W (z + (j : ℂ) * ((p : ℝ) / q : ℝ))).trace := by
  unfold dSum
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [perIter_rotate hper p hq z (Finset.mem_range.1 hj), Matrix.trace_mul_comm]
  simp only [mul_assoc]

/-! ### Arzelà–Ascoli for uniformly Lipschitz periodic families -/

lemma continuous_of_lip {f : ℝ → M2} {L0 : ℝ} (hlip : ∀ x y, ‖f x - f y‖ ≤ L0 * |x - y|) :
    Continuous f := by
  refine Metric.continuous_iff.mpr ?_
  intro x ε hε
  have hL0 : 0 ≤ L0 := by
    have := hlip 1 0
    norm_num at this
    exact (norm_nonneg _).trans this
  refine ⟨ε / (L0 + 1), by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm]
  rw [Real.dist_eq] at hy
  calc ‖f y - f x‖ ≤ L0 * |y - x| := hlip y x
    _ ≤ L0 * (ε / (L0 + 1)) := mul_le_mul_of_nonneg_left hy.le hL0
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem exists_uniform_subseq {f : ℕ → ℝ → M2} {K L0 : ℝ}
    (hb : ∀ n x, ‖f n x‖ ≤ K) (hlip : ∀ n x y, ‖f n x - f n y‖ ≤ L0 * |x - y|)
    (hp : ∀ n, Function.Periodic (f n) 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℝ → M2, Continuous F ∧ Function.Periodic F 1 ∧
      TendstoUniformly (fun n => f (φ n)) F atTop := by
  have hL0 : 0 ≤ L0 := by
    have := hlip 0 1 0
    norm_num at this
    exact (norm_nonneg _).trans this
  have hcont : ∀ n, Continuous (f n) := fun n => continuous_of_lip (hlip n)
  let X := Icc (0 : ℝ) 1
  let g : ℕ → BoundedContinuousFunction X M2 := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => f n x, (hcont n).comp continuous_subtype_val⟩
  have hg : ∀ n (x : X), g n x = f n x := fun n x => rfl
  set S := Set.range g with hS
  have hin : ∀ (h : BoundedContinuousFunction X M2) (x : X), h ∈ S →
      h x ∈ Metric.closedBall (0 : M2) K := by
    rintro h x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hg]
    exact hb n x
  have heq : Equicontinuous fun h : S => ((h : BoundedContinuousFunction X M2) : X → M2) := by
    intro x₀
    refine Metric.equicontinuousAt_iff.mpr ?_
    intro ε hε
    refine ⟨ε / (L0 + 1), by positivity, fun x hx h => ?_⟩
    obtain ⟨n, hn⟩ := h.2
    rw [← hn, hg, hg, dist_eq_norm]
    have hx' : |(x : ℝ) - x₀| < ε / (L0 + 1) := by
      rw [Subtype.dist_eq, Real.dist_eq] at hx; exact hx
    calc ‖f n x₀ - f n x‖ ≤ L0 * |(x₀ : ℝ) - x| := hlip n x₀ x
      _ ≤ L0 * (ε / (L0 + 1)) := by rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hx'.le hL0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hcomp := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : M2) K)
    (isCompact_closedBall 0 K) S hin heq
  obtain ⟨G, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := g) (fun n => subset_closure ⟨n, rfl⟩)
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  set Fr : ℝ → M2 := fun t => G (Set.projIcc 0 1 h01 t) with hFr
  have hFrc : Continuous Fr := G.continuous.comp continuous_projIcc
  have hev : ∀ x : X, Tendsto (fun n => f (φ n) x) atTop (𝓝 (G x)) := by
    intro x
    have h2 := tendsto_iff_dist_tendsto_zero.mp hlim
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h2
    exact BoundedContinuousFunction.dist_coe_le_dist (f := g (φ n)) (g := G) x
  have hFr01 : Fr 0 = Fr 1 := by
    have h0 := hev ⟨0, left_mem_Icc.2 h01⟩
    have h1 := hev ⟨1, right_mem_Icc.2 h01⟩
    have e : (fun n => f (φ n) ((⟨1, right_mem_Icc.2 h01⟩ : X) : ℝ)) =
        fun n => f (φ n) ((⟨0, left_mem_Icc.2 h01⟩ : X) : ℝ) := by
      funext n; simpa using hp (φ n) 0
    rw [e] at h1
    have := tendsto_nhds_unique h0 h1
    simp only [hFr, Set.projIcc_left, Set.projIcc_right]
    exact this
  refine ⟨φ, hφ, Fr ∘ Int.fract, ContinuousOn.comp_fract'' hFrc.continuousOn hFr01, ?_, ?_⟩
  · intro x; simp [Int.fract_add_one]
  · refine Metric.tendstoUniformly_iff.mpr ?_
    intro ε hε
    have := Metric.tendsto_nhds.1 hlim ε hε
    filter_upwards [this] with n hn x
    have hm : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have e1 : (Fr ∘ Int.fract) x = G ⟨Int.fract x, hm⟩ := by
      simp only [Function.comp, hFr, Set.projIcc_of_mem h01 hm]
    have e2 : f (φ n) x = g (φ n) ⟨Int.fract x, hm⟩ := by
      rw [hg]; exact (periodic_fract_eq (hp (φ n)) x).symm
    rw [e1, e2]
    have := BoundedContinuousFunction.dist_coe_le_dist (f := G) (g := g (φ n)) ⟨Int.fract x, hm⟩
    rw [dist_comm] at hn
    simp only [Function.comp] at hn
    linarith

/-! ### The derivative bound at periodic approximants (Lemma `gam`, pointwise form) -/

lemma deriv_jk_mul {τ0 : ℂ} (hτ : 2 < ‖τ0‖) :
    deriv jk τ0 * (jk τ0 - jkc τ0) = jk τ0 := by
  have hd := (differentiableAt_jk hτ).hasDerivAt
  have hlam := jk_ne_zero hτ
  have hsum := hd.add (hd.inv hlam)
  have hev : (fun σ => jk σ + (jk σ)⁻¹) =ᶠ[𝓝 τ0] id := by
    filter_upwards [isOpen_norm_gt_two.mem_nhds hτ] with σ hσ
    rw [← jkc_eq_inv hσ]
    exact jk_add_jkc σ
  have hid : HasDerivAt (fun σ => jk σ + (jk σ)⁻¹) 1 τ0 :=
    (hasDerivAt_id τ0).congr_of_eventuallyEq hev
  have huniq := hsum.unique hid
  rw [jkc_eq_inv hτ]
  calc deriv jk τ0 * (jk τ0 - (jk τ0)⁻¹)
      = jk τ0 * (deriv jk τ0 + -deriv jk τ0 / jk τ0 ^ 2) := by field_simp; ring
    _ = jk τ0 := by rw [huniq, mul_one]

lemma differentiable_citer_pert (β : ℝ) (A W : ℂ → M2) (n : ℕ) (z : ℂ) :
    Differentiable ℂ (fun s : ℂ => citer β (fun w => A w * (1 + s • W w)) n z) := by
  induction n with
  | zero => exact differentiable_const _
  | succ n ih =>
    have e : (fun s : ℂ => citer β (fun w => A w * (1 + s • W w)) (n + 1) z) =
        fun s => (A (z + (n : ℂ) * β) * (1 + s • W (z + (n : ℂ) * β))) *
          citer β (fun w => A w * (1 + s • W w)) n z := rfl
    rw [e]
    exact ((differentiable_const _).mul ((differentiable_const _).add
      (differentiable_id.smul_const _))).mul ih

lemma trace_perIter_shift {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z)
    (hdet : ∀ x : ℝ, (A x).det = 1) (p : ℤ) {q : ℕ} (hq : 0 < q) (x : ℝ) (j : ℕ) :
    (perIter A p q (x + (j : ℂ) * ((p : ℝ) / q : ℝ))).trace = (perIter A p q x).trace := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have hw : (x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ) = ((x + j * ((p : ℝ) / q) : ℝ) : ℂ) := by
      push_cast; ring
    have hdw : (A ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ))).det = 1 := by rw [hw]; exact hdet _
    have hu : IsUnit (A ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ))).det := by
      rw [hdw]; exact isUnit_one
    have hc := conj_relation hper p hq ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ))
    have e : (x : ℂ) + ((j + 1 : ℕ) : ℂ) * ((p : ℝ) / q : ℝ) =
        (x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ) + (p : ℂ) / q := by push_cast; ring
    rw [e]
    have : perIter A p q ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ) + (p : ℂ) / q) =
        A ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ)) *
          perIter A p q ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ)) *
            (A ((x : ℂ) + (j : ℂ) * ((p : ℝ) / q : ℝ)))⁻¹ := by
      rw [hc, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [this, Matrix.trace_mul_comm, ← mul_assoc, nonsing_inv_mul _ hu, one_mul]

lemma trace_specProj_mul (P W : M2) (hW : W.trace = 0) :
    (specProj P * W).trace = (jk P.trace - jkc P.trace)⁻¹ * (P * W).trace := by
  unfold specProj
  rw [smul_mul_assoc, Matrix.trace_smul, sub_mul, Matrix.trace_sub, smul_mul_assoc, one_mul,
    Matrix.trace_smul, hW, smul_eq_mul, smul_eq_mul, mul_zero, sub_zero]

/-- **Pointwise derivative bound.**  If the perturbations `A (1 + sW)`, `|s| < R`, of a cocycle
have hyperbolic period products on the real line and are bounded by `C`, then the orbit sums
`∑_j tr(Π(x + jp/q) W(x + jp/q))` (`Π` the expanding spectral projection) are bounded by
`4 (log 3 + q log C + 1)/R`. -/
theorem derivBound {At W : ℂ → M2} (hper : ∀ z, At (z + 1) = At z)
    (hdet : ∀ x : ℝ, (At x).det = 1) (htrW : ∀ z, (W z).trace = 0)
    (p : ℤ) {q : ℕ} (hq : 0 < q) {R C : ℝ} (hR : 0 < R) (hC : 1 ≤ C)
    (hhyp : ∀ s ∈ Metric.ball (0 : ℂ) R, ∀ x : ℝ,
      2 < ‖(perIter (fun w => At w * (1 + s • W w)) p q x).trace‖)
    (hbd : ∀ s ∈ Metric.ball (0 : ℂ) R, ∀ x : ℝ, ‖At x * (1 + s • W x)‖ ≤ C) (x : ℝ) :
    ‖∑ j ∈ Finset.range q, (specProj (perIter At p q (x + (j : ℂ) * ((p : ℝ) / q : ℝ))) *
        W (x + (j : ℂ) * ((p : ℝ) / q : ℝ))).trace‖ ≤
      4 * (Real.log 3 + q * Real.log C + 1) / R := by
  set τ : ℂ → ℂ := fun s => (perIter (fun w => At w * (1 + s • W w)) p q x).trace with hτ
  have hB0 : (fun w => At w * (1 + (0 : ℂ) • W w)) = At := by funext w; simp
  have hτ0 : τ 0 = (perIter At p q x).trace := by simp only [hτ, hB0]
  have hτd : HasDerivAt τ (dSum ((p : ℝ) / q) At W q x).trace 0 := by
    have h := hasDerivAt_citer_pert ((p : ℝ) / q) At W q (x : ℂ)
    have h00 := (entryCLM 0 0).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h
    have h11 := (entryCLM 1 1).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h
    have hs := h00.add h11
    simp only [Function.comp_def, entryCLM_apply] at hs
    rw [Matrix.trace_fin_two]
    convert hs using 1
    · funext s
      simp only [hτ, perIter, Matrix.trace_fin_two, Pi.add_apply]
    · first | rfl | simp [entryCLM_apply]
  have hτdiff : Differentiable ℂ τ := by
    have h := differentiable_citer_pert ((p : ℝ) / q) At W q (x : ℂ)
    have h00 := (entryCLM 0 0).differentiable.comp h
    have h11 := (entryCLM 1 1).differentiable.comp h
    have hs := h00.add h11
    convert hs using 1
    funext s
    simp only [hτ, perIter, Matrix.trace_fin_two, Function.comp_def, entryCLM_apply, Pi.add_apply]
  set g : ℂ → ℂ := fun s => jk (τ s) with hgdef
  have hg : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    intro s hs
    have hgs : DifferentiableAt ℂ jk (τ s) := differentiableAt_jk (hhyp s hs x)
    exact (hgs.comp s (hτdiff s)).differentiableWithinAt
  have hg1 : ∀ s ∈ Metric.ball (0 : ℂ) R, 1 ≤ ‖g s‖ := fun s hs =>
    (one_lt_norm_jk (hhyp s hs x)).le
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hCq : 1 ≤ C ^ q := one_le_pow₀ hC
  have hgM : ∀ s ∈ Metric.ball (0 : ℂ) R, ‖g s‖ ≤ 3 * C ^ q := by
    intro s hs
    refine (norm_jk_le (hhyp s hs x)).trans ?_
    have hb : ∀ w : ℂ, w.im = 0 → ‖At w * (1 + s • W w)‖ ≤ C := by
      intro w hw
      have : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw]
      rw [this]; exact hbd s hs w.re
    have hP := norm_citer_le (A := fun w => At w * (1 + s • W w)) (α := (p : ℝ) / q) hC0
      (y := 0) hb q (z := (x : ℂ)) (by simp)
    have htr := norm_trace_le (perIter (fun w => At w * (1 + s • W w)) p q x)
    simp only [perIter] at htr
    simp only [hτ, perIter]
    linarith
  have hlog := logDeriv_bound hR hg hg1 hgM
  have hlog3 : Real.log (3 * C ^ q) = Real.log 3 + q * Real.log C := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  rw [hlog3] at hlog
  have hτ0' : 2 < ‖τ 0‖ := hhyp 0 (Metric.mem_ball_self hR) x
  have hgd : HasDerivAt g (deriv jk (τ 0) * (dSum ((p : ℝ) / q) At W q x).trace) 0 :=
    (differentiableAt_jk hτ0').hasDerivAt.comp 0 hτd
  rw [hgd.deriv] at hlog
  have hlam := jk_ne_zero hτ0'
  have hD := jk_sub_jkc_ne_zero hτ0'
  have hdj := deriv_jk_mul hτ0'
  have hsum : ∑ j ∈ Finset.range q, (specProj (perIter At p q (x + (j : ℂ) * ((p : ℝ) / q : ℝ))) *
        W (x + (j : ℂ) * ((p : ℝ) / q : ℝ))).trace =
      (jk (τ 0) - jkc (τ 0))⁻¹ * (dSum ((p : ℝ) / q) At W q x).trace := by
    rw [trace_dSum hper p hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [trace_specProj_mul _ _ (htrW _), trace_perIter_shift hper hdet p hq x j, hτ0]
  rw [hsum]
  have hinv' : (jk (τ 0) - jkc (τ 0))⁻¹ = deriv jk (τ 0) / jk (τ 0) := by
    rw [eq_div_iff hlam]
    calc (jk (τ 0) - jkc (τ 0))⁻¹ * jk (τ 0)
        = (jk (τ 0) - jkc (τ 0))⁻¹ * (deriv jk (τ 0) * (jk (τ 0) - jkc (τ 0))) := by rw [hdj]
      _ = deriv jk (τ 0) := by field_simp
  have key : (jk (τ 0) - jkc (τ 0))⁻¹ * (dSum ((p : ℝ) / q) At W q x).trace =
      deriv jk (τ 0) * (dSum ((p : ℝ) / q) At W q x).trace / g 0 := by
    simp only [hgdef]
    rw [hinv']
    ring
  rw [key, norm_div]
  have hg0 : 0 < ‖g 0‖ := lt_of_lt_of_le one_pos (hg1 0 (Metric.mem_ball_self hR))
  rw [div_le_iff₀ hg0]
  exact hlog

/-! ### Robust hyperbolicity of periodic approximants (Lemma `per`, neighbourhood form) -/

lemma IsAnalyticCocycle.mono' {δ δ' : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    (h0 : 0 < δ') (h : δ' ≤ δ) : IsAnalyticCocycle δ' A := by
  have hsub : strip δ' ⊆ strip δ := fun z (hz : |z.im| < δ') => (lt_of_lt_of_le hz h : |z.im| < δ)
  exact ⟨h0, hA.holo.mono hsub, hA.periodic, fun z hz => hA.det_eq_one z (hsub hz)⟩

lemma norm_sub_of_re_eq {z w : ℂ} (h : z.re = w.re) : ‖z - w‖ = |z.im - w.im| := by
  have e : z - w = ((z.im - w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [h]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma unif_cont_strip {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {Y : ℝ} (hY : Y < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ z w : ℂ, |z.im| ≤ Y → |w.im| ≤ Y → z.re = w.re → |z.im - w.im| < η →
      ‖A z - A w‖ < ε := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-Y) Y) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : Icc (0 : ℝ) 1 ×ℂ Icc (-Y) Y ⊆ strip δ := by
    intro z hz
    rw [mem_reProdIm] at hz
    show |z.im| < δ
    rw [abs_lt]; constructor <;> linarith [hz.2.1, hz.2.2]
  have hu := hK.uniformContinuousOn_of_continuous (hA.continuousOn.mono hsub)
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨η, hη, fun z w hz hw hre him => ?_⟩
  set n : ℤ := ⌊z.re⌋
  have hz' : A z = A (z - n) := by
    have := periodic_int hA.periodic n (z - n); rw [sub_add_cancel] at this; exact this
  have hw' : A w = A (w - n) := by
    have := periodic_int hA.periodic n (w - n); rw [sub_add_cancel] at this; exact this
  rw [hz', hw', ← dist_eq_norm]
  have hmem : ∀ v : ℂ, v.re = z.re → |v.im| ≤ Y → v - n ∈ Icc (0 : ℝ) 1 ×ℂ Icc (-Y) Y := by
    intro v hv hvY
    rw [mem_reProdIm]
    have h1 : (v - (n : ℂ)).re = v.re - n := by simp
    have h2 : (v - (n : ℂ)).im = v.im := by simp
    rw [h1, h2, hv]
    exact ⟨⟨by linarith [Int.floor_le z.re], by linarith [Int.lt_floor_add_one z.re]⟩,
      abs_le.1 hvY⟩
  refine h _ (hmem z rfl hz) _ (hmem w hre.symm hw) ?_
  rw [dist_eq_norm, norm_sub_of_re_eq (by simp [hre])]
  simpa using him

/-- **Lemma `per`, neighbourhood form.** -/
theorem robustPer (hJKS : JKSHyp) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) {η0 a b : ℝ} (hη0 : 0 < η0)
    (haff : ∀ t, |t| < η0 → L α A t = a + b * t)
    {T d : ℝ} (hT : 0 ≤ T) (hTη : T < η0) (hpos : ∀ t, |t| ≤ T → 0 < a + b * t) (hd : 0 < d)
    (hdT : d + T < δ) :
    ∃ ρ > 0, ∃ r0 > 0, ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ B : ℂ → M2, IsAnalyticCocycle d B →
      ∀ t : ℝ, |t| ≤ T → (∀ z ∈ strip d, ‖B z - A (z + t * I)‖ ≤ r0) →
        ∀ x : ℝ, 2 < ‖(perIter B r.num r.den x).trace‖ := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ r : ℚ, |(r : ℝ) - α| < 1 / ((n : ℝ) + 1) ∧ ∃ B : ℂ → M2,
      IsAnalyticCocycle d B ∧ ∃ t : ℝ, |t| ≤ T ∧
        (∀ z ∈ strip d, ‖B z - A (z + t * I)‖ ≤ 1 / ((n : ℝ) + 1)) ∧
          ∃ x : ℝ, ‖(perIter B r.num r.den x).trace‖ ≤ 2 :=
    fun n => hcon _ (by positivity) _ (by positivity)
  choose rs hrs Bs hBs ts hts hBclose xs hxs using hseq
  obtain ⟨ts0, hts0, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq (x := ts)
    (fun n => (abs_le.1 (hts n) : _ ∧ _) : ∀ n, ts n ∈ Icc (-T) T)
  have hts0' : |ts0| ≤ T := abs_le.2 hts0
  have hAt : IsAnalyticCocycle d (cshift A ts0) :=
    (hA.cshift (by linarith)).mono' hd (by linarith)
  have haff' : ∀ s, |s| < η0 - T → L α (cshift A ts0) s = (a + b * ts0) + b * s := by
    intro s hs
    rw [L_cshift, haff _ (by linarith [abs_add_le s ts0])]
    ring
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrsα : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) h1n)
    rw [Real.norm_eq_abs]; exact (hrs n).le
  have hφt := hφ.tendsto_atTop
  have hrsφ : Tendsto (fun n => ((rs (φ n) : ℚ) : ℝ)) atTop (𝓝 α) := hrsα.comp hφt
  have hconv : TendstoUniformlyOn (fun n => Bs (φ n)) (cshift A ts0) atTop (strip d) := by
    refine Metric.tendstoUniformlyOn_iff.mpr ?_
    intro ε hε
    obtain ⟨η, hη, hη'⟩ := unif_cont_strip hA (Y := d + T) hdT (by positivity : 0 < ε / 2)
    have ev1 : ∀ᶠ n in atTop, |ts (φ n) - ts0| < η := by
      have := (Metric.tendsto_nhds.1 hlim) η hη
      filter_upwards [this] with n hn
      rwa [Real.dist_eq] at hn
    have ev2 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < ε / 2 :=
      (h1n.comp hφt).eventually (gt_mem_nhds (by positivity))
    filter_upwards [ev1, ev2] with n hn1 hn2 z hz
    have hz' : |z.im| < d := hz
    rw [dist_eq_norm, norm_sub_rev]
    have e1 := hBclose (φ n) z hz
    have e2 := hη' (z + ts (φ n) * I) (z + ts0 * I)
      (by simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
            add_zero]
          linarith [abs_add_le z.im (ts (φ n)), hts (φ n)])
      (by simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
            add_zero]
          linarith [abs_add_le z.im ts0])
      (by simp)
      (by simpa using hn1)
    have := norm_sub_le_norm_sub_add_norm_sub (Bs (φ n) z) (A (z + ts (φ n) * I))
      (A (z + ts0 * I))
    simp only [cshift]
    linarith
  have hev := perCore hJKS hAt hα (by linarith : 0 < η0 - T) haff' (hpos ts0 hts0') hrsφ
    (fun n => hBs (φ n)) hconv
  obtain ⟨n, hn⟩ := hev.exists
  have := hn (xs (φ n))
  have := hxs (φ n)
  linarith

/-! ### Fourier bounds and uniform estimates -/

lemma exists_bound_periodic {T Y : ℝ} {f : ℂ → M2} (hf : ContinuousOn f (strip T))
    (hper : ∀ z, f (z + 1) = f z) (hY : Y < T) : ∃ M, ∀ z : ℂ, |z.im| ≤ Y → ‖f z‖ ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-Y) Y) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : Icc (0 : ℝ) 1 ×ℂ Icc (-Y) Y ⊆ strip T := by
    intro z hz
    rw [mem_reProdIm] at hz
    show |z.im| < T
    rw [abs_lt]; constructor <;> linarith [hz.2.1, hz.2.2]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨M, fun z hz => ?_⟩
  set n : ℤ := ⌊z.re⌋
  have hz' : f z = f (z - n) := by
    have := periodic_int hper n (z - n); rw [sub_add_cancel] at this; exact this
  rw [hz']
  refine hM _ ?_
  have h1 : (z - (n : ℂ)).re = z.re - n := by simp
  have h2 : (z - (n : ℂ)).im = z.im := by simp
  rw [mem_reProdIm, h1, h2]
  exact ⟨⟨by linarith [Int.floor_le z.re], by linarith [Int.lt_floor_add_one z.re]⟩,
    abs_le.1 hz⟩

lemma norm_le_of_entries (M : M2) {K : ℝ} (h : ∀ i j, ‖M i j‖ ≤ K) : ‖M‖ ≤ 2 * K := by
  obtain ⟨i, hi⟩ := exists_row_norm_eq M
  rw [hi]; linarith [h i 0, h i 1]

/-- Entries of a rank-one projection are controlled by its off-diagonal entries. -/
lemma proj_entry_bound {M : M2} (htr : M.trace = 1) (hdet : M.det = 0) {K : ℝ} (hK : 0 ≤ K)
    (h01 : ‖M 0 1‖ ≤ K) (h10 : ‖M 1 0‖ ≤ K) : ∀ i j, ‖M i j‖ ≤ 2 + K := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have e11 : M 1 1 = 1 - M 0 0 := by linear_combination htr
  have hprod : ‖M 0 0‖ * ‖1 - M 0 0‖ ≤ K * K := by
    have : M 0 0 * (1 - M 0 0) = M 0 1 * M 1 0 := by rw [← e11]; linear_combination hdet
    rw [← norm_mul, this, norm_mul]
    exact mul_le_mul h01 h10 (norm_nonneg _) hK
  have h00 : ‖M 0 0‖ ≤ 1 + K := by
    by_contra hcon
    push Not at hcon
    have h1 : ‖M 0 0‖ - 1 ≤ ‖1 - M 0 0‖ := by
      have := norm_sub_norm_le (M 0 0) 1
      rw [norm_one, norm_sub_rev] at this; linarith
    have h2 : (1 + K) * K < ‖M 0 0‖ * (‖M 0 0‖ - 1) := by
      have : K < ‖M 0 0‖ - 1 := by linarith
      nlinarith
    nlinarith [norm_nonneg (1 - M 0 0)]
  have h11 : ‖M 1 1‖ ≤ 2 + K := by
    rw [e11]
    have := norm_sub_le (1 : ℂ) (M 0 0)
    rw [norm_one] at this; linarith
  rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, h11⟩⟩

lemma sup_bound_of_fcoef {f : ℂ → ℂ} {ε M K γ : ℝ} (hf : DifferentiableOn ℂ f (strip ε))
    (hper : ∀ z, f (z + 1) = f z) (hb : ∀ z ∈ strip ε, ‖f z‖ ≤ M) (hγ : 0 < γ) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖fcoef f m 0‖ ≤ K * Real.exp (-(2 * Real.pi * γ) * |(m : ℝ)|))
    {z : ℂ} (hz : |z.im| ≤ γ / 2) (hzε : |z.im| < ε) :
    ‖f z‖ ≤ K * ∑' m : ℤ, Real.exp (-(Real.pi * γ) * |(m : ℝ)|) := by
  have hs := hasSum_fcoef hf hper hb hzε
  have hsum := (summable_exp_neg_abs (by positivity : 0 < Real.pi * γ)).hasSum.mul_left K
  refine hs.norm_le_of_bounded hsum fun m => ?_
  rw [norm_mul, norm_eC]
  have him : ((m : ℂ) * z).im = m * z.im := by simp
  rw [him]
  have h1 := hc m
  have h2 : Real.exp (-2 * Real.pi * (m * z.im)) ≤ Real.exp (Real.pi * γ * |(m : ℝ)|) := by
    apply Real.exp_le_exp.2
    have : -((m : ℝ) * z.im) ≤ |(m : ℝ)| * (γ / 2) := by
      calc -((m : ℝ) * z.im) ≤ |(m : ℝ) * z.im| := neg_le_abs _
        _ = |(m : ℝ)| * |z.im| := abs_mul _ _
        _ ≤ |(m : ℝ)| * (γ / 2) := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  calc ‖fcoef f m 0‖ * Real.exp (-2 * Real.pi * (m * z.im))
      ≤ (K * Real.exp (-(2 * Real.pi * γ) * |(m : ℝ)|)) * Real.exp (Real.pi * γ * |(m : ℝ)|) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = K * Real.exp (-(Real.pi * γ) * |(m : ℝ)|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma integral_orbit_avg {h : ℝ → ℂ} (hc : Continuous h) (hp : Function.Periodic h 1) {q : ℕ}
    (hq : 0 < q) (β : ℝ) {K : ℝ} (hb : ∀ x, ‖∑ j ∈ Finset.range q, h (x + j * β)‖ ≤ q * K) :
    ‖∫ x in (0 : ℝ)..1, h x‖ ≤ K := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hshift : ∀ c : ℝ, ∫ x in (0 : ℝ)..1, h (x + c) = ∫ x in (0 : ℝ)..1, h x := by
    intro c
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm 1 c,
      hp.intervalIntegral_add_eq c 0, zero_add]
  have hsum : ∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range q, h (x + j * β) =
      q * ∫ x in (0 : ℝ)..1, h x := by
    rw [intervalIntegral.integral_finset_sum]
    · simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro j _
      exact (hc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun x => ∑ j ∈ Finset.range q, h (x + j * β)) (C := q * K) (fun x _ => hb x)
  rw [hsum, norm_mul, Complex.norm_natCast] at hle
  simp only [sub_zero, abs_one, mul_one] at hle
  exact le_of_mul_le_mul_left hle hqpos

lemma convex_strip (c : ℝ) : Convex ℝ (strip c) := by
  intro x hx y hy a b ha hb hab
  show |(a • x + b • y).im| < c
  have hx' : |x.im| < c := hx
  have hy' : |y.im| < c := hy
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
    _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < c := by
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp at hab; subst hab; simpa using hy'
      · have h1 := mul_lt_mul_of_pos_left hx' h
        have h2 := mul_le_mul_of_nonneg_left hy'.le hb
        have : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
        linarith

/-! ### Uniform hyperbolicity of periodic approximants (`PerClaim`) -/

lemma continuousOn_specProj {P : ℂ → M2} {s : Set ℂ} (hP : ContinuousOn P s)
    (hh : ∀ z ∈ s, 2 < ‖(P z).trace‖) : ContinuousOn (fun z => specProj (P z)) s := by
  have htr : ContinuousOn (fun z => (P z).trace) s := by
    have h00 := (entryCLM 0 0).continuous.comp_continuousOn hP
    have h11 := (entryCLM 1 1).continuous.comp_continuousOn hP
    refine (h00.add h11).congr fun z _ => ?_
    simp [Matrix.trace_fin_two]
  have hjk : ContinuousOn (fun z => jk (P z).trace) s := fun z hz =>
    ((differentiableAt_jk (hh z hz)).continuousAt.comp_continuousWithinAt
      (f := fun z => (P z).trace) (htr z hz))
  have hjkc : ContinuousOn (fun z => jkc (P z).trace) s := fun z hz =>
    ((differentiableAt_jkc (hh z hz)).continuousAt.comp_continuousWithinAt
      (f := fun z => (P z).trace) (htr z hz))
  unfold specProj
  exact ((hjk.sub hjkc).inv₀ fun z hz => jk_sub_jkc_ne_zero (hh z hz)).smul
    (hP.sub (hjkc.smul continuousOn_const))

/-- A periodic cocycle whose period products are hyperbolic on the real line is uniformly
hyperbolic. -/
theorem uh_of_periodic_hyp {δ : ℝ} {B : ℂ → M2} (hB : IsAnalyticCocycle δ B) (r : ℚ)
    (hh : ∀ x : ℝ, 2 < ‖(perIter B r.num r.den x).trace‖) : UH r B := by
  set p := r.num
  set q := r.den
  have hq : 0 < q := r.den_pos
  have hr : ((r : ℚ) : ℝ) = (p : ℝ) / q := by rw [Rat.cast_def]
  have hδ := hB.pos
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ strip δ := fun x => by simpa [strip] using hδ
  set P : ℝ → M2 := fun x => perIter B p q x with hPdef
  have hPdet : ∀ x, (P x).det = 1 := fun x => det_citer hB _ q (hreal x)
  set F : ℝ → M2 := fun x => specProj (P x) with hF
  have hFc : Continuous F := by
    have := continuousOn_specProj (P := fun z : ℂ => perIter B p q z) (s := Set.range Complex.ofReal)
      ((differentiableOn_citer hB _ q).continuousOn.mono (by rintro _ ⟨x, rfl⟩; exact hreal x))
      (by rintro _ ⟨x, rfl⟩; exact hh x)
    exact this.comp_continuous Complex.continuous_ofReal (fun x => ⟨x, rfl⟩)
  have hPp : Function.Periodic P 1 := fun x => by
    simp only [hPdef, perIter]; push_cast; exact citer_periodic hB.periodic _ _ _
  have hFp : Function.Periodic F 1 := fun x => by simp only [hF, hPp x]
  have hidem : ∀ x, F x * F x = F x := fun x => specProj_idem (hPdet x) (hh x)
  have htrF : ∀ x, (F x).trace = 1 := fun x => trace_specProj (hPdet x) (hh x)
  have hdetF : ∀ x, (F x).det = 0 := fun x => det_specProj (hPdet x) (hh x)
  have hinv : ∀ x, shift B 0 x * F x = F (x + r) * shift B 0 x := by
    intro x
    have hA0x : shift B 0 x = B x := by simp [shift]
    rw [hA0x]
    have hc := conj_relation hB.periodic p hq (x : ℂ)
    have hdet : (B x).det ≠ 0 := by rw [hB.det_eq_one _ (hreal x)]; exact one_ne_zero
    have h' := specProj_conj hdet hc
    have e : ((x + (r : ℝ) : ℝ) : ℂ) = (x : ℂ) + (p : ℂ) / q := by rw [hr]; push_cast; ring
    show B x * specProj (perIter B p q x) = specProj (perIter B p q ((x + (r : ℝ) : ℝ) : ℂ)) * B x
    rw [e]
    exact h'
  set G : ℝ → M2 := fun x => 1 - F x with hG
  have hGc : Continuous G := continuous_const.sub hFc
  have hGp : Function.Periodic G 1 := fun x => by simp only [hG, hFp x]
  have hGidem : ∀ x, G x * G x = G x := fun x => by
    simp only [hG, sub_mul, mul_sub, one_mul, mul_one, hidem]; abel
  have hGtr : ∀ x, (G x).trace = 1 := fun x => by
    have := htrF x
    simp only [hG, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, this]
    norm_num
  have hGdet : ∀ x, (G x).det = 0 := fun x => by
    have h1 := hdetF x
    have h2 := htrF x
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [Matrix.trace_fin_two] at h2
    simp only [hG, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
      (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    linear_combination h1 - h2
  have hGinv : ∀ x, shift B 0 x * G x = G (x + r) * shift B 0 x := fun x => by
    simp only [hG, mul_sub, sub_mul, mul_one, one_mul, hinv]
  obtain ⟨u, huc, hup, hu0, huF⟩ := exists_section hFc hFp hidem hdetF htrF
  obtain ⟨s, hsc, hsp, hs0, hsG⟩ := exists_section hGc hGp hGidem hGdet hGtr
  have step : ∀ {E : ℝ → M2} {v : ℝ → (Fin 2 → ℂ)}, (∀ x, (E x).det = 0) → (∀ x, v x ≠ 0) →
      (∀ x, E x *ᵥ v x = v x) → (∀ x, shift B 0 x * E x = E (x + r) * shift B 0 x) →
      ∀ x, ∃ c : ℂ, shift B 0 x *ᵥ v x = c • v (x + r) := by
    intro E v hEd hv0 hvE hEinv x
    refine parallel_of_det_zero' (hEd (x + r)) ?_ (hvE (x + r)) (hv0 (x + r))
    rw [Matrix.mulVec_mulVec, ← hEinv, ← Matrix.mulVec_mulVec, hvE]
  have hiter : ∀ x : ℝ, iter (r : ℝ) (shift B 0) q x = P x := fun x => by
    have := citer_shift ((p : ℝ) / q) B 0 q x
    simp only [ofReal_zero, zero_mul, add_zero] at this
    simp only [hPdef, perIter, hr, this]
  unfold UH IsUH
  refine ⟨u, s, huc, hsc, hup, hsp, hu0, hs0, step hdetF hu0 huF hinv,
    step hGdet hs0 hsG hGinv, q, hq, fun x => ⟨?_, ?_⟩⟩
  · rw [hiter]
    have hdec : P x = jkc (P x).trace • (1 : M2) +
        (jk (P x).trace - jkc (P x).trace) • specProj (P x) := eq_specProj_decomp (hh x)
    have hsx : specProj (P x) *ᵥ s x = 0 := by
      have h1 : F x *ᵥ s x = 0 := by
        rw [← hsG x, Matrix.mulVec_mulVec]
        simp only [hG, mul_sub, mul_one, hidem, sub_self, Matrix.zero_mulVec]
      exact h1
    have : P x *ᵥ s x = jkc (P x).trace • s x := by
      conv_lhs => rw [hdec]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hsx,
        Matrix.one_mulVec, smul_zero, add_zero]
    rw [this, norm_smul]
    have h1 := norm_jkc_lt_one (hh x)
    have h2 : 0 < ‖s x‖ := norm_pos_iff.2 (hs0 x)
    nlinarith
  · rw [hiter]
    have huF' : specProj (P x) *ᵥ u x = u x := huF x
    have : P x *ᵥ u x = jk (P x).trace • u x := by
      conv_lhs => rw [← huF']
      rw [Matrix.mulVec_mulVec, mul_specProj (hPdet x) (hh x), Matrix.smul_mulVec, huF']
    rw [this, norm_smul]
    have h1 := one_lt_norm_jk (hh x)
    have h2 : 0 < ‖u x‖ := norm_pos_iff.2 (hu0 x)
    nlinarith

/-- **Lemma `per`** (formal statement `PerClaim`), from Theorem [JKS]. -/
theorem perClaim_of_jks (hJKS : JKSHyp) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    {α : ℝ} (hα : Irrational α) (hreg : IsRegular α A) (hpos : 0 < L α A 0) {r : ℕ → ℚ}
    (hr : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 α)) {As : ℕ → ℂ → M2}
    (hAs : ∀ n, IsAnalyticCocycle δ (As n)) (hconv : TendstoUniformlyOn As A atTop (strip δ)) :
    ∀ᶠ n in atTop, UH (r n) (As n) := by
  obtain ⟨η0, hη0, a, b, haff⟩ := hreg
  have ha : 0 < a := by
    have := haff 0 (by simpa using hη0); simp at this; linarith
  filter_upwards [perCore hJKS hA hα hη0 haff ha hr hAs hconv] with n hn
  exact uh_of_periodic_hyp (hAs n) (r n) hn

/-! ### The hard direction of Theorem `uniformly hyperbolic` -/

/-- Elementary matrices. -/
def E01 : M2 := !![0, 1; 0, 0]
/-- Elementary matrices. -/
def E10 : M2 := !![0, 0; 1, 0]

lemma E01_props : E01.trace = 0 ∧ ‖E01‖ ≤ 1 ∧ ∀ c : ℂ, (1 + c • E01).det = 1 := by
  refine ⟨by simp [E01, Matrix.trace_fin_two], ?_, fun c => by simp [E01, Matrix.det_fin_two]⟩
  obtain ⟨i, hi⟩ := exists_row_norm_eq E01
  rw [hi]; fin_cases i <;> simp [E01]

lemma E10_props : E10.trace = 0 ∧ ‖E10‖ ≤ 1 ∧ ∀ c : ℂ, (1 + c • E10).det = 1 := by
  refine ⟨by simp [E10, Matrix.trace_fin_two], ?_, fun c => by simp [E10, Matrix.det_fin_two]⟩
  obtain ⟨i, hi⟩ := exists_row_norm_eq E10
  rw [hi]; fin_cases i <;> simp [E10]

lemma trace_mul_E01 (M : M2) : (M * E01).trace = M 1 0 := by
  simp [E01, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma trace_mul_E10 (M : M2) : (M * E10).trace = M 0 1 := by
  simp [E10, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma continuous_trace_M2 : Continuous fun M : M2 => M.trace := by
  have h00 := (entryCLM 0 0).continuous
  have h11 := (entryCLM 1 1).continuous
  refine (h00.add h11).congr fun M => ?_
  simp [Matrix.trace_fin_two]

lemma continuous_det_M2 : Continuous fun M : M2 => M.det := by
  have h00 := (entryCLM 0 0).continuous
  have h01 := (entryCLM 0 1).continuous
  have h10 := (entryCLM 1 0).continuous
  have h11 := (entryCLM 1 1).continuous
  refine ((h00.mul h11).sub (h01.mul h10)).congr fun M => ?_
  simp [Matrix.det_fin_two]

set_option maxHeartbeats 4000000 in
/-- **Theorem `uniformly hyperbolic`, "only if" direction.**  Regular cocycles with positive
Lyapunov exponent at irrational frequency are uniformly hyperbolic. -/
theorem regularPosUH_main (hJKS : JKSHyp) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    {α : ℝ} (hα : Irrational α) (hreg : IsRegular α A) (hL : 0 < L α A 0) : UH α A := by
  obtain ⟨η0, hη0, a, b, haff⟩ := hreg
  have hδ := hA.pos
  have hpi := Real.pi_pos
  have ha0 : 0 < a := by
    have := haff 0 (by simpa using hη0); simp at this; linarith
  set T := min (min (η0 / 2) (δ / 4)) (a / (2 * (|b| + 1))) with hTdef
  have hb1 : 0 < 2 * (|b| + 1) := by positivity
  have hT0 : 0 < T := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hTη : T < η0 := by
    have := min_le_left (min (η0 / 2) (δ / 4)) (a / (2 * (|b| + 1)))
    have := min_le_left (η0 / 2) (δ / 4); linarith
  have hTδ : T ≤ δ / 4 := by
    have := min_le_left (min (η0 / 2) (δ / 4)) (a / (2 * (|b| + 1)))
    have := min_le_right (η0 / 2) (δ / 4); linarith
  have hTa : T ≤ a / (2 * (|b| + 1)) := min_le_right _ _
  have hpos : ∀ t, |t| ≤ T → 0 < a + b * t := by
    intro t ht
    have h1 : |b * t| ≤ |b| * T := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    have h2 : |b| * T ≤ |b| * (a / (2 * (|b| + 1))) :=
      mul_le_mul_of_nonneg_left hTa (abs_nonneg _)
    have h3 : |b| * (a / (2 * (|b| + 1))) < a / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hb1 (by norm_num)]
      nlinarith [abs_nonneg b]
    have := neg_abs_le (b * t)
    linarith
  set d := T / 8 with hd
  have hd0 : 0 < d := by positivity
  obtain ⟨ρ, hρ, r0, hr0, hrob⟩ := robustPer hJKS hA hα hη0 haff hT0.le hTη hpos hd0
    (by linarith)
  have hshift : ∀ t, |t| ≤ T → IsAnalyticCocycle d (cshift A t) := fun t ht =>
    (hA.cshift (by linarith)).mono' hd0 (by linarith)
  have hband : ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ z : ℂ, |z.im| ≤ T →
      2 < ‖(perIter A r.num r.den z).trace‖ := by
    intro r hr z hz
    have h := hrob r hr (cshift A z.im) (hshift _ hz) z.im hz
      (fun w _ => by simp only [cshift, sub_self, norm_zero]; exact hr0.le) z.re
    have e : perIter (cshift A z.im) r.num r.den z.re = perIter A r.num r.den z := by
      unfold perIter; rw [citer_cshift, Complex.re_add_im]
    rwa [e] at h
  have hstripδ : ∀ z : ℂ, |z.im| ≤ T → z ∈ strip δ := fun z hz => by
    show |z.im| < δ; linarith
  have hPdet : ∀ r : ℚ, ∀ z : ℂ, |z.im| ≤ T → (perIter A r.num r.den z).det = 1 :=
    fun r z hz => det_citer hA _ _ (hstripδ z hz)
  set Prj : ℚ → ℂ → M2 := fun r z => specProj (perIter A r.num r.den z) with hPrj
  have hPrjHol : ∀ r : ℚ, |(r : ℝ) - α| < ρ → DifferentiableOn ℂ (Prj r) (strip T) := by
    intro r hr z hz
    have hzT : |z.im| ≤ T := le_of_lt hz
    have hzδ := hstripδ z hzT
    have hdP := differentiableOn_citer hA ((r.num : ℝ) / r.den) r.den
    have hPz : DifferentiableAt ℂ (perIter A r.num r.den) z :=
      hdP.differentiableAt ((isOpen_strip δ).mem_nhds hzδ)
    have htz : DifferentiableAt ℂ (fun w => (perIter A r.num r.den w).trace) z :=
      (differentiableOn_trace hdP).differentiableAt ((isOpen_strip δ).mem_nhds hzδ)
    have hτ := hband r hr z hzT
    have hjk : DifferentiableAt ℂ (fun w => jk (perIter A r.num r.den w).trace) z := by
      have := (differentiableAt_jk hτ).comp z htz
      exact this
    have hjkc : DifferentiableAt ℂ (fun w => jkc (perIter A r.num r.den w).trace) z := by
      have := (differentiableAt_jkc hτ).comp z htz
      exact this
    have hinv := (hjk.sub hjkc).inv (jk_sub_jkc_ne_zero hτ)
    have : DifferentiableAt ℂ (Prj r) z := by
      simp only [hPrj]
      unfold specProj
      exact hinv.smul (hPz.sub (hjkc.smul_const (1 : M2)))
    exact this.differentiableWithinAt
  have hPrjPer : ∀ r : ℚ, ∀ z, Prj r (z + 1) = Prj r z := fun r z => by
    simp only [hPrj, perIter, citer_periodic hA.periodic]
  obtain ⟨CA, hCA1, hCA⟩ := exists_bound_strip hA (ε := T / 2 + d) (by linarith)
  set R := r0 / CA with hR
  have hR0 : 0 < R := by positivity
  set C := CA * (1 + R) with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  set K' := 4 * (Real.log 3 + Real.log C + 1) / R with hK'
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hlog3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  have hK'0 : 0 ≤ K' := by
    rw [hK']; apply div_nonneg _ hR0.le; linarith
  have hCAne : CA ≠ 0 := ne_of_gt (by linarith)
  set γ := T / 2 - d with hγ
  have hγ0 : 0 < γ := by rw [hγ, hd]; linarith
  -- Fourier coefficient bounds (Lemma `gam`)
  have hcoef : ∀ E : M2, E.trace = 0 → ‖E‖ ≤ 1 → (∀ c : ℂ, (1 + c • E).det = 1) →
      ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ m : ℤ,
        ‖fcoef (fun z => (Prj r z * E).trace) m 0‖ ≤
          K' * Real.exp (-(2 * Real.pi * γ) * |(m : ℝ)|) := by
    intro E hEtr hEn hEdet r hr m
    have hq : 0 < r.den := r.den_pos
    set y0 : ℝ := if 0 ≤ m then -(T / 2) else T / 2 with hy0
    have hy0abs : |y0| = T / 2 := by
      rw [hy0]; split_ifs
      · rw [abs_neg, abs_of_pos (by linarith)]
      · rw [abs_of_pos (by linarith)]
    have hmy0 : (m : ℝ) * y0 = -(|(m : ℝ)| * (T / 2)) := by
      rw [hy0]; split_ifs with hm
      · have : (0 : ℝ) ≤ m := by exact_mod_cast hm
        rw [abs_of_nonneg this]; ring
      · have : (m : ℝ) < 0 := by exact_mod_cast (not_le.1 hm)
        rw [abs_of_neg this]; ring
    set At := cshift A y0 with hAt
    have hAtc : IsAnalyticCocycle d At := hshift y0 (by rw [hy0abs]; linarith)
    set c0 : ℂ := ((Real.exp (-(2 * Real.pi * |(m : ℝ)| * d)) : ℝ) : ℂ) with hc0
    set W : ℂ → M2 := fun z => (c0 * eC (-((m : ℂ) * z))) • E with hW
    have hWd : Differentiable ℂ W := by
      have : Differentiable ℂ fun z : ℂ => c0 * eC (-((m : ℂ) * z)) :=
        (differentiable_const _).mul (differentiable_eC.comp (by fun_prop))
      exact this.smul_const E
    have hWper : ∀ z, W (z + 1) = W z := by
      intro z
      simp only [hW]
      congr 2
      rw [show -((m : ℂ) * (z + 1)) = -((m : ℂ) * z) + ((-m : ℤ) : ℂ) by push_cast; ring,
        eC_add, eC_intCast, mul_one]
    have hWb : ∀ z ∈ strip d, ‖W z‖ ≤ 1 := by
      intro z hz
      have hz' : |z.im| < d := hz
      simp only [hW]
      rw [norm_smul, norm_mul, hc0, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        norm_eC]
      have him : (-((m : ℂ) * z)).im = -(m * z.im) := by simp
      rw [him, ← Real.exp_add]
      have h1 : (m : ℝ) * z.im ≤ |(m : ℝ)| * d := by
        calc (m : ℝ) * z.im ≤ |(m : ℝ) * z.im| := le_abs_self _
          _ = |(m : ℝ)| * |z.im| := abs_mul _ _
          _ ≤ |(m : ℝ)| * d := mul_le_mul_of_nonneg_left hz'.le (abs_nonneg _)
      have h2 : Real.exp (-(2 * Real.pi * |(m : ℝ)| * d) + -2 * Real.pi * -(m * z.im)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
      calc Real.exp (-(2 * Real.pi * |(m : ℝ)| * d) + -2 * Real.pi * -(m * z.im)) * ‖E‖
          ≤ 1 * 1 := mul_le_mul h2 hEn (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htrW : ∀ z, (W z).trace = 0 := fun z => by
      simp only [hW, Matrix.trace_smul, hEtr, smul_zero]
    set B : ℂ → ℂ → M2 := fun s w => At w * (1 + s • W w) with hB
    have hBcoc : ∀ s : ℂ, IsAnalyticCocycle d (B s) := by
      intro s
      refine ⟨hd0, ?_, ?_, ?_⟩
      · exact hAtc.holo.mul ((differentiableOn_const _).add
          ((hWd.const_smul s).differentiableOn))
      · intro z; simp only [hB, hAtc.periodic, hWper]
      · intro z hz
        simp only [hB]
        rw [Matrix.det_mul, hAtc.det_eq_one z hz, one_mul]
        simp only [hW, smul_smul]
        exact hEdet _
    have hclose : ∀ s ∈ Metric.ball (0 : ℂ) R, ∀ z ∈ strip d,
        ‖B s z - A (z + y0 * I)‖ ≤ r0 := by
      intro s hs z hz
      have hz' : |z.im| < d := hz
      have hAz : ‖At z‖ ≤ CA := by
        simp only [hAt, cshift]
        apply hCA
        simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        linarith [abs_add_le z.im y0]
      have hs' : ‖s‖ < R := by simpa using hs
      have e : B s z - A (z + y0 * I) = At z * (s • W z) := by
        simp only [hB, hAt, cshift, mul_add, mul_one, add_sub_cancel_left]
      rw [e]
      calc ‖At z * (s • W z)‖ ≤ ‖At z‖ * (‖s‖ * ‖W z‖) := by
            refine (norm_mul_le _ _).trans ?_
            rw [norm_smul]
        _ ≤ CA * (R * 1) := by
            refine mul_le_mul hAz (mul_le_mul hs'.le (hWb z hz) (norm_nonneg _) hR0.le)
              (by positivity) (by linarith)
        _ = r0 := by rw [hR, mul_one]; field_simp
    have hhyp : ∀ s ∈ Metric.ball (0 : ℂ) R, ∀ x : ℝ,
        2 < ‖(perIter (fun w => At w * (1 + s • W w)) r.num r.den x).trace‖ := fun s hs x =>
      hrob r hr (B s) (hBcoc s) y0 (by rw [hy0abs]; linarith) (hclose s hs) x
    have hreal : ∀ x : ℝ, (x : ℂ) ∈ strip d := fun x => by simpa [strip] using hd0
    have hbd : ∀ s ∈ Metric.ball (0 : ℂ) R, ∀ x : ℝ, ‖At x * (1 + s • W x)‖ ≤ C := by
      intro s hs x
      have hs' : ‖s‖ < R := by simpa using hs
      have hAx : ‖At x‖ ≤ CA := by
        simp only [hAt, cshift]
        apply hCA
        simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
          add_zero, zero_add]
        rw [hy0abs]; linarith
      calc ‖At x * (1 + s • W x)‖ ≤ ‖At x‖ * (1 + ‖s‖ * ‖W x‖) := by
            refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            refine (norm_add_le _ _).trans ?_
            rw [norm_one, norm_smul]
        _ ≤ CA * (1 + R * 1) := by
            refine mul_le_mul hAx ?_ (by positivity) (by linarith)
            have := mul_le_mul hs'.le (hWb x (hreal x)) (norm_nonneg _) hR0.le
            linarith
        _ = C := by rw [mul_one]
    have hdetAt : ∀ x : ℝ, (At x).det = 1 := fun x => hAtc.det_eq_one _ (hreal x)
    have hDB := derivBound hAtc.periodic hdetAt htrW r.num hq hR0 hC1 hhyp hbd
    set f : ℂ → ℂ := fun z => (Prj r z * E).trace with hf
    have hPrjAt : ∀ x : ℝ, specProj (perIter At r.num r.den x) = Prj r (x + y0 * I) := by
      intro x
      simp only [hPrj, hAt]
      unfold perIter
      rw [citer_cshift]
    set h : ℝ → ℂ := fun x => (specProj (perIter At r.num r.den x) * W x).trace with hh
    have hPrjC : ContinuousOn (Prj r) (strip T) := (hPrjHol r hr).continuousOn
    have hline : ∀ x : ℝ, (x : ℂ) + y0 * I ∈ strip T := fun x => by
      show |((x : ℂ) + y0 * I).im| < T
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        zero_add]
      rw [hy0abs]; linarith
    have hhc : Continuous h := by
      have h1 : Continuous fun x : ℝ => Prj r ((x : ℂ) + y0 * I) :=
        hPrjC.comp_continuous (by fun_prop) hline
      have h2 : Continuous fun x : ℝ => W x := hWd.continuous.comp Complex.continuous_ofReal
      have h3 : Continuous fun x : ℝ => Prj r ((x : ℂ) + y0 * I) * W x := h1.mul h2
      refine (continuous_trace_M2.comp h3).congr fun x => ?_
      simp only [hh, hPrjAt, Function.comp_apply]
    have hhp : Function.Periodic h 1 := by
      intro x
      simp only [hh]
      push_cast
      rw [hWper]
      unfold perIter
      rw [citer_periodic hAtc.periodic]
    have hhb : ∀ x : ℝ, ‖∑ j ∈ Finset.range r.den, h (x + j * ((r.num : ℝ) / r.den))‖ ≤
        r.den * K' := by
      intro x
      have e : ∀ j : ℕ, h (x + j * ((r.num : ℝ) / r.den)) =
          (specProj (perIter At r.num r.den ((x : ℂ) + (j : ℂ) * ((r.num : ℝ) / r.den : ℝ))) *
            W ((x : ℂ) + (j : ℂ) * ((r.num : ℝ) / r.den : ℝ))).trace := by
        intro j
        simp only [hh]
        push_cast
        rfl
      simp only [e]
      refine (hDB x).trans ?_
      rw [hK', mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hR0.le
      have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast hq
      nlinarith
    have hint := integral_orbit_avg hhc hhp hq ((r.num : ℝ) / r.den) hhb
    have hfd : DifferentiableOn ℂ f (strip T) :=
      differentiableOn_trace ((hPrjHol r hr).mul_const E)
    have hfper : ∀ z, f (z + 1) = f z := fun z => by simp only [hf, hPrjPer]
    have hcoefy : fcoef f m 0 = fcoef f m y0 :=
      fcoef_indep hfd hfper m (by simpa using hT0) (by rw [hy0abs]; linarith)
    have hint_eq : (∫ x in (0 : ℝ)..1, h x) = (c0 * eC ((m : ℂ) * (y0 * I))) * fcoef f m y0 := by
      unfold fcoef
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hh, hPrjAt, hW, hf, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have e1 : eC (-((m : ℂ) * x)) =
          eC ((m : ℂ) * (y0 * I)) * eC (-((m : ℂ) * (x + y0 * I))) := by
        rw [← eC_add]; congr 1; ring
      rw [e1]
      ring
    have hnorm_e : ‖eC ((m : ℂ) * (y0 * I))‖ =
        Real.exp (2 * Real.pi * (|(m : ℝ)| * (T / 2))) := by
      rw [norm_eC]
      congr 1
      have : ((m : ℂ) * (y0 * I)).im = m * y0 := by simp
      rw [this, hmy0]; ring
    have hc0n : ‖c0‖ = Real.exp (-(2 * Real.pi * |(m : ℝ)| * d)) := by
      rw [hc0, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hint_eq, norm_mul, norm_mul, hnorm_e, hc0n] at hint
    rw [hcoefy]
    have hpos' : 0 < Real.exp (-(2 * Real.pi * |(m : ℝ)| * d)) *
        Real.exp (2 * Real.pi * (|(m : ℝ)| * (T / 2))) := by positivity
    have : ‖fcoef f m y0‖ ≤ K' / (Real.exp (-(2 * Real.pi * |(m : ℝ)| * d)) *
        Real.exp (2 * Real.pi * (|(m : ℝ)| * (T / 2)))) := by
      rw [le_div_iff₀ hpos']; linarith
    refine this.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, ← Real.exp_add, ← Real.exp_neg]
    congr 2
    rw [hγ]; ring
  -- entry bounds
  set S := ∑' m : ℤ, Real.exp (-(Real.pi * γ) * |(m : ℝ)|) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => (Real.exp_pos _).le
  set K1 := K' * S with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg hK'0 hS0
  have hentry : ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ z : ℂ, |z.im| ≤ γ / 2 →
      ‖Prj r z 1 0‖ ≤ K1 ∧ ‖Prj r z 0 1‖ ≤ K1 := by
    intro r hr z hz
    have hzT : |z.im| < 3 * T / 4 := by
      have : γ / 2 < 3 * T / 4 := by rw [hγ, hd]; linarith
      linarith
    obtain ⟨M, hM⟩ := exists_bound_periodic ((hPrjHol r hr).continuousOn) (hPrjPer r)
      (by linarith : 3 * T / 4 < T)
    have hsub : strip (3 * T / 4) ⊆ strip T := fun w (hw : |w.im| < 3 * T / 4) =>
      (by show |w.im| < T; linarith)
    have hgen : ∀ E : M2, E.trace = 0 → ‖E‖ ≤ 1 → (∀ c : ℂ, (1 + c • E).det = 1) →
        ‖(Prj r z * E).trace‖ ≤ K1 := by
      intro E hEtr hEn hEdet
      have hfd : DifferentiableOn ℂ (fun w => (Prj r w * E).trace) (strip (3 * T / 4)) :=
        (differentiableOn_trace ((hPrjHol r hr).mul_const E)).mono hsub
      have hfb : ∀ w ∈ strip (3 * T / 4), ‖(Prj r w * E).trace‖ ≤ 2 * (M * ‖E‖) := by
        intro w hw
        refine (norm_trace_le _).trans ?_
        have := norm_mul_le (Prj r w) E
        have := mul_le_mul_of_nonneg_right (hM w (le_of_lt hw)) (norm_nonneg E)
        linarith
      exact sup_bound_of_fcoef hfd (fun w => by simp only [hPrjPer]) hfb hγ0 hK'0
        (hcoef E hEtr hEn hEdet r hr) hz hzT
    have h1 := hgen E01 E01_props.1 E01_props.2.1 E01_props.2.2
    have h2 := hgen E10 E10_props.1 E10_props.2.1 E10_props.2.2
    rw [trace_mul_E01] at h1
    rw [trace_mul_E10] at h2
    exact ⟨h1, h2⟩
  set K2 := 2 * (2 + K1) with hK2
  have hPrjbound : ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ z : ℂ, |z.im| ≤ γ / 2 →
      ‖Prj r z‖ ≤ K2 := by
    intro r hr z hz
    have hzT : |z.im| ≤ T := by
      have : γ / 2 ≤ T := by rw [hγ, hd]; linarith
      linarith
    obtain ⟨h1, h2⟩ := hentry r hr z hz
    exact norm_le_of_entries _ (proj_entry_bound
      (trace_specProj (hPdet r z hzT) (hband r hr z hzT))
      (det_specProj (hPdet r z hzT) (hband r hr z hzT)) hK10 h2 h1)
  -- uniform Lipschitz bound on the real line
  set L0 := K2 / (γ / 4) with hL0
  have hlip : ∀ r : ℚ, |(r : ℝ) - α| < ρ → ∀ x y : ℝ,
      ‖Prj r x - Prj r y‖ ≤ L0 * |x - y| := by
    intro r hr x y
    have hγ4 : 0 < γ / 4 := by positivity
    have hder : ∀ w ∈ strip (γ / 4), ‖deriv (Prj r) w‖ ≤ L0 := by
      intro w hw
      have hw' : |w.im| < γ / 4 := hw
      have hcl : DiffContOnCl ℂ (Prj r) (Metric.ball w (γ / 4)) := by
        apply DifferentiableOn.diffContOnCl
        refine (hPrjHol r hr).mono ?_
        rw [closure_ball _ hγ4.ne']
        intro v hv
        show |v.im| < T
        have h1 : |v.im - w.im| ≤ ‖v - w‖ := by simpa using Complex.abs_im_le_norm (v - w)
        rw [Metric.mem_closedBall, dist_eq_norm] at hv
        have : γ / 4 + γ / 4 < T := by rw [hγ, hd]; linarith
        linarith [abs_sub_abs_le_abs_sub v.im w.im]
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hγ4 hcl fun v hv => ?_
      refine hPrjbound r hr v ?_
      have h1 : |v.im - w.im| ≤ ‖v - w‖ := by simpa using Complex.abs_im_le_norm (v - w)
      rw [Metric.mem_sphere, dist_eq_norm] at hv
      linarith [abs_sub_abs_le_abs_sub v.im w.im]
    have hdiffAt : ∀ w ∈ strip (γ / 4), DifferentiableAt ℂ (Prj r) w := by
      intro w hw
      have hw' : |w.im| < γ / 4 := hw
      have hwT : w ∈ strip T := by
        show |w.im| < T
        have : γ / 4 < T := by rw [hγ, hd]; linarith
        linarith
      exact (hPrjHol r hr).differentiableAt ((isOpen_strip T).mem_nhds hwT)
    have hxs : (x : ℂ) ∈ strip (γ / 4) := by simpa [strip] using hγ4
    have hys : (y : ℂ) ∈ strip (γ / 4) := by simpa [strip] using hγ4
    have := (convex_strip (γ / 4)).norm_image_sub_le_of_norm_deriv_le hdiffAt hder hys hxs
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  -- a sequence of rationals
  have hex : ∀ n : ℕ, ∃ r : ℚ, α < r ∧ (r : ℝ) < α + min ρ (1 / ((n : ℝ) + 1)) := fun n =>
    exists_rat_btwn (by have : 0 < min ρ (1 / ((n : ℝ) + 1)) := lt_min hρ (by positivity)
                        linarith)
  choose rs hrs1 hrs2 using hex
  have hrsρ : ∀ n, |(rs n : ℝ) - α| < ρ := fun n => by
    rw [abs_of_pos (by linarith [hrs1 n])]
    have := min_le_left ρ (1 / ((n : ℝ) + 1)); linarith [hrs2 n]
  have hrsα : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α) := by
    have hu : Tendsto (fun n : ℕ => α + 1 / ((n : ℝ) + 1)) atTop (𝓝 α) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add α
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => (hrs1 n).le) (fun n => ?_)
    have := min_le_right ρ (1 / ((n : ℝ) + 1)); linarith [hrs2 n]
  -- Arzelà–Ascoli
  set fs : ℕ → ℝ → M2 := fun n x => Prj (rs n) x with hfs
  have hfsb : ∀ n x, ‖fs n x‖ ≤ K2 := fun n x =>
    hPrjbound (rs n) (hrsρ n) x (by simp; linarith)
  have hfslip : ∀ n x y, ‖fs n x - fs n y‖ ≤ L0 * |x - y| := fun n x y =>
    hlip (rs n) (hrsρ n) x y
  have hfsp : ∀ n, Function.Periodic (fs n) 1 := fun n x => by
    simp only [hfs]; push_cast; exact hPrjPer _ _
  obtain ⟨φ, hφ, F, hFc, hFp, hFu⟩ := exists_uniform_subseq hfsb hfslip hfsp
  have hFlim : ∀ x, Tendsto (fun n => fs (φ n) x) atTop (𝓝 (F x)) := fun x => hFu.tendsto_at x
  have hreal : ∀ x : ℝ, |(x : ℂ).im| ≤ T := fun x => by simp; linarith
  have hidem : ∀ x, F x * F x = F x := by
    intro x
    have h1 := (hFlim x).mul (hFlim x)
    have h2 : (fun n => fs (φ n) x * fs (φ n) x) = fun n => fs (φ n) x := by
      funext n
      exact specProj_idem (hPdet _ _ (hreal x)) (hband _ (hrsρ _) _ (hreal x))
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hFlim x)
  have htr : ∀ x, (F x).trace = 1 := by
    intro x
    have h1 := (continuous_trace_M2.tendsto _).comp (hFlim x)
    have h2 : ((fun M : M2 => M.trace) ∘ fun n => fs (φ n) x) = fun _ => 1 := by
      funext n
      exact trace_specProj (hPdet _ _ (hreal x)) (hband _ (hrsρ _) _ (hreal x))
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hdet : ∀ x, (F x).det = 0 := by
    intro x
    have h1 := (continuous_det_M2.tendsto _).comp (hFlim x)
    have h2 : ((fun M : M2 => M.det) ∘ fun n => fs (φ n) x) = fun _ => 0 := by
      funext n
      exact det_specProj (hPdet _ _ (hreal x)) (hband _ (hrsρ _) _ (hreal x))
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hinv : ∀ x, shift A 0 x * F x = F (x + α) * shift A 0 x := by
    intro x
    have hA0x : shift A 0 x = A x := by simp [shift]
    rw [hA0x]
    have happrox : ∀ n, A x * fs (φ n) x = fs (φ n) (x + rs (φ n)) * A x := by
      intro n
      have hq : 0 < (rs (φ n)).den := (rs (φ n)).den_pos
      have hc := conj_relation hA.periodic (rs (φ n)).num hq (x : ℂ)
      have hdA : (A x).det ≠ 0 := by
        rw [hA.det_eq_one _ (hstripδ _ (hreal x))]; exact one_ne_zero
      have h' := specProj_conj hdA hc
      have e : ((x + ((rs (φ n) : ℚ) : ℝ) : ℝ) : ℂ) =
          (x : ℂ) + ((rs (φ n)).num : ℂ) / (rs (φ n)).den := by
        rw [Rat.cast_def]; push_cast; ring
      show A x * specProj (perIter A (rs (φ n)).num (rs (φ n)).den x) =
        specProj (perIter A (rs (φ n)).num (rs (φ n)).den ((x + ((rs (φ n) : ℚ) : ℝ) : ℝ) : ℂ)) *
          A x
      rw [e]
      exact h'
    have h1 : Tendsto (fun n => A x * fs (φ n) x) atTop (𝓝 (A x * F x)) :=
      tendsto_const_nhds.mul (hFlim x)
    have h2 : Tendsto (fun n => fs (φ n) (x + rs (φ n))) atTop (𝓝 (F (x + α))) :=
      hFu.tendsto_comp hFc.continuousAt
        ((tendsto_const_nhds.add (hrsα.comp hφ.tendsto_atTop)))
    have h3 := h2.mul (tendsto_const_nhds (x := A x))
    simp only [happrox] at h1
    exact tendsto_nhds_unique h1 h3
  have hSL : IsSLCocycle (shift A 0) := hA.isSLCocycle_shift (by simpa using hδ)
  exact isUH_of_proj hα hSL hL hFc hFp hidem hdet htr hinv

/-! ### Final statements -/

/-- **Lemma `per`** (`PerClaim`), from Theorem [JKS] (the statement of `Hypotheses.jks`). -/
theorem per_proof
    (hJKS : ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α →
      ∀ {αs : ℕ → ℝ} {As : ℕ → ℂ → M2}, (∀ n, IsAnalyticCocycle δ (As n)) →
        Tendsto αs atTop (𝓝 α) → TendstoUniformlyOn As A atTop (strip δ) →
          Tendsto (fun n => L (αs n) (As n) 0) atTop (𝓝 (L α A 0))) :
    PerClaim := by
  intro δ A hA α hα hreg hpos r hr As hAs hconv
  exact perClaim_of_jks @hJKS hA hα hreg hpos hr hAs hconv

/-- **Theorem `uniformly hyperbolic`, hard direction** (the statement of the field
`Hypotheses.regularPosUH`), proved from Theorem [JKS] (the statement of `Hypotheses.jks`)
alone. -/
theorem regularPosUH_proof
    (hJKS : ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α →
      ∀ {αs : ℕ → ℝ} {As : ℕ → ℂ → M2}, (∀ n, IsAnalyticCocycle δ (As n)) →
        Tendsto αs atTop (𝓝 α) → TendstoUniformlyOn As A atTop (strip δ) →
          Tendsto (fun n => L (αs n) (As n) 0) atTop (𝓝 (L α A 0))) :
    ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α →
      IsRegular α A → 0 < L α A 0 → UH α A := by
  intro δ A hA α hα hreg hpos
  exact regularPosUH_main @hJKS hA hα hreg hpos

/-- The "only if" direction (the hard part) of **Theorem `uniformly hyperbolic`**: regular
cocycles with positive Lyapunov exponent are uniformly hyperbolic.  It uses only [JKS]. -/
theorem regular_pos_imp_uh [H : Hypotheses] {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    {α : ℝ} (hα : Irrational α) (hreg : IsRegular α A) (hpos : 0 < L α A 0) : UH α A :=
  regularPosUH_proof H.jks hA hα hreg hpos

/-- **Lemma `per`** (from [JKS]). -/
theorem per [H : Hypotheses] : PerClaim := per_proof H.jks

end AvilaGlobal
