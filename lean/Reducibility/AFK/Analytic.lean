/-
# Analytic and algebraic infrastructure for §4 of Avila–Fayad–Krikorian

This file collects the elementary tools used throughout §4 of
*A KAM scheme for SL(2,ℝ) cocycles with Liouvillean frequencies* (Avila, Fayad, Krikorian),
in particular in the proof of Proposition `CT`.

* **Strips.** `strip h = Δ_h = {z : ℂ | |Im z| < h}` and the sup-norm
  `stripNorm h f = sup_{z ∈ Δ_h} ‖f z‖ ∈ ℝ≥0∞` (unbounded functions have norm `⊤`).
* **Cauchy estimates.** For `f` holomorphic on `Δ_h` with `‖f‖ ≤ K` there, and `h' < h`:
  `‖f' z‖ ≤ K / (h - h')` for `|Im z| ≤ h'` (`norm_deriv_le_of_strip`), hence
  `‖f w - f z‖ ≤ K / (h - h') ‖w - z‖` on `|Im| ≤ h'` (`norm_sub_le_of_strip`) and in
  particular `‖f (z + t) - f z‖ ≤ |t| K / (h - h')` for real `t` (`norm_translate_sub_le`).
  No extra absolute constant is needed.
* **Rotations over ℂ.** `rot θ = R_θ = [[cos θ, -sin θ], [sin θ, cos θ]]`:
  `R_a R_b = R_{a+b}`, `det R_θ = 1`, `R_θ⁻¹ = R_{-θ}`, and
  `R_{2θ} - 1 = 2 sin θ · [[-sin θ, -cos θ], [cos θ, -sin θ]]`, so `R_{2θ} - 1` is invertible
  iff `sin θ ≠ 0` iff `θ ∉ πℤ`, with an explicit inverse and the bound
  `‖(R_{2θ} - 1)⁻¹‖ ≤ (|sin θ| + |cos θ|) / (2 |sin θ|)`.
  (We use the convention `R_θ` = rotation by angle `θ`, not `2πθ` as in the paper.)
* **The projection `𝒬`.** `J = [[0,-1],[1,0]]`, `𝒬 M = (M + J M J)/2`.  `M - 𝒬 M` commutes with
  all rotations, `R_{-θ} 𝒬 M = 𝒬 (M R_θ)`, `R_θ 𝒬 M = 𝒬 (R_θ M)`, and identity (Q):
  `(R_{-θ₁} - R_{θ₂}) 𝒬 M = 𝒬 (M R_{θ₁} - R_{θ₂} M)`.  Moreover `M` commutes with all
  rotations iff `𝒬 M = 0` iff `M = [[a,-b],[b,a]]`.
* **Projection to rotations.** If `det M = 1` and `‖𝒬 M‖ ≤ 1/2`, then
  `soProj M = (M - 𝒬 M) / √det (M - 𝒬 M)` is a rotation `R_φ` (`φ ∈ ℂ`) with
  `‖soProj M - M‖ ≤ (‖M‖ + 2) ‖𝒬 M‖`.

Matrices are `2 × 2` complex matrices with the `ℓ^∞` operator norm
(`open scoped Matrix.Norms.Operator`).
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open scoped Matrix.Norms.Operator ENNReal NNReal
open Matrix Metric Set Filter Topology Complex

namespace Red.AFK

/-! ### Strips and the strip norm -/

/-- The strip `Δ_h = {z : ℂ | |Im z| < h}`. -/
def strip (h : ℝ) : Set ℂ := {z | |z.im| < h}

lemma mem_strip {h : ℝ} {z : ℂ} : z ∈ strip h ↔ |z.im| < h := Iff.rfl

lemma isOpen_strip (h : ℝ) : IsOpen (strip h) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

lemma strip_mono {h h' : ℝ} (hh : h' ≤ h) : strip h' ⊆ strip h :=
  fun _ hz => lt_of_lt_of_le hz hh

/-- The strip is invariant under real translations. -/
lemma add_real_mem_strip {h : ℝ} {z : ℂ} (t : ℝ) : z + t ∈ strip h ↔ z ∈ strip h := by
  simp [mem_strip]

variable {E : Type*} [NormedAddCommGroup E]

/-- The strip norm `‖f‖_h = sup_{|Im z| < h} ‖f z‖`, valued in `ℝ≥0∞`
(it is `⊤` iff `f` is unbounded on the strip). -/
def stripNorm (h : ℝ) (f : ℂ → E) : ℝ≥0∞ := ⨆ z ∈ strip h, ‖f z‖ₑ

lemma enorm_le_stripNorm {h : ℝ} {f : ℂ → E} {z : ℂ} (hz : z ∈ strip h) :
    ‖f z‖ₑ ≤ stripNorm h f :=
  le_iSup₂ (f := fun z (_ : z ∈ strip h) => ‖f z‖ₑ) z hz

/-- `‖f‖_h ≤ K` iff `‖f z‖ ≤ K` on the strip. -/
lemma stripNorm_le_iff {h K : ℝ} {f : ℂ → E} (hK : 0 ≤ K) :
    stripNorm h f ≤ ENNReal.ofReal K ↔ ∀ z ∈ strip h, ‖f z‖ ≤ K := by
  simp only [stripNorm, iSup₂_le_iff]
  refine forall₂_congr fun z _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hK]

lemma stripNorm_mono {h h' : ℝ} (hh : h' ≤ h) (f : ℂ → E) : stripNorm h' f ≤ stripNorm h f :=
  biSup_mono fun _ hz => strip_mono hh hz

/-- For a bounded function the real strip norm bounds the values. -/
lemma norm_le_toReal_stripNorm {h : ℝ} {f : ℂ → E} (hf : stripNorm h f ≠ ⊤) {z : ℂ}
    (hz : z ∈ strip h) : ‖f z‖ ≤ (stripNorm h f).toReal := by
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono hf (enorm_le_stripNorm hz)

/-! ### Cauchy estimates on strips -/

variable [NormedSpace ℂ E]

/-- **Cauchy estimate on a strip.** If `f` is holomorphic on `Δ_h` and bounded by `K` there,
then `‖f' z‖ ≤ K / (h - h')` whenever `|Im z| ≤ h' < h`. -/
theorem norm_deriv_le_of_strip {f : ℂ → E} {h h' K : ℝ} (hf : DifferentiableOn ℂ f (strip h))
    (hK : ∀ z ∈ strip h, ‖f z‖ ≤ K) (hh : h' < h) {z : ℂ} (hz : |z.im| ≤ h') :
    ‖deriv f z‖ ≤ K / (h - h') := by
  have key : ∀ r ∈ Ioo 0 (h - h'), ‖deriv f z‖ ≤ K / r := by
    rintro r ⟨hr0, hr⟩
    have hsub : closedBall z r ⊆ strip h := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      have hi : |w.im - z.im| ≤ ‖w - z‖ := by
        rw [← sub_im]; exact abs_im_le_norm _
      rw [mem_strip]
      calc |w.im| = |z.im + (w.im - z.im)| := by ring_nf
        _ ≤ |z.im| + |w.im - z.im| := abs_add_le _ _
        _ < h := by linarith
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr0 (hf.diffContOnCl_ball hsub) ?_
    intro w hw
    exact hK w (hsub (sphere_subset_closedBall hw))
  have ht : Tendsto (fun r => K / r) (𝓝[<] (h - h')) (𝓝 (K / (h - h'))) :=
    ((continuousAt_const.div continuousAt_id (sub_pos.2 hh).ne').tendsto).mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_of_mem (Ioo_mem_nhdsLT (sub_pos.2 hh)) key)

/-- **Lipschitz bound on a smaller strip.** If `f` is holomorphic on `Δ_h` and bounded by `K`
there, then on `{|Im| ≤ h'}`, `h' < h`, we have `‖f w - f z‖ ≤ K / (h - h') ‖w - z‖`. -/
theorem norm_sub_le_of_strip {f : ℂ → E} {h h' K : ℝ} (hf : DifferentiableOn ℂ f (strip h))
    (hK : ∀ z ∈ strip h, ‖f z‖ ≤ K) (hh : h' < h) {z w : ℂ} (hz : |z.im| ≤ h')
    (hw : |w.im| ≤ h') : ‖f w - f z‖ ≤ K / (h - h') * ‖w - z‖ := by
  set s : Set ℂ := {u | |u.im| ≤ h'}
  have hs : Convex ℝ s := by
    have : s = Complex.imLm ⁻¹' Icc (-h') h' := by
      ext u; simp [s, abs_le]
    rw [this]; exact (convex_Icc _ _).linear_preimage _
  refine hs.norm_image_sub_le_of_norm_deriv_le (fun u hu => ?_)
    (fun u hu => norm_deriv_le_of_strip hf hK hh hu) hz hw
  exact hf.differentiableAt ((isOpen_strip h).mem_nhds (lt_of_le_of_lt hu hh))

/-- **Cauchy estimate for differences** (used repeatedly in Proposition `CT`): for `f`
holomorphic on `Δ_h` with `‖f‖ ≤ K`, `|Im z| ≤ h' < h` and `t ∈ ℝ`,
`‖f (z + t) - f z‖ ≤ |t| K / (h - h')`. -/
theorem norm_translate_sub_le {f : ℂ → E} {h h' K : ℝ} (hf : DifferentiableOn ℂ f (strip h))
    (hK : ∀ z ∈ strip h, ‖f z‖ ≤ K) (hh : h' < h) {z : ℂ} (hz : |z.im| ≤ h') (t : ℝ) :
    ‖f (z + t) - f z‖ ≤ |t| * K / (h - h') := by
  have := norm_sub_le_of_strip hf hK hh hz (w := z + t) (by simpa using hz)
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
  calc _ ≤ K / (h - h') * |t| := this
    _ = |t| * K / (h - h') := by ring

/-- Strip-norm form of `norm_translate_sub_le`: on `Δ_{h'}` the translate difference is
bounded by `|t| K / (h - h')`. -/
theorem norm_translate_sub_le_of_mem_strip {f : ℂ → E} {h h' K : ℝ}
    (hf : DifferentiableOn ℂ f (strip h)) (hK : ∀ z ∈ strip h, ‖f z‖ ≤ K) (hh : h' < h)
    {z : ℂ} (hz : z ∈ strip h') (t : ℝ) :
    ‖f (z + t) - f z‖ ≤ |t| * K / (h - h') :=
  norm_translate_sub_le hf hK hh (le_of_lt hz) t

/-! ### `2 × 2` matrices: norm helpers -/

/-- `2 × 2` complex matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Rows of a `2 × 2` matrix are bounded by the `ℓ^∞` operator norm. -/
lemma row_sum_le_norm (M : M2) (i : Fin 2) : ‖M i 0‖ + ‖M i 1‖ ≤ ‖M‖ := by
  have h := Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) (Finset.mem_univ i)
  rw [← linfty_opNNNorm_def] at h
  have h' : ((∑ j : Fin 2, ‖M i j‖₊ : NNReal) : ℝ) ≤ (‖M‖₊ : ℝ) := by exact_mod_cast h
  simpa [Fin.sum_univ_two] using h'

/-- The `ℓ^∞` operator norm is bounded by any bound on the row sums. -/
lemma norm_le_of_rows (M : M2) {C : ℝ} (h0 : ‖M 0 0‖ + ‖M 0 1‖ ≤ C)
    (h1 : ‖M 1 0‖ + ‖M 1 1‖ ≤ C) : ‖M‖ ≤ C := by
  have hC : 0 ≤ C := le_trans (by positivity) h0
  rw [linfty_opNorm_def]
  have : ((Finset.univ : Finset (Fin 2)).sup fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) ≤
      ⟨C, hC⟩ := by
    refine Finset.sup_le fun i _ => ?_
    refine NNReal.coe_le_coe.1 ?_
    change _ ≤ C
    fin_cases i
    · simpa [Fin.sum_univ_two] using h0
    · simpa [Fin.sum_univ_two] using h1
  exact_mod_cast this

/-! ### Rotations over `ℂ` -/

/-- The (complexified) rotation `R_θ = [[cos θ, -sin θ], [sin θ, cos θ]]`, `θ ∈ ℂ`. -/
def rot (θ : ℂ) : M2 := !![cos θ, -sin θ; sin θ, cos θ]

/-- `J = [[0, -1], [1, 0]]`. -/
def Jm : M2 := !![0, -1; 1, 0]

/-- `R_a R_b = R_{a+b}`. -/
theorem rot_mul_rot (a b : ℂ) : rot a * rot b = rot (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, cos_add, sin_add] <;> ring

@[simp] theorem rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

/-- `det R_θ = 1`. -/
@[simp] theorem det_rot (θ : ℂ) : (rot θ).det = 1 := by
  simp only [rot, det_fin_two_of]
  linear_combination cos_sq_add_sin_sq θ

theorem rot_mul_rot_neg (θ : ℂ) : rot θ * rot (-θ) = 1 := by
  rw [rot_mul_rot, add_neg_cancel, rot_zero]

/-- `R_θ⁻¹ = R_{-θ}`. -/
theorem inv_rot (θ : ℂ) : (rot θ)⁻¹ = rot (-θ) :=
  Matrix.inv_eq_right_inv (rot_mul_rot_neg θ)

theorem rot_pi_div_two : rot ((Real.pi : ℂ) / 2) = Jm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, Jm, cos_pi_div_two, sin_pi_div_two]

theorem Jm_mul_Jm : Jm * Jm = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix `[[-sin θ, -cos θ], [cos θ, -sin θ]]` (`= R_{θ + π/2}`). -/
def rotAux (θ : ℂ) : M2 := !![-sin θ, -cos θ; cos θ, -sin θ]

/-- The matrix `[[-sin θ, cos θ], [-cos θ, -sin θ]]` (`= R_{-θ - π/2}`), inverse of `rotAux θ`. -/
def rotAuxInv (θ : ℂ) : M2 := !![-sin θ, cos θ; -cos θ, -sin θ]

/-- `R_{2θ} - 1 = 2 sin θ · R_{θ + π/2}`. -/
theorem rot_two_mul_sub_one (θ : ℂ) : rot (2 * θ) - 1 = (2 * sin θ) • rotAux θ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, rotAux, cos_two_mul, sin_two_mul] <;>
    linear_combination 2 * cos_sq_add_sin_sq θ

theorem rotAux_mul_rotAuxInv (θ : ℂ) : rotAux θ * rotAuxInv θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotAux, rotAuxInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination cos_sq_add_sin_sq θ
    | linear_combination sin_sq_add_cos_sq θ
    | ring

theorem det_rot_two_mul_sub_one (θ : ℂ) : (rot (2 * θ) - 1).det = (2 * sin θ) ^ 2 := by
  rw [rot_two_mul_sub_one, det_smul]
  simp only [Fintype.card_fin, rotAux, det_fin_two_of]
  linear_combination (2 * sin θ) ^ 2 * sin_sq_add_cos_sq θ

/-- Explicit inverse: `(R_{2θ} - 1)⁻¹ = (2 sin θ)⁻¹ · R_{-θ-π/2}` when `sin θ ≠ 0`. -/
theorem inv_rot_two_mul_sub_one {θ : ℂ} (hs : sin θ ≠ 0) :
    (rot (2 * θ) - 1)⁻¹ = (2 * sin θ)⁻¹ • rotAuxInv θ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [rot_two_mul_sub_one, smul_mul_smul_comm, rotAux_mul_rotAuxInv,
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero hs), one_smul]

/-- `R_{2θ} - 1` is invertible iff `sin θ ≠ 0`. -/
theorem isUnit_rot_two_mul_sub_one_iff (θ : ℂ) : IsUnit (rot (2 * θ) - 1) ↔ sin θ ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_rot_two_mul_sub_one, isUnit_iff_ne_zero]
  simp

/-- `R_{2θ} - 1` is invertible iff `θ ∉ πℤ`. -/
theorem isUnit_rot_two_mul_sub_one_iff' (θ : ℂ) :
    IsUnit (rot (2 * θ) - 1) ↔ ∀ k : ℤ, θ ≠ k * (Real.pi : ℂ) := by
  rw [isUnit_rot_two_mul_sub_one_iff, Ne, Complex.sin_eq_zero_iff, not_exists]

/-- Norm bound `‖(R_{2θ} - 1)⁻¹‖ ≤ (|sin θ| + |cos θ|) / (2 |sin θ|)`. -/
theorem norm_inv_rot_two_mul_sub_one_le {θ : ℂ} (hs : sin θ ≠ 0) :
    ‖(rot (2 * θ) - 1)⁻¹‖ ≤ (‖sin θ‖ + ‖cos θ‖) / (2 * ‖sin θ‖) := by
  rw [inv_rot_two_mul_sub_one hs, norm_smul]
  have hW : ‖rotAuxInv θ‖ ≤ ‖sin θ‖ + ‖cos θ‖ := by
    refine norm_le_of_rows _ ?_ ?_
    · simp [rotAuxInv]
    · simp [rotAuxInv, add_comm]
  have hpos : 0 < ‖sin θ‖ := norm_pos_iff.2 hs
  rw [norm_inv, norm_mul, Complex.norm_two, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hW (by positivity)

/-! ### The projection `𝒬` -/

/-- The projection `𝒬 M = (M + J M J) / 2` onto symmetric traceless matrices. -/
def Q (M : M2) : M2 := (1 / 2 : ℂ) • (M + Jm * M * Jm)

theorem Q_eq (M : M2) :
    Q M = !![(M 0 0 - M 1 1) / 2, (M 0 1 + M 1 0) / 2;
      (M 0 1 + M 1 0) / 2, (M 1 1 - M 0 0) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Q, Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- `M - 𝒬 M = [[a, -b], [b, a]]` with `a = (M₀₀ + M₁₁)/2`, `b = (M₁₀ - M₀₁)/2`. -/
theorem sub_Q_eq (M : M2) :
    M - Q M = !![(M 0 0 + M 1 1) / 2, -((M 1 0 - M 0 1) / 2);
      (M 1 0 - M 0 1) / 2, (M 0 0 + M 1 1) / 2] := by
  rw [Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem Q_sub (M N : M2) : Q (M - N) = Q M - Q N := by
  rw [Q_eq, Q_eq, Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem Q_add (M N : M2) : Q (M + N) = Q M + Q N := by
  rw [Q_eq, Q_eq, Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Matrices of the form `[[a, -b], [b, a]]` commute with every `R_θ`, `θ ∈ ℂ`. -/
theorem conformal_mul_rot (a b θ : ℂ) :
    !![a, -b; b, a] * rot θ = rot θ * !![a, -b; b, a] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `M - 𝒬 M` commutes with every `R_θ`, `θ ∈ ℂ`. -/
theorem sub_Q_mul_rot (M : M2) (θ : ℂ) : (M - Q M) * rot θ = rot θ * (M - Q M) := by
  rw [sub_Q_eq]
  exact conformal_mul_rot _ _ θ

/-- `R_{-θ} 𝒬(M) = 𝒬(M R_θ)`. -/
theorem rot_neg_mul_Q (M : M2) (θ : ℂ) : rot (-θ) * Q M = Q (M * rot θ) := by
  rw [Q_eq, Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `R_θ 𝒬(M) = 𝒬(R_θ M)`. -/
theorem rot_mul_Q (M : M2) (θ : ℂ) : rot θ * Q M = Q (rot θ * M) := by
  rw [Q_eq, Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Identity (Q)**: `(R_{-θ₁} - R_{θ₂}) 𝒬(M) = 𝒬(M R_{θ₁} - R_{θ₂} M)`. -/
theorem rot_sub_rot_mul_Q (M : M2) (θ₁ θ₂ : ℂ) :
    (rot (-θ₁) - rot θ₂) * Q M = Q (M * rot θ₁ - rot θ₂ * M) := by
  rw [Matrix.sub_mul, rot_neg_mul_Q, rot_mul_Q, Q_sub]

/-- `𝒬 M = 0` iff `M = [[a, -b], [b, a]]`. -/
theorem Q_eq_zero_iff (M : M2) : Q M = 0 ↔ ∃ a b : ℂ, M = !![a, -b; b, a] := by
  constructor
  · intro h
    have h1 : (M 0 0 - M 1 1) / 2 = 0 := by
      simpa [Q_eq] using congrFun (congrFun h 0) 0
    have h2 : (M 0 1 + M 1 0) / 2 = 0 := by
      simpa [Q_eq] using congrFun (congrFun h 0) 1
    refine ⟨M 0 0, M 1 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;>
      first
      | linear_combination 2 * h1
      | linear_combination (-2) * h1
      | linear_combination 2 * h2
  · rintro ⟨a, b, rfl⟩
    rw [Q_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `M` commutes with all rotations `R_θ`, `θ ∈ ℂ`, iff `𝒬 M = 0`. -/
theorem commute_rot_iff_Q_eq_zero (M : M2) : (∀ θ : ℂ, M * rot θ = rot θ * M) ↔ Q M = 0 := by
  constructor
  · intro h
    have e := h ((Real.pi : ℂ) / 2)
    rw [rot_pi_div_two] at e
    simp only [Q]
    rw [← e, Matrix.mul_assoc, Jm_mul_Jm]
    simp
  · intro h θ
    obtain ⟨a, b, rfl⟩ := (Q_eq_zero_iff M).1 h
    exact conformal_mul_rot a b θ

/-! ### Projection onto rotations -/

/-- `a² + b² = 1` over `ℂ` implies `(a, b) = (cos φ, sin φ)` for some `φ ∈ ℂ`. -/
theorem exists_cos_sin {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) : ∃ φ : ℂ, cos φ = a ∧ sin φ = b := by
  set w := a + b * I with hwdef
  have hw : w * (a - b * I) = 1 := by
    rw [hwdef]; linear_combination h - b ^ 2 * I_sq
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw
  have hinv : a - b * I = w⁻¹ := eq_inv_of_mul_eq_one_right hw
  refine ⟨-I * log w, ?_⟩
  set φ := -I * log w
  have hφ : φ * I = log w := by
    simp only [φ]; linear_combination (-log w) * I_sq
  have e1 : cos φ + sin φ * I = a + b * I := by
    rw [← exp_mul_I, hφ, exp_log hw0]
  have e2 : cos φ - sin φ * I = a - b * I := by
    have := exp_mul_I (-φ)
    rw [cos_neg, sin_neg, neg_mul, hφ, exp_neg, exp_log hw0, ← hinv] at this
    linear_combination -this
  refine ⟨by linear_combination (e1 + e2) / 2, ?_⟩
  have : (sin φ - b) * (2 * I) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' (mul_ne_zero two_ne_zero I_ne_zero)

/-- The principal square root `d ^ (1/2)` has nonnegative real part. -/
theorem re_cpow_inv_two_nonneg (d : ℂ) : 0 ≤ (d ^ (2⁻¹ : ℂ)).re := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [zero_cpow (by norm_num)]; simp
  rw [cpow_def_of_ne_zero hd, exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have := neg_pi_lt_arg d
    have e : (log d * 2⁻¹).im = arg d / 2 := by simp [mul_im, log_im]; ring
    rw [e]; linarith
  · have := arg_le_pi d
    have e : (log d * 2⁻¹).im = arg d / 2 := by simp [mul_im, log_im]; ring
    rw [e]; linarith

/-- The "SO(2) projection" `(M - 𝒬 M) / √det(M - 𝒬 M)` (principal square root). -/
def soProj (M : M2) : M2 := (((M - Q M).det) ^ (2⁻¹ : ℂ))⁻¹ • (M - Q M)

/-- `det M = det (M - 𝒬 M) + det (𝒬 M)`. -/
theorem det_eq_det_sub_Q_add_det_Q (M : M2) : M.det = (M - Q M).det + (Q M).det := by
  rw [sub_Q_eq, Q_eq, det_fin_two_of, det_fin_two_of, det_fin_two M]
  ring

/-- If `det (M - 𝒬 M) ≠ 0`, then `soProj M` is a rotation `R_φ`, `φ ∈ ℂ`. -/
theorem soProj_eq_rot (M : M2) (hd : (M - Q M).det ≠ 0) : ∃ φ : ℂ, soProj M = rot φ := by
  set d := (M - Q M).det with hddef
  set s := d ^ (2⁻¹ : ℂ) with hsdef
  have hs2 : s ^ 2 = d := by
    rw [hsdef]; exact_mod_cast cpow_nat_inv_pow d (n := 2) two_ne_zero
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hs2; exact hd (by simpa using hs2.symm)
  set α := (M 0 0 + M 1 1) / 2
  set β := (M 1 0 - M 0 1) / 2
  have hdet : d = α ^ 2 + β ^ 2 := by
    rw [hddef, sub_Q_eq, det_fin_two_of]; ring
  have h1 : (s⁻¹ * α) ^ 2 + (s⁻¹ * β) ^ 2 = 1 := by
    field_simp
    rw [hs2, hdet]
  obtain ⟨φ, hc, hsn⟩ := exists_cos_sin h1
  refine ⟨φ, ?_⟩
  simp only [soProj]
  rw [← hddef, ← hsdef, sub_Q_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, hc, hsn, α, β]

/-- **Projection onto rotations** (end of the proof of Proposition `CT`): if `det M = 1` and
`‖𝒬 M‖ ≤ 1/2`, then `soProj M` is a rotation `R_φ` with `‖soProj M - M‖ ≤ (‖M‖ + 2) ‖𝒬 M‖`. -/
theorem soProj_spec (M : M2) (hM : M.det = 1) (hL : ‖Q M‖ ≤ 1 / 2) :
    (∃ φ : ℂ, soProj M = rot φ) ∧ ‖soProj M - M‖ ≤ (‖M‖ + 2) * ‖Q M‖ := by
  set ℓ := ‖Q M‖ with hℓ
  set p := (M 0 0 - M 1 1) / 2
  set q := (M 0 1 + M 1 0) / 2
  have hpq : ‖p‖ + ‖q‖ ≤ ℓ := by
    have := row_sum_le_norm (Q M) 0
    have e0 : Q M 0 0 = p := by simp [Q_eq, p]
    have e1 : Q M 0 1 = q := by simp [Q_eq, q]
    rwa [e0, e1] at this
  set d := (M - Q M).det with hddef
  have hdL : d = 1 + p ^ 2 + q ^ 2 := by
    have hLdet : (Q M).det = -(p ^ 2 + q ^ 2) := by
      rw [Q_eq, det_fin_two_of]; simp only [p, q]; ring
    have h := det_eq_det_sub_Q_add_det_Q M
    rw [hM, hLdet, ← hddef] at h
    linear_combination -h
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have hd1 : ‖d - 1‖ ≤ ℓ ^ 2 := by
    have : d - 1 = p ^ 2 + q ^ 2 := by rw [hdL]; ring
    rw [this]
    calc ‖p ^ 2 + q ^ 2‖ ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_; rw [norm_pow, norm_pow]
      _ ≤ (‖p‖ + ‖q‖) ^ 2 := by nlinarith [norm_nonneg p, norm_nonneg q]
      _ ≤ ℓ ^ 2 := by gcongr
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hd1
    nlinarith
  refine ⟨soProj_eq_rot M hd0, ?_⟩
  set s := d ^ (2⁻¹ : ℂ) with hsdef
  have hs2 : s ^ 2 = d := by
    rw [hsdef]; exact_mod_cast cpow_nat_inv_pow d (n := 2) two_ne_zero
  have hsre : 0 ≤ s.re := re_cpow_inv_two_nonneg d
  -- `‖s - 1‖ ≤ ‖d - 1‖`
  have hs1 : ‖s - 1‖ ≤ ‖d - 1‖ := by
    have hprod : ‖s - 1‖ * ‖s + 1‖ = ‖d - 1‖ := by
      rw [← norm_mul, ← hs2]; congr 1; ring
    have hge : 1 ≤ ‖s + 1‖ := by
      have := re_le_norm (s + 1)
      simp only [add_re, one_re] at this
      linarith
    nlinarith [norm_nonneg (s - 1)]
  have hsn : 3 / 4 ≤ ‖s‖ := by
    have := norm_sub_norm_le (1 : ℂ) s
    rw [norm_one, norm_sub_rev] at this
    nlinarith
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsn; linarith
  have hinv : ‖s⁻¹ - 1‖ ≤ 4 / 3 * ℓ ^ 2 := by
    have e : s⁻¹ - 1 = (1 - s) / s := by field_simp
    rw [e, norm_div, norm_sub_rev, div_le_iff₀ (by linarith)]
    nlinarith
  have hP : ‖M - Q M‖ ≤ ‖M‖ + ℓ := norm_sub_le _ _
  have hdecomp : soProj M - M = (s⁻¹ - 1) • (M - Q M) - Q M := by
    simp only [soProj]
    rw [← hddef, ← hsdef, sub_smul, one_smul]
    abel
  rw [hdecomp]
  have hA : ‖(s⁻¹ - 1) • (M - Q M)‖ ≤ 4 / 3 * ℓ ^ 2 * (‖M‖ + ℓ) := by
    rw [norm_smul]
    exact mul_le_mul hinv hP (norm_nonneg _) (by positivity)
  have hMn : 0 ≤ ‖M‖ := norm_nonneg _
  calc ‖(s⁻¹ - 1) • (M - Q M) - Q M‖ ≤ ‖(s⁻¹ - 1) • (M - Q M)‖ + ℓ := norm_sub_le _ _
    _ ≤ 4 / 3 * ℓ ^ 2 * (‖M‖ + ℓ) + ℓ := by linarith
    _ ≤ (‖M‖ + 2) * ℓ := by
      have h1 : ℓ * (‖M‖ + ℓ) ≤ 1 / 2 * (‖M‖ + 1 / 2) := by
        apply mul_le_mul hL (by linarith) (by positivity) (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left h1 hℓ0]

end Red.AFK
