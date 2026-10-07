/-
# The cosine actions  (paper §2, Lemma `c-lem:cosine-actions`, (2.6)–(2.7))

For the rectangular cosine potential `V_μ(x) = 2 - cos(2πx₁/μ) - cos(2πx₂)` we define the
electric Agmon length `ℓ_V(c) = ∫₀¹ √(V(c t)) |ċ(t)| dt` (Euclidean `|·|`) of `C¹` curves, the
Agmon distance `d_V(x,y) = inf ℓ_V(c)` and the lattice distance `D(r,q) = d_V(0, (rμ, q))`
(paper `c-eq:agmon-distance`), and prove Lemma `c-lem:cosine-actions`
(`c-eq:all-cosine-distances`):

* `cosineDist_eq`: `D(r,q) = |r| S₁ + |q| S₂`, `S₁ = 2√2μ/π`, `S₂ = 2√2/π`, for every `μ > 0`;
* `cosineDist_isLatticeDistance`: `D` satisfies (2.6) (`c-eq:distance-properties`);
* `cosine_Srem`: `S_rem = inf_{m ∉ 𝒩} D(m) = 2 min{S₁, S₂}`;

together with the harmonic levels of the square well `μ = 1`:
`λ_𝐧 = 2√2π(n₁+n₂+1)` with multiplicity `d_{λ_N} = N + 1`.

The lower bound is the calibration argument of the paper (Cauchy–Schwarz
`c-eq:cosine-calibration` plus the change of variables `F_j ∘ x_j`); the upper bound is
realized exactly by an `L`-shaped path along the coordinate axes, smoothly reparametrized by
`Real.smoothTransition`, so the infimum is attained.
-/
import ContinuumMagnetic.Basic

noncomputable section

open Real intervalIntegral

namespace CMS

lemma Scos_pos : 0 < Scos := by
  unfold Scos; positivity

/-- `√(1 - cos 2θ) = √2 |sin θ|`. -/
lemma sqrt_one_sub_cos_two_mul (θ : ℝ) :
    Real.sqrt (1 - Real.cos (2 * θ)) = Real.sqrt 2 * |Real.sin θ| := by
  have : 1 - Real.cos (2 * θ) = 2 * Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']; ring
  rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]

/-- The well profile `w(s) = √(1 - cos 2πs)`. -/
def wellProfile (s : ℝ) : ℝ := Real.sqrt (1 - Real.cos (2 * Real.pi * s))

lemma wellProfile_continuous : Continuous wellProfile := by
  unfold wellProfile; fun_prop

lemma wellProfile_periodic : Function.Periodic wellProfile 1 := by
  intro s; unfold wellProfile
  rw [show 2 * π * (s + 1) = 2 * π * s + 2 * π by ring, Real.cos_add_two_pi]

lemma wellProfile_neg (s : ℝ) : wellProfile (-s) = wellProfile s := by
  unfold wellProfile; rw [show 2 * π * -s = -(2 * π * s) by ring, Real.cos_neg]

/-- `∫₀¹ √(1 - cos 2πs) ds = 2√2/π`. -/
lemma integral_wellProfile_one : ∫ s in (0:ℝ)..1, wellProfile s = Scos := by
  have h : ∀ s ∈ Set.uIcc (0:ℝ) 1, wellProfile s = Real.sqrt 2 * Real.sin (π * s) := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    unfold wellProfile
    rw [show 2 * π * s = 2 * (π * s) by ring, sqrt_one_sub_cos_two_mul,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [pi_pos, hs.1])
        (by nlinarith [pi_pos, hs.2]))]
  rw [integral_congr h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) pi_ne_zero, integral_sin]
  simp [Scos]
  field_simp
  norm_num

/-- `∫₀^k √(1 - cos 2πs) ds = k · 2√2/π` for `k ∈ ℤ`. -/
lemma integral_wellProfile_int (k : ℤ) : ∫ s in (0:ℝ)..k, wellProfile s = k * Scos := by
  have := wellProfile_periodic.intervalIntegral_add_zsmul_eq k 0
    (fun a b => wellProfile_continuous.intervalIntegrable a b)
  simpa [integral_wellProfile_one] using this

/-! ### Agmon length and Agmon distance -/

/-- The Euclidean norm `√(v₁² + v₂²)` on `ℝ × ℝ` (Mathlib's default norm on `ℝ × ℝ` is the
sup norm, which is *not* the one in the Agmon metric). -/
def eucl (v : ℝ × ℝ) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

/-- The electric Agmon length `ℓ_V(c) = ∫₀¹ √(V(c(t))) |ċ(t)| dt` (paper (2.7)). -/
def agmonLength (V : ℝ × ℝ → ℝ) (c : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, Real.sqrt (V (c t)) * eucl (deriv c t)

/-- Admissible curves from `x` to `y`: `C¹` curves `c` with `c 0 = x`, `c 1 = y`. -/
def AgmonCurve (x y : ℝ × ℝ) : Type :=
  {c : ℝ → ℝ × ℝ // ContDiff ℝ 1 c ∧ c 0 = x ∧ c 1 = y}

/-- The Agmon distance `d_V(x,y) = inf_{c(0)=x, c(1)=y} ℓ_V(c)` (paper (2.7)). -/
def agmonDist (V : ℝ × ℝ → ℝ) (x y : ℝ × ℝ) : ℝ :=
  ⨅ c : AgmonCurve x y, agmonLength V c.1

/-- The lattice distance `D(r,q) = d_V(0, r a₁ + q a₂)` of the cosine potential `V_μ`,
with `a₁ = (μ,0)`, `a₂ = (0,1)`. -/
def cosineDist (μ : ℝ) (m : ℤ × ℤ) : ℝ :=
  agmonDist (cosinePotential μ) 0 ((m.1 : ℝ) * μ, (m.2 : ℝ))

/-- `S₁ = 2√2 μ/π`. -/
def cosineAction₁ (μ : ℝ) : ℝ := Scos * μ

/-- `S₂ = 2√2/π`. -/
def cosineAction₂ : ℝ := Scos

/-! ### Auxiliary facts -/

lemma wellProfile_nonneg (s : ℝ) : 0 ≤ wellProfile s := Real.sqrt_nonneg _

lemma wellProfile_sq (s : ℝ) : wellProfile s ^ 2 = 1 - Real.cos (2 * π * s) :=
  Real.sq_sqrt (by linarith [Real.cos_le_one (2 * π * s)])

lemma wellProfile_intCast (k : ℤ) : wellProfile k = 0 := by
  unfold wellProfile
  rw [show 2 * π * (k : ℝ) = k * (2 * π) by ring, Real.cos_int_mul_two_pi]; simp

lemma cosinePotential_eq (μ : ℝ) (x : ℝ × ℝ) :
    cosinePotential μ x = wellProfile (x.1 / μ) ^ 2 + wellProfile x.2 ^ 2 := by
  rw [wellProfile_sq, wellProfile_sq, cosinePotential, mul_div_assoc]; ring

/-- Cauchy–Schwarz in `ℝ²` (paper `c-eq:cosine-calibration`). -/
lemma cauchySchwarz_two {a b x y : ℝ} :
    a * |x| + b * |y| ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have := sq_nonneg (a * |y| - b * |x|)
  have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith [abs_nonneg x, abs_nonneg y]

lemma hasDerivAt_fst_of {c : ℝ → ℝ × ℝ} {t : ℝ} (h : DifferentiableAt ℝ c t) :
    HasDerivAt (fun s => (c s).1) (deriv c t).1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h.hasDerivAt

lemma hasDerivAt_snd_of {c : ℝ → ℝ × ℝ} {t : ℝ} (h : DifferentiableAt ℝ c t) :
    HasDerivAt (fun s => (c s).2) (deriv c t).2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h.hasDerivAt

/-- The one–dimensional calibration: `∫₀¹ g(x)|ẋ| ≥ |∫_{x(0)}^{x(1)} g|`. -/
lemma calibration {x : ℝ → ℝ} (hx : ContDiff ℝ 1 x) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ s, 0 ≤ g s) :
    |∫ s in x 0..x 1, g s| ≤ ∫ t in (0:ℝ)..1, g (x t) * |deriv x t| := by
  have hd := hx.differentiable (by norm_num)
  have hc := hx.continuous_deriv le_rfl
  rw [← integral_comp_mul_deriv (fun t _ => (hd t).hasDerivAt) hc.continuousOn hg]
  refine (abs_integral_le_integral_abs zero_le_one).trans (le_of_eq ?_)
  congr 1; ext t; simp [abs_mul, abs_of_nonneg (hg0 _)]

/-- Equality case for monotone reparametrizations of a segment and an even weight. -/
lemma integral_even_comp_monotone {g : ℝ → ℝ} (hg : Continuous g) (hge : ∀ s, g (-s) = g s)
    (a : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hmono : Monotone φ) :
    ∫ t in (0:ℝ)..1, g (a * φ t) * |deriv (fun t => a * φ t) t|
      = ∫ s in |a| * φ 0..|a| * φ 1, g s := by
  have hd := hφ.differentiable (by norm_num)
  have hc := hφ.continuous_deriv le_rfl
  have hpt : ∀ t, g (a * φ t) * |deriv (fun t => a * φ t) t|
      = g (|a| * φ t) * (|a| * deriv φ t) := by
    intro t
    rw [deriv_const_mul _ (hd t), abs_mul, abs_of_nonneg hmono.deriv_nonneg]
    rcases abs_choice a with h | h
    · rw [h]
    · rw [h, neg_mul a (φ t), hge]
  simp_rw [hpt]
  exact integral_comp_mul_deriv (f := fun t => |a| * φ t) (g := g)
    (fun t _ => (hd t).hasDerivAt.const_mul |a|) (continuous_const.mul hc).continuousOn hg

lemma integral_wellProfile_div {μ : ℝ} (hμ : 0 < μ) (k : ℤ) :
    ∫ s in (0:ℝ)..k * μ, wellProfile (s / μ) = k * μ * Scos := by
  rw [intervalIntegral.integral_comp_div _ hμ.ne', zero_div, mul_div_cancel_right₀ _ hμ.ne',
    integral_wellProfile_int, smul_eq_mul]; ring

/-! ### Lower bound -/

/-- The calibration lower bound for an arbitrary `C¹` curve. -/
lemma agmonLength_cosine_ge (μ : ℝ) {c : ℝ → ℝ × ℝ} (hc : ContDiff ℝ 1 c) :
    |∫ s in (c 0).1..(c 1).1, wellProfile (s / μ)| + |∫ s in (c 0).2..(c 1).2, wellProfile s|
      ≤ agmonLength (cosinePotential μ) c := by
  have hd := hc.differentiable (by norm_num)
  have hcc := hc.continuous
  have hdc := hc.continuous_deriv le_rfl
  have hx₁ : ContDiff ℝ 1 (fun t => (c t).1) := contDiff_fst.comp hc
  have hx₂ : ContDiff ℝ 1 (fun t => (c t).2) := contDiff_snd.comp hc
  have hg₁ : Continuous fun s => wellProfile (s / μ) :=
    wellProfile_continuous.comp (continuous_id.div_const μ)
  have e₁ : ∀ t, deriv (fun s => (c s).1) t = (deriv c t).1 := fun t =>
    (hasDerivAt_fst_of (hd t)).deriv
  have e₂ : ∀ t, deriv (fun s => (c s).2) t = (deriv c t).2 := fun t =>
    (hasDerivAt_snd_of (hd t)).deriv
  have c₁ := calibration hx₁ hg₁ (fun s => wellProfile_nonneg _)
  have c₂ := calibration hx₂ wellProfile_continuous wellProfile_nonneg
  simp only [e₁, e₂] at c₁ c₂
  refine (add_le_add c₁ c₂).trans ?_
  have hi₁ : Continuous fun t => wellProfile ((c t).1 / μ) * |(deriv c t).1| := by
    have := hg₁.comp (continuous_fst.comp hcc)
    exact this.mul (continuous_abs.comp (continuous_fst.comp hdc))
  have hi₂ : Continuous fun t => wellProfile (c t).2 * |(deriv c t).2| :=
    (wellProfile_continuous.comp (continuous_snd.comp hcc)).mul
      (continuous_abs.comp (continuous_snd.comp hdc))
  rw [← integral_add (hi₁.intervalIntegrable _ _) (hi₂.intervalIntegrable _ _)]
  unfold agmonLength
  have hV : Continuous fun t => Real.sqrt (cosinePotential μ (c t)) * eucl (deriv c t) := by
    unfold cosinePotential eucl; fun_prop
  refine integral_mono_on zero_le_one ((hi₁.add hi₂).intervalIntegrable _ _)
    (hV.intervalIntegrable _ _) (fun t _ => ?_)
  rw [cosinePotential_eq]
  exact cauchySchwarz_two

/-- Lower bound for every admissible curve from `0` to `(rμ, q)`. -/
lemma agmonLength_cosine_ge_lattice {μ : ℝ} (hμ : 0 < μ) (m : ℤ × ℤ)
    (c : AgmonCurve 0 ((m.1 : ℝ) * μ, (m.2 : ℝ))) :
    |(m.1 : ℝ)| * cosineAction₁ μ + |(m.2 : ℝ)| * cosineAction₂
      ≤ agmonLength (cosinePotential μ) c.1 := by
  obtain ⟨c, hc, h0, h1⟩ := c
  have := agmonLength_cosine_ge μ hc
  rw [h0, h1] at this
  simp only [Prod.fst_zero, Prod.snd_zero] at this
  rw [integral_wellProfile_div hμ, integral_wellProfile_int] at this
  convert this using 2
  · rw [abs_mul, abs_mul, abs_of_pos hμ, abs_of_pos Scos_pos, cosineAction₁]; ring
  · rw [abs_mul, abs_of_pos Scos_pos, cosineAction₂]

/-! ### Upper bound: an `L`-shaped `C^∞` path -/

/-- The `L`-shaped path: first horizontally from `0` to `(rμ,0)` (for `t ∈ [0,1/3]`), then
vertically to `(rμ,q)` (for `t ∈ [2/3,1]`), smoothly reparametrized. -/
def lPath (μ : ℝ) (m : ℤ × ℤ) (t : ℝ) : ℝ × ℝ :=
  ((m.1 : ℝ) * μ * smoothTransition (3 * t), (m.2 : ℝ) * smoothTransition (3 * t - 2))

lemma lPath_contDiff (μ : ℝ) (m : ℤ × ℤ) : ContDiff ℝ 1 (lPath μ m) := by
  unfold lPath
  refine ContDiff.prodMk ?_ ?_
  · exact contDiff_const.mul (smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))
  · exact contDiff_const.mul (smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma lPath_zero (μ : ℝ) (m : ℤ × ℤ) : lPath μ m 0 = 0 := by
  simp [lPath, smoothTransition.zero_of_nonpos (show (-2:ℝ) ≤ 0 by norm_num)]

lemma lPath_one (μ : ℝ) (m : ℤ × ℤ) : lPath μ m 1 = ((m.1 : ℝ) * μ, (m.2 : ℝ)) := by
  simp [lPath, smoothTransition.one_of_one_le (show (1:ℝ) ≤ 3 by norm_num),
    show (3:ℝ) - 2 = 1 by norm_num]

/-- The admissible `L`-shaped curve. -/
def lCurve (μ : ℝ) (m : ℤ × ℤ) : AgmonCurve 0 ((m.1 : ℝ) * μ, (m.2 : ℝ)) :=
  ⟨lPath μ m, lPath_contDiff μ m, lPath_zero μ m, lPath_one μ m⟩

/-- The `L`-shaped path realizes the calibration bound. -/
lemma agmonLength_lPath {μ : ℝ} (hμ : 0 < μ) (m : ℤ × ℤ) :
    agmonLength (cosinePotential μ) (lPath μ m)
      = |(m.1 : ℝ)| * cosineAction₁ μ + |(m.2 : ℝ)| * cosineAction₂ := by
  set a : ℝ := (m.1 : ℝ) * μ with ha_def
  set b : ℝ := (m.2 : ℝ) with hb_def
  set φ₁ : ℝ → ℝ := fun t => smoothTransition (3 * t) with hφ₁_def
  set φ₂ : ℝ → ℝ := fun t => smoothTransition (3 * t - 2) with hφ₂_def
  have hφ₁ : ContDiff ℝ 1 φ₁ := smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hφ₂ : ContDiff ℝ 1 φ₂ := smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hm₁ : Monotone φ₁ := fun s t h => smoothTransition.monotone (by linarith)
  have hm₂ : Monotone φ₂ := fun s t h => smoothTransition.monotone (by linarith)
  have hd₁ := hφ₁.differentiable (by norm_num)
  have hd₂ := hφ₂.differentiable (by norm_num)
  have hc₁ : Continuous fun t => a * φ₁ t := continuous_const.mul hφ₁.continuous
  have hc₂ : Continuous fun t => b * φ₂ t := continuous_const.mul hφ₂.continuous
  have hdc₁ : Continuous (deriv fun t => a * φ₁ t) :=
    (contDiff_const.mul hφ₁).continuous_deriv le_rfl
  have hdc₂ : Continuous (deriv fun t => b * φ₂ t) :=
    (contDiff_const.mul hφ₂).continuous_deriv le_rfl
  have hg₁ : Continuous fun s => wellProfile (s / μ) :=
    wellProfile_continuous.comp (continuous_id.div_const μ)
  have hpath : lPath μ m = fun t => (a * φ₁ t, b * φ₂ t) := rfl
  have hderiv : ∀ t, deriv (lPath μ m) t
      = (deriv (fun t => a * φ₁ t) t, deriv (fun t => b * φ₂ t) t) := fun t => by
    rw [hpath, deriv_const_mul _ (hd₁ t), deriv_const_mul _ (hd₂ t)]
    exact (((hd₁ t).hasDerivAt.const_mul a).prodMk ((hd₂ t).hasDerivAt.const_mul b)).deriv
  have h00 : wellProfile 0 = 0 := by simpa using wellProfile_intCast 0
  -- pointwise, the Cauchy–Schwarz inequality is an equality along the `L`-path
  have hpt : ∀ t, Real.sqrt (cosinePotential μ (lPath μ m t)) * eucl (deriv (lPath μ m) t)
      = wellProfile (a * φ₁ t / μ) * |deriv (fun t => a * φ₁ t) t|
        + wellProfile (b * φ₂ t) * |deriv (fun t => b * φ₂ t) t| := by
    intro t
    rw [hderiv, cosinePotential_eq, hpath]
    simp only [eucl]
    rcases lt_or_ge t (2 / 3) with ht | ht
    · have hz : φ₂ t = 0 := smoothTransition.zero_of_nonpos (by linarith)
      have hev : (fun t => b * φ₂ t) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        simp [φ₂, smoothTransition.zero_of_nonpos (show 3 * s - 2 ≤ 0 by linarith)]
      rw [hev.deriv_eq, deriv_const, hz, mul_zero, h00]
      simp only [abs_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [Real.sqrt_sq (wellProfile_nonneg _), Real.sqrt_sq_eq_abs]
    · have hz : φ₁ t = 1 := smoothTransition.one_of_one_le (by linarith)
      have hev : (fun t => a * φ₁ t) =ᶠ[nhds t] fun _ => a := by
        filter_upwards [eventually_gt_nhds (show (1:ℝ) / 3 < t by linarith)] with s hs
        simp [φ₁, smoothTransition.one_of_one_le (show 1 ≤ 3 * s by linarith)]
      have h0 : wellProfile (a / μ) = 0 := by
        rw [show a / μ = ((m.1 : ℤ) : ℝ) by simp [a, hμ.ne']]; exact wellProfile_intCast _
      rw [hev.deriv_eq, deriv_const, hz, mul_one, h0]
      simp only [abs_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [Real.sqrt_sq (wellProfile_nonneg _), Real.sqrt_sq_eq_abs]
  unfold agmonLength
  simp_rw [hpt]
  have hi₁ : Continuous fun t => wellProfile (a * φ₁ t / μ) * |deriv (fun t => a * φ₁ t) t| :=
    (hg₁.comp hc₁).mul (continuous_abs.comp hdc₁)
  have hi₂ : Continuous fun t => wellProfile (b * φ₂ t) * |deriv (fun t => b * φ₂ t) t| :=
    (wellProfile_continuous.comp hc₂).mul (continuous_abs.comp hdc₂)
  rw [integral_add (hi₁.intervalIntegrable _ _) (hi₂.intervalIntegrable _ _)]
  rw [integral_even_comp_monotone (g := fun s => wellProfile (s / μ)) hg₁
      (fun s => by simp only [neg_div, wellProfile_neg]) a hφ₁ hm₁,
    integral_even_comp_monotone wellProfile_continuous wellProfile_neg b hφ₂ hm₂]
  have e10 : φ₁ 0 = 0 := by simp [φ₁]
  have e11 : φ₁ 1 = 1 := smoothTransition.one_of_one_le (by norm_num)
  have e20 : φ₂ 0 = 0 := smoothTransition.zero_of_nonpos (by norm_num)
  have e21 : φ₂ 1 = 1 := smoothTransition.one_of_one_le (by norm_num)
  rw [e10, e11, e20, e21, mul_zero, mul_one, mul_zero, mul_one]
  have ha : |a| = ((|m.1| : ℤ) : ℝ) * μ := by
    rw [ha_def, abs_mul, abs_of_pos hμ, Int.cast_abs]
  have hb : |b| = ((|m.2| : ℤ) : ℝ) := by rw [hb_def, Int.cast_abs]
  rw [ha, hb, integral_wellProfile_div hμ, integral_wellProfile_int, cosineAction₁,
    cosineAction₂, Int.cast_abs, Int.cast_abs]
  ring

/-! ### The cosine actions -/

/-- **Lemma c-lem:cosine-actions** (distance formula). For every `μ > 0`, the Agmon lattice
distance of the cosine potential is `D(r,q) = |r| S₁ + |q| S₂`, `S₁ = 2√2μ/π`, `S₂ = 2√2/π`. -/
theorem cosineDist_eq {μ : ℝ} (hμ : 0 < μ) (m : ℤ × ℤ) :
    cosineDist μ m = |(m.1 : ℝ)| * cosineAction₁ μ + |(m.2 : ℝ)| * cosineAction₂ := by
  have hlow := agmonLength_cosine_ge_lattice hμ m
  apply le_antisymm
  · refine (ciInf_le ⟨|(m.1 : ℝ)| * cosineAction₁ μ + |(m.2 : ℝ)| * cosineAction₂, ?_⟩
      (lCurve μ m)).trans (le_of_eq (agmonLength_lPath hμ m))
    rintro _ ⟨c, rfl⟩; exact hlow c
  · have : Nonempty (AgmonCurve 0 ((m.1 : ℝ) * μ, (m.2 : ℝ))) := ⟨lCurve μ m⟩
    exact le_ciInf hlow

/-- The infimum defining the cosine distance is attained by the `L`-shaped path. -/
theorem cosineDist_attained {μ : ℝ} (hμ : 0 < μ) (m : ℤ × ℤ) :
    agmonLength (cosinePotential μ) (lCurve μ m).1 = cosineDist μ m := by
  rw [cosineDist_eq hμ]; exact agmonLength_lPath hμ m

lemma cosineAction₁_pos {μ : ℝ} (hμ : 0 < μ) : 0 < cosineAction₁ μ :=
  mul_pos Scos_pos hμ

lemma cosineAction₂_pos : 0 < cosineAction₂ := Scos_pos

/-- A weighted `ℓ¹` norm with positive weights is a lattice distance. -/
theorem isLatticeDistance_weighted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsLatticeDistance (fun m : ℤ × ℤ => |(m.1 : ℝ)| * a + |(m.2 : ℝ)| * b) where
  zero := by simp
  symm m := by simp
  pos m hm := by
    rcases eq_or_ne m.1 0 with h1 | h1
    · have h2 : m.2 ≠ 0 := fun h2 => hm (Prod.ext h1 h2)
      have : (0:ℝ) < |(m.2 : ℝ)| := abs_pos.2 (by exact_mod_cast h2)
      positivity
    · have : (0:ℝ) < |(m.1 : ℝ)| := abs_pos.2 (by exact_mod_cast h1)
      positivity
  triangle m n := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    nlinarith [abs_add_le (m.1 : ℝ) n.1, abs_add_le (m.2 : ℝ) n.2]
  coercive := by
    refine ⟨min a b, 0, lt_min ha hb, fun m => ?_⟩
    unfold l1
    nlinarith [min_le_left a b, min_le_right a b, abs_nonneg (m.1 : ℝ), abs_nonneg (m.2 : ℝ)]

/-- The cosine distance `D` is a lattice distance (paper (2.6)). -/
theorem cosineDist_isLatticeDistance {μ : ℝ} (hμ : 0 < μ) :
    IsLatticeDistance (cosineDist μ) := by
  have : cosineDist μ = fun m : ℤ × ℤ => |(m.1 : ℝ)| * cosineAction₁ μ
      + |(m.2 : ℝ)| * cosineAction₂ := funext (cosineDist_eq hμ)
  rw [this]
  exact isLatticeDistance_weighted (cosineAction₁_pos hμ) cosineAction₂_pos

lemma two_le_of_not_mem_axialNbhd {m : ℤ × ℤ} (hm : m ∉ axialNbhd) :
    (2 : ℝ) ≤ |(m.1 : ℝ)| + |(m.2 : ℝ)| := by
  have : (2 : ℤ) ≤ |m.1| + |m.2| := by
    by_contra h
    apply hm
    have h1 : |m.1| ≤ 1 := by linarith [abs_nonneg m.2]
    have h2 : |m.2| ≤ 1 := by linarith [abs_nonneg m.1]
    rw [abs_le] at h1 h2
    obtain ⟨x, y⟩ := m
    simp only at h1 h2 h
    simp only [axialNbhd, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    interval_cases x <;> interval_cases y <;> simp_all
  rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast this

/-- **Lemma c-lem:cosine-actions** (remote action). `S_rem = inf_{m ∉ 𝒩} D(m) = 2 min{S₁,S₂}`. -/
theorem cosine_Srem {μ : ℝ} (hμ : 0 < μ) :
    ⨅ m : {m : ℤ × ℤ // m ∉ axialNbhd}, cosineDist μ m.1
      = 2 * min (cosineAction₁ μ) cosineAction₂ := by
  have hlow : ∀ m : {m : ℤ × ℤ // m ∉ axialNbhd},
      2 * min (cosineAction₁ μ) cosineAction₂ ≤ cosineDist μ m.1 := by
    rintro ⟨m, hm⟩
    rw [cosineDist_eq hμ]
    have := two_le_of_not_mem_axialNbhd hm
    have h1 := cosineAction₁_pos hμ
    have h2 := cosineAction₂_pos
    nlinarith [min_le_left (cosineAction₁ μ) cosineAction₂,
      min_le_right (cosineAction₁ μ) cosineAction₂, abs_nonneg (m.1 : ℝ), abs_nonneg (m.2 : ℝ),
      lt_min h1 h2]
  have h20 : ((2, 0) : ℤ × ℤ) ∉ axialNbhd := by simp [axialNbhd]
  have h02 : ((0, 2) : ℤ × ℤ) ∉ axialNbhd := by simp [axialNbhd]
  have : Nonempty {m : ℤ × ℤ // m ∉ axialNbhd} := ⟨⟨_, h20⟩⟩
  refine le_antisymm ?_ (le_ciInf hlow)
  have hbdd : BddBelow (Set.range fun m : {m : ℤ × ℤ // m ∉ axialNbhd} => cosineDist μ m.1) :=
    ⟨_, by rintro _ ⟨m, rfl⟩; exact hlow m⟩
  rcases min_choice (cosineAction₁ μ) cosineAction₂ with h | h
  · refine (ciInf_le hbdd ⟨_, h20⟩).trans (le_of_eq ?_)
    rw [cosineDist_eq hμ, h]; norm_num
  · refine (ciInf_le hbdd ⟨_, h02⟩).trans (le_of_eq ?_)
    rw [cosineDist_eq hμ, h]; norm_num

/-! ### Harmonic levels of the square well (`μ = 1`) -/

/-- For `μ = 1`, `λ_𝐧 = 2√2π(n₁+n₂+1)`. -/
theorem harmonicLevel_one (n : ℕ × ℕ) :
    harmonicLevel 1 n = 2 * Real.sqrt 2 * π * (n.1 + n.2 + 1) := by
  unfold harmonicLevel; ring

/-- For `μ = 1`, `λ_𝐧 = λ_N := 2√2π(N+1)` iff `n₁ + n₂ = N`. -/
theorem harmonicLevel_one_eq_iff (n : ℕ × ℕ) (N : ℕ) :
    harmonicLevel 1 n = 2 * Real.sqrt 2 * π * (N + 1) ↔ n.1 + n.2 = N := by
  rw [harmonicLevel_one]
  have hc : (0 : ℝ) < 2 * Real.sqrt 2 * π := by positivity
  constructor
  · intro h
    have := mul_left_cancel₀ hc.ne' h
    have h' : ((n.1 + n.2 : ℕ) : ℝ) = N := by push_cast; linarith
    exact_mod_cast h'
  · intro h
    rw [← h]; push_cast; ring

/-- For `μ = 1`, the level `λ_N = 2√2π(N+1)` has multiplicity `d_{λ_N} = N + 1`. -/
theorem harmonicLevel_one_multiplicity (N : ℕ) :
    {n : ℕ × ℕ | harmonicLevel 1 n = 2 * Real.sqrt 2 * π * (N + 1)}.ncard = N + 1 := by
  have : {n : ℕ × ℕ | harmonicLevel 1 n = 2 * Real.sqrt 2 * π * (N + 1)}
      = ↑(Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)) := by
    ext n; simp [harmonicLevel_one_eq_iff]
  rw [this, Set.ncard_coe_finset, Finset.Nat.card_antidiagonal]

end CMS
