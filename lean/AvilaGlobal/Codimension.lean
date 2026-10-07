/-
# Codimensionality of critical cocycles  (paper §1.4 and §4: Theorems `cod`, `cod1`)

* `Pot δ` — the real Banach space `C^ω_δ(ℝ/ℤ, ℝ)`: bounded continuous functions on the closed
  strip `|Im z| ≤ δ`, holomorphic inside, `1`-periodic and real on `ℝ`, with the sup norm.
* `lyapunov_conj` — conjugate cocycles have the same Lyapunov exponent (proved).
* `schr_coeff_symm` — for Schrödinger cocycles, `q₂(x + α) = -q₃(x)` (proved).
* `coeffs_riemann` — in Riemann-sphere coordinates `u = a/c`, `s = b/d`:
  `q₂ = 1/(u - s)` and `q₃ = -us/(u - s)` (proved).  (The paper writes `q₃ = us/(u - s)`;
  with its own definition `q₃ = -ba` the sign is as here.)
* `rotation_L_zero` — a cocycle of rotations `x ↦ R_{2πφ(x)}`, `φ` real-analytic, has
  `L(α, R_ε) = 0` for irrational `α` and small `ε` (proved from Weyl's theorem and Cauchy).
* `cod1` — **Theorem `cod1`**: `v ↦ L_{δ,j}(α, A^{(v)})` is a submersion near any `v_*` with
  `ω(α, A^{(v_*)}) = j > 0`.
* `cod_of_cod1` — **Theorem `cod`** from `cod1` (the theorem itself, `cod`, is in `Cod1.lean`): the critical set is contained in a countable union of
  codimension-one analytic submanifolds of `C^ω_δ(ℝ/ℤ, ℝ) × ℝ`.
-/
import AvilaGlobal.Stratified

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

variable [hH : Hypotheses]
include hH

/-! ### The Banach space `C^ω_δ(ℝ/ℤ, ℝ)` -/

omit hH in
/-- The closed strip `|Im z| ≤ δ`. -/
def cstrip (δ : ℝ) : Set ℂ := {z | |z.im| ≤ δ}

omit hH in
open Classical in
/-- Extension by `0` of a function on the closed strip. -/
def extend {δ : ℝ} (f : BoundedContinuousFunction (cstrip δ) ℂ) (z : ℂ) : ℂ :=
  if h : z ∈ cstrip δ then f ⟨z, h⟩ else 0

lemma extend_add {δ : ℝ} (f g : BoundedContinuousFunction (cstrip δ) ℂ) :
    extend (f + g) = extend f + extend g := by
  funext z; by_cases h : z ∈ cstrip δ <;> simp [extend, h]

lemma extend_smul {δ : ℝ} (c : ℝ) (f : BoundedContinuousFunction (cstrip δ) ℂ) :
    extend (c • f) = fun z => (c : ℂ) * extend f z := by
  funext z; by_cases h : z ∈ cstrip δ <;> simp [extend, h, Complex.real_smul]

lemma extend_zero {δ : ℝ} : extend (0 : BoundedContinuousFunction (cstrip δ) ℂ) = 0 := by
  funext z; by_cases h : z ∈ cstrip δ <;> simp [extend, h]

omit hH in
/-- `C^ω_δ(ℝ/ℤ, ℝ)` as a closed real subspace of the bounded continuous functions on the closed
strip. -/
def PotSpace (δ : ℝ) : Submodule ℝ (BoundedContinuousFunction (cstrip δ) ℂ) where
  carrier := {f | DifferentiableOn ℂ (extend f) (strip δ) ∧ (∀ z, extend f (z + 1) = extend f z) ∧
    ∀ x : ℝ, (extend f x).im = 0}
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [extend_add]; exact hf1.add hg1
    · intro z; rw [extend_add]; simp [hf2, hg2]
    · intro x; rw [extend_add]; simp [hf3, hg3]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [extend_zero]
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [extend_smul]; exact hf1.const_mul _
    · intro z; rw [extend_smul]; simp [hf2]
    · intro x; rw [extend_smul]; simp [hf3]

omit hH in
/-- The space `C^ω_δ(ℝ/ℤ, ℝ)`. -/
abbrev Pot (δ : ℝ) := ↥(PotSpace δ)

omit hH in
/-- A potential in `C^ω_δ(ℝ/ℤ, ℝ)`, as a function on `ℂ`. -/
def Pot.toFun {δ : ℝ} (v : Pot δ) : ℂ → ℂ := extend v.1

theorem Pot.isRealAnalyticPotential {δ : ℝ} (hδ : 0 < δ) (v : Pot δ) :
    IsRealAnalyticPotential δ v.toFun :=
  ⟨hδ, v.2.1, v.2.2.1, v.2.2.2⟩

omit hH in
/-- A codimension-one analytic submanifold of a real normed space `X`: near each of its
points it is the zero set of a real-analytic function with nonvanishing derivative. -/
def IsAnalyticHypersurface {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (S : Set X) :
    Prop :=
  ∀ p ∈ S, ∃ W ∈ 𝓝 p, ∃ F : X → ℝ, AnalyticOnNhd ℝ F W ∧ (∀ q ∈ W, fderiv ℝ F q ≠ 0) ∧
    S ∩ W = {q ∈ W | F q = 0}

/-! ### Conjugacy invariance and the rotation lemma -/

/-- A continuous `1`-periodic function is bounded. -/
lemma bound_of_periodic {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    (hp : Function.Periodic f 1) : ∃ K, ∀ x, ‖f x‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨K, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]; exact hK y (Ico_subset_Icc_self hy)

/-- Conjugate cocycles have the same Lyapunov exponent: if `B` is continuous, `1`-periodic,
with `det B = 1`, then `L(α, B(·+α) A B⁻¹) = L(α, A)`. -/
theorem lyapunov_conj {α : ℝ} {A B : ℝ → M2} (hA : IsSLCocycle A) (hBc : Continuous B)
    (hBp : Function.Periodic B 1) (hBdet : ∀ x, (B x).det = 1) :
    lyapunov α (fun x => B (x + α) * A x * (B x)⁻¹) = lyapunov α A := by
  have hu : ∀ x, IsUnit (B x).det := fun x => by rw [hBdet]; exact isUnit_one
  have hBi : Continuous fun x => (B x)⁻¹ := by
    have : (fun x => (B x)⁻¹) = fun x => (B x).adjugate := funext fun x => by
      rw [Matrix.inv_def, hBdet]; simp
    rw [this]; exact hBc.matrix_adjugate
  set C : ℝ → M2 := fun x => B (x + α) * A x * (B x)⁻¹ with hCdef
  have hC : IsSLCocycle C := by
    refine ⟨((hBc.comp (continuous_id.add continuous_const)).mul hA.continuous).mul hBi, ?_, ?_⟩
    · intro x
      simp only [hCdef]
      rw [add_right_comm x 1 α, hBp (x + α), hA.periodic x, hBp x]
    · intro x
      simp [hCdef, Matrix.det_mul, Matrix.det_nonsing_inv, hBdet, hA.det_eq_one]
  have hiter : ∀ n x, iter α C n x = B (x + n * α) * iter α A n x * (B x)⁻¹ := by
    intro n x
    induction n with
    | zero => simp [iter, Matrix.mul_nonsing_inv _ (hu x)]
    | succ n ih =>
      rw [iter, iter, ih]
      have e : x + ((n + 1 : ℕ) : ℝ) * α = x + n * α + α := by push_cast; ring
      rw [e]
      simp only [hCdef, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((B (x + n * α))⁻¹), Matrix.nonsing_inv_mul _ (hu _), Matrix.one_mul]
  obtain ⟨K1, hK1⟩ := bound_of_periodic hBc hBp
  obtain ⟨K2, hK2⟩ := bound_of_periodic hBi (fun x => by simp only [hBp x])
  set K : ℝ := max (max K1 K2) 1 with hK
  have hK1' : ∀ x, ‖B x‖ ≤ K := fun x => (hK1 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hK2' : ∀ x, ‖(B x)⁻¹‖ ≤ K := fun x =>
    (hK2 x).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hKone : 1 ≤ K := le_max_right _ _
  have hKpos : 0 < K := by linarith
  have norm3 : ∀ M1 M2' M3 : M2, ‖M1‖ ≤ K → ‖M3‖ ≤ K → ‖M1 * M2' * M3‖ ≤ K ^ 2 * ‖M2'‖ := by
    intro M1 M2' M3 h1 h3
    calc ‖M1 * M2' * M3‖ ≤ ‖M1‖ * ‖M2'‖ * ‖M3‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ K * ‖M2'‖ * K := by gcongr
      _ = K ^ 2 * ‖M2'‖ := by ring
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKone
  have hpt : ∀ n x, |Real.log ‖iter α C n x‖ - Real.log ‖iter α A n x‖| ≤ 2 * Real.log K := by
    intro n x
    have ha := hC.one_le_norm_iter (α := α) n x
    have hb := hA.one_le_norm_iter (α := α) n x
    have h1 : ‖iter α C n x‖ ≤ K ^ 2 * ‖iter α A n x‖ := by
      rw [hiter]; exact norm3 _ _ _ (hK1' _) (hK2' _)
    have h2 : ‖iter α A n x‖ ≤ K ^ 2 * ‖iter α C n x‖ := by
      have e : iter α A n x = (B (x + n * α))⁻¹ * iter α C n x * B x := by
        rw [hiter]
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu x), Matrix.mul_one]
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _), Matrix.one_mul]
      rw [e]; exact norm3 _ _ _ (hK2' _) (hK1' _)
    have hlog2 : Real.log (K ^ 2) = 2 * Real.log K := by
      rw [Real.log_pow]; norm_num
    have l1 : Real.log ‖iter α C n x‖ ≤ 2 * Real.log K + Real.log ‖iter α A n x‖ := by
      rw [← hlog2, ← Real.log_mul (pow_pos hKpos 2).ne' (zero_lt_one.trans_le hb).ne']
      exact Real.log_le_log (by linarith) h1
    have l2 : Real.log ‖iter α A n x‖ ≤ 2 * Real.log K + Real.log ‖iter α C n x‖ := by
      rw [← hlog2, ← Real.log_mul (pow_pos hKpos 2).ne' (zero_lt_one.trans_le ha).ne']
      exact Real.log_le_log (by linarith) h2
    rw [abs_le]; constructor <;> linarith
  have hseq : ∀ n, |lyapSeq α C n - lyapSeq α A n| ≤ 2 * Real.log K := by
    intro n
    have hi := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
      ((hC.continuous_log_norm_iter (α := α) n).intervalIntegrable 0 1)
      ((hA.continuous_log_norm_iter (α := α) n).intervalIntegrable 0 1)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := 2 * Real.log K)
      (f := fun x => Real.log ‖iter α C n x‖ - Real.log ‖iter α A n x‖)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hpt n x)
    have e : lyapSeq α C n - lyapSeq α A n =
        ∫ x in (0 : ℝ)..1, (Real.log ‖iter α C n x‖ - Real.log ‖iter α A n x‖) := hi.symm
    rw [e]
    simpa [Real.norm_eq_abs] using hb
  have hdiff : Tendsto (fun n : ℕ => (lyapSeq α C n - lyapSeq α A n) / n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 2 * Real.log K * (1 / (n : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * Real.log K)
      rwa [mul_zero] at h
    refine squeeze_zero_norm (fun n => ?_) hlim
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hseq n) (by positivity)
  have h2 : Tendsto (fun n : ℕ => lyapSeq α C n / n) atTop (𝓝 (lyapunov α A)) := by
    have h := (hA.tendsto_lyapunov (α := α)).add hdiff
    rw [add_zero] at h
    refine Tendsto.congr (fun n => ?_) h
    ring
  exact tendsto_nhds_unique (hC.tendsto_lyapunov (α := α)) h2

omit hH in
/-- The rotation matrix `R_θ` (for complex `θ`). -/
def rot (θ : ℂ) : M2 := !![Complex.cos θ, -Complex.sin θ; Complex.sin θ, Complex.cos θ]

lemma rot_mul (a b : ℂ) : rot a * rot b = rot (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Complex.cos_add, Complex.sin_add] <;> ring

lemma rot_zero : rot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

lemma det_rot (θ : ℂ) : (rot θ).det = 1 := by
  simp only [rot, Matrix.det_fin_two_of]
  linear_combination Complex.cos_sq_add_sin_sq θ

lemma continuous_rot : Continuous rot :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [rot] <;> fun_prop

lemma norm_exp_mul_I_le (z : ℂ) : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
  rw [Complex.norm_exp, Complex.mul_I_re]
  exact Real.exp_le_exp.mpr (neg_le_abs _)

lemma norm_exp_neg_mul_I_le (z : ℂ) : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
  rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
  exact Real.exp_le_exp.mpr (le_abs_self _)

lemma norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h : ‖(2 : ℂ) * Complex.cos z‖ ≤ 2 * Real.exp |z.im| := by
    rw [Complex.two_cos]
    linarith [norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I)), norm_exp_mul_I_le z,
      norm_exp_neg_mul_I_le z]
  rw [norm_mul] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at h
  linarith

lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h : ‖(2 : ℂ) * Complex.sin z‖ ≤ 2 * Real.exp |z.im| := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
    linarith [norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I)), norm_exp_mul_I_le z,
      norm_exp_neg_mul_I_le z]
  rw [norm_mul] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at h
  linarith

/-- Entrywise bound for the `ℓ^∞` operator norm of a `2 × 2` matrix. -/
lemma norm_M2_le (M : M2) {K : ℝ} (hK : 0 ≤ K) (h : ∀ i j, ‖M i j‖ ≤ K) : ‖M‖ ≤ 2 * K := by
  have hrow : ∀ i, ‖M i 0‖ + ‖M i 1‖ ≤ 2 * K := fun i => by linarith [h i 0, h i 1]
  rw [linfty_opNorm_def]
  have : ((Finset.univ : Finset (Fin 2)).sup fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) ≤
      ⟨2 * K, by positivity⟩ := by
    refine Finset.sup_le fun i _ => ?_
    refine NNReal.coe_le_coe.1 ?_
    change _ ≤ 2 * K
    simpa [Fin.sum_univ_two] using hrow i
  exact_mod_cast this

lemma norm_rot_le (θ : ℂ) : ‖rot θ‖ ≤ 2 * Real.exp |θ.im| := by
  refine norm_M2_le _ (Real.exp_pos _).le fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rot, norm_cos_le_exp, norm_sin_le_exp]

/-- **End of §4**: if `φ` is a real-analytic `1`-periodic function and `α` is irrational, the
cocycle of rotations `x ↦ R_{2πφ(x)}` has `L(α, R_ε) = 0` for `|ε| < δ`. -/
theorem rotation_L_zero {δ : ℝ} {φ : ℂ → ℂ} (hφ : IsRealAnalyticPotential δ φ) {α : ℝ}
    (hα : Irrational α) {ε : ℝ} (hε : |ε| < δ) :
    L α (fun z => rot (2 * Real.pi * φ z)) ε = 0 := by
  have hδ := hφ.pos
  set f : ℝ → ℂ := fun y => φ (y + ε * I) with hf
  have hmem : ∀ y : ℝ, (y : ℂ) + ε * I ∈ strip δ := mem_strip_shift hε
  have hpath : Continuous fun y : ℝ => (y : ℂ) + ε * I := by fun_prop
  have hfc : Continuous f := hφ.holo.continuousOn.comp_continuous hpath hmem
  have hfp : Function.Periodic f 1 := fun y => by
    simp only [hf]; push_cast; rw [add_right_comm, hφ.periodic]
  -- the cocycle is a continuous `SL(2,ℂ)` cocycle
  have hS : IsSLCocycle (shift (fun z => rot (2 * Real.pi * φ z)) ε) := by
    refine ⟨?_, ?_, ?_⟩
    · show Continuous fun x => rot (2 * Real.pi * f x)
      exact continuous_rot.comp (continuous_const.mul hfc)
    · intro x
      show rot (2 * Real.pi * f (x + 1)) = rot (2 * Real.pi * f x)
      rw [hfp x]
    · intro x; exact det_rot _
  -- iterates
  have hiter : ∀ n x, iter α (shift (fun z => rot (2 * Real.pi * φ z)) ε) n x =
      rot (2 * Real.pi * ∑ k ∈ Finset.range n, f (x + k * α)) := by
    intro n x
    induction n with
    | zero => simp [iter, rot_zero]
    | succ n ih =>
      rw [iter, ih, Finset.sum_range_succ]
      show rot (2 * Real.pi * f (x + n * α)) * _ = _
      rw [rot_mul]
      congr 1
      ring
  -- `Im ∫₀¹ f = 0` (Cauchy on a rectangle, periodicity, reality on `ℝ`)
  have hint : (∫ y in (0 : ℝ)..1, f y).im = 0 := by
    have hw_re : (1 + ε * I : ℂ).re = 1 := by simp
    have hw_im : (1 + ε * I : ℂ).im = ε := by simp
    have H : DifferentiableOn ℂ φ (Set.uIcc (0 : ℂ).re (1 + ε * I : ℂ).re ×ℂ
        Set.uIcc (0 : ℂ).im (1 + ε * I : ℂ).im) := by
      refine hφ.holo.mono fun z hz => ?_
      rw [Complex.mem_reProdIm] at hz
      have h2 := hz.2
      rw [Complex.zero_im, hw_im, Set.mem_uIcc] at h2
      show |z.im| < δ
      rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hε).1], by linarith [(abs_lt.mp hε).2]⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ 0 (1 + ε * I) H
    rw [Complex.zero_re, Complex.zero_im, hw_re, hw_im] at h
    have hvert : (∫ y in (0 : ℝ)..ε, φ (((1 : ℝ) : ℂ) + y * I)) =
        ∫ y in (0 : ℝ)..ε, φ (((0 : ℝ) : ℂ) + y * I) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_add]
      rw [add_comm]; exact hφ.periodic _
    have hhor : (∫ x in (0 : ℝ)..1, φ (x + ((0 : ℝ) : ℂ) * I)) = ∫ x in (0 : ℝ)..1, φ x := by
      simp
    rw [hvert, hhor, add_sub_cancel_right, sub_eq_zero] at h
    have hreal : (∫ x in (0 : ℝ)..1, φ x) = ∫ x in (0 : ℝ)..1, ((φ x).re : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      apply Complex.ext <;> simp [hφ.real x]
    change (∫ y in (0 : ℝ)..1, φ (y + ε * I)).im = 0
    rw [← h, hreal, intervalIntegral.integral_ofReal, Complex.ofReal_im]
  -- conclusion
  have hL : L α (fun z => rot (2 * Real.pi * φ z)) ε =
      lyapunov α (shift (fun z => rot (2 * Real.pi * φ z)) ε) := rfl
  rw [hL]
  refine le_antisymm ?_ hS.lyapunov_nonneg
  refine le_of_forall_pos_le_add fun η hη => ?_
  rw [zero_add]
  have hη' : 0 < η / (4 * Real.pi) := by positivity
  obtain ⟨n₀, hn₀⟩ := weyl_uniform hα hfc hfp hη'
  set n : ℕ := max n₀ (⌈2 * Real.log 2 / η⌉₊ + 1) with hn
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnlarge : 2 * Real.log 2 ≤ n * η := by
    have h1 : 2 * Real.log 2 / η ≤ (⌈2 * Real.log 2 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * Real.log 2 / η⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (Nat.le_succ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hη] at h1
    nlinarith
  have hpt : ∀ x, Real.log ‖iter α (shift (fun z => rot (2 * Real.pi * φ z)) ε) n x‖ ≤
      Real.log 2 + n * η / 2 := by
    intro x
    set S := ∑ k ∈ Finset.range n, f (x + k * α) with hSdef
    have hW := hn₀ n (le_max_left _ _) x
    have hSb : (n : ℂ) * birk α f n x = S := by
      rw [birk, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn0), one_mul]
    have hSim : S.im = n * (birk α f n x).im := by
      rw [← hSb]; simp [Complex.mul_im]
    have hbim : |(birk α f n x).im| ≤ η / (4 * Real.pi) := by
      have : (birk α f n x).im = (birk α f n x - ∫ y in (0 : ℝ)..1, f y).im := by
        rw [Complex.sub_im, hint, sub_zero]
      rw [this]
      exact (Complex.abs_im_le_norm _).trans hW
    have hSabs : |S.im| ≤ n * (η / (4 * Real.pi)) := by
      rw [hSim, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left hbim hnpos.le
    have hθ : |(2 * (Real.pi : ℂ) * S).im| = 2 * Real.pi * |S.im| := by
      have h : (2 * (Real.pi : ℂ) * S).im = 2 * Real.pi * S.im := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [h, abs_mul, abs_of_pos (by positivity)]
    have hnorm := norm_rot_le (2 * Real.pi * S)
    rw [hθ] at hnorm
    have hc : 2 * Real.pi * |S.im| ≤ n * η / 2 := by
      have e : 2 * Real.pi * (n * (η / (4 * Real.pi))) = n * η / 2 := by
        rw [show (2 : ℝ) * Real.pi * (n * (η / (4 * Real.pi))) =
          n * η / 2 * (Real.pi / Real.pi) by ring, div_self Real.pi_ne_zero, mul_one]
      calc 2 * Real.pi * |S.im| ≤ 2 * Real.pi * (n * (η / (4 * Real.pi))) :=
            mul_le_mul_of_nonneg_left hSabs (by positivity)
        _ = n * η / 2 := e
    have hone : 1 ≤ ‖rot (2 * Real.pi * S)‖ := by
      have := hS.one_le_norm_iter (α := α) n x
      rwa [hiter] at this
    rw [hiter]
    calc Real.log ‖rot (2 * Real.pi * S)‖ ≤ Real.log (2 * Real.exp (2 * Real.pi * |S.im|)) :=
          Real.log_le_log (by linarith) hnorm
      _ = Real.log 2 + 2 * Real.pi * |S.im| := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log 2 + n * η / 2 := by linarith
  have hseq : lyapSeq α (shift (fun z => rot (2 * Real.pi * φ z)) ε) n ≤
      Real.log 2 + n * η / 2 := by
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (zero_le_one : (0 : ℝ) ≤ 1)
      ((hS.continuous_log_norm_iter (α := α) n).intervalIntegrable 0 1)
      (g := fun _ => Real.log 2 + n * η / 2)
      (continuous_const.intervalIntegrable 0 1) (fun x _ => hpt x)
    simpa [lyapSeq] using h
  calc lyapunov α (shift (fun z => rot (2 * Real.pi * φ z)) ε)
      ≤ lyapSeq α (shift (fun z => rot (2 * Real.pi * φ z)) ε) n / n := hS.lyapunov_le n hn0
    _ ≤ η := by
        rw [div_le_iff₀ hnpos]
        nlinarith

/-! ### Algebra of the derivative coefficients -/

/-- For a Schrödinger cocycle `A = [[v, -1], [1, 0]]`, if `B(x+α)⁻¹ A(x) B(x)` is diagonal (with
`B ∈ SL(2,ℂ)`), then `q₂(x + α) = -q₃(x)`. -/
theorem schr_coeff_symm {v : ℂ} {B B' : M2} (hB : B.det = 1) (hB' : B'.det = 1)
    (hdiag : (B'⁻¹ * !![v, -1; 1, 0] * B) 0 1 = 0 ∧ (B'⁻¹ * !![v, -1; 1, 0] * B) 1 0 = 0) :
    derivCoeffs B' 1 = -derivCoeffs B 2 := by
  set D := B'⁻¹ * !![v, -1; 1, 0] * B with hDdef
  have hu : IsUnit B'.det := by rw [hB']; exact isUnit_one
  have hD : B' * D = !![v, -1; 1, 0] * B := by
    rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hdetD : D.det = 1 := by
    rw [hDdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hB', hB]
    simp [Matrix.det_fin_two]
  rw [Matrix.det_fin_two, hdiag.1, hdiag.2] at hdetD
  have h10 := congrFun (congrFun hD 1) 0
  have h11 := congrFun (congrFun hD 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hdiag.1, hdiag.2] at h10 h11
  simp only [derivCoeffs, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.cons_val_zero, neg_neg, Matrix.tail_cons]
  linear_combination (B 0 1) * h10 + (B' 1 0 * D 0 0) * h11 - (B' 1 0 * B' 1 1) * hdetD

/-- In Riemann-sphere coordinates `u = a/c`, `s = b/d` of the columns of `B ∈ SL(2,ℂ)`:
`q₂ = 1/(u - s)` and `q₃ = -us/(u - s)`. -/
theorem coeffs_riemann {B : M2} (hB : B.det = 1) (hc : B 1 0 ≠ 0) (hd : B 1 1 ≠ 0) :
    derivCoeffs B 1 = 1 / (B 0 0 / B 1 0 - B 0 1 / B 1 1) ∧
      derivCoeffs B 2 = -(B 0 0 / B 1 0 * (B 0 1 / B 1 1)) / (B 0 0 / B 1 0 - B 0 1 / B 1 1) := by
  rw [Matrix.det_fin_two] at hB
  have e : B 0 0 / B 1 0 - B 0 1 / B 1 1 = 1 / (B 1 0 * B 1 1) := by
    field_simp; linear_combination hB
  rw [e]
  change B 1 0 * B 1 1 = _ ∧ -(B 0 1 * B 0 0) = _
  constructor
  · rw [one_div_one_div]
  · field_simp

/-! ### Helpers for Theorem `cod` -/

lemma strip_sub_cstrip {δ : ℝ} : strip δ ⊆ cstrip δ := fun z hz => by
  show |z.im| ≤ δ; exact le_of_lt hz

lemma continuousOn_extend {δ : ℝ} (f : BoundedContinuousFunction (cstrip δ) ℂ) :
    ContinuousOn (extend f) (cstrip δ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : cstrip δ => extend f x)
  have : (fun x : cstrip δ => extend f x) = f := by
    funext ⟨z, hz⟩; simp [extend, hz]
  rw [this]; exact f.continuous

omit hH in
/-- The constant potential `1`. -/
def Pot.one (δ : ℝ) : Pot δ :=
  ⟨BoundedContinuousFunction.const (cstrip δ) (1 : ℂ), by
    change DifferentiableOn ℂ (extend (BoundedContinuousFunction.const (cstrip δ) (1 : ℂ)))
        (strip δ) ∧
      (∀ z, extend (BoundedContinuousFunction.const (cstrip δ) (1 : ℂ)) (z + 1) =
        extend (BoundedContinuousFunction.const (cstrip δ) (1 : ℂ)) z) ∧
      ∀ x : ℝ, (extend (BoundedContinuousFunction.const (cstrip δ) (1 : ℂ)) x).im = 0
    refine ⟨?_, ?_, ?_⟩
    · refine (differentiableOn_const (1 : ℂ)).congr fun z hz => ?_
      have : z ∈ cstrip δ := strip_sub_cstrip hz
      simp [extend, this]
    · intro z
      have h : (z + 1 ∈ cstrip δ) ↔ z ∈ cstrip δ := by simp [cstrip]
      by_cases hz : z ∈ cstrip δ
      · simp [extend, hz, h.mpr hz]
      · simp [extend, hz, mt h.mp hz]
    · intro x
      by_cases hx : (x : ℂ) ∈ cstrip δ <;> simp [extend, hx]⟩

omit hH in
/-- The continuous linear map `(v, E) ↦ E - v` from `C^ω_δ(ℝ/ℤ, ℝ) × ℝ` to `C^ω_δ(ℝ/ℤ, ℝ)`. -/
def potShift (δ : ℝ) : Pot δ × ℝ →L[ℝ] Pot δ :=
  (ContinuousLinearMap.snd ℝ (Pot δ) ℝ).smulRight (Pot.one δ) - ContinuousLinearMap.fst ℝ (Pot δ) ℝ

lemma potShift_apply {δ : ℝ} (v : Pot δ) (E : ℝ) : potShift δ (v, E) = E • Pot.one δ - v := rfl

lemma potShift_toFun {δ : ℝ} (v : Pot δ) (E : ℝ) {z : ℂ} (hz : z ∈ strip δ) :
    (potShift δ (v, E)).toFun z = eShift E v.toFun z := by
  rw [potShift_apply]
  have hz' := strip_sub_cstrip hz
  simp [Pot.toFun, eShift, extend, hz', Pot.one, Complex.real_smul]

lemma schr_eqOn_potShift {δ : ℝ} (p : Pot δ × ℝ) :
    EqOn (schr (eShift p.2 p.1.toFun)) (schr (potShift δ p).toFun) (strip δ) := by
  intro z hz
  show !![eShift p.2 p.1.toFun z, -1; 1, 0] = !![(potShift δ (p.1, p.2)).toFun z, -1; 1, 0]
  rw [potShift_toFun p.1 p.2 hz]

/-- Schwarz reflection: a potential in `C^ω_δ(ℝ/ℤ, ℝ)` satisfies `v(z̄) = conj v(z)`. -/
lemma Pot.conj_symm {δ : ℝ} (hδ : 0 < δ) (v : Pot δ) (z : ℂ) :
    v.toFun (conj z) = conj (v.toFun z) := by
  have hv := v.isRealAnalyticPotential hδ
  have hcs : ∀ w : ℂ, conj w ∈ cstrip δ ↔ w ∈ cstrip δ := fun w => by simp [cstrip]
  have hss : ∀ w : ℂ, conj w ∈ strip δ ↔ w ∈ strip δ := fun w => by simp [strip]
  have hopen : EqOn v.toFun (conj ∘ v.toFun ∘ conj) (strip δ) := by
    have hf : AnalyticOnNhd ℂ v.toFun (strip δ) := hv.holo.analyticOnNhd (isOpen_strip δ)
    have hg : AnalyticOnNhd ℂ (conj ∘ v.toFun ∘ conj) (strip δ) := by
      refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) (isOpen_strip δ)
      have hw' : conj w ∈ strip δ := (hss w).mpr hw
      have h := (hv.holo.differentiableAt ((isOpen_strip δ).mem_nhds hw')).conj_conj
      rw [Complex.conj_conj] at h
      exact h.differentiableWithinAt
    have hpc : IsPreconnected (strip δ) := by
      have e : strip δ = Complex.imLm ⁻¹' (Ioo (-δ) δ) := by
        ext w; simp [strip, abs_lt]
      rw [e]; exact ((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected
    have h0 : (0 : ℂ) ∈ strip δ := by show |(0 : ℂ).im| < δ; simpa using hδ
    refine hf.eqOn_of_preconnected_of_frequently_eq hg hpc h0 ?_
    have hu : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa using this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact one_div_ne_zero (by positivity)
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    simp only [Function.comp_apply, Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.mpr (hv.real _)).symm
  have hclosed : EqOn v.toFun (conj ∘ v.toFun ∘ conj) (cstrip δ) := by
    refine hopen.of_subset_closure (continuousOn_extend v.1) ?_ strip_sub_cstrip ?_
    · exact Complex.continuous_conj.comp_continuousOn ((continuousOn_extend v.1).comp
        Complex.continuous_conj.continuousOn fun w hw => (hcs w).mpr hw)
    · have e1 : strip δ = (univ : Set ℝ) ×ℂ Ioo (-δ) δ := by
        ext w; simp [strip, Complex.mem_reProdIm, abs_lt]
      rw [e1, Complex.closure_reProdIm, closure_univ, closure_Ioo (by linarith : -δ ≠ δ)]
      intro w hw
      rw [Complex.mem_reProdIm]
      exact ⟨mem_univ _, abs_le.mp hw⟩
  by_cases hz : z ∈ cstrip δ
  · have := hclosed ((hcs z).mpr hz)
    simp only [Function.comp_apply, Complex.conj_conj] at this
    exact this
  · have hz' : conj z ∉ cstrip δ := fun h => hz ((hcs z).mp h)
    simp [Pot.toFun, extend, hz, hz']

lemma schr_realSymm {δ : ℝ} (hδ : 0 < δ) (v : Pot δ) (E : ℝ) :
    IsRealSymmetric (schr (eShift E v.toFun)) := by
  intro z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schr, eShift, Pot.conj_symm hδ v z]

section congr

variable {δ α : ℝ} {A A' : ℂ → M2}

lemma shift_congr (h : EqOn A A' (strip δ)) {ε : ℝ} (hε : |ε| < δ) : shift A ε = shift A' ε :=
  funext fun x => h (mem_strip_shift hε x)

lemma L_congr (h : EqOn A A' (strip δ)) {ε : ℝ} (hε : |ε| < δ) : L α A ε = L α A' ε := by
  unfold L; rw [shift_congr h hε]

lemma accel_congr (h : EqOn A A' (strip δ)) (hδ : 0 < δ) (α : ℝ) : accel α A = accel α A' := by
  have hev : (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => (L α A' ε - L α A' 0) / (2 * Real.pi * ε)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have h1 : |ε| < δ := abs_lt.mpr ⟨by linarith [hε.1], hε.2⟩
    have h0 : |(0 : ℝ)| < δ := by rw [abs_zero]; exact hδ
    rw [L_congr h h1, L_congr h h0]
  simp only [accel, limUnder]
  rw [Filter.map_congr hev]

lemma mapsTo_cshift' {δ ε : ℝ} :
    MapsTo (fun z : ℂ => z + ε * I) (strip (δ - |ε|)) (strip δ) := by
  intro z hz
  simp only [strip, Set.mem_setOf_eq, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
    I_re, mul_zero, add_zero] at hz ⊢
  calc |z.im + ε| ≤ |z.im| + |ε| := abs_add_le _ _
    _ < δ := by linarith

lemma cshift_eqOn (h : EqOn A A' (strip δ)) (t : ℝ) :
    EqOn (cshift A t) (cshift A' t) (strip (δ - |t|)) := fun _ hz => h (mapsTo_cshift' hz)

lemma uh_congr (h : EqOn A A' (strip δ)) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    UH α (cshift A t) ↔ UH α (cshift A' t) := by
  have ht' : |t| < δ := by rw [abs_of_pos ht.1]; exact ht.2
  have : shift (cshift A t) 0 = shift (cshift A' t) 0 :=
    shift_congr (cshift_eqOn h t) (by rw [abs_zero]; linarith)
  unfold UH
  rw [this]

lemma omega_congr (h : EqOn A A' (strip δ)) {j : ℤ} :
    OmegaSet δ j α A ↔ OmegaSet δ j α A' := by
  have key : ∀ t ∈ Ioo 0 δ, (UH α (cshift A t) ↔ UH α (cshift A' t)) ∧
      accel α (cshift A t) = accel α (cshift A' t) := by
    intro t ht
    have ht' : |t| < δ := by rw [abs_of_pos ht.1]; exact ht.2
    have hc := cshift_eqOn h t
    refine ⟨?_, accel_congr hc (by linarith) α⟩
    have : shift (cshift A t) 0 = shift (cshift A' t) 0 :=
      shift_congr hc (by rw [abs_zero]; linarith)
    simp only [UH, this]
  constructor
  · rintro ⟨t, ht, hU, hω⟩
    refine ⟨t, ht, (key t ht).1.mp hU, ?_⟩
    rw [← (key t ht).2]; exact hω
  · rintro ⟨t, ht, hU, hω⟩
    refine ⟨t, ht, (key t ht).1.mpr hU, ?_⟩
    rw [(key t ht).2]; exact hω

lemma Ldj_congr (hA : IsAnalyticCocycle δ A) (h : EqOn A A' (strip δ)) {j : ℤ} :
    Ldj δ j α A' = Ldj δ j α A := by
  by_cases hO : OmegaSet δ j α A'
  · obtain ⟨h1, h2, h3⟩ := Exists.choose_spec hO
    have ht' : |hO.choose| < δ := by rw [abs_of_pos h1.1]; exact h1.2
    have hcs := cshift_eqOn h hO.choose
    have hU : UH α (cshift A hO.choose) := (uh_congr h h1).mpr h2
    have hw : accel α (cshift A hO.choose) = j := by
      rw [accel_congr hcs (by linarith) α]; exact h3
    rw [Ldj_eq hA h1 hU hw]
    simp only [Ldj, dif_pos hO]
    rw [L_congr h ht']
  · have hO' : ¬ OmegaSet δ j α A := fun H => hO ((omega_congr h).mp H)
    simp only [Ldj, dif_neg hO, dif_neg hO']

end congr

omit hH in
/-- `g_j(v, E) = L_{δ,j}(α, A^{(E - v)})`. -/
def codG (δ α : ℝ) (j : ℤ) : Pot δ × ℝ → ℝ := fun p => Ldj δ j α (schr (eShift p.2 p.1.toFun))

omit hH in
/-- The open set where `g_j` is analytic with nonvanishing derivative. -/
def codGood (δ α : ℝ) (j : ℤ) : Set (Pot δ × ℝ) :=
  {p | ∃ W, IsOpen W ∧ p ∈ W ∧ AnalyticOnNhd ℝ (codG δ α j) W ∧
    ∀ q ∈ W, fderiv ℝ (codG δ α j) q ≠ 0}

omit hH in
/-- The hypersurface `{g_j = 0}` inside `codGood`. -/
def codS (δ α : ℝ) (j : ℤ) : Set (Pot δ × ℝ) := {p | p ∈ codGood δ α j ∧ codG δ α j p = 0}

lemma mem_codGood {δ α : ℝ} {j : ℤ} {p : Pot δ × ℝ} : p ∈ codGood δ α j ↔
    ∃ W, IsOpen W ∧ p ∈ W ∧ AnalyticOnNhd ℝ (codG δ α j) W ∧
      ∀ q ∈ W, fderiv ℝ (codG δ α j) q ≠ 0 := Iff.rfl

lemma mem_codS {δ α : ℝ} {j : ℤ} {p : Pot δ × ℝ} :
    p ∈ codS δ α j ↔ p ∈ codGood δ α j ∧ codG δ α j p = 0 := Iff.rfl

lemma codGood_open {δ α : ℝ} {j : ℤ} : IsOpen (codGood δ α j) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨W, hW, hpW, h1, h2⟩ := mem_codGood.mp hp
  exact Filter.mem_of_superset (hW.mem_nhds hpW) fun q hq => mem_codGood.mpr ⟨W, hW, hq, h1, h2⟩

lemma codS_hypersurface {δ α : ℝ} (j : ℤ) : IsAnalyticHypersurface (codS δ α j) := by
  intro p hp
  obtain ⟨hpG, -⟩ := mem_codS.mp hp
  refine ⟨codGood δ α j, codGood_open.mem_nhds hpG, codG δ α j, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨W, -, hqW, h1, -⟩ := mem_codGood.mp hq; exact h1 q hqW
  · obtain ⟨W, -, hqW, -, h2⟩ := mem_codGood.mp hq; exact h2 q hqW
  · ext q
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_codS]
    tauto

/-! ### The theorems -/

omit hH in
/-- **Theorem `cod1`** (stated, not proved here; `cod` takes it as a hypothesis).  Let `α` be irrational, `δ > 0`, `j > 0`.  If `v_* ∈ C^ω_δ(ℝ/ℤ, ℝ)` has
`ω(α, A^{(v_*)}) = j`, then `v ↦ L_{δ,j}(α, A^{(v)})` is real-analytic near `v_*` with
nonvanishing derivative at `v_*` (hence a submersion near `v_*`). -/
def Cod1Claim (δ α : ℝ) : Prop :=
  0 < δ → Irrational α → ∀ {j : ℤ}, 0 < j → ∀ {vstar : Pot δ}, accel α (schr vstar.toFun) = j →
    ∃ W ∈ 𝓝 vstar, AnalyticOnNhd ℝ (fun v : Pot δ => Ldj δ j α (schr v.toFun)) W ∧
      fderiv ℝ (fun v : Pot δ => Ldj δ j α (schr v.toFun)) vstar ≠ 0

/-- **Theorem `cod`.**  For irrational `α`, the set of `(v, E) ∈ C^ω_δ(ℝ/ℤ, ℝ) × ℝ` such that `E`
is a critical energy of `H_{α,v}` is contained in a countable union of codimension-one analytic
submanifolds. -/
theorem cod_of_cod1 {δ : ℝ} (hδ : 0 < δ) {α : ℝ} (hα : Irrational α) (hcod1 : Cod1Claim δ α) :
    ∃ S : ℕ → Set (Pot δ × ℝ), (∀ i, IsAnalyticHypersurface (S i)) ∧
      {p : Pot δ × ℝ | IsCriticalEnergy α p.1.toFun p.2} ⊆ ⋃ i, S i := by
  refine ⟨fun i => codS δ α ((i : ℤ) + 1), fun i => codS_hypersurface _, ?_⟩
  rintro ⟨v, E⟩ hcrit
  obtain ⟨hnreg, hL0⟩ := hcrit
  have hnreg' : ¬ IsRegular α (schr (eShift E v.toFun)) := hnreg
  have hL0' : L α (schr (eShift E v.toFun)) 0 = 0 := hL0
  have hA : ∀ p : Pot δ × ℝ, IsAnalyticCocycle δ (schr (eShift p.2 p.1.toFun)) := fun p =>
    (p.1.isRealAnalyticPotential hδ).schr p.2
  have hAa : IsAnalyticCocycle δ (schr (eShift E v.toFun)) := hA (v, E)
  have hsym := schr_realSymm hδ v E
  obtain ⟨-, k, hk⟩ := quantized hAa hα
  have hk0 : k ≠ 0 := by
    intro h0; apply hnreg'
    rw [isRegular_iff_accel_eq_zero hAa hsym hα, hk, h0, Int.cast_zero]
  have hkpos : 0 < k := by
    have h1 := accel_nonneg hAa hsym α
    rw [hk] at h1
    have h2 : (0 : ℤ) ≤ k := by exact_mod_cast h1
    omega
  obtain ⟨-, -, hLd⟩ := pluri_mem hAa hα hk hk0
  have hω : accel α (schr (potShift δ (v, E)).toFun) = k := by
    rw [← accel_congr (schr_eqOn_potShift (v, E)) hδ α]; exact hk
  obtain ⟨W, hW, hWan, hder⟩ := hcod1 hδ hα hkpos hω
  have hgF : codG δ α k = (fun w : Pot δ => Ldj δ k α (schr w.toFun)) ∘ potShift δ := by
    funext p; exact (Ldj_congr (hA p) (schr_eqOn_potShift p)).symm
  set U := interior (potShift δ ⁻¹' W) with hUdef
  have hU : IsOpen U := isOpen_interior
  have hpU : (v, E) ∈ U :=
    mem_interior_iff_mem_nhds.mpr ((potShift δ).continuous.continuousAt.preimage_mem_nhds hW)
  have hgan : AnalyticOnNhd ℝ (codG δ α k) U := by
    intro q hq
    rw [hgF]
    exact (hWan _ (interior_subset (s := potShift δ ⁻¹' W) hq)).comp ((potShift δ).analyticAt q)
  have hfd : fderiv ℝ (codG δ α k) (v, E) =
      (fderiv ℝ (fun w : Pot δ => Ldj δ k α (schr w.toFun)) (potShift δ (v, E))).comp
        (potShift δ) := by
    rw [hgF, fderiv_comp (v, E) ((hWan _ (interior_subset (s := potShift δ ⁻¹' W) hpU)).differentiableAt)
      (potShift δ).differentiableAt, ContinuousLinearMap.fderiv]
  have hpd : fderiv ℝ (codG δ α k) (v, E) ≠ 0 := by
    rw [hfd]
    intro h
    apply hder
    ext w
    have := congrArg (fun M : Pot δ × ℝ →L[ℝ] ℝ => M (-w, 0)) h
    simpa [potShift_apply] using this
  have hcont : ContinuousOn (fderiv ℝ (codG δ α k)) U := hgan.fderiv.continuousOn
  have hV : IsOpen (U ∩ fderiv ℝ (codG δ α k) ⁻¹' {L | 0 < ‖L‖}) :=
    hcont.isOpen_inter_preimage hU
      (isOpen_lt continuous_const (by exact @continuous_norm (Pot δ × ℝ →L[ℝ] ℝ) _))
  refine mem_iUnion.mpr ⟨k.toNat - 1, ?_⟩
  have hkk : (((k.toNat - 1 : ℕ) : ℤ) + 1) = k := by omega
  show (v, E) ∈ codS δ α (((k.toNat - 1 : ℕ) : ℤ) + 1)
  rw [hkk]
  refine mem_codS.mpr ⟨mem_codGood.mpr ⟨_, hV, ⟨hpU, (norm_pos_iff (a := fderiv ℝ (codG δ α k) (v, E))).mpr hpd⟩, hgan.mono inter_subset_left,
    fun q hq => (norm_pos_iff (a := fderiv ℝ (codG δ α k) q)).mp hq.2⟩, ?_⟩
  show Ldj δ k α (schr (eShift E v.toFun)) = 0
  rw [← hLd]; exact hL0'

end AvilaGlobal
