/-
# Coefficient functions of Weyl symbols  (paper §2.2)

A symbol `R ∈ 𝒲_{s,ℓ}` is the difference operator `∑_r a_r(x) U^r` with phase coefficients
`a_r(z) = ∑_q R_{r,q} e(αrq/2 + qz)`.  We prove (no `sorry`):
* weighted Fourier series are analytic and `1`-periodic on the strip `|Im z| < ℓ/2π`, with the
  bound `|a_r(z)| ≤ ∑_q |R_{r,q}| e^{ℓ|q|}`;
* a self-adjoint symbol supported on hopping indices `{-1,0,1}` is, on every fibre, exactly the
  Jacobi operator `a_1(x+nα) U + \overline{a_1(x+(n-1)α)} U^{-1} + a_0(x+nα)` with real `a_0`.
-/
import AnalyticPerturbationsAMO.WeylAlgebra
import AnalyticPerturbationsAMO.SymbolCalculus

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open Complex L2

namespace AMO

/-- `e(z) = exp(2πiz)` for complex `z`. -/
def ec (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * I * z)

lemma ec_ofReal (t : ℝ) : ec t = e t := by
  unfold ec e; congr 1; push_cast; ring

lemma norm_ec (z : ℂ) : ‖ec z‖ = Real.exp (-2 * Real.pi * z.im) := by
  unfold ec
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

lemma ec_add (z w : ℂ) : ec (z + w) = ec z * ec w := by
  unfold ec; rw [← Complex.exp_add]; congr 1; ring

lemma ec_intCast (k : ℤ) : ec k = 1 := by
  unfold ec
  rw [show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-! ### Weighted Fourier series -/

/-- The series `∑_q d_q e(β_q + σ q z)`. -/
def fser (d : ℤ → ℂ) (β : ℤ → ℝ) (σ : ℤ) (z : ℂ) : ℂ := ∑' q, d q * ec (β q + σ * q * z)

variable {d : ℤ → ℂ} {β : ℤ → ℝ} {σ : ℤ} {ℓ : ℝ}

lemma norm_fser_term_le (hσ : |σ| ≤ 1) (q : ℤ) {z : ℂ} (hz : |z.im| ≤ ℓ / (2 * Real.pi)) :
    ‖d q * ec (β q + σ * q * z)‖ ≤ ‖d q‖ * Real.exp (ℓ * |(q : ℝ)|) := by
  rw [norm_mul, norm_ec]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.2
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : (β q + σ * q * z : ℂ).im = σ * q * z.im := by simp
  rw [h1]
  have hσ' : |(σ : ℝ)| ≤ 1 := by exact_mod_cast hσ
  have hle : -2 * Real.pi * (σ * q * z.im) ≤ 2 * Real.pi * (|(q : ℝ)| * |z.im|) := by
    have : |(σ : ℝ) * q * z.im| ≤ |(q : ℝ)| * |z.im| := by
      rw [abs_mul, abs_mul]
      calc |(σ : ℝ)| * |(q : ℝ)| * |z.im| ≤ 1 * |(q : ℝ)| * |z.im| := by gcongr
        _ = _ := by ring
    have := neg_abs_le ((σ : ℝ) * q * z.im)
    nlinarith
  calc -2 * Real.pi * (σ * q * z.im) ≤ 2 * Real.pi * (|(q : ℝ)| * |z.im|) := hle
    _ ≤ 2 * Real.pi * (|(q : ℝ)| * (ℓ / (2 * Real.pi))) := by gcongr
    _ = ℓ * |(q : ℝ)| := by field_simp

/-- The open strip `|Im z| < w` is open. -/
lemma isOpen_strip (w : ℝ) : IsOpen (strip w) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem fser_analytic (hσ : |σ| ≤ 1) (hd : Summable fun q => ‖d q‖ * Real.exp (ℓ * |(q : ℝ)|)) :
    AnalyticOnNhd ℂ (fser d β σ) (strip (ℓ / (2 * Real.pi))) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_strip _)
  refine differentiableOn_tsum_of_summable_norm hd (fun q => ?_) (isOpen_strip _)
    (fun q z hz => norm_fser_term_le hσ q (le_of_lt hz))
  unfold ec
  fun_prop

lemma norm_fser_le (hσ : |σ| ≤ 1) (hd : Summable fun q => ‖d q‖ * Real.exp (ℓ * |(q : ℝ)|))
    {z : ℂ} (hz : |z.im| ≤ ℓ / (2 * Real.pi)) :
    ‖fser d β σ z‖ ≤ ∑' q, ‖d q‖ * Real.exp (ℓ * |(q : ℝ)|) := by
  unfold fser
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact hd.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_fser_term_le hσ q hz)
  · exact (hd.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_fser_term_le hσ q hz)).tsum_le_tsum
      (fun q => norm_fser_term_le hσ q hz) hd

lemma fser_add_one (z : ℂ) : fser d β σ (z + 1) = fser d β σ z := by
  unfold fser
  congr 1
  funext q
  rw [show (β q : ℂ) + σ * q * (z + 1) = (β q + σ * q * z) + ((σ * q : ℤ) : ℂ) by push_cast; ring,
    ec_add, ec_intCast, mul_one]

lemma fser_ofReal (t : ℝ) : fser d β σ t = ∑' q, d q * e (β q + σ * q * t) := by
  unfold fser
  congr 1
  funext q
  rw [← ec_ofReal]
  push_cast
  rfl

/-! ### Coefficient functions of a symbol -/

/-- The phase coefficient `a_r(z) = ∑_q R_{r,q} e(αrq/2 + qz)` of hopping index `r`. -/
def coefFn (α : ℝ) (R : Symbol) (r : ℤ) : ℂ → ℂ :=
  fser (fun q => R (r, q)) (fun q => α * r * q / 2) 1

lemma summable_fiber {s ℓ : ℝ} (hs : 0 ≤ s) {R : Symbol} (hR : WSum s ℓ R) (r : ℤ) :
    Summable fun q : ℤ => ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) := by
  refine ((hR.prod_factor r).mul_left (Real.exp (-(s * |(r : ℝ)|)))).of_nonneg_of_le
    (fun _ => by positivity) (fun q => le_of_eq ?_)
  simp only [wt]
  rw [show ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) =
    Real.exp (-(s * |(r : ℝ)|)) * (‖R (r, q)‖ * Real.exp (s * |(r : ℝ)| + ℓ * |(q : ℝ)|)) by
    rw [Real.exp_add, Real.exp_neg]; field_simp]

lemma coefFn_analytic {s ℓ : ℝ} (hs : 0 ≤ s) {R : Symbol} (hR : WSum s ℓ R) (α : ℝ) (r : ℤ) :
    AnalyticOnNhd ℂ (coefFn α R r) (strip (ℓ / (2 * Real.pi))) :=
  fser_analytic (by norm_num) (summable_fiber hs hR r)

lemma coefFn_add_one (α : ℝ) (R : Symbol) (r : ℤ) (z : ℂ) :
    coefFn α R r (z + 1) = coefFn α R r z := fser_add_one z

lemma coefFn_ofReal (α : ℝ) (R : Symbol) (r : ℤ) (t : ℝ) :
    coefFn α R r t = ∑' q, R (r, q) * e (α * r * q / 2 + q * t) := by
  unfold coefFn
  rw [fser_ofReal]
  congr 1; funext q; congr 2; push_cast; ring

lemma norm_coefFn_le {s ℓ : ℝ} (hs : 0 ≤ s) {R : Symbol} (hR : WSum s ℓ R) (α : ℝ) (r : ℤ)
    {z : ℂ} (hz : |z.im| ≤ ℓ / (2 * Real.pi)) :
    ‖coefFn α R r z‖ ≤ ∑' q : ℤ, ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) :=
  norm_fser_le (by norm_num) (summable_fiber hs hR r) hz

/-- The weight of hopping `r` costs `e^{s|r|}`: `∑_q |R_{r,q}| e^{ℓ|q|} ≤ e^{-s|r|} ‖R‖_{s,ℓ}`. -/
lemma fiber_le_wnorm {s ℓ : ℝ} (hs : 0 ≤ s) {R : Symbol} (hR : WSum s ℓ R) (r : ℤ) :
    ∑' q : ℤ, ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) ≤
      Real.exp (-(s * |(r : ℝ)|)) * wnorm s ℓ R := by
  have hfib : ∑' q : ℤ, ‖R (r, q)‖ * wt s ℓ (r, q) ≤ wnorm s ℓ R := by
    rw [wnorm_eq, hR.tsum_prod' (fun r => hR.prod_factor r)]
    exact hR.prod.le_tsum r (fun _ _ => tsum_nonneg fun _ => mul_nonneg (norm_nonneg _)
      (wt_pos _).le)
  have heq : ∑' q : ℤ, ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) =
      Real.exp (-(s * |(r : ℝ)|)) * ∑' q : ℤ, ‖R (r, q)‖ * wt s ℓ (r, q) := by
    rw [← tsum_mul_left]
    congr 1; funext q
    simp only [wt]
    rw [Real.exp_add, Real.exp_neg]; field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hfib (Real.exp_pos _).le

lemma bdd_coefFn {s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) {R : Symbol} (hR : WSum s ℓ R) (α : ℝ)
    (r : ℤ) (f : ℤ → ℝ) : Bdd (fun n => coefFn α R r (f n : ℝ)) :=
  ⟨_, fun n => norm_coefFn_le hs hR α r (z := (f n : ℝ)) (by simp; positivity)⟩

/-! ### Three-diagonal symbols are Jacobi operators -/

lemma inner_delta_op {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) (u : L2 ℤ) (n : ℤ) :
    op α R x u n = ∑' p : ℤ × ℤ, R p * W α x p.1 p.2 u n := by
  rw [← inner_delta_left, op_apply hR]
  have heval : ⟪delta n, ∑' p : ℤ × ℤ, R p • W α x p.1 p.2 u⟫_ℂ =
      ∑' p : ℤ × ℤ, ⟪delta n, R p • W α x p.1 p.2 u⟫_ℂ :=
    ((summable_op_apply (α := α) hR x u).hasSum.mapL (innerSL ℂ (delta n))).tsum_eq.symm
  rw [heval]
  congr 1
  funext p
  rw [inner_smul_right, inner_delta_left]

/-- On every fibre, a symbol supported on hopping indices `{-1, 0, 1}` acts as
`a_1(x+nα) u_{n+1} + a_{-1}(x+nα) u_{n-1} + a_0(x+nα) u_n`. -/
theorem op_three_diag {s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) {α : ℝ} {R : Symbol}
    (hR : WSum s ℓ R) (hge : HopGE R (-1)) (hle : HopLE R 1) (x : ℝ) :
    op α R x =
      weightedShift (fun n : ℤ => coefFn α R 1 (x + n * α : ℝ)) (Equiv.addRight 1) +
      weightedShift (fun n : ℤ => coefFn α R (-1) (x + n * α : ℝ)) (Equiv.addRight (-1)) +
      weightedShift (fun n : ℤ => coefFn α R 0 (x + n * α : ℝ)) (Equiv.refl ℤ) := by
  have hR1 := hR.symbolSummable hs hℓ
  ext u n
  rw [inner_delta_op hR1]
  simp only [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    weightedShift_apply (bdd_coefFn hs hℓ hR α _ _)]
  -- the double sum over `(r, q)`
  set F : ℤ × ℤ → ℂ := fun p => R p * W α x p.1 p.2 u n
  have hF : Summable F := by
    refine Summable.of_norm (hR1.mul_right ‖u‖ |>.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => ?_))
    simp only [F, norm_mul, W_apply, norm_e, one_mul]
    gcongr
    exact lp.norm_apply_le_norm (by norm_num) u _
  rw [hF.tsum_prod]
  have hzero : ∀ r : ℤ, r ∉ ({1, -1, 0} : Finset ℤ) → ∑' q, F (r, q) = 0 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    have : ∀ q, F (r, q) = 0 := by
      intro q
      simp only [F]
      by_cases h : r < -1
      · rw [hge (r, q) h, zero_mul]
      · rw [hle (r, q) (by omega), zero_mul]
    simp [this]
  rw [tsum_eq_sum (s := {1, -1, 0}) hzero]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have hrow : ∀ r : ℤ, ∑' q, F (r, q) = coefFn α R r (x + n * α : ℝ) * u (n + r) := by
    intro r
    rw [coefFn_ofReal, ← tsum_mul_right]
    congr 1; funext q
    simp only [F, W_apply]
    rw [show α * r * q / 2 + q * (x + n * α) = α * r * q / 2 + q * (x + n * α) from rfl]
    ring
  rw [hrow, hrow, hrow]
  simp only [Equiv.coe_addRight, Equiv.coe_refl, id_eq, add_zero]
  ring_nf

/-- For a self-adjoint symbol, `a_{-1}(x) = \overline{a_1(x - α)}` on the real axis. -/
lemma coefFn_neg_one {α : ℝ} {R : Symbol} (hsa : SymbolSelfAdjoint R) (t : ℝ) :
    coefFn α R (-1) t = conj (coefFn α R 1 (t - α : ℝ)) := by
  rw [coefFn_ofReal, coefFn_ofReal, Complex.conj_tsum]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext q
  simp only [Equiv.neg_apply, map_mul, conj_e]
  have h := hsa (1, q)
  rw [Prod.neg_mk] at h
  rw [h]
  congr 1
  congr 1
  push_cast
  ring

/-- For a self-adjoint symbol, `a_0` is real on the real axis. -/
lemma coefFn_zero_real {α : ℝ} {R : Symbol} (hsa : SymbolSelfAdjoint R) (t : ℝ) :
    conj (coefFn α R 0 t) = coefFn α R 0 t := by
  rw [coefFn_ofReal, Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext q
  simp only [Equiv.neg_apply, map_mul, conj_e]
  have h := hsa (0, q)
  rw [Prod.neg_mk, neg_zero] at h
  rw [h, Complex.conj_conj]
  congr 2
  push_cast
  ring

/-- **Three-diagonal self-adjoint symbols are prepared Jacobi operators.** -/
theorem op_eq_jacobi {s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) {α : ℝ} {R : Symbol}
    (hR : WSum s ℓ R) (hsa : SymbolSelfAdjoint R) (hge : HopGE R (-1)) (hle : HopLE R 1)
    (x : ℝ) : op α R x = jacobi α (coefFn α R 1) (coefFn α R 0) x := by
  rw [op_three_diag hs hℓ hR hge hle x, jacobi]
  congr 2
  apply weightedShift_congr
  · intro n
    rw [coefFn_neg_one hsa]
    congr 3
    ring
  · intro n; rfl

end AMO
