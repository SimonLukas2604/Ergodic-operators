/-
# The comparison family and the rooted-resolvent quadrant balance

Formalization of §3 ("Gap opening for the comparison family", `gap:sec:comparison`) of
S. Becker, *Self-dual perturbations of the critical almost Mathieu operator*,
`spectral_gaps_and_dimension.tex`, lines 2754–3170 and 3225–3240.

* **Comparison constants** (l. 2786–2808): `d = (1+√(1-4b²))/2`, `c = (1-√(1-4b²))/2`
  satisfy `d + c = 1`, `dc = b²`, `d > c ≥ 0`, `d ≥ 1/2`; the Jacobi hopping
  `p_t(z) = d z⁻¹ + 2bt + ct² z = d z⁻¹ (1 + (b/d) t z)²`, and on the unit circle
  `|p_t(z)| = q_t(z) = d + ct² + bt(z + z⁻¹) ≥ (√d - t√c)² > 0`
  (`gap:eq:positive-comparison-hopping`).
* **Rooted-resolvent objects** (l. 3097–3128): `L²(𝒜_α, τ)` is modelled by coefficient arrays
  `u : ℤ × ℤ → ℂ` in the basis `e_{j,k} = W_{j,k}` with root `Ω = W_{0,0} = Id`.  All operators
  are finite band, so they are defined pointwise on *all* arrays.  Left/right multiplication by
  a symbol `h` supported in `{-1,0,1}²` (`Lop`, `Rop`, which agree with the twisted product
  `AMO.tmul` of the Weyl algebra, `W_m W_n = e^{πiα m∧n} W_{m+n}`), `M = (L+R)/2`,
  `D = (L-R)/(2i)`, the diagonal `Q`, the midpoint weight `w`, and the matrix `K`.
* **Lemma `gap:lem:quadrant-balance`** (l. 3130): for irrational `α`,
  `u_{0,0} = 0`, `(L - R)u = 0` imply `Q L u = K u`, proved for an *arbitrary* coefficient
  array on the steps `{-1,0,1}²` (in particular for `C_t`, eq. `gap:eq:comparison-path`).
* The source identity `Q C_t Ω = t C_t' Ω` and `0 ≤ Q ≤ 2` (`gap:eq:quadrant-source`); `K` is
  finite band, symmetric, real and selfadjoint, with absolute row and column sums at most
  twice the sum of the absolute hopping coefficients.
* The automorphism `U ↦ -U`, `V ↦ -V` (l. 3232–3235) on symbols: it is multiplicative for the
  twisted product, `*`-preserving and trace preserving, fixes `D`, and maps `H_b` to `-H_{-b}`.
-/
import AnalyticPerturbationsAMO.WeylAlgebra

noncomputable section

open Complex
open scoped ComplexConjugate

namespace SGD

namespace QuadrantBalance

/-! ### Comparison constants -/

/-- **§3, l. 2786 (`gap:sec:comparison`)**: the constant `d = (1 + √(1-4b²))/2`. -/
def dC (b : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * b ^ 2)) / 2

/-- **§3, l. 2786 (`gap:sec:comparison`)**: the constant `c = (1 - √(1-4b²))/2`. -/
def cC (b : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * b ^ 2)) / 2

/-- **§3, l. 2788**: `d + c = 1`. -/
theorem dC_add_cC (b : ℝ) : dC b + cC b = 1 := by unfold dC cC; ring

/-- **§3, l. 2788**: `d c = b²` (for `0 ≤ b < 1/2`). -/
theorem dC_mul_cC {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) : dC b * cC b = b ^ 2 := by
  have h : 0 ≤ 1 - 4 * b ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h
  unfold dC cC
  linear_combination (-1 / 4 : ℝ) * hs

lemma sqrt_disc_pos {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    0 < Real.sqrt (1 - 4 * b ^ 2) := Real.sqrt_pos.2 (by nlinarith)

lemma sqrt_disc_le_one (b : ℝ) : Real.sqrt (1 - 4 * b ^ 2) ≤ 1 := by
  rw [Real.sqrt_le_one]; nlinarith [sq_nonneg b]

/-- **§3, l. 2788**: `c ≥ 0`. -/
theorem cC_nonneg (b : ℝ) : 0 ≤ cC b := by
  unfold cC; linarith [sqrt_disc_le_one b]

/-- **§3, l. 2788**: `d > c` (for `0 ≤ b < 1/2`). -/
theorem cC_lt_dC {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) : cC b < dC b := by
  unfold cC dC; linarith [sqrt_disc_pos hb0 hb]

/-- **§3, l. 2786**: `d ≥ 1/2`. -/
theorem half_le_dC (b : ℝ) : 1 / 2 ≤ dC b := by
  unfold dC; linarith [Real.sqrt_nonneg (1 - 4 * b ^ 2)]

lemma dC_pos (b : ℝ) : 0 < dC b := by linarith [half_le_dC b]

/-- **§3, l. 2802**: the Jacobi hopping `p_t(z) = d z⁻¹ + 2bt + c t² z` of `C_t`. -/
def pHop (b t : ℝ) (z : ℂ) : ℂ := dC b * z⁻¹ + 2 * b * t + cC b * t ^ 2 * z

/-- **§3, l. 2809 (`gap:eq:positive-comparison-hopping`)**: the real function
`q_t(z) = d + c t² + bt(z + z⁻¹)` on the unit circle, written with `z + z⁻¹ = 2 Re z`. -/
def qHop (b t : ℝ) (z : ℂ) : ℝ := dC b + cC b * t ^ 2 + b * t * (2 * z.re)

/-- **§3, l. 2802**: the factorization `p_t(z) = d z⁻¹ (1 + (b/d) t z)²` (`z ≠ 0`). -/
theorem pHop_factor {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    pHop b t z = dC b * z⁻¹ * (1 + (b / dC b) * t * z) ^ 2 := by
  have hd : (dC b : ℂ) ≠ 0 := by exact_mod_cast (dC_pos b).ne'
  have hdc : (dC b : ℂ) * cC b = (b : ℂ) ^ 2 := by exact_mod_cast dC_mul_cC hb0 hb
  unfold pHop
  field_simp
  linear_combination z ^ 2 * (t : ℂ) ^ 2 * hdc

/-- **§3, l. 2810**: on the unit circle `q_t(z) = d + ct² + bt(z + z̄)` as a complex number
(`z⁻¹ = z̄` there). -/
theorem qHop_complex (b t : ℝ) (z : ℂ) :
    (qHop b t z : ℂ) = dC b + cC b * t ^ 2 + b * t * (z + conj z) := by
  have : z + conj z = ((2 * z.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
    try push_cast
    try ring
  rw [this, qHop]
  try push_cast
  try ring

/-- **§3, l. 2810 (`gap:eq:positive-comparison-hopping`)**: `|p_t(z)| = q_t(z)` for `|z| = 1`
and real `t`. -/
theorem norm_pHop {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖pHop b t z‖ = qHop b t z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hd := dC_pos b
  have hdc := dC_mul_cC hb0 hb
  have hz2 : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz]; norm_num
  rw [pHop_factor hb0 hb t hz0, norm_mul, norm_mul, norm_inv, hz, norm_pow,
    Complex.sq_norm, Complex.normSq_apply]
  have hw : (1 + (b / dC b : ℂ) * t * z) = 1 + ((b / dC b * t : ℝ) : ℂ) * z := by
    push_cast; ring
  have hre : (1 + (b / dC b : ℂ) * t * z).re = 1 + b / dC b * t * z.re := by
    rw [hw, Complex.add_re, Complex.re_ofReal_mul]; simp
  have him : (1 + (b / dC b : ℂ) * t * z).im = b / dC b * t * z.im := by
    rw [hw, Complex.add_im, Complex.im_ofReal_mul]; simp
  rw [hre, him, Complex.norm_real, Real.norm_of_nonneg hd.le, qHop]
  field_simp
  linear_combination (t ^ 2 * b ^ 2) * hz2 + (- t ^ 2) * hdc

/-- **§3, l. 2811 (`gap:eq:positive-comparison-hopping`)**: `q_t(z) ≥ (√d - t√c)² > 0` on the
unit circle, for `0 < t ≤ 1`. -/
theorem qHop_lower {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (Real.sqrt (dC b) - t * Real.sqrt (cC b)) ^ 2 ≤ qHop b t z ∧
      0 < (Real.sqrt (dC b) - t * Real.sqrt (cC b)) ^ 2 := by
  have hd := dC_pos b
  have hc := cC_nonneg b
  have hsd := Real.sq_sqrt hd.le
  have hsc := Real.sq_sqrt hc
  have hprod : Real.sqrt (dC b) * Real.sqrt (cC b) = b := by
    rw [← Real.sqrt_mul hd.le, dC_mul_cC hb0 hb, Real.sqrt_sq hb0]
  have hre : -1 ≤ z.re := by
    have := Complex.abs_re_le_norm z; rw [hz] at this; linarith [abs_le.1 this]
  refine ⟨?_, ?_⟩
  · have : (Real.sqrt (dC b) - t * Real.sqrt (cC b)) ^ 2 = dC b - 2 * t * b + cC b * t ^ 2 := by
      linear_combination hsd + t ^ 2 * hsc - 2 * t * hprod
    rw [this, qHop]; nlinarith [mul_nonneg (mul_nonneg hb0 ht0.le) (by linarith : 0 ≤ z.re + 1)]
  · have hlt : Real.sqrt (cC b) < Real.sqrt (dC b) :=
      Real.sqrt_lt_sqrt hc (cC_lt_dC hb0 hb)
    have : t * Real.sqrt (cC b) ≤ Real.sqrt (cC b) := by
      nlinarith [Real.sqrt_nonneg (cC b)]
    have : 0 < Real.sqrt (dC b) - t * Real.sqrt (cC b) := by linarith
    positivity

/-! ### The rooted-resolvent objects -/

/-- **§3, l. 3141**: the steps `{-1,0,1}²` of the comparison family. -/
def steps : Finset (ℤ × ℤ) := Finset.Icc (-1) 1 ×ˢ Finset.Icc (-1) 1

/-- **l. 403**: the symplectic form `m ∧ n = m₁ n₂ - m₂ n₁`. -/
def wedge (m n : ℤ × ℤ) : ℤ := m.1 * n.2 - m.2 * n.1

/-- The angle `πα (s ∧ x)`. -/
def ang (α : ℝ) (s x : ℤ × ℤ) : ℝ := Real.pi * α * wedge s x

/-- **§3, l. 3106**: left multiplication `L` by the symbol `h` (supported in `{-1,0,1}²`) on
coefficient arrays: `(Lu)_x = ∑_s h_s e^{πiα s∧x} u_{x-s}`, from `W_s W_{x-s} = e^{πiα s∧x} W_x`. -/
def Lop (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  ∑ s ∈ steps, h s * Complex.exp ((ang α s x : ℂ) * I) * u (x - s)

/-- **§3, l. 3106**: right multiplication `R` by `h`: `(Ru)_x = ∑_s h_s e^{-πiα s∧x} u_{x-s}`. -/
def Rop (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  ∑ s ∈ steps, h s * Complex.exp (-(ang α s x : ℂ) * I) * u (x - s)

/-- **§3, l. 3108**: `M = (L + R)/2`. -/
def Mop (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ := (Lop α h u x + Rop α h u x) / 2

/-- **§3, l. 3108**: `D = (L - R)/(2i)`. -/
def Dop (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ := (Lop α h u x - Rop α h u x) / (2 * I)

lemma wedge_sub (s x : ℤ × ℤ) : wedge x (x - s) = wedge s x := by
  simp only [wedge, Prod.fst_sub, Prod.snd_sub]; ring

/-- Consistency with the Weyl algebra (l. 403–405): `L u = h ⋆ u`, the twisted product
`AMO.tmul` with `W_m W_n = e^{πiα m∧n} W_{m+n}`. -/
theorem Lop_eq_tmul (α : ℝ) {h : ℤ × ℤ → ℂ} (hsupp : ∀ s ∉ steps, h s = 0) (u : ℤ × ℤ → ℂ)
    (x : ℤ × ℤ) : Lop α h u x = AMO.tmul α h u x := by
  unfold AMO.tmul
  rw [tsum_eq_sum (s := steps) (fun s hs => by simp [hsupp s hs])]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_right_comm]
  congr 1
  simp only [AMO.wphase, AMO.e, ang, wedge, Prod.fst_sub, Prod.snd_sub]
  congr 1; push_cast; ring

/-- Consistency with the Weyl algebra (l. 403–405): `R u = u ⋆ h`. -/
theorem Rop_eq_tmul (α : ℝ) {h : ℤ × ℤ → ℂ} (hsupp : ∀ s ∉ steps, h s = 0) (u : ℤ × ℤ → ℂ)
    (x : ℤ × ℤ) : Rop α h u x = AMO.tmul α u h x := by
  unfold AMO.tmul
  rw [← (Equiv.subLeft x).tsum_eq]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [tsum_eq_sum (s := steps) (fun s hs => by simp [hsupp s hs])]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show h s * Complex.exp (-(ang α s x : ℂ) * I) * u (x - s)
      = u (x - s) * h s * Complex.exp (-(ang α s x : ℂ) * I) by ring]
  congr 1
  simp only [AMO.wphase, AMO.e, ang, wedge, Prod.fst_sub, Prod.snd_sub]
  congr 1; push_cast; ring

/-- **§3, l. 3144**: the rows of `M`: `(Mu)_x = ∑_s h_s cos(πα(s∧x)) u_{x-s}`. -/
theorem Mop_apply (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    Mop α h u x = ∑ s ∈ steps, h s * (Real.cos (ang α s x) : ℂ) * u (x - s) := by
  unfold Mop Lop Rop
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_cos, Complex.cos]; ring

/-- **§3, l. 3146**: the rows of `D`: `(Du)_x = ∑_s h_s sin(πα(s∧x)) u_{x-s}`. -/
theorem Dop_apply (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    Dop α h u x = ∑ s ∈ steps, h s * (Real.sin (ang α s x) : ℂ) * u (x - s) := by
  unfold Dop Lop Rop
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_sin, Complex.sin]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- `L = M + iD` (definitional rearrangement of l. 3108). -/
theorem Lop_eq_M_add_D (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    Lop α h u x = Mop α h u x + I * Dop α h u x := by
  unfold Mop Dop; field_simp; ring

/-- The quadrant weight `w(a,b)` on integer coordinates: `2` if `ab > 0`, `1` if `ab = 0`,
`0` if `ab < 0`. -/
def wZ (a b : ℤ) : ℝ := if 0 < a * b then 2 else if a * b = 0 then 1 else 0

/-- **§3, l. 3110**: the diagonal operator `Q`: `Q_{0,0} = 0`, and `Q_{j,k} = 2, 1, 0` according
as `jk > 0`, `jk = 0`, `jk < 0`. -/
def Q (x : ℤ × ℤ) : ℝ := if x = 0 then 0 else wZ x.1 x.2

/-- **§3, l. 3120**: the midpoint weight `w(z)` for `z ∈ ℝ²`. -/
def wMid (z : ℝ × ℝ) : ℝ := if 0 < z.1 * z.2 then 2 else if z.1 * z.2 = 0 then 1 else 0

/-- The midpoint `(x + y)/2 ∈ ℝ²` of two lattice points. -/
def mid (x y : ℤ × ℤ) : ℝ × ℝ := (((x.1 + y.1 : ℤ) : ℝ) / 2, ((x.2 + y.2 : ℤ) : ℝ) / 2)

/-- The matrix of `M` in the basis `e_x`: `M_{x,y} = h_{x-y} cos(πα (x ∧ y))`. -/
def Mmat (α : ℝ) (h : ℤ × ℤ → ℂ) (x y : ℤ × ℤ) : ℂ :=
  h (x - y) * (Real.cos (Real.pi * α * wedge x y) : ℂ)

/-- **§3, l. 3125**: the matrix `K`: zero root row and column, otherwise
`K_{x,y} = w((x+y)/2) M_{x,y}`. -/
def Kmat (α : ℝ) (h : ℤ × ℤ → ℂ) (x y : ℤ × ℤ) : ℂ :=
  if x = 0 ∨ y = 0 then 0 else (wMid (mid x y) : ℂ) * Mmat α h x y

/-- The finite-band operator `K` acting on coefficient arrays. -/
def Kop (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  ∑ s ∈ steps, Kmat α h x (x - s) * u (x - s)

lemma wMid_half (a b : ℤ) : wMid ((a : ℝ) / 2, (b : ℝ) / 2) = wZ a b := by
  have h1 : (0 < (a : ℝ) / 2 * ((b : ℝ) / 2)) ↔ 0 < a * b := by
    rw [show (a : ℝ) / 2 * ((b : ℝ) / 2) = ((a * b : ℤ) : ℝ) / 4 by push_cast; ring]
    rw [div_pos_iff_of_pos_right (by norm_num)]; exact_mod_cast Iff.rfl
  have h2 : ((a : ℝ) / 2 * ((b : ℝ) / 2) = 0) ↔ a * b = 0 := by
    rw [show (a : ℝ) / 2 * ((b : ℝ) / 2) = ((a * b : ℤ) : ℝ) / 4 by push_cast; ring]
    rw [div_eq_zero_iff]; norm_num
  simp only [wMid, wZ, h1, h2]

lemma Mop_eq_mat (α : ℝ) (h u : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    Mop α h u x = ∑ s ∈ steps, Mmat α h x (x - s) * u (x - s) := by
  rw [Mop_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Mmat, sub_sub_cancel, wedge_sub, ang]

lemma wZ_of_pos {a b : ℤ} (h : 0 < a * b) : wZ a b = 2 := by simp [wZ, h]
lemma wZ_of_zero {a b : ℤ} (h : a * b = 0) : wZ a b = 1 := by simp [wZ, h]
lemma wZ_of_neg {a b : ℤ} (h : a * b < 0) : wZ a b = 0 := by
  simp [wZ, h.ne, not_lt.2 h.le]

lemma wZ_congr {a b a' b' : ℤ} (ha : 0 < a ↔ 0 < a') (ha' : a < 0 ↔ a' < 0)
    (hb : 0 < b ↔ 0 < b') (hb' : b < 0 ↔ b' < 0) : wZ a b = wZ a' b' := by
  have h1 : 0 < a * b ↔ 0 < a' * b' := by rw [mul_pos_iff, mul_pos_iff]; tauto
  have h2 : a * b = 0 ↔ a' * b' = 0 := by simp only [mul_eq_zero]; omega
  simp only [wZ, h1, h2]

/-- `0 ≤ Q ≤ 2` (**`gap:eq:quadrant-source`**, l. 3117). -/
theorem Q_nonneg_le_two (x : ℤ × ℤ) : 0 ≤ Q x ∧ Q x ≤ 2 := by
  unfold Q wZ; split_ifs <;> norm_num

lemma wMid_nonneg_le_two (z : ℝ × ℝ) : 0 ≤ wMid z ∧ wMid z ≤ 2 := by
  unfold wMid; split_ifs <;> norm_num

/-- `QM - K` on the row `x ≠ 0`, as a single finite sum (uses `u_{0,0} = 0` for the root column). -/
lemma QM_sub_K (α : ℝ) (h u : ℤ × ℤ → ℂ) (hu : u 0 = 0) {x : ℤ × ℤ} (hx : x ≠ 0) :
    (Q x : ℂ) * Mop α h u x - Kop α h u x
      = ∑ s ∈ steps, h s * (((Q x - wZ (2 * x.1 - s.1) (2 * x.2 - s.2) : ℝ) : ℂ)
          * (Real.cos (ang α s x) : ℂ)) * u (x - s) := by
  rw [Mop_apply, Kop, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : x - s = 0
  · rw [hs, hu]; ring
  · have hK : Kmat α h x (x - s)
        = (wZ (2 * x.1 - s.1) (2 * x.2 - s.2) : ℂ) * h s * (Real.cos (ang α s x) : ℂ) := by
      simp only [Kmat, hx, hs, or_self, ↓reduceIte, Mmat, sub_sub_cancel, wedge_sub, ang, mid]
      rw [wMid_half]
      have hw : wZ (x.1 + (x - s).1) (x.2 + (x - s).2) = wZ (2 * x.1 - s.1) (2 * x.2 - s.2) := by
        congr 1 <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
      rw [hw]; ring
    rw [hK]; push_cast; ring

lemma sin_ne_zero_of_irrational {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    Real.sin (Real.pi * α * k) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h0
  have : α * k = n := by
    have := Real.pi_pos
    have h' : Real.pi * (α * k) = Real.pi * n := by rw [← mul_assoc, ← hn]; ring
    exact (mul_left_cancel₀ Real.pi_ne_zero h')
  exact (hα.mul_intCast hk).ne_int n this

/-- **Lemma 3.x (`gap:lem:quadrant-balance`, l. 3130)**: for irrational `α` and any coefficient
array `h` on the steps `{-1,0,1}²` (in particular the comparison operator `C_t`,
`gap:eq:comparison-path`; see `quadrant_balance_comparison`),
`u_{0,0} = 0` and `(L - R)u = 0` imply `Q L u = K u` (coordinatewise). -/
theorem quadrant_balance {α : ℝ} (hα : Irrational α) (h u : ℤ × ℤ → ℂ) (hu : u 0 = 0)
    (hLR : ∀ x, Lop α h u x - Rop α h u x = 0) (x : ℤ × ℤ) :
    (Q x : ℂ) * Lop α h u x = Kop α h u x := by
  have hD : ∀ y, Dop α h u y = 0 := fun y => by simp [Dop, hLR y]
  rw [Lop_eq_M_add_D, hD x, mul_zero, add_zero]
  by_cases hx : x = 0
  · subst hx
    simp [Q, Kop, Kmat]
  rw [← sub_eq_zero, QM_sub_K α h u hu hx]
  obtain ⟨j, k⟩ := x
  by_cases hj : j = 0
  · -- the vertical axis `x = (0,k)`, `k ≠ 0`
    subst hj
    have hk : k ≠ 0 := fun hk => hx (by simp [hk])
    have hsin := sin_ne_zero_of_irrational hα hk
    set θ := Real.pi * α * k with hθ
    have hang : ∀ s : ℤ × ℤ, ang α s (0, k) = s.1 * θ := fun s => by
      simp only [ang, wedge, hθ]; push_cast; ring
    have hQ : Q (0, k) = 1 := by simp [Q, hk, wZ]
    obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, (0 < k → ε = 1) ∧ (k < 0 → ε = -1) :=
      if hk' : 0 < k then ⟨1, fun _ => rfl, fun h => absurd h (not_lt.2 hk'.le)⟩
      else ⟨-1, fun h => absurd h hk', fun _ => rfl⟩
    have key : ∀ s ∈ steps, ((Q (0, k) - wZ (2 * 0 - s.1) (2 * k - s.2) : ℝ) *
        Real.cos (ang α s (0, k))) * Real.sin θ = ε * Real.cos θ * Real.sin (ang α s (0, k)) := by
      intro s hs
      obtain ⟨s1, s2⟩ := s
      simp only [steps, Finset.mem_product, Finset.mem_Icc] at hs
      rw [hang, hQ]
      simp only
      have : s1 = -1 ∨ s1 = 0 ∨ s1 = 1 := by omega
      rcases this with rfl | rfl | rfl
      · rcases lt_or_gt_of_ne hk with hk' | hk'
        · rw [wZ_of_neg (by ring_nf; omega), hε' hk']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
        · rw [wZ_of_pos (by ring_nf; omega), hε hk']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
      · rw [wZ_of_zero (by ring)]; simp
      · rcases lt_or_gt_of_ne hk with hk' | hk'
        · rw [wZ_of_pos (by ring_nf; omega), hε' hk']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
        · rw [wZ_of_neg (by ring_nf; omega), hε hk']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
    have hsum : (Real.sin θ : ℂ) * ∑ s ∈ steps, h s * (((Q (0, k) - wZ (2 * (0, k).1 - s.1)
        (2 * (0, k).2 - s.2) : ℝ) : ℂ) * (Real.cos (ang α s (0, k)) : ℂ)) * u ((0, k) - s)
        = (ε : ℂ) * Real.cos θ * Dop α h u (0, k) := by
      rw [Dop_apply, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have := congrArg (fun r : ℝ => (r : ℂ)) (key s hs)
      push_cast at this ⊢
      linear_combination h s * u ((0, k) - s) * this
    exact (mul_eq_zero.1 (hsum.trans (by rw [hD]; ring :
      (ε : ℂ) * Real.cos θ * Dop α h u (0, k) = 0))).resolve_left (Complex.ofReal_ne_zero.2 hsin)
  by_cases hk : k = 0
  · -- the horizontal axis `x = (j,0)`, `j ≠ 0`
    subst hk
    have hsin := sin_ne_zero_of_irrational hα hj
    set θ := Real.pi * α * j with hθ
    have hang : ∀ s : ℤ × ℤ, ang α s (j, 0) = -(s.2 * θ) := fun s => by
      simp only [ang, wedge, hθ]; push_cast; ring
    have hQ : Q (j, 0) = 1 := by simp [Q, hj, wZ]
    obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, (0 < j → ε = 1) ∧ (j < 0 → ε = -1) :=
      if hj' : 0 < j then ⟨1, fun _ => rfl, fun h => absurd h (not_lt.2 hj'.le)⟩
      else ⟨-1, fun h => absurd h hj', fun _ => rfl⟩
    have key : ∀ s ∈ steps, ((Q (j, 0) - wZ (2 * j - s.1) (2 * 0 - s.2) : ℝ) *
        Real.cos (ang α s (j, 0))) * Real.sin θ
          = -(ε * Real.cos θ * Real.sin (ang α s (j, 0))) := by
      intro s hs
      obtain ⟨s1, s2⟩ := s
      simp only [steps, Finset.mem_product, Finset.mem_Icc] at hs
      rw [hang, hQ]
      simp only
      have : s2 = -1 ∨ s2 = 0 ∨ s2 = 1 := by omega
      rcases this with rfl | rfl | rfl
      · rcases lt_or_gt_of_ne hj with hj' | hj'
        · rw [wZ_of_neg (by ring_nf; omega), hε' hj']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
        · rw [wZ_of_pos (by ring_nf; omega), hε hj']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
      · rw [wZ_of_zero (by ring)]; simp
      · rcases lt_or_gt_of_ne hj with hj' | hj'
        · rw [wZ_of_pos (by ring_nf; omega), hε' hj']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
        · rw [wZ_of_neg (by ring_nf; omega), hε hj']; push_cast
          try simp only [neg_mul, one_mul, neg_neg, Real.cos_neg, Real.sin_neg] -- normalize signs
          ring
    have hsum : (Real.sin θ : ℂ) * ∑ s ∈ steps, h s * (((Q (j, 0) - wZ (2 * (j, 0).1 - s.1)
        (2 * (j, 0).2 - s.2) : ℝ) : ℂ) * (Real.cos (ang α s (j, 0)) : ℂ)) * u ((j, 0) - s)
        = -((ε : ℂ) * Real.cos θ * Dop α h u (j, 0)) := by
      rw [Dop_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      have := congrArg (fun r : ℝ => (r : ℂ)) (key s hs)
      push_cast at this ⊢
      linear_combination h s * u ((j, 0) - s) * this
    exact (mul_eq_zero.1 (hsum.trans (by rw [hD]; ring :
      -((ε : ℂ) * Real.cos θ * Dop α h u (j, 0)) = 0))).resolve_left (Complex.ofReal_ne_zero.2 hsin)
  · -- off the axes every midpoint weight equals `Q_x`
    refine Finset.sum_eq_zero fun s hs => ?_
    obtain ⟨s1, s2⟩ := s
    simp only [steps, Finset.mem_product, Finset.mem_Icc] at hs
    have hQ : Q (j, k) = wZ (2 * j - s1) (2 * k - s2) := by
      simp only [Q, hx, ↓reduceIte]
      apply wZ_congr <;> omega
    simp [hQ]

/-! ### The comparison family -/

/-- **§3, eq. `gap:eq:comparison-path` (l. 2797)**: the coefficient array of
`C_t = d D_- + t(2bX + Y) + c t² D_+`, i.e. `h = d` at `±(1,-1)`, `2bt` at `±(1,0)`,
`t` at `±(0,1)`, `ct²` at `±(1,1)`, and `0` elsewhere. -/
def hC (b t : ℝ) (x : ℤ × ℤ) : ℝ :=
  if x = (1, -1) ∨ x = (-1, 1) then dC b
  else if x = (1, 0) ∨ x = (-1, 0) then 2 * b * t
  else if x = (0, 1) ∨ x = (0, -1) then t
  else if x = (1, 1) ∨ x = (-1, -1) then cC b * t ^ 2
  else 0

/-- The coefficient array of `C_t' = ∂_t C_t = 2bX + Y + 2ct D_+`. -/
def hC' (b t : ℝ) (x : ℤ × ℤ) : ℝ :=
  if x = (1, -1) ∨ x = (-1, 1) then 0
  else if x = (1, 0) ∨ x = (-1, 0) then 2 * b
  else if x = (0, 1) ∨ x = (0, -1) then 1
  else if x = (1, 1) ∨ x = (-1, -1) then 2 * cC b * t
  else 0

/-- `hC'` is the `t`-derivative of the coefficient array of `C_t`. -/
theorem hasDerivAt_hC (b t : ℝ) (x : ℤ × ℤ) :
    HasDerivAt (fun t => hC b t x) (hC' b t x) t := by
  unfold hC hC'
  by_cases h1 : x = (1, -1) ∨ x = (-1, 1)
  · simp only [h1, ↓reduceIte]; exact hasDerivAt_const _ _
  by_cases h2 : x = (1, 0) ∨ x = (-1, 0)
  · simp only [h1, h2, ↓reduceIte]
    simpa using (hasDerivAt_id t).const_mul (2 * b)
  by_cases h3 : x = (0, 1) ∨ x = (0, -1)
  · simp only [h1, h2, h3, ↓reduceIte]; exact hasDerivAt_id t
  by_cases h4 : x = (1, 1) ∨ x = (-1, -1)
  · simp only [h1, h2, h3, h4, ↓reduceIte]
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hasDerivAt_pow 2 t).const_mul (cC b)
  · simp only [h1, h2, h3, h4, ↓reduceIte]; exact hasDerivAt_const _ _

/-- The coefficients of `C_t` are supported on the steps `{-1,0,1}²`. -/
theorem hC_supp (b t : ℝ) : ∀ s ∉ steps, hC b t s = 0 := by
  intro s hs
  unfold hC
  split_ifs with h1 h2 h3 h4 <;>
    first
    | rfl
    | (exfalso; apply hs; rcases h1 with rfl | rfl <;> decide)
    | (exfalso; apply hs; rcases h2 with rfl | rfl <;> decide)
    | (exfalso; apply hs; rcases h3 with rfl | rfl <;> decide)
    | (exfalso; apply hs; rcases h4 with rfl | rfl <;> decide)

theorem hC'_supp (b t : ℝ) : ∀ s ∉ steps, hC' b t s = 0 := by
  intro s hs
  unfold hC'
  split_ifs with h1 h2 h3 h4 <;>
    first
    | rfl
    | (exfalso; apply hs; rcases h2 with rfl | rfl <;> decide)
    | (exfalso; apply hs; rcases h3 with rfl | rfl <;> decide)
    | (exfalso; apply hs; rcases h4 with rfl | rfl <;> decide)

/-- The coefficients of `C_t` are even: `h_{-s} = h_s` (`C_t` is selfadjoint). -/
theorem hC_neg (b t : ℝ) (s : ℤ × ℤ) : hC b t (-s) = hC b t s := by
  obtain ⟨a, c⟩ := s
  simp only [hC, Prod.neg_mk, Prod.mk.injEq]
  split_ifs <;> first | rfl | omega

/-- The root vector `Ω = W_{0,0} = Id` as a coefficient array. -/
def Ω : ℤ × ℤ → ℂ := fun y => if y = 0 then 1 else 0

/-- `L_h Ω = h`: the coefficient array of `C Ω = C`. -/
theorem Lop_Ω (α : ℝ) {h : ℤ × ℤ → ℂ} (hsupp : ∀ s ∉ steps, h s = 0) (x : ℤ × ℤ) :
    Lop α h Ω x = h x := by
  unfold Lop Ω
  have hw : ∀ s, s = x → (ang α s x : ℂ) = 0 := by
    rintro s rfl; simp [ang, wedge, mul_comm]
  by_cases hx : x ∈ steps
  · rw [Finset.sum_eq_single x]
    · simp [hw x rfl]
    · intro s _ hs; simp [sub_eq_zero, Ne.symm hs]
    · intro h'; exact absurd hx h'
  · rw [hsupp x hx]
    refine Finset.sum_eq_zero fun s hs => ?_
    have : x - s ≠ 0 := by rw [sub_ne_zero]; rintro rfl; exact hx hs
    simp [this]

/-- **§3, eq. `gap:eq:quadrant-source` (l. 3117)**: the source identity `Q C_t Ω = t C_t' Ω`,
coordinatewise. -/
theorem quadrant_source (α b t : ℝ) (x : ℤ × ℤ) :
    (Q x : ℂ) * Lop α (fun s => (hC b t s : ℂ)) Ω x
      = t * Lop α (fun s => (hC' b t s : ℂ)) Ω x := by
  rw [Lop_Ω α (fun s hs => by simp [hC_supp b t s hs]),
    Lop_Ω α (fun s hs => by simp [hC'_supp b t s hs])]
  have : Q x * hC b t x = t * hC' b t x := by
    unfold hC hC'
    split_ifs with h1 h2 h3 h4
    · rcases h1 with rfl | rfl <;> norm_num [Q, wZ]
    · rcases h2 with rfl | rfl <;> norm_num [Q, wZ] <;> ring
    · rcases h3 with rfl | rfl <;> norm_num [Q, wZ]
    · rcases h4 with rfl | rfl <;> norm_num [Q, wZ] <;> ring
    · simp
  exact_mod_cast this

/-- **Lemma `gap:lem:quadrant-balance` for the comparison family** `C_t`
(eq. `gap:eq:comparison-path`): for irrational `α`, `0 ≤ b < 1/2` (any real `b, t`),
`u_{0,0} = 0` and `(L_t - R_t) u = 0` imply `Q L_t u = K_t u`. -/
theorem quadrant_balance_comparison {α : ℝ} (hα : Irrational α) (b t : ℝ) (u : ℤ × ℤ → ℂ)
    (hu : u 0 = 0) (hLR : ∀ x, Lop α (fun s => (hC b t s : ℂ)) u x
      - Rop α (fun s => (hC b t s : ℂ)) u x = 0) (x : ℤ × ℤ) :
    (Q x : ℂ) * Lop α (fun s => (hC b t s : ℂ)) u x = Kop α (fun s => (hC b t s : ℂ)) u x :=
  quadrant_balance hα _ u hu hLR x

/-! ### Properties of `K` (l. 3125–3128) -/

/-- **§3, l. 3127**: `K` is finite band: `K_{x,y} = 0` unless `x - y ∈ {-1,0,1}²`. -/
theorem Kmat_band (α : ℝ) {h : ℤ × ℤ → ℂ} (hsupp : ∀ s ∉ steps, h s = 0) {x y : ℤ × ℤ}
    (hxy : x - y ∉ steps) : Kmat α h x y = 0 := by
  simp [Kmat, Mmat, hsupp _ hxy]

/-- **§3, l. 3127**: `K` is symmetric, `K_{x,y} = K_{y,x}`, when `h_{-s} = h_s`. -/
theorem Kmat_symm (α : ℝ) {h : ℤ × ℤ → ℂ} (hsym : ∀ s, h (-s) = h s) (x y : ℤ × ℤ) :
    Kmat α h x y = Kmat α h y x := by
  have hm : mid x y = mid y x := by simp only [mid, add_comm]
  have hw : wedge y x = -wedge x y := by simp only [wedge]; ring
  have hh : h (y - x) = h (x - y) := by rw [← neg_sub, hsym]
  simp only [Kmat, Mmat, hm, hh, hw, or_comm, Int.cast_neg, mul_neg, Real.cos_neg]

/-- **§3, l. 3127**: `K` is real when `h` is real. -/
theorem Kmat_im (α : ℝ) (g : ℤ × ℤ → ℝ) (x y : ℤ × ℤ) :
    (Kmat α (fun s => (g s : ℂ)) x y).im = 0 := by
  unfold Kmat Mmat
  split_ifs
  · simp
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_im]

/-- **§3, l. 3127**: `K` is selfadjoint, `K_{x,y} = conj K_{y,x}`, for real even `h`
(e.g. `C_t`). -/
theorem Kmat_selfAdjoint (α : ℝ) (g : ℤ × ℤ → ℝ) (hsym : ∀ s, g (-s) = g s) (x y : ℤ × ℤ) :
    Kmat α (fun s => (g s : ℂ)) x y = conj (Kmat α (fun s => (g s : ℂ)) y x) := by
  rw [Kmat_symm α (fun s => by simp [hsym]) x y]
  apply Complex.ext <;> simp [Kmat_im]

lemma norm_Kmat_le (α : ℝ) (h : ℤ × ℤ → ℂ) (x y : ℤ × ℤ) :
    ‖Kmat α h x y‖ ≤ 2 * ‖h (x - y)‖ := by
  unfold Kmat Mmat
  split_ifs
  · simp
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (wMid_nonneg_le_two _).1]
    have h1 := (wMid_nonneg_le_two (mid x y)).2
    have h2 := Real.abs_cos_le_one (Real.pi * α * wedge x y)
    have h3 := norm_nonneg (h (x - y))
    calc _ ≤ 2 * (‖h (x - y)‖ * 1) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 h3) (by positivity) (by norm_num)
      _ = _ := by ring

/-- **§3, l. 3127**: absolute row sums of `K` are at most twice the sum of the absolute
hopping coefficients. -/
theorem Kmat_row_sum_le (α : ℝ) (h : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    ∑ s ∈ steps, ‖Kmat α h x (x - s)‖ ≤ 2 * ∑ s ∈ steps, ‖h s‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  simpa [sub_sub_cancel] using norm_Kmat_le α h x (x - s)

/-- **§3, l. 3127**: absolute column sums of `K` are at most twice the sum of the absolute
hopping coefficients. -/
theorem Kmat_col_sum_le (α : ℝ) (h : ℤ × ℤ → ℂ) (y : ℤ × ℤ) :
    ∑ s ∈ steps, ‖Kmat α h (y + s) y‖ ≤ 2 * ∑ s ∈ steps, ‖h s‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  simpa using norm_Kmat_le α h (y + s) y

/-! ### The automorphism `U ↦ -U`, `V ↦ -V` (l. 3232–3235) -/

/-- The sign `(-1)^{r+s}` by which `U ↦ -U`, `V ↦ -V` multiplies `W_{r,s}`. -/
def par (p : ℤ × ℤ) : ℂ := (-1 : ℂ) ^ (p.1 + p.2)

/-- **§3, l. 3234**: the automorphism `U ↦ -U`, `V ↦ -V` on symbols:
the coefficient at `(r,s)` is multiplied by `(-1)^{r+s}`. -/
def flip (R : AMO.Symbol) : AMO.Symbol := fun p => par p * R p

lemma par_add (p q : ℤ × ℤ) : par (p + q) = par p * par q := by
  unfold par
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1; simp only [Prod.fst_add, Prod.snd_add]; ring

/-- **§3, l. 3232**: `U ↦ -U`, `V ↦ -V` is multiplicative for the twisted product. -/
theorem flip_tmul (α : ℝ) (R S : AMO.Symbol) :
    flip (AMO.tmul α R S) = AMO.tmul α (flip R) (flip S) := by
  funext p
  simp only [flip, AMO.tmul]
  rw [← tsum_mul_left]
  congr 1; funext p₁
  have : par p = par p₁ * par (p - p₁) := by rw [← par_add]; simp
  rw [this]; ring

/-- **§3, l. 3232**: `U ↦ -U`, `V ↦ -V` commutes with the involution. -/
theorem flip_sstar (R : AMO.Symbol) : flip (AMO.sstar R) = AMO.sstar (flip R) := by
  funext p
  have h1 : par (-p) = par p := by
    have h := par_add p (-p)
    simp only [add_neg_cancel] at h
    have h0 : par 0 = 1 := by simp [par]
    have hsq : par p * par p = 1 := by
      unfold par; rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      rw [← two_mul, zpow_mul]; norm_num
    rw [h0] at h
    calc par (-p) = par (-p) * (par p * par p) := by rw [hsq, mul_one]
      _ = (par p * par (-p)) * par p := by ring
      _ = par p := by rw [← h, one_mul]
  have h2 : conj (par p) = par p := by simp [par]
  simp only [flip, AMO.sstar, map_mul, h1, h2]

/-- **§3, l. 3232**: `U ↦ -U`, `V ↦ -V` preserves the trace `τ(R) = R_{0,0}`. -/
theorem flip_trace (R : AMO.Symbol) : flip R 0 = R 0 := by simp [flip, par]

/-- **l. 534–538**: the symbol of `H_0 = U + U* + V + V*`. -/
def H0sym : AMO.Symbol := fun p =>
  if ((p.1 = 1 ∨ p.1 = -1) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)) then 1 else 0

/-- **l. 538**: the symbol of `D = ∑_{m,n=±1} W_{m,n}`. -/
def Dsym : AMO.Symbol := fun p => if (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1) then 1 else 0

/-- **§3, l. 3234**: `U ↦ -U`, `V ↦ -V` fixes `D`. -/
theorem flip_Dsym : flip Dsym = Dsym := by
  funext p
  obtain ⟨a, c⟩ := p
  simp only [flip, Dsym]
  split_ifs with h
  · rcases h with ⟨rfl | rfl, rfl | rfl⟩ <;> norm_num [par]
  · simp

/-- **§3, l. 3234**: `U ↦ -U`, `V ↦ -V` negates `H_0`. -/
theorem flip_H0sym : flip H0sym = -H0sym := by
  funext p
  obtain ⟨a, c⟩ := p
  simp only [flip, H0sym, Pi.neg_apply]
  split_ifs with h
  · rcases h with ⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> norm_num [par]
  · simp

/-- **§3, l. 3234**: `U ↦ -U`, `V ↦ -V` maps `H_b = H_0 + bD` to `-H_{-b} = -(H_0 - bD)`. -/
theorem flip_Hb (b : ℝ) :
    flip (H0sym + (b : ℂ) • Dsym) = -(H0sym + ((-b : ℝ) : ℂ) • Dsym) := by
  have hlin : flip (H0sym + (b : ℂ) • Dsym) = flip H0sym + (b : ℂ) • flip Dsym := by
    funext p; simp only [flip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hlin, flip_H0sym, flip_Dsym]
  funext p; simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring

end QuadrantBalance

end SGD
