import Reducibility.SmallDivisors

/-!
# AFK §3: growth of cocycles of rotations (Birkhoff sums over the rotation by `α`)

Formalization of §2.3 (continued-fraction preliminaries, used through `CAH.q`, `CAH.delta`,
best approximation) and §3 of A. Avila, B. Fayad, R. Krikorian, *A KAM scheme for SL(2,ℝ)
cocycles with Liouvillean frequencies* (`Reducibility/AFK/afk_source.tex`, lines ~993–1176).

## Modelling
A function `φ ∈ C^ω_h(𝕋)` is represented by its Fourier coefficients `φ̂ = a : ℤ → ℂ` with the
Cauchy bound `|φ̂(l)| e^{2π|l|h} ≤ K` for `l ≠ 0` (`K` plays the role of `‖φ - φ̂(0)‖_h`).
The Birkhoff sum `S_nφ - nφ̂(0)` has coefficients `birkhoffCoeff α n a l = φ̂(l) ∑_{j<n} e(jlα)`
(`= φ̂(l)(1-e(nlα))/(1-e(lα))`) for `l ≠ 0` and `0` for `l = 0` (`birkhoff_fourier`).
The strip norm at width `h'` is replaced by the weighted norm
`wnorm b h' = ∑_l |b(l)| e^{2π|l|h'}`, which dominates `sup_{|Im z| ≤ h'} |∑ b(l) e(lz)|`
(`norm_fourierC_le_wnorm`).  Denominators are `CAH.q α n` (real) / `CAH.qN α n` (natural).

## Main results (paper labels)
* `denjoy_el` — Lemma `denjoy.el`:
  `wnorm(S_{q_{s₂}}φ - q_{s₂}φ̂(0), h(1-δ)) ≤ C K (s₂⁴ q_{s₁}/q_{s₂+1} + q_{s₂}/q_{s₁}^U)`
  for `q_{s₁} ≤ q_{s₂}`, `δ ≥ max(1/√q_{s₁}, η/(10 s₂²))`, `h ≥ h_*`, `C = C(h_*, η, U)`.
* `IsCDBridge`, `dioph_bridge` — CD bridges and Lemma `dioph.bridge` (**corrected**: the
  bridges are `CD(A, A, A⁴)` instead of `CD(A, A, A³)`; the paper's statement is false in
  general, see the docstring of `dioph_bridge`).  `IsAFKSeq` packages its conclusions.
* `cor3`, `cor3_Q` — Corollary `cor3` (with `U = A⁵`, `A = 2M`; `T₀` depends on `η` too).
* `cor4` — Corollary `cor4` (Birkhoff sums of arbitrary length `m ≤ Q_{k+1}`).
* `denjoy` — Proposition `denjoy`, with a single constant `C(h_*, η, M)` valid for all `k > 0`
  (small `Q_k` are handled by `denjoy_small`).

## Deviations from the paper (all explained in the docstrings)
* `dioph.bridge`: `CD(A,A,A³)` replaced by `CD(A,A,A⁴)` (counterexample to the original);
  consequently `U = 16M⁴ = A⁴` is replaced by `U = A⁵` in `cor3`/`cor4`/`denjoy`.  The bound
  `Q_{k+1} ≤ Q̄_k^{A⁴} = Q̄_k^{16M⁴}` of Proposition `denjoy` is unchanged.
* `cor3`: the paper writes `S_{q_n}φ` for `S_{q_n}φ - q_nφ̂(0)` and `T₀(h_*, M)` for
  `T₀(h_*, η, M)`.  `cor4`: `lφ̂(0)` should be `mφ̂(0)`.
* All estimates are in the weighted coefficient norm (see Modelling).

The file is `sorry`-free; `#print axioms denjoy` reports only `propext`, `Classical.choice`,
`Quot.sound`.
-/

open Real Finset

namespace Red.AFK

/-! ### Complex exponentials and Fourier series on the strip -/

/-- `e(w) = exp(2πiw)` for complex `w`. -/
noncomputable def eC (w : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * w)

lemma eC_ofReal (t : ℝ) : eC t = eT t := rfl

lemma norm_eC (w : ℂ) : ‖eC w‖ = Real.exp (-(2 * π * w.im)) := by
  rw [eC, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma eT_pow (t : ℝ) (n : ℕ) : eT t ^ n = eT (n * t) := by
  rw [eT, eT, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- The Birkhoff multiplier `∑_{j<n} e(lα)^j = ∑_{j<n} e(jlα)`. -/
noncomputable def bmult (α : ℝ) (n : ℕ) (l : ℤ) : ℂ :=
  ∑ j ∈ range n, eT (l * α) ^ j

/-- Fourier coefficients of `S_nφ - nφ̂(0)`: `φ̂(l) (1 - e(nlα))/(1 - e(lα))` for `l ≠ 0`,
and `0` for `l = 0`. -/
noncomputable def birkhoffCoeff (α : ℝ) (n : ℕ) (a : ℤ → ℂ) (l : ℤ) : ℂ :=
  if l = 0 then 0 else a l * bmult α n l

/-- The weighted `ℓ¹` norm `∑_l |b(l)| e^{2π|l|h'}` (dominates the sup norm on `|Im z| ≤ h'`). -/
noncomputable def wnorm (b : ℤ → ℂ) (h' : ℝ) : ℝ :=
  ∑' l : ℤ, ‖b l‖ * Real.exp (2 * π * |(l : ℝ)| * h')

/-- The Fourier series `z ↦ ∑_l b(l) e(lz)` on the complex strip. -/
noncomputable def fourierC (b : ℤ → ℂ) (z : ℂ) : ℂ := ∑' l : ℤ, b l * eC (l * z)

lemma norm_eC_mul_le {l : ℤ} {z : ℂ} {h' : ℝ} (hz : |z.im| ≤ h') :
    ‖eC (l * z)‖ ≤ Real.exp (2 * π * |(l : ℝ)| * h') := by
  rw [norm_eC]
  apply Real.exp_le_exp.2
  have him : ((l : ℂ) * z).im = l * z.im := by simp [Complex.mul_im]
  rw [him]
  have h1 : -((l : ℝ) * z.im) ≤ |(l : ℝ)| * |z.im| := by
    rw [← abs_mul]; exact neg_le_abs _
  have h2 : |(l : ℝ)| * |z.im| ≤ |(l : ℝ)| * h' := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  nlinarith [pi_pos]

lemma summable_fourier_of_weighted {b : ℤ → ℂ} {h' : ℝ}
    (hs : Summable (fun l : ℤ => ‖b l‖ * Real.exp (2 * π * |(l : ℝ)| * h'))) {z : ℂ}
    (hz : |z.im| ≤ h') : Summable (fun l : ℤ => ‖b l * eC (l * z)‖) :=
  by
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hs
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_eC_mul_le hz) (norm_nonneg _)

/-- The weighted norm dominates the sup norm on the closed strip `|Im z| ≤ h'`. -/
theorem norm_fourierC_le_wnorm {b : ℤ → ℂ} {h' : ℝ}
    (hs : Summable (fun l : ℤ => ‖b l‖ * Real.exp (2 * π * |(l : ℝ)| * h'))) {z : ℂ}
    (hz : |z.im| ≤ h') : ‖fourierC b z‖ ≤ wnorm b h' := by
  have hs' := summable_fourier_of_weighted hs hz
  refine (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum (fun l => ?_) hs' hs)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_eC_mul_le hz) (norm_nonneg _)

lemma eC_shift (l : ℤ) (z : ℂ) (α : ℝ) (j : ℕ) :
    eC (l * (z + (j : ℝ) * α)) = eC (l * z) * eT (l * α) ^ j := by
  rw [eT, eC, eC, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring

lemma bmult_zero (α : ℝ) (n : ℕ) : bmult α n 0 = n := by
  simp [bmult, eT_zero]

/-- **Fourier coefficients of Birkhoff sums.**  For `φ(z) = ∑ φ̂(l) e(lz)` with
`∑ |φ̂(l)| e^{2π|l|h'} < ∞` and `|Im z| ≤ h'`:
`S_nφ(z) - nφ̂(0) = ∑_l birkhoffCoeff α n φ̂ l · e(lz)`. -/
theorem birkhoff_fourier {a : ℤ → ℂ} {h' : ℝ}
    (hs : Summable (fun l : ℤ => ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h'))) (α : ℝ) (n : ℕ)
    {z : ℂ} (hz : |z.im| ≤ h') :
    ∑ j ∈ range n, fourierC a (z + (j : ℝ) * α) - n * a 0 =
      fourierC (birkhoffCoeff α n a) z := by
  have hsum : ∀ j : ℕ, Summable (fun l : ℤ => a l * eC (l * (z + (j : ℝ) * α))) := by
    intro j
    refine (summable_fourier_of_weighted hs (z := z + (j : ℝ) * α) ?_).of_norm
    simpa using hz
  unfold fourierC
  rw [← Summable.tsum_finsetSum (fun j _ => hsum j)]
  have hF : Summable (fun l : ℤ => ∑ j ∈ range n, a l * eC (l * (z + (j : ℝ) * α))) :=
    summable_sum (fun j _ => hsum j)
  rw [hF.tsum_eq_add_tsum_ite 0]
  have h0 : ∑ j ∈ range n, a 0 * eC (((0 : ℤ) : ℂ) * (z + (j : ℝ) * α)) = n * a 0 := by
    simp [eC]
  rw [h0, add_sub_cancel_left]
  congr 1; funext l
  by_cases hl : l = 0
  · simp [hl, birkhoffCoeff]
  · simp only [hl, ite_false, birkhoffCoeff, bmult]
    simp_rw [eC_shift]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => by ring)

/-! ### Bounds on the Birkhoff multiplier -/

lemma norm_bmult_le (α : ℝ) (n : ℕ) (l : ℤ) : ‖bmult α n l‖ ≤ n := by
  unfold bmult
  refine (norm_sum_le _ _).trans ?_
  simp [norm_pow, norm_eT]

lemma bmult_mul (α : ℝ) (n : ℕ) (l : ℤ) :
    bmult α n l * (eT (l * α) - 1) = eT (n * (l * α)) - 1 := by
  rw [bmult, geom_sum_mul, eT_pow]

/-- `|e(t) - 1| ≤ 2π|t - m|` for every integer `m`. -/
lemma norm_eT_sub_one_le (t : ℝ) (m : ℤ) : ‖eT t - 1‖ ≤ 2 * π * |t - m| := by
  rw [norm_eT_sub_one]
  have hs : Real.sin (π * t) = (-1) ^ m * Real.sin (π * (t - m)) := by
    rw [← Real.sin_add_int_mul_pi]; congr 1; ring
  have h1 : |Real.sin (π * t)| = |Real.sin (π * (t - m))| := by
    rw [hs, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [h1]
  have := Real.abs_sin_le_abs (x := π * (t - m))
  rw [abs_mul, abs_of_pos pi_pos] at this
  linarith

/-- `|1 - e(q_s l α)| ≤ 2π|l|/q_{s+1}` (uses `‖q_s α‖ ≤ 1/q_{s+1}`). -/
lemma norm_eT_q_mul_sub_one_le {α : ℝ} (hα : Irrational α) (s : ℕ) (l : ℤ) :
    ‖eT ((CAH.qN α s : ℝ) * (l * α)) - 1‖ ≤ 2 * π * |(l : ℝ)| / CAH.q α (s + 1) := by
  have h := norm_eT_sub_one_le ((CAH.qN α s : ℝ) * (l * α)) (l * CAH.pZ α s)
  have heq : (CAH.qN α s : ℝ) * (l * α) - ((l * CAH.pZ α s : ℤ) : ℝ) = l * CAH.delta α s := by
    rw [CAH.qN_cast hα, CAH.delta]; push_cast; rw [CAH.pZ_cast]; ring
  rw [heq, abs_mul] at h
  have hd := (CAH.abs_delta_bounds hα s).2
  have hq := CAH.q_pos hα (s + 1)
  refine h.trans ?_
  rw [mul_div_assoc]
  have : |(l : ℝ)| * |CAH.delta α s| ≤ |(l : ℝ)| / CAH.q α (s + 1) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hd.le (abs_nonneg _)
  nlinarith [pi_pos]

/-- `|1 - e(lα)| ≥ 2/q_{j+1}` for `0 < |l| < q_{j+1}` (best approximation). -/
lemma two_div_le_norm_eT_sub_one {α : ℝ} (hα : Irrational α) (j : ℕ) (l : ℤ) (hl : l ≠ 0)
    (hl' : l.natAbs < CAH.qN α (j + 1)) :
    2 / CAH.q α (j + 1) ≤ ‖eT (l * α) - 1‖ := by
  have h1 := four_norm_le_norm_eT_sub_one ((l : ℝ) * α)
  have h2 := abs_delta_le_norm hα j l hl hl'
  have h3 := (CAH.abs_delta_bounds hα j).1
  have h4 := CAH.q_le_succ hα j
  have h5 := CAH.q_pos hα j
  have h6 : 1 / (2 * CAH.q α (j + 1)) ≤ 1 / (CAH.q α (j + 1) + CAH.q α j) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have : 2 / CAH.q α (j + 1) = 4 * (1 / (2 * CAH.q α (j + 1))) := by
    field_simp; norm_num
  rw [this]; linarith

/-- `|(1-e(q_{s₂} l α))/(1-e(lα))| ≤ π|l| q_{j+1}/q_{s₂+1}` for `0 < |l| < q_{j+1}`. -/
lemma norm_bmult_le_small {α : ℝ} (hα : Irrational α) (j s : ℕ) (l : ℤ) (hl : l ≠ 0)
    (hl' : l.natAbs < CAH.qN α (j + 1)) :
    ‖bmult α (CAH.qN α s) l‖ ≤ π * |(l : ℝ)| * CAH.q α (j + 1) / CAH.q α (s + 1) := by
  have hlow := two_div_le_norm_eT_sub_one hα j l hl hl'
  have hup := norm_eT_q_mul_sub_one_le hα s l
  have hm := bmult_mul α (CAH.qN α s) l
  have hq1 := CAH.q_pos hα (j + 1)
  have hq2 := CAH.q_pos hα (s + 1)
  have hprod : ‖bmult α (CAH.qN α s) l‖ * ‖eT (l * α) - 1‖ ≤ 2 * π * |(l : ℝ)| / CAH.q α (s + 1) := by
    rw [← norm_mul, hm]; exact hup
  have hpos : 0 < 2 / CAH.q α (j + 1) := by positivity
  have hb := norm_nonneg (bmult α (CAH.qN α s) l)
  have h3 : ‖bmult α (CAH.qN α s) l‖ * (2 / CAH.q α (j + 1)) ≤
      2 * π * |(l : ℝ)| / CAH.q α (s + 1) :=
    (mul_le_mul_of_nonneg_left hlow hb).trans hprod
  rw [show π * |(l : ℝ)| * CAH.q α (j + 1) / CAH.q α (s + 1) =
    (2 * π * |(l : ℝ)| / CAH.q α (s + 1)) / (2 / CAH.q α (j + 1)) by field_simp]
  rw [le_div_iff₀ hpos]; exact h3

/-! ### Geometric sums over `ℤ` and an elementary growth estimate -/

lemma hasSum_exp_neg_abs {b : ℝ} (hb : 0 < b) :
    HasSum (fun l : ℤ => Real.exp (-(b * |(l : ℝ)|)))
      ((1 - Real.exp (-b))⁻¹ + Real.exp (-b) * (1 - Real.exp (-b))⁻¹) := by
  have hr0 : 0 ≤ Real.exp (-b) := (Real.exp_pos _).le
  have hr1 : Real.exp (-b) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  apply HasSum.of_nat_of_neg_add_one
  · convert hasSum_geometric_of_lt_one hr0 hr1 using 1
    funext n
    rw [← Real.exp_nat_mul]; congr 1; push_cast
    rw [abs_of_nonneg (by positivity)]; ring
  · convert (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-b)) using 1
    funext n
    rw [← pow_succ', ← Real.exp_nat_mul]; congr 1; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]; ring

/-- `∑_{l ∈ ℤ} e^{-b|l|} ≤ 1 + 2/b`. -/
lemma summable_exp_neg_abs' {b : ℝ} (hb : 0 < b) :
    Summable (fun l : ℤ => Real.exp (-(b * |(l : ℝ)|))) ∧
      ∑' l : ℤ, Real.exp (-(b * |(l : ℝ)|)) ≤ 1 + 2 / b := by
  have H := hasSum_exp_neg_abs hb
  refine ⟨H.summable, ?_⟩
  rw [H.tsum_eq]
  set r := Real.exp (-b) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have key : b * r ≤ 1 - r := by
    have h1 := Real.add_one_le_exp b
    have h2 : Real.exp b * r = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  have h1r : 0 < 1 - r := by linarith
  rw [show (1 - r)⁻¹ + r * (1 - r)⁻¹ = 1 + 2 * (r / (1 - r)) by field_simp; ring]
  have : r / (1 - r) ≤ 1 / b := by
    rw [div_le_div_iff₀ h1r hb]; linarith
  have : 2 * (r / (1 - r)) ≤ 2 / b := by
    rw [show 2 / b = 2 * (1 / b) by ring]; linarith
  linarith

/-- `x^r e^{-bx}` is bounded on `[1, ∞)`. -/
lemma exists_rpow_mul_exp_neg_le {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → x ^ r * Real.exp (-(b * x)) ≤ C := by
  refine ⟨((⌈r⌉₊).factorial : ℝ) / b ^ ⌈r⌉₊, by positivity, fun x hx => ?_⟩
  set N := ⌈r⌉₊
  have h1 : x ^ r ≤ x ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil r)
  rw [Real.rpow_natCast] at h1
  have h2 := Real.pow_div_factorial_le_exp (b * x) (by positivity) N
  rw [div_le_iff₀ (by positivity), mul_pow] at h2
  have h3 : x ^ N * Real.exp (-(b * x)) ≤ (N.factorial : ℝ) / b ^ N := by
    rw [le_div_iff₀ (pow_pos hb N)]
    calc x ^ N * Real.exp (-(b * x)) * b ^ N = (b ^ N * x ^ N) * Real.exp (-(b * x)) := by ring
      _ ≤ (Real.exp (b * x) * N.factorial) * Real.exp (-(b * x)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = N.factorial * (Real.exp (b * x) * Real.exp (-(b * x))) := by ring
      _ = N.factorial := by rw [← Real.exp_add]; simp
  exact (mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)).trans h3

/-- `t e^{-ct} ≤ (2/c) e^{-ct/2}` for `c > 0`. -/
lemma mul_exp_neg_le {c t : ℝ} (hc : 0 < c) :
    t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (-(c / 2 * t)) := by
  have h1 : c / 2 * t ≤ Real.exp (c / 2 * t) := by linarith [Real.add_one_le_exp (c / 2 * t)]
  have h2 : t ≤ 2 / c * Real.exp (c / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  have h3 : Real.exp (c / 2 * t) * Real.exp (-(c * t)) = Real.exp (-(c / 2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (c / 2 * t) * Real.exp (-(c * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = 2 / c * Real.exp (-(c / 2 * t)) := by rw [mul_assoc, h3]

/-! ### Lemma `denjoy.el` -/

/-- Pointwise bound on the weighted coefficients of `S_{q_{s₂}}φ - q_{s₂}φ̂(0)`. -/
lemma term_bound {α : ℝ} (hα : Irrational α) {s₁ s₂ : ℕ} {h δ K c : ℝ} {a : ℤ → ℂ}
    (hc : c = 2 * π * h * δ) (hcpos : 0 < c)
    (hK : ∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) (l : ℤ) :
    ‖birkhoffCoeff α (CAH.qN α s₂) a l‖ * Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ))) ≤
      K * ((if 2 ≤ CAH.qN α s₁ then π * CAH.q α s₁ / CAH.q α (s₂ + 1) * (2 / c) else 0) +
        CAH.q α s₂ * Real.exp (-(c * CAH.q α s₁ / 2))) * Real.exp (-(c / 2 * |(l : ℝ)|)) := by
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hA0 : 0 ≤ (if 2 ≤ CAH.qN α s₁ then π * CAH.q α s₁ / CAH.q α (s₂ + 1) * (2 / c) else 0) := by
    have := CAH.q_pos hα s₁; have := CAH.q_pos hα (s₂ + 1)
    split_ifs <;> positivity
  have hB0 : 0 ≤ CAH.q α s₂ * Real.exp (-(c * CAH.q α s₁ / 2)) := by
    have := CAH.q_pos hα s₂; positivity
  by_cases hl : l = 0
  · simp only [hl, birkhoffCoeff, ite_true, norm_zero, zero_mul]
    positivity
  simp only [hl, birkhoffCoeff, ite_false, norm_mul]
  have hexp : Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ))) =
      Real.exp (2 * π * |(l : ℝ)| * h) * Real.exp (-(c * |(l : ℝ)|)) := by
    rw [← Real.exp_add, hc]; congr 1; ring
  rw [hexp]
  have hal := hK l hl
  have hm0 := norm_nonneg (bmult α (CAH.qN α s₂) l)
  -- it suffices to bound `‖bmult‖ e^{-c|l|}`
  suffices hs : ‖bmult α (CAH.qN α s₂) l‖ * Real.exp (-(c * |(l : ℝ)|)) ≤
      ((if 2 ≤ CAH.qN α s₁ then π * CAH.q α s₁ / CAH.q α (s₂ + 1) * (2 / c) else 0) +
        CAH.q α s₂ * Real.exp (-(c * CAH.q α s₁ / 2))) * Real.exp (-(c / 2 * |(l : ℝ)|)) by
    calc ‖a l‖ * ‖bmult α (CAH.qN α s₂) l‖ *
          (Real.exp (2 * π * |(l : ℝ)| * h) * Real.exp (-(c * |(l : ℝ)|)))
        = (‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h)) *
          (‖bmult α (CAH.qN α s₂) l‖ * Real.exp (-(c * |(l : ℝ)|))) := by ring
      _ ≤ K * (‖bmult α (CAH.qN α s₂) l‖ * Real.exp (-(c * |(l : ℝ)|))) :=
          mul_le_mul_of_nonneg_right hal (by positivity)
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs hK0
  have hE := Real.exp_nonneg (-(c / 2 * |(l : ℝ)|))
  by_cases hsmall : l.natAbs < CAH.qN α s₁
  · -- small frequencies: use the small divisor estimate
    have h2 : 2 ≤ CAH.qN α s₁ := by
      have : 1 ≤ l.natAbs := Int.natAbs_pos.2 hl
      omega
    obtain ⟨j, rfl⟩ : ∃ j, s₁ = j + 1 := by
      rcases s₁ with _ | j
      · rw [qN_zero] at h2; omega
      · exact ⟨j, rfl⟩
    have hb := norm_bmult_le_small hα j s₂ l hl hsmall
    have hq2 := CAH.q_pos hα (s₂ + 1)
    have hq1 := CAH.q_pos hα (j + 1)
    have hme := mul_exp_neg_le (t := |(l : ℝ)|) hcpos
    simp only [h2, ite_true]
    calc ‖bmult α (CAH.qN α s₂) l‖ * Real.exp (-(c * |(l : ℝ)|))
        ≤ π * |(l : ℝ)| * CAH.q α (j + 1) / CAH.q α (s₂ + 1) * Real.exp (-(c * |(l : ℝ)|)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = π * CAH.q α (j + 1) / CAH.q α (s₂ + 1) * (|(l : ℝ)| * Real.exp (-(c * |(l : ℝ)|))) := by
          ring
      _ ≤ π * CAH.q α (j + 1) / CAH.q α (s₂ + 1) * (2 / c * Real.exp (-(c / 2 * |(l : ℝ)|))) :=
          mul_le_mul_of_nonneg_left hme (by positivity)
      _ ≤ _ := by nlinarith
  · -- large frequencies: trivial bound `|bmult| ≤ q_{s₂}`
    have hb := norm_bmult_le α (CAH.qN α s₂) l
    rw [CAH.qN_cast hα] at hb
    have hQl : CAH.q α s₁ ≤ |(l : ℝ)| := by
      have h1 : (CAH.qN α s₁ : ℤ) ≤ |l| := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast not_lt.1 hsmall
      rw [← CAH.qN_cast hα]
      have h2 := (Int.cast_le (R := ℝ)).2 h1
      push_cast at h2; exact h2
    have he : Real.exp (-(c * |(l : ℝ)|)) ≤
        Real.exp (-(c * CAH.q α s₁ / 2)) * Real.exp (-(c / 2 * |(l : ℝ)|)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    calc ‖bmult α (CAH.qN α s₂) l‖ * Real.exp (-(c * |(l : ℝ)|))
        ≤ CAH.q α s₂ * (Real.exp (-(c * CAH.q α s₁ / 2)) * Real.exp (-(c / 2 * |(l : ℝ)|))) :=
          mul_le_mul hb he (Real.exp_nonneg _) (CAH.q_pos hα s₂).le
      _ ≤ _ := by nlinarith

lemma small_freq_factor {c κ s P : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (hcinv : 1 / c ≤ κ * s ^ 2) :
    P * (2 / c) * (1 + 2 / (c / 2)) ≤ 2 * κ * (1 + 4 * κ) * s ^ 4 * P := by
  have e1 : P * (2 / c) * (1 + 2 / (c / 2)) = 2 * P * ((1 / c) * (1 + 4 * (1 / c))) := by
    field_simp; ring
  rw [e1]
  have hc1 : 0 ≤ 1 / c := by positivity
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h1 : 1 + 4 * (1 / c) ≤ (1 + 4 * κ) * s ^ 2 := by nlinarith
  have e2 : (1 / c) * (1 + 4 * (1 / c)) ≤ (κ * s ^ 2) * ((1 + 4 * κ) * s ^ 2) :=
    mul_le_mul hcinv h1 (by positivity) (by positivity)
  have e3 : 2 * P * ((1 / c) * (1 + 4 * (1 / c))) ≤ 2 * P * ((κ * s ^ 2) * ((1 + 4 * κ) * s ^ 2)) :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  calc _ ≤ 2 * P * ((κ * s ^ 2) * ((1 + 4 * κ) * s ^ 2)) := e3
    _ = _ := by rw [hs4]; ring

lemma large_freq_factor {c b x Q U C₂ q : ℝ} (hc : 0 < c) (hb : 0 < b) (hx1 : 1 ≤ x)
    (hxQ : x ^ 2 = Q) (hq : 0 ≤ q) (hinv : 1 / c ≤ x / (2 * b))
    (hC₂b : x ^ (2 * U + 1) * Real.exp (-(b * x)) ≤ C₂) :
    q * Real.exp (-(c * Q / 2)) * (1 + 2 / (c / 2)) ≤ (1 + 2 / b) * C₂ * (q / Q ^ U) := by
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by rw [← hxQ]; positivity
  have hQU : 0 < Q ^ U := Real.rpow_pos_of_pos hQ0 U
  have hcQ : b * x ≤ c * Q / 2 := by
    rw [div_le_div_iff₀ hc (by positivity)] at hinv
    rw [← hxQ]; nlinarith
  have hE : Real.exp (-(c * Q / 2)) ≤ Real.exp (-(b * x)) := Real.exp_le_exp.2 (by linarith)
  have hF : 1 + 2 / (c / 2) ≤ (1 + 2 / b) * x := by
    have e : 2 / (c / 2) = 4 * (1 / c) := by field_simp; ring
    have e2 : 4 * (x / (2 * b)) = 2 / b * x := by field_simp; ring
    rw [e]; nlinarith
  have hpow : x * Real.exp (-(b * x)) ≤ C₂ / Q ^ U := by
    rw [le_div_iff₀ hQU]
    have h7 : x ^ (2 * U + 1) = Q ^ U * x := by
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le, ← hxQ]
      norm_num
    rw [h7] at hC₂b; nlinarith
  calc q * Real.exp (-(c * Q / 2)) * (1 + 2 / (c / 2))
      ≤ q * Real.exp (-(b * x)) * ((1 + 2 / b) * x) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hE hq) hF (by positivity) (by positivity)
    _ = (1 + 2 / b) * q * (x * Real.exp (-(b * x))) := by ring
    _ ≤ (1 + 2 / b) * q * (C₂ / Q ^ U) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (1 + 2 / b) * C₂ * (q / Q ^ U) := by ring

/-- **Lemma `denjoy.el`** (coefficient form).  Let `h_*, η > 0` and `U ∈ ℝ`.  There is
`C = C(h_*, η, U) > 0` such that for every irrational `α`, every pair of denominators
`q_{s₁} ≤ q_{s₂}`, every `h ≥ h_*`, every `δ ≥ max(1/√q_{s₁}, η/(10 s₂²))` and every
`φ̂ : ℤ → ℂ` with `|φ̂(l)| e^{2π|l|h} ≤ K` for `l ≠ 0`, the coefficients of
`S_{q_{s₂}}φ - q_{s₂}φ̂(0)` satisfy
`∑_l |coeff(l)| e^{2π|l|h(1-δ)} ≤ C K (s₂⁴ q_{s₁}/q_{s₂+1} + q_{s₂}/q_{s₁}^U)`
(and the weighted series converges).  By `norm_fourierC_le_wnorm` and `birkhoff_fourier` the
left side dominates `sup_{|Im z| ≤ h(1-δ)} |S_{q_{s₂}}φ(z) - q_{s₂}φ̂(0)|`. -/
theorem denjoy_el {hstar η : ℝ} (hh : 0 < hstar) (hη : 0 < η) (U : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, Irrational α → ∀ s₁ s₂ : ℕ, CAH.q α s₁ ≤ CAH.q α s₂ →
      ∀ (h δ K : ℝ) (a : ℤ → ℂ), hstar ≤ h →
      1 / Real.sqrt (CAH.q α s₁) ≤ δ → η / (10 * (s₂ : ℝ) ^ 2) ≤ δ →
      (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
      Summable (fun l : ℤ => ‖birkhoffCoeff α (CAH.qN α s₂) a l‖ *
          Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ)))) ∧
      wnorm (birkhoffCoeff α (CAH.qN α s₂) a) (h * (1 - δ)) ≤
        C * K * ((s₂ : ℝ) ^ 4 * CAH.q α s₁ / CAH.q α (s₂ + 1) +
          CAH.q α s₂ / CAH.q α s₁ ^ U) := by
  obtain ⟨C₂, hC₂, hC₂b⟩ := exists_rpow_mul_exp_neg_le (b := π * hstar) (by positivity) (2 * U + 1)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 5 / (π * hstar * η) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hC₁0 : 0 < 2 * κ * (1 + 4 * κ) * π := by positivity
  have hC₃0 : 0 < (1 + 2 / (π * hstar)) * C₂ := by positivity
  refine ⟨2 * κ * (1 + 4 * κ) * π + (1 + 2 / (π * hstar)) * C₂, by positivity, ?_⟩
  intro α hα s₁ s₂ hq h δ K a hh' hδ1 hδ2 hK
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hQ1 : 1 ≤ CAH.q α s₁ := CAH.q_one_le hα s₁
  obtain ⟨x, hx⟩ : ∃ x, x = Real.sqrt (CAH.q α s₁) := ⟨_, rfl⟩
  rw [← hx] at hδ1
  have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_sqrt.2 hQ1
  have hx0 : 0 < x := by linarith
  have hxQ : x ^ 2 = CAH.q α s₁ := by rw [hx]; exact Real.sq_sqrt (by linarith)
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ1
  have hhpos : 0 < h := by linarith
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * π * h * δ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  have hq2 := CAH.q_pos hα s₂
  have hq3 := CAH.q_pos hα (s₂ + 1)
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = (if 2 ≤ CAH.qN α s₁ then
      π * CAH.q α s₁ / CAH.q α (s₂ + 1) * (2 / c) else 0) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = CAH.q α s₂ * Real.exp (-(c * CAH.q α s₁ / 2)) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A' := by rw [hA']; split_ifs <;> positivity
  have hB0 : 0 ≤ B' := by rw [hB']; positivity
  have hterm := term_bound (s₁ := s₁) (s₂ := s₂) hα hc hcpos hK
  rw [← hA', ← hB'] at hterm
  obtain ⟨hsum, hle⟩ := summable_exp_neg_abs' (b := c / 2) (by positivity)
  have hg : Summable (fun l : ℤ => K * (A' + B') * Real.exp (-(c / 2 * |(l : ℝ)|))) :=
    hsum.mul_left _
  have hS : Summable (fun l : ℤ => ‖birkhoffCoeff α (CAH.qN α s₂) a l‖ *
      Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ)))) :=
    Summable.of_nonneg_of_le (fun l => by positivity) hterm hg
  refine ⟨hS, ?_⟩
  have h1 : wnorm (birkhoffCoeff α (CAH.qN α s₂) a) (h * (1 - δ)) ≤
      K * (A' + B') * (1 + 2 / (c / 2)) := by
    unfold wnorm
    refine (Summable.tsum_le_tsum hterm hS hg).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  obtain ⟨T₁, hT₁⟩ : ∃ T, T = (s₂ : ℝ) ^ 4 * CAH.q α s₁ / CAH.q α (s₂ + 1) := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T, T = CAH.q α s₂ / CAH.q α s₁ ^ U := ⟨_, rfl⟩
  rw [← hT₁, ← hT₂]
  have hT₁0 : 0 ≤ T₁ := by rw [hT₁]; positivity
  have hQU : 0 < CAH.q α s₁ ^ U := Real.rpow_pos_of_pos (by linarith) U
  have hT₂0 : 0 ≤ T₂ := by rw [hT₂]; positivity
  have hinv : 1 / c ≤ x / (2 * (π * hstar)) := by
    rw [div_le_div_iff₀ hcpos (by positivity)]
    have h3 : 1 ≤ δ * x := by
      have := mul_le_mul_of_nonneg_right hδ1 hx0.le
      rwa [one_div, inv_mul_cancel₀ hx0.ne'] at this
    have h4 : hstar * 1 ≤ h * (δ * x) := mul_le_mul hh' h3 zero_le_one hhpos.le
    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * π by positivity)
    rw [hc]; nlinarith
  have hA : A' * (1 + 2 / (c / 2)) ≤ (2 * κ * (1 + 4 * κ) * π) * T₁ := by
    rw [hA']
    split_ifs with h2
    · have hs2 : 1 ≤ s₂ := by
        rcases Nat.eq_zero_or_pos s₂ with h0 | h0
        · exfalso
          have h3 : (2 : ℝ) ≤ CAH.q α s₁ := by rw [← CAH.qN_cast hα]; exact_mod_cast h2
          rw [h0, q_zero] at hq; linarith
        · exact h0
      have hs2r : (1 : ℝ) ≤ s₂ := by exact_mod_cast hs2
      have hcinv : 1 / c ≤ κ * (s₂ : ℝ) ^ 2 := by
        rw [div_le_iff₀ hcpos]
        have h10 : η ≤ δ * (10 * (s₂ : ℝ) ^ 2) := by
          rwa [div_le_iff₀ (by positivity)] at hδ2
        rw [hκ, hc, show 5 / (π * hstar * η) * (s₂ : ℝ) ^ 2 * (2 * π * h * δ) =
          (h * (δ * (10 * (s₂ : ℝ) ^ 2))) / (hstar * η) by field_simp; ring]
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul hh' h10 hη.le hhpos.le
        linarith
      have := small_freq_factor hcpos hκ0 hs2r
        (show 0 ≤ π * CAH.q α s₁ / CAH.q α (s₂ + 1) by positivity) hcinv
      refine this.trans (le_of_eq ?_)
      rw [hT₁]; ring
    · simp only [zero_mul]; positivity
  have hB : B' * (1 + 2 / (c / 2)) ≤ ((1 + 2 / (π * hstar)) * C₂) * T₂ := by
    rw [hB', hT₂]
    exact large_freq_factor hcpos (by positivity) hx1 hxQ hq2.le hinv (hC₂b x hx1)
  calc wnorm (birkhoffCoeff α (CAH.qN α s₂) a) (h * (1 - δ))
      ≤ K * (A' + B') * (1 + 2 / (c / 2)) := h1
    _ = K * (A' * (1 + 2 / (c / 2)) + B' * (1 + 2 / (c / 2))) := by ring
    _ ≤ K * ((2 * κ * (1 + 4 * κ) * π) * T₁ + ((1 + 2 / (π * hstar)) * C₂) * T₂) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hK0
    _ ≤ _ := by nlinarith [mul_nonneg hK0 hT₁0, mul_nonneg hK0 hT₂0]

/-! ## Lemma `dioph.bridge`: the subsequence `(Q_k)` -/

section Bridge

variable (α : ℝ)

/-- `CD(a,b,c)` bridges (paper, Definition before Lemma `dioph.bridge`): the pair of
denominators `(q_l, q_n)` forms a `CD(a,b,c)` bridge if `q_{i+1} ≤ q_i^a` for `l ≤ i < n` and
`q_l^b ≤ q_n ≤ q_l^c`. -/
def IsCDBridge (a b c : ℝ) (l n : ℕ) : Prop :=
  (∀ i, l ≤ i → i < n → CAH.q α (i + 1) ≤ CAH.q α i ^ a) ∧
    CAH.q α l ^ b ≤ CAH.q α n ∧ CAH.q α n ≤ CAH.q α l ^ c

/-- `log q_i`. -/
noncomputable def Lq (i : ℕ) : ℝ := Real.log (CAH.q α i)

variable {α}

lemma Lq_nonneg (hα : Irrational α) (i : ℕ) : 0 ≤ Lq α i :=
  Real.log_nonneg (CAH.q_one_le hα i)

lemma Lq_zero : Lq α 0 = 0 := by simp [Lq, q_zero]

lemma q_mono (hα : Irrational α) : Monotone (CAH.q α) :=
  monotone_nat_of_le_succ (CAH.q_le_succ hα)

lemma Lq_mono (hα : Irrational α) {i j : ℕ} (hij : i ≤ j) : Lq α i ≤ Lq α j :=
  Real.log_le_log (CAH.q_pos hα i) (q_mono hα hij)

lemma lt_of_Lq_lt (hα : Irrational α) {i j : ℕ} (h : Lq α i < Lq α j) : i < j := by
  by_contra hc; push Not at hc; linarith [Lq_mono hα hc]

lemma Lq_unbounded (hα : Irrational α) (T : ℝ) : ∃ i, T ≤ Lq α i := by
  refine ⟨⌈Real.exp T⌉₊ + 1, ?_⟩
  have h1 := le_qN_succ hα ⌈Real.exp T⌉₊
  have h2 : Real.exp T ≤ CAH.q α (⌈Real.exp T⌉₊ + 1) := by
    rw [← CAH.qN_cast hα]
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) h2

lemma rpow_le_iff_log {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ a ≤ y ↔ a * Real.log x ≤ Real.log y := by
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx a) hy, Real.log_rpow hx]

lemma le_rpow_iff_log {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y ≤ x ^ a ↔ Real.log y ≤ a * Real.log x := by
  rw [← Real.log_le_log_iff hy (Real.rpow_pos_of_pos hx a), Real.log_rpow hx]

variable (α)

/-- Small jump at `i` (log form of `q_{i+1} ≤ q_i^A`). -/
def SJ (A : ℝ) (i : ℕ) : Prop := Lq α (i + 1) ≤ A * Lq α i

/-- Big jump at `i` (log form of `q_i^A ≤ q_{i+1}`). -/
def BJ (A : ℝ) (i : ℕ) : Prop := A * Lq α i ≤ Lq α (i + 1)

/-- Log form of a `CD(A, A, A⁴)` bridge. -/
def Br (A : ℝ) (x y : ℕ) : Prop :=
  (∀ i, x ≤ i → i < y → SJ α A i) ∧ A * Lq α x ≤ Lq α y ∧ Lq α y ≤ A ^ 4 * Lq α x

/-- Chains of bridges from `x` to `n` (each intermediate point `y` with predecessor `x`
satisfies `Br x y` and `Br (x+1) y`). -/
inductive Reach (A : ℝ) : ℕ → ℕ → Prop
  | last {x n : ℕ} : Br α A x n → Br α A (x + 1) n → Reach A x n
  | cons {x y n : ℕ} : Br α A x y → Br α A (x + 1) y → Reach A y n → Reach A x n

variable {α}

lemma isCDBridge_iff (hα : Irrational α) (A : ℝ) (x y : ℕ) :
    IsCDBridge α A A (A ^ 4) x y ↔ Br α A x y := by
  have hp := CAH.q_pos hα
  simp only [IsCDBridge, Br, SJ, Lq]
  refine and_congr (forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ =>
    le_rpow_iff_log (hp _) (hp _)) (and_congr (rpow_le_iff_log (hp _) (hp _))
      (le_rpow_iff_log (hp _) (hp _)))

lemma Reach.snoc {A : ℝ} {x w z : ℕ} (h : Reach α A x w) (h1 : Br α A w z)
    (h2 : Br α A (w + 1) z) : Reach α A x z := by
  induction h with
  | last hb hb' => exact Reach.cons hb hb' (Reach.last h1 h2)
  | cons hb hb' _ ih => exact Reach.cons hb hb' (ih h1 h2)

/-- **Backward greedy construction** of a chain of `CD(A,A,A⁴)` bridges ending at `z`. -/
lemma back_chain (hα : Irrational α) {A : ℝ} (hA : 1 < A) {m n : ℕ} (hm : 0 < Lq α m)
    (hsj : ∀ i, m ≤ i → i < n → SJ α A i) :
    ∀ z, z ≤ n → A ^ 4 * Lq α m < Lq α z → ∃ y, Br α A m y ∧ Reach α A y z := by
  have hA0 : 0 < A := by linarith
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA.le
  have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hA.le
  have hA4 : 1 ≤ A ^ 4 := one_le_pow₀ hA.le
  have hLnn := Lq_nonneg hα
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
  intro hzn hz
  have hzpos : 0 < Lq α z := by nlinarith
  have hmz : m < z := by
    by_contra hc; push Not at hc
    have := Lq_mono hα hc
    nlinarith
  -- the predicate defining the predecessor
  let P : ℕ → Prop := fun w => m ≤ w ∧ A * Lq α (w + 1) ≤ Lq α z
  have hPm : P m := by
    refine ⟨le_rfl, ?_⟩
    have h1 := hsj m le_rfl (by omega)
    unfold SJ at h1
    have : A * Lq α (m + 1) ≤ A * (A * Lq α m) := mul_le_mul_of_nonneg_left h1 hA0.le
    have : A * (A * Lq α m) ≤ A ^ 4 * Lq α m := by
      have : A * A ≤ A ^ 4 := by nlinarith
      nlinarith
    linarith
  set w := Nat.findGreatest P (z - 1) with hw
  have hPw : P w := Nat.findGreatest_spec (P := P) (show m ≤ z - 1 by omega) hPm
  have hmw : m ≤ w := Nat.le_findGreatest (show m ≤ z - 1 by omega) hPm
  have hwz : w ≤ z - 1 := Nat.findGreatest_le (z - 1)
  have hw1 : w + 1 < z := by
    by_contra hc
    have : w + 1 = z := by omega
    have h2 := hPw.2
    rw [this] at h2
    nlinarith
  have hnot : ¬ P (w + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := z - 1) (k := w + 1) (by omega) (by omega)
  have hlt : Lq α z < A * Lq α (w + 2) := by
    by_contra hc; push Not at hc; exact hnot ⟨by omega, hc⟩
  have hs1 := hsj (w + 1) (by omega) (by omega)
  have hs0 := hsj w hmw (by omega)
  unfold SJ at hs1 hs0
  have hLw := hLnn w
  have hLw1 := hLnn (w + 1)
  have hzw1 : Lq α z < A ^ 2 * Lq α (w + 1) := by
    have := mul_le_mul_of_nonneg_left hs1 hA0.le
    nlinarith
  have hzw : Lq α z < A ^ 3 * Lq α w := by
    have := mul_le_mul_of_nonneg_left hs0 (show 0 ≤ A ^ 2 by positivity)
    nlinarith
  have hmono := Lq_mono hα (Nat.le_succ w)
  have hsjwz : ∀ i, w ≤ i → i < z → SJ α A i := fun i hi hi' => hsj i (by omega) (by omega)
  have hBr1 : Br α A w z := by
    refine ⟨hsjwz, ?_, ?_⟩
    · nlinarith [hPw.2]
    · nlinarith
  have hBr2 : Br α A (w + 1) z := by
    refine ⟨fun i hi hi' => hsjwz i (by omega) hi', hPw.2, ?_⟩
    nlinarith
  by_cases hcase : Lq α w ≤ A ^ 4 * Lq α m
  · refine ⟨w, ⟨fun i hi hi' => hsj i hi (by omega), ?_, hcase⟩, Reach.last hBr1 hBr2⟩
    -- `A^3 (A L m) = A^4 L m < L z < A^3 L w`
    have h3 : A ^ 3 * (A * Lq α m) < A ^ 3 * Lq α w := by
      have : A ^ 3 * (A * Lq α m) = A ^ 4 * Lq α m := by ring
      linarith
    exact (lt_of_mul_lt_mul_left h3 (by positivity)).le
  · push Not at hcase
    obtain ⟨y, hy1, hy2⟩ := ih w (by omega) (by omega) hcase
    exact ⟨y, hy1, hy2.snoc hBr1 hBr2⟩

/-- **Forward greedy step** (when there are no big jumps after `m`). -/
lemma forward_step (hα : Irrational α) {A : ℝ} (hA : 1 < A) {m : ℕ} (hm : 0 < Lq α m)
    (hsj : ∀ i, m ≤ i → SJ α A i) :
    ∃ y, m < y ∧ Br α A m y ∧ Lq α y ≤ A ^ 2 * Lq α m := by
  classical
  have hA0 : 0 < A := by linarith
  have hex : ∃ y, A * Lq α m ≤ Lq α y := Lq_unbounded hα _
  set y := Nat.find hex with hy
  have hyspec : A * Lq α m ≤ Lq α y := Nat.find_spec hex
  have hmy : m < y := lt_of_Lq_lt hα (by nlinarith)
  have hprev : Lq α (y - 1) < A * Lq α m := by
    have := Nat.find_min hex (show y - 1 < y by omega)
    push Not at this; exact this
  have hs := hsj (y - 1) (by omega)
  unfold SJ at hs
  rw [show y - 1 + 1 = y by omega] at hs
  have hyle : Lq α y ≤ A ^ 2 * Lq α m := by
    have := mul_le_mul_of_nonneg_left hprev.le hA0.le
    nlinarith
  refine ⟨y, hmy, ⟨fun i hi _ => hsj i hi, hyspec, ?_⟩, hyle⟩
  have : A ^ 2 ≤ A ^ 4 := pow_le_pow_right₀ hA.le (by norm_num)
  nlinarith [Lq_nonneg hα m]

variable (α)

/-- The invariant carried along the construction of `(Q_k)`: the current index is a big jump,
or it starts a finite chain of bridges ending at a big jump, or there are no big jumps after it. -/
def Inv (A : ℝ) (x : ℕ) : Prop :=
  BJ α A x ∨ (0 < Lq α x ∧ ∃ n, BJ α A n ∧ Reach α A x n) ∨
    (0 < Lq α x ∧ ∀ i, x ≤ i → SJ α A i)

/-- The step relation between consecutive terms `x = n_k`, `y = n_{k+1}`. -/
def Step (A : ℝ) (x y : ℕ) : Prop :=
  x < y ∧ Lq α y ≤ A ^ 4 * Lq α (x + 1) ∧ (BJ α A y ∨ Br α A (x + 1) y) ∧
    (BJ α A x ∨ Br α A x y) ∧ (∀ i, x + 1 ≤ i → i < y → SJ α A i)

variable {α}

lemma pos_of_Br (hα : Irrational α) {A : ℝ} (hA : 1 < A) {x y : ℕ} (hx : 0 < Lq α x)
    (h : Br α A x y) : x < y ∧ 0 < Lq α y := by
  have : Lq α x < Lq α y := by nlinarith [h.2.1]
  exact ⟨lt_of_Lq_lt hα this, by linarith⟩

lemma step_exists (hα : Irrational α) {A : ℝ} (hA : 1 < A) {x : ℕ} (hx : Inv α A x) :
    ∃ y, Step α A x y ∧ Inv α A y := by
  classical
  have hA0 : 0 < A := by linarith
  have hA4 : 1 ≤ A ^ 4 := one_le_pow₀ hA.le
  have hLnn := Lq_nonneg hα
  rcases hx with hbj | ⟨hxpos, n, hbn, hR⟩ | ⟨hxpos, hsj⟩
  · -- `x` is a big jump
    by_cases hbm : BJ α A (x + 1)
    · refine ⟨x + 1, ⟨by omega, by nlinarith [hLnn (x + 1)], Or.inl hbm, Or.inl hbj,
        fun i hi hi' => by omega⟩,
        Or.inl hbm⟩
    have hmpos : 0 < Lq α (x + 1) := by
      unfold BJ at hbm; push Not at hbm
      have := Lq_mono hα (Nat.le_succ (x + 1))
      by_contra hc; push Not at hc
      nlinarith
    by_cases hex : ∃ n, x + 1 ≤ n ∧ BJ α A n
    · set n := Nat.find hex with hn
      obtain ⟨hmn, hbn⟩ := Nat.find_spec hex
      have hsj : ∀ i, x + 1 ≤ i → i < n → SJ α A i := by
        intro i hi hi'
        have := Nat.find_min hex hi'
        have hb : ¬ BJ α A i := fun hb => this ⟨hi, hb⟩
        unfold BJ at hb; unfold SJ; push Not at hb; exact hb.le
      by_cases hsmall : Lq α n ≤ A ^ 4 * Lq α (x + 1)
      · have hxn : x < n := by omega
        exact ⟨n, ⟨hxn, hsmall, Or.inl hbn, Or.inl hbj, hsj⟩, Or.inl hbn⟩
      · push Not at hsmall
        obtain ⟨y, hy1, hy2⟩ := back_chain hα hA hmpos hsj n le_rfl hsmall
        obtain ⟨hxy, hypos⟩ := pos_of_Br hα hA hmpos hy1
        exact ⟨y, ⟨by omega, hy1.2.2, Or.inr hy1, Or.inl hbj, hy1.1⟩, Or.inr (Or.inl ⟨hypos, n, hbn, hy2⟩)⟩
    · push Not at hex
      have hsj : ∀ i, x + 1 ≤ i → SJ α A i := by
        intro i hi
        have hb : ¬ BJ α A i := hex i hi
        unfold BJ at hb; unfold SJ; push Not at hb; exact hb.le
      obtain ⟨y, hxy, hBr, -⟩ := forward_step hα hA hmpos hsj
      obtain ⟨-, hypos⟩ := pos_of_Br hα hA hmpos hBr
      refine ⟨y, ⟨by omega, hBr.2.2, Or.inr hBr, Or.inl hbj, hBr.1⟩, Or.inr (Or.inr ⟨hypos, ?_⟩)⟩
      intro i hi; exact hsj i (by omega)
  · -- `x` is on a chain of bridges towards the big jump `n`
    cases hR with
    | last h1 h2 =>
      obtain ⟨hxn, -⟩ := pos_of_Br hα hA hxpos h1
      exact ⟨n, ⟨hxn, h2.2.2, Or.inl hbn, Or.inr h1, h2.1⟩, Or.inl hbn⟩
    | cons h1 h2 h3 =>
      rename_i y
      obtain ⟨hxy, hypos⟩ := pos_of_Br hα hA hxpos h1
      exact ⟨y, ⟨hxy, h2.2.2, Or.inr h2, Or.inr h1, h2.1⟩, Or.inr (Or.inl ⟨hypos, n, hbn, h3⟩)⟩
  · -- no big jumps after `x`
    have hmpos : 0 < Lq α (x + 1) := lt_of_lt_of_le hxpos (Lq_mono hα (Nat.le_succ x))
    obtain ⟨y, hxy, hBr, hyle⟩ :=
      forward_step hα hA hmpos (fun i hi => hsj i (by omega))
    obtain ⟨-, hypos⟩ := pos_of_Br hα hA hmpos hBr
    have hsx := hsj x le_rfl
    unfold SJ at hsx
    have hBrx : Br α A x y := by
      refine ⟨fun i hi _ => hsj i hi, ?_, ?_⟩
      · have := hBr.2.1
        have := Lq_mono hα (Nat.le_succ x)
        nlinarith
      · have h1 : A ^ 2 * Lq α (x + 1) ≤ A ^ 2 * (A * Lq α x) :=
          mul_le_mul_of_nonneg_left hsx (by positivity)
        have h2 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA.le (by norm_num)
        have h3 : A ^ 3 * Lq α x ≤ A ^ 4 * Lq α x := mul_le_mul_of_nonneg_right h2 (hLnn x)
        nlinarith
    refine ⟨y, ⟨by omega, hBr.2.2, Or.inr hBr, Or.inr hBrx, hBr.1⟩, Or.inr (Or.inr ⟨hypos, ?_⟩)⟩
    intro i hi; exact hsj i (by omega)

/-- Dependent choice along `ℕ`. -/
lemma exists_seq_of_step {β : Type*} {I : β → Prop} {R : β → β → Prop} (x₀ : β) (h₀ : I x₀)
    (hstep : ∀ x, I x → ∃ y, R x y ∧ I y) : ∃ f : ℕ → β, f 0 = x₀ ∧ ∀ k, R (f k) (f (k + 1)) := by
  let g : ℕ → {x // I x} := fun k => Nat.rec ⟨x₀, h₀⟩
    (fun _ p => ⟨Classical.choose (hstep p.1 p.2), (Classical.choose_spec (hstep p.1 p.2)).2⟩) k
  exact ⟨fun k => (g k).1, rfl, fun k => (Classical.choose_spec (hstep (g k).1 (g k).2)).1⟩

/-- **Lemma `dioph.bridge`** (corrected form).  For every `A > 1` and irrational `α` there is a
strictly increasing sequence of indices `n_k` with `n_0 = 0` (so `Q_0 = q_0 = 1`), writing
`Q_k = q_{n_k}`, `Q̄_k = q_{n_k+1}`:
* `Q_{k+1} ≤ Q̄_k^{A⁴}`;
* `q_{i+1} ≤ q_i^A` for `n_k < i < n_{k+1}` (used "by construction" in Corollary `cor4`);
* either `Q̄_k ≥ Q_k^A`, or `k > 0` and both `(Q̄_{k-1}, Q_k)` and `(Q_k, Q_{k+1})` are
  `CD(A, A, A⁴)` bridges.

**Deviation from the paper.**  The paper claims `CD(A, A, A³)` bridges.  This is false in
general: take `A = 2` and denominators with `log q_{m+i} ≈ L·2^{e_i/3}`,
`e = (0, 2, 4.9, 7.8, 9.8, 12.7, 15.6, 17.6)` (`L` large), preceded by a huge jump
`q_m ≫ q_{m-1}` and followed by a big jump at `m+7`; all steps in between satisfy
`q_{i+1} < q_i^2`.  Then `Q_k = q_{m-1}` is forced, the next big jump
`q_{m+7} ≈ q_m^{58} > Q̄_k^{16}` cannot be `Q_{k+1}`, and a direct
check of the windows `[A log q_{x+1}, A³ log q_x]` shows that no chain of `CD(2,2,8)` bridges
from `Q̄_k = q_m` reaches `q_{m+7}`.  (The paper's proof also over-requires the bridge
`(q_{n_0+1}, q_{n_1})` at the first step.)  With upper exponent `A⁴` the backward greedy
construction `back_chain` always works.  Downstream, only the fact that the upper exponent is a
fixed power of `A` matters; we compensate by taking `U = A⁵` in `cor3`, `cor4`, `denjoy`. -/
theorem dioph_bridge (hα : Irrational α) {A : ℝ} (hA : 1 < A) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ n 0 = 0 ∧ ∀ k : ℕ,
      CAH.q α (n (k + 1)) ≤ CAH.q α (n k + 1) ^ (A ^ 4) ∧
      (∀ i, n k + 1 ≤ i → i < n (k + 1) → CAH.q α (i + 1) ≤ CAH.q α i ^ A) ∧
      (CAH.q α (n k) ^ A ≤ CAH.q α (n k + 1) ∨
        (0 < k ∧ IsCDBridge α A A (A ^ 4) (n (k - 1) + 1) (n k) ∧
          IsCDBridge α A A (A ^ 4) (n k) (n (k + 1)))) := by
  have h0 : Inv α A 0 := Or.inl (by unfold BJ; rw [Lq_zero, mul_zero]; exact Lq_nonneg hα 1)
  obtain ⟨n, hn0, hstep⟩ := exists_seq_of_step (R := Step α A) 0 h0
    (fun x hx => step_exists hα hA hx)
  have hp := CAH.q_pos hα
  have hBJ : ∀ k, BJ α A (n k) → CAH.q α (n k) ^ A ≤ CAH.q α (n k + 1) := fun k h =>
    (rpow_le_iff_log (hp _) (hp _)).2 h
  refine ⟨n, strictMono_nat_of_lt_succ (fun k => (hstep k).1), hn0, fun k => ⟨?_, ?_, ?_⟩⟩
  · exact (le_rpow_iff_log (hp _) (hp _)).2 (hstep k).2.1
  · exact fun i hi hi' => (le_rpow_iff_log (hp _) (hp _)).2 ((hstep k).2.2.2.2 i hi hi')
  · rcases k with _ | j
    · left; apply hBJ; rw [hn0]; unfold BJ; rw [Lq_zero, mul_zero]; exact Lq_nonneg hα 1
    · rcases (hstep j).2.2.1 with h | h
      · exact Or.inl (hBJ _ h)
      rcases (hstep (j + 1)).2.2.2.1 with h' | h'
      · exact Or.inl (hBJ _ h')
      right
      refine ⟨Nat.succ_pos j, ?_, ?_⟩
      · rw [isCDBridge_iff hα]; simpa using h
      · rw [isCDBridge_iff hα]; exact h'

end Bridge

/-! ## Asymptotic bookkeeping -/

section Asymptotics

variable {α : ℝ}

/-- `n ≤ 1 + 3 log q_n` (the denominators grow at least geometrically). -/
lemma idx_le_log (hα : Irrational α) (n : ℕ) : (n : ℝ) ≤ 1 + 3 * Real.log (CAH.q α n) := by
  have h := CAH.two_rpow_le_q hα n
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_rpow (by norm_num)] at hl
  have h2 := Real.log_two_gt_d9
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.log_nonneg (CAH.q_one_le hα 0); simp; linarith
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 0 ≤ ((n : ℝ) - 1) * (Real.log 2 / 2 - 1 / 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- `n ≤ (1 + 3/ε) q_n^ε` for every `ε > 0`. -/
lemma idx_le_rpow (hα : Irrational α) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (n : ℝ) ≤ (1 + 3 / ε) * CAH.q α n ^ ε := by
  have h1 := idx_le_log hα n
  have h2 := Real.log_le_rpow_div (CAH.q_pos hα n).le hε
  have h3 : 1 ≤ CAH.q α n ^ ε := Real.one_le_rpow (CAH.q_one_le hα n) hε.le
  have h4 : 3 * (CAH.q α n ^ ε / ε) = 3 / ε * CAH.q α n ^ ε := by ring
  rw [add_mul, one_mul]
  linarith

/-- `n^4 ≤ (1 + 3/ε)^4 q_n^{4ε}`. -/
lemma idx_pow_four_le (hα : Irrational α) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (n : ℝ) ^ 4 ≤ (1 + 3 / ε) ^ 4 * CAH.q α n ^ (4 * ε) := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg n) (idx_le_rpow hα n hε) 4
  rw [mul_pow, ← Real.rpow_mul_natCast (CAH.q_pos hα n).le] at h
  rw [show 4 * ε = ε * ((4 : ℕ) : ℝ) by push_cast; ring]; exact h

lemma exists_le_rpow (B : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x → B ≤ x ^ r := by
  refine ⟨max 1 (|B| ^ (1 / r)), le_max_left _ _, fun x hx => ?_⟩
  have h0 : 0 ≤ |B| ^ (1 / r) := by positivity
  have h1 : |B| ^ (1 / r) ≤ x := (le_max_right _ _).trans hx
  have h2 := Real.rpow_le_rpow h0 h1 hr.le
  rw [← Real.rpow_mul (abs_nonneg B), one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one] at h2
  exact (le_abs_self B).trans h2

/-- For `q_n` large, `η/n² ≥ 1/√q_l` whenever `q_l ≥ q_n^ρ`. -/
lemma delta_ok {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ α : ℝ, Irrational α → ∀ n l : ℕ, T ≤ CAH.q α n →
      CAH.q α n ^ ρ ≤ CAH.q α l → 1 / Real.sqrt (CAH.q α l) ≤ η / (n : ℝ) ^ 2 := by
  obtain ⟨T, hT1, hT⟩ := exists_le_rpow ((1 + 3 / (ρ / 8)) ^ 2 / η) (show 0 < ρ / 4 by positivity)
  refine ⟨max 2 T, le_max_left _ _, fun α hα n l hn' hl => ?_⟩
  have hn : T ≤ CAH.q α n := (le_max_right _ _).trans hn'
  have hn2' : 2 ≤ CAH.q α n := (le_max_left _ _).trans hn'
  have hq0 := CAH.q_pos hα n
  have hB := hT _ hn
  rw [div_le_iff₀ hη] at hB
  have hN := pow_le_pow_left₀ (Nat.cast_nonneg n) (idx_le_rpow hα n (show 0 < ρ / 8 by positivity)) 2
  rw [mul_pow, ← Real.rpow_mul_natCast hq0.le] at hN
  have e1 : ρ / 8 * ((2 : ℕ) : ℝ) = ρ / 4 := by push_cast; ring
  rw [e1] at hN
  have hsq : CAH.q α n ^ (ρ / 2) ≤ Real.sqrt (CAH.q α l) := by
    rw [Real.sqrt_eq_rpow, show ρ / 2 = ρ * (1 / 2) by ring, Real.rpow_mul hq0.le]
    exact Real.rpow_le_rpow (by positivity) hl (by norm_num)
  have e2 : CAH.q α n ^ (ρ / 2) = CAH.q α n ^ (ρ / 4) * CAH.q α n ^ (ρ / 4) := by
    rw [← Real.rpow_add hq0]; ring_nf
  have hpos : 0 < CAH.q α n ^ (ρ / 4) := Real.rpow_pos_of_pos hq0 _
  have hn2 : (n : ℝ) ^ 2 ≤ η * Real.sqrt (CAH.q α l) := by
    have h3 : (n : ℝ) ^ 2 ≤ CAH.q α n ^ (ρ / 4) * η * CAH.q α n ^ (ρ / 4) :=
      hN.trans (mul_le_mul_of_nonneg_right hB hpos.le)
    nlinarith
  have hl0 : 0 < Real.sqrt (CAH.q α l) := Real.sqrt_pos.2 (CAH.q_pos hα l)
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [q_zero] at hn2'; norm_num at hn2'
  rw [div_le_div_iff₀ hl0 (by positivity)]; linarith

lemma rpow_mul_eq {x a b c : ℝ} (hx : 0 < x) (h : a + b = c) : x ^ a * x ^ b = x ^ c := by
  rw [← Real.rpow_add hx, h]

/-- Real-variable core of Corollary `cor3`(1). -/
lemma cor3_case1_real {M C D N x y : ℝ} (hC : 0 < C) (hD : 0 < D) (hx : 1 ≤ x)
    (hy : x ^ (2 * M) ≤ y) (hN : N ^ 4 ≤ D ^ 4 * x ^ ((M - 1) / 2))
    (hT1 : 2 * C * D ^ 4 ≤ x ^ ((M - 1) / 2))
    (hT2 : 2 * C ≤ x ^ ((2 * M) ^ 5 - 1 - M)) :
    C * (N ^ 4 * x / y + x / x ^ ((2 * M) ^ 5)) ≤ x ^ (-M) := by
  have hx0 : 0 < x := by linarith
  have hxA : 0 < x ^ (2 * M) := Real.rpow_pos_of_pos hx0 _
  have hy0 : 0 < y := lt_of_lt_of_le hxA hy
  have hpow : ∀ a b : ℝ, x ^ (a + b) = x ^ a * x ^ b := fun a b => Real.rpow_add hx0 a b
  have hx1 : x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
  -- first term
  have t1 : C * (N ^ 4 * x / y) ≤ x ^ (-M) / 2 := by
    have h1 : N ^ 4 * x / y ≤ N ^ 4 * x / x ^ (2 * M) :=
      div_le_div_of_nonneg_left (by positivity) hxA hy
    have h2 : N ^ 4 * x / x ^ (2 * M) ≤ D ^ 4 * x ^ ((M - 1) / 2) * x / x ^ (2 * M) := by
      gcongr
    have e : x ^ (-M) = x ^ ((M - 1) / 2) * x ^ ((M - 1) / 2) * x / x ^ (2 * M) := by
      rw [eq_div_iff hxA.ne']
      calc x ^ (-M) * x ^ (2 * M) = x ^ M := rpow_mul_eq hx0 (by ring)
        _ = x ^ ((M - 1) / 2) * x ^ ((M - 1) / 2) * x ^ (1 : ℝ) := by
          rw [rpow_mul_eq hx0 (show (M - 1) / 2 + (M - 1) / 2 = M - 1 by ring),
            rpow_mul_eq hx0 (show M - 1 + 1 = M by ring)]
        _ = _ := by rw [Real.rpow_one]
    have h3 : C * (D ^ 4 * x ^ ((M - 1) / 2) * x / x ^ (2 * M)) ≤ x ^ (-M) / 2 := by
      rw [e]
      have hp : 0 < x ^ ((M - 1) / 2) := Real.rpow_pos_of_pos hx0 _
      rw [show C * (D ^ 4 * x ^ ((M - 1) / 2) * x / x ^ (2 * M)) =
        (2 * C * D ^ 4) * (x ^ ((M - 1) / 2) * x / x ^ (2 * M)) / 2 by ring]
      rw [show x ^ ((M - 1) / 2) * x ^ ((M - 1) / 2) * x / x ^ (2 * M) / 2 =
        x ^ ((M - 1) / 2) * (x ^ ((M - 1) / 2) * x / x ^ (2 * M)) / 2 by ring]
      gcongr
    calc C * (N ^ 4 * x / y) ≤ C * (D ^ 4 * x ^ ((M - 1) / 2) * x / x ^ (2 * M)) := by gcongr
      _ ≤ _ := h3
  -- second term
  have t2 : C * (x / x ^ ((2 * M) ^ 5)) ≤ x ^ (-M) / 2 := by
    have hU : 0 < x ^ ((2 * M) ^ 5) := Real.rpow_pos_of_pos hx0 _
    have e : x ^ (-M) = x ^ ((2 * M) ^ 5 - 1 - M) * x / x ^ ((2 * M) ^ 5) := by
      rw [eq_div_iff hU.ne']
      calc x ^ (-M) * x ^ ((2 * M) ^ 5) = x ^ ((2 * M) ^ 5 - 1 - M) * x ^ (1 : ℝ) := by
            rw [rpow_mul_eq hx0 rfl, rpow_mul_eq hx0 rfl]; congr 1; ring
        _ = _ := by rw [Real.rpow_one]
    rw [e, show C * (x / x ^ ((2 * M) ^ 5)) = (2 * C) * (x / x ^ ((2 * M) ^ 5)) / 2 by ring,
      show x ^ ((2 * M) ^ 5 - 1 - M) * x / x ^ ((2 * M) ^ 5) / 2 =
        x ^ ((2 * M) ^ 5 - 1 - M) * (x / x ^ ((2 * M) ^ 5)) / 2 by ring]
    gcongr
  linarith [mul_add C (N ^ 4 * x / y) (x / x ^ ((2 * M) ^ 5))]

/-- Real-variable core of Corollary `cor3`(2). -/
lemma cor3_case2_real {M C D N x y z : ℝ} (hM : 1 < M) (hC : 0 < C) (hD : 0 < D) (hx : 1 ≤ x)
    (hxy : x ≤ y) (hz1 : x ^ (1 / (2 * M) ^ 4) ≤ z) (hz2 : z ≤ x ^ (1 / (2 * M)))
    (hN : N ^ 4 ≤ D ^ 4 * x ^ (1 / (4 * M)))
    (hT1 : C * D ^ 4 ≤ x ^ (1 / (4 * M))) (hT2 : C ≤ x ^ (M - 1)) :
    C * (N ^ 4 * z / y + x / z ^ ((2 * M) ^ 5)) ≤ y ^ (-1 + 1 / M) + x ^ (-M) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hM0 : 0 < M := by linarith
  have hpow : ∀ a b : ℝ, x ^ (a + b) = x ^ a * x ^ b := fun a b => Real.rpow_add hx0 a b
  have hx1 : x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
  have hz0 : 0 < z := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hz1
  have t1 : C * (N ^ 4 * z / y) ≤ y ^ (-1 + 1 / M) := by
    have h1 : C * (N ^ 4 * z) ≤ x ^ (1 / M) := by
      have := mul_le_mul hN hz2 hz0.le (by positivity)
      have h2 : C * (N ^ 4 * z) ≤ (C * D ^ 4) * x ^ (1 / (4 * M)) * x ^ (1 / (2 * M)) := by
        nlinarith
      have h3 : (C * D ^ 4) * x ^ (1 / (4 * M)) * x ^ (1 / (2 * M)) ≤
          x ^ (1 / (4 * M)) * x ^ (1 / (4 * M)) * x ^ (1 / (2 * M)) := by
        gcongr
      rw [← hpow, ← hpow] at h3
      have e : 1 / (4 * M) + 1 / (4 * M) + 1 / (2 * M) = 1 / M := by field_simp; ring
      rw [e] at h3; linarith
    have h4 : x ^ (1 / M) ≤ y ^ (1 / M) := Real.rpow_le_rpow hx0.le hxy (by positivity)
    have e2 : y ^ (-1 + 1 / M) = y ^ (1 / M) / y := by
      rw [Real.rpow_add hy0, Real.rpow_neg_one]; ring
    rw [e2, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h1.trans h4) hy0.le
  have t2 : C * (x / z ^ ((2 * M) ^ 5)) ≤ x ^ (-M) := by
    have hzU : x ^ (2 * M) ≤ z ^ ((2 * M) ^ 5) := by
      have := Real.rpow_le_rpow (by positivity) hz1 (show (0 : ℝ) ≤ (2 * M) ^ 5 by positivity)
      rw [← Real.rpow_mul hx0.le] at this
      have e : 1 / (2 * M) ^ 4 * (2 * M) ^ 5 = 2 * M := by field_simp
      rwa [e] at this
    have hxA : 0 < x ^ (2 * M) := Real.rpow_pos_of_pos hx0 _
    have h1 : C * (x / z ^ ((2 * M) ^ 5)) ≤ C * (x / x ^ (2 * M)) := by gcongr
    have e : x ^ (-M) = x ^ (M - 1) * x / x ^ (2 * M) := by
      rw [eq_div_iff hxA.ne']
      calc x ^ (-M) * x ^ (2 * M) = x ^ (M - 1) * x ^ (1 : ℝ) := by
            rw [rpow_mul_eq hx0 rfl, rpow_mul_eq hx0 rfl]; congr 1; ring
        _ = _ := by rw [Real.rpow_one]
    rw [e] at *
    refine h1.trans ?_
    rw [show C * (x / x ^ (2 * M)) = C * (x / x ^ (2 * M)) by rfl,
      show x ^ (M - 1) * x / x ^ (2 * M) = x ^ (M - 1) * (x / x ^ (2 * M)) by ring]
    gcongr
  linarith [mul_add C (N ^ 4 * z / y) (x / z ^ ((2 * M) ^ 5))]

end Asymptotics

/-! ## Corollary `cor3` -/

/-- **Corollary `cor3`** (coefficient form, with `A = 2M` and `U = A⁵`).  Given `h_*, η > 0`
and `M > 1` there is `T₀` such that for every irrational `α`, every denominator `q_n ≥ T₀`,
every `h ≥ h_*`, `δ ≥ η/n²` and `φ̂` with `|φ̂(l)| e^{2π|l|h} ≤ K` (`l ≠ 0`):
1. if `q_{n+1} ≥ q_n^{A}` then `‖S_{q_n}φ - q_nφ̂(0)‖_{h(1-δ)} ≤ K q_n^{-M}`;
2. if `q_n^{1/A⁴} ≤ q_l ≤ q_n^{1/A}` then
   `‖S_{q_n}φ - q_nφ̂(0)‖_{h(1-δ)} ≤ K (q_{n+1}^{-1+1/M} + q_n^{-M})`.

Deviations: the paper writes `S_{q_n}φ` for `S_{q_n}φ - q_nφ̂(0)`; `T₀` must also depend on `η`
(it is needed for `η/n² ≥ 1/√q_l`); in (2) the lower exponent is `1/A⁴` (instead of `1/A³`)
to match the corrected bridges of `dioph_bridge`, which forces `U = A⁵` (instead of `A⁴`). -/
theorem cor3 {hstar η M : ℝ} (hh : 0 < hstar) (hη : 0 < η) (hM : 1 < M) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ α : ℝ, Irrational α → ∀ n : ℕ, T₀ ≤ CAH.q α n →
      ∀ (h δ K : ℝ) (a : ℤ → ℂ), hstar ≤ h → η / (n : ℝ) ^ 2 ≤ δ →
      (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
      (CAH.q α n ^ (2 * M) ≤ CAH.q α (n + 1) →
        wnorm (birkhoffCoeff α (CAH.qN α n) a) (h * (1 - δ)) ≤ K * CAH.q α n ^ (-M)) ∧
      (∀ l : ℕ, CAH.q α n ^ (1 / (2 * M) ^ 4) ≤ CAH.q α l →
        CAH.q α l ≤ CAH.q α n ^ (1 / (2 * M)) →
        wnorm (birkhoffCoeff α (CAH.qN α n) a) (h * (1 - δ)) ≤
          K * (CAH.q α (n + 1) ^ (-1 + 1 / M) + CAH.q α n ^ (-M))) := by
  have hM0 : 0 < M := by linarith
  have hA1 : 1 ≤ 2 * M := by linarith
  have hρ0 : 0 < 1 / (2 * M) ^ 4 := by positivity
  have hρ1 : 1 / (2 * M) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hA1
  have hU : 0 < (2 * M) ^ 5 - 1 - M := by
    have : 2 * M ≤ (2 * M) ^ 5 := le_self_pow₀ hA1 (by norm_num)
    linarith
  obtain ⟨C, hC, hden⟩ := denjoy_el hh hη ((2 * M) ^ 5)
  obtain ⟨T₁, hT₁2, hT₁⟩ := delta_ok hη hρ0
  obtain ⟨T₂, -, hT₂⟩ := exists_le_rpow (2 * C * (1 + 3 / ((M - 1) / 8)) ^ 4)
    (show 0 < (M - 1) / 2 by linarith)
  obtain ⟨T₃, -, hT₃⟩ := exists_le_rpow (2 * C) hU
  obtain ⟨T₄, -, hT₄⟩ := exists_le_rpow (C * (1 + 3 / (1 / (16 * M))) ^ 4)
    (show 0 < 1 / (4 * M) by positivity)
  obtain ⟨T₅, -, hT₅⟩ := exists_le_rpow C (show 0 < M - 1 by linarith)
  refine ⟨max T₁ (max T₂ (max T₃ (max T₄ T₅))), le_trans hT₁2 (le_max_left _ _), ?_⟩
  intro α hα n hn h δ K a hh' hδ hK
  have hn1 : T₁ ≤ CAH.q α n := (le_max_left _ _).trans hn
  have hn2 : T₂ ≤ CAH.q α n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn3 : T₃ ≤ CAH.q α n :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn4 : T₄ ≤ CAH.q α n := ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn5 : T₅ ≤ CAH.q α n := ((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hq1 := CAH.q_one_le hα n
  have hqn0 : 0 < CAH.q α n := CAH.q_pos hα n
  have hnpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · rw [q_zero] at hn1; linarith
    · exact h0
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hδ2 : η / (10 * (n : ℝ) ^ 2) ≤ δ := by
    refine le_trans (div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)) hδ
  refine ⟨fun hbig => ?_, fun l hl1 hl2 => ?_⟩
  · -- case (1): `s₁ = s₂ = n`
    have hρn : CAH.q α n ^ (1 / (2 * M) ^ 4) ≤ CAH.q α n := by
      calc CAH.q α n ^ (1 / (2 * M) ^ 4) ≤ CAH.q α n ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq1 hρ1
        _ = _ := Real.rpow_one _
    have hδ1 : 1 / Real.sqrt (CAH.q α n) ≤ δ := (hT₁ α hα n n hn1 hρn).trans hδ
    have hb := (hden α hα n n le_rfl h δ K a hh' hδ1 hδ2 hK).2
    have hN := idx_pow_four_le hα n (show 0 < (M - 1) / 8 by linarith)
    rw [show 4 * ((M - 1) / 8) = (M - 1) / 2 by ring] at hN
    have hc := cor3_case1_real hC (by positivity) hq1 hbig hN (hT₂ _ hn2) (hT₃ _ hn3)
    calc _ ≤ C * K * ((n : ℝ) ^ 4 * CAH.q α n / CAH.q α (n + 1) +
          CAH.q α n / CAH.q α n ^ (2 * M) ^ 5) := hb
      _ = K * (C * ((n : ℝ) ^ 4 * CAH.q α n / CAH.q α (n + 1) +
          CAH.q α n / CAH.q α n ^ (2 * M) ^ 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hK0
  · -- case (2): `s₁ = l`, `s₂ = n`
    have hql : CAH.q α l ≤ CAH.q α n := by
      refine hl2.trans ?_
      calc CAH.q α n ^ (1 / (2 * M)) ≤ CAH.q α n ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq1 (by rw [div_le_one (by positivity)]; exact hA1)
        _ = _ := Real.rpow_one _
    have hδ1 : 1 / Real.sqrt (CAH.q α l) ≤ δ := (hT₁ α hα n l hn1 hl1).trans hδ
    have hb := (hden α hα l n hql h δ K a hh' hδ1 hδ2 hK).2
    have hN := idx_pow_four_le hα n (show 0 < 1 / (16 * M) by positivity)
    rw [show 4 * (1 / (16 * M)) = 1 / (4 * M) by field_simp; ring] at hN
    have hc := cor3_case2_real hM hC (by positivity) hq1 (CAH.q_le_succ hα n) hl1 hl2 hN
      (hT₄ _ hn4) (hT₅ _ hn5)
    calc _ ≤ C * K * ((n : ℝ) ^ 4 * CAH.q α l / CAH.q α (n + 1) +
          CAH.q α n / CAH.q α l ^ (2 * M) ^ 5) := hb
      _ = K * (C * ((n : ℝ) ^ 4 * CAH.q α l / CAH.q α (n + 1) +
          CAH.q α n / CAH.q α l ^ (2 * M) ^ 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hK0

/-- The properties of the subsequence `n_k` (`Q_k = q_{n_k}`) produced by `dioph_bridge`. -/
def IsAFKSeq (α A : ℝ) (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ n 0 = 0 ∧ ∀ k : ℕ,
      CAH.q α (n (k + 1)) ≤ CAH.q α (n k + 1) ^ (A ^ 4) ∧
      (∀ i, n k + 1 ≤ i → i < n (k + 1) → CAH.q α (i + 1) ≤ CAH.q α i ^ A) ∧
      (CAH.q α (n k) ^ A ≤ CAH.q α (n k + 1) ∨
        (0 < k ∧ IsCDBridge α A A (A ^ 4) (n (k - 1) + 1) (n k) ∧
          IsCDBridge α A A (A ^ 4) (n k) (n (k + 1))))

theorem exists_isAFKSeq {α : ℝ} (hα : Irrational α) {A : ℝ} (hA : 1 < A) :
    ∃ n, IsAFKSeq α A n := dioph_bridge hα hA

lemma rpow_inv_le_of_le_rpow {x y a : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (ha : 0 < a)
    (h : y ≤ x ^ a) : y ^ (1 / a) ≤ x := by
  have := Real.rpow_le_rpow hy h (show 0 ≤ 1 / a by positivity)
  rwa [← Real.rpow_mul hx.le, mul_one_div_cancel ha.ne', Real.rpow_one] at this

lemma le_rpow_inv_of_rpow_le {x y a : ℝ} (hx : 0 < x) (ha : 0 < a)
    (h : x ^ a ≤ y) : x ≤ y ^ (1 / a) := by
  have := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx a).le h (show 0 ≤ 1 / a by positivity)
  rwa [← Real.rpow_mul hx.le, mul_one_div_cancel ha.ne', Real.rpow_one] at this

lemma IsAFKSeq.le_self {α A : ℝ} {n : ℕ → ℕ} (hn : IsAFKSeq α A n) (k : ℕ) : k ≤ n k :=
  hn.1.id_le k

/-- **Corollary `cor3`, conclusion** for the subsequence: if `Q_k ≥ T₀` then
`‖S_{Q_k}φ - Q_kφ̂(0)‖_{h(1-η/k²)} ≤ K (Q_k^{-M} + Q̄_k^{-1+1/M})`. -/
theorem cor3_Q {hstar η M : ℝ} (hh : 0 < hstar) (hη : 0 < η) (hM : 1 < M) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ α : ℝ, Irrational α → ∀ n : ℕ → ℕ, IsAFKSeq α (2 * M) n →
      ∀ k : ℕ, T₀ ≤ CAH.q α (n k) →
      ∀ (h δ K : ℝ) (a : ℤ → ℂ), hstar ≤ h → η / (k : ℝ) ^ 2 ≤ δ →
      (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
      wnorm (birkhoffCoeff α (CAH.qN α (n k)) a) (h * (1 - δ)) ≤
        K * (CAH.q α (n k) ^ (-M) + CAH.q α (n k + 1) ^ (-1 + 1 / M)) := by
  obtain ⟨T₀, hT₀, hcor⟩ := cor3 hh hη hM
  refine ⟨T₀, hT₀, fun α hα n hn k hk h δ K a hh' hδ hK => ?_⟩
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h0
    · rw [hn.2.1, q_zero] at hk; linarith
    · exact h0
  have hkn : (k : ℝ) ≤ n k := by exact_mod_cast hn.le_self k
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hδ' : η / ((n k : ℕ) : ℝ) ^ 2 ≤ δ :=
    le_trans (div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)) hδ
  obtain ⟨c1, c2⟩ := hcor α hα (n k) hk h δ K a hh' hδ' hK
  have hp1 : 0 ≤ CAH.q α (n k) ^ (-M) := (Real.rpow_pos_of_pos (CAH.q_pos hα _) _).le
  have hp2 : 0 ≤ CAH.q α (n k + 1) ^ (-1 + 1 / M) :=
    (Real.rpow_pos_of_pos (CAH.q_pos hα _) _).le
  rcases (hn.2.2 k).2.2 with hbig | ⟨-, hbr, -⟩
  · exact (c1 hbig).trans (mul_le_mul_of_nonneg_left (by linarith) hK0)
  · obtain ⟨-, hb1, hb2⟩ := hbr
    have hA4 : 0 < (2 * M) ^ 4 := by positivity
    have hql := CAH.q_pos hα (n (k - 1) + 1)
    have hl1 := rpow_inv_le_of_le_rpow hql (CAH.q_pos hα _).le hA4 hb2
    have hl2 := le_rpow_inv_of_rpow_le hql (show 0 < 2 * M by linarith) hb1
    exact (c2 _ hl1 hl2).trans (le_of_eq (by ring))

/-! ## Corollary `cor4`: Birkhoff sums of arbitrary length -/

section Cor4

variable {α : ℝ}

lemma bmult_add (α : ℝ) (m₁ m₂ : ℕ) (l : ℤ) :
    bmult α (m₁ + m₂) l = bmult α m₁ l + eT (l * α) ^ m₁ * bmult α m₂ l := by
  simp only [bmult, Finset.sum_range_add, pow_add, Finset.mul_sum]

lemma norm_bmult_add_le (α : ℝ) (m₁ m₂ : ℕ) (l : ℤ) :
    ‖bmult α (m₁ + m₂) l‖ ≤ ‖bmult α m₁ l‖ + ‖bmult α m₂ l‖ := by
  rw [bmult_add]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_pow, norm_eT, one_pow, one_mul]

lemma norm_bmult_mul_le (α : ℝ) (c q : ℕ) (l : ℤ) :
    ‖bmult α (c * q) l‖ ≤ c * ‖bmult α q l‖ := by
  induction c with
  | zero => simp [bmult]
  | succ c ih =>
    rw [Nat.succ_mul]
    refine (norm_bmult_add_le α _ _ l).trans ?_
    push_cast; linarith

lemma norm_birkhoffCoeff (α : ℝ) (m : ℕ) (a : ℤ → ℂ) (l : ℤ) :
    ‖birkhoffCoeff α m a l‖ = ‖a l‖ * (if l = 0 then 0 else ‖bmult α m l‖) := by
  unfold birkhoffCoeff; split_ifs <;> simp

lemma norm_birkhoffCoeff_add_le (α : ℝ) (m₁ m₂ : ℕ) (a : ℤ → ℂ) (l : ℤ) :
    ‖birkhoffCoeff α (m₁ + m₂) a l‖ ≤ ‖birkhoffCoeff α m₁ a l‖ + ‖birkhoffCoeff α m₂ a l‖ := by
  simp only [norm_birkhoffCoeff]
  split_ifs
  · simp
  · rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_bmult_add_le α _ _ l) (norm_nonneg _)

lemma norm_birkhoffCoeff_mul_le (α : ℝ) (c q : ℕ) (a : ℤ → ℂ) (l : ℤ) :
    ‖birkhoffCoeff α (c * q) a l‖ ≤ c * ‖birkhoffCoeff α q a l‖ := by
  simp only [norm_birkhoffCoeff]
  split_ifs
  · simp
  · have := mul_le_mul_of_nonneg_left (norm_bmult_mul_le α c q l) (norm_nonneg (a l))
    linarith [mul_comm (c : ℝ) (‖a l‖ * ‖bmult α q l‖), mul_assoc (‖a l‖) (c : ℝ) ‖bmult α q l‖]

/-- Weighted summability predicate. -/
def WSummable (b : ℤ → ℂ) (h' : ℝ) : Prop :=
  Summable (fun l : ℤ => ‖b l‖ * Real.exp (2 * π * |(l : ℝ)| * h'))

/-- Subadditivity of the weighted norm along the decomposition `m = c q + r`. -/
lemma wnorm_decomp_le (α : ℝ) (a : ℤ → ℂ) (h' : ℝ) (c q r : ℕ)
    (hq : WSummable (birkhoffCoeff α q a) h') (hr : WSummable (birkhoffCoeff α r a) h') :
    WSummable (birkhoffCoeff α (c * q + r) a) h' ∧
      wnorm (birkhoffCoeff α (c * q + r) a) h' ≤
        c * wnorm (birkhoffCoeff α q a) h' + wnorm (birkhoffCoeff α r a) h' := by
  have hpt : ∀ l : ℤ, ‖birkhoffCoeff α (c * q + r) a l‖ * Real.exp (2 * π * |(l : ℝ)| * h') ≤
      c * (‖birkhoffCoeff α q a l‖ * Real.exp (2 * π * |(l : ℝ)| * h')) +
        ‖birkhoffCoeff α r a l‖ * Real.exp (2 * π * |(l : ℝ)| * h') := by
    intro l
    have h1 := norm_birkhoffCoeff_add_le α (c * q) r a l
    have h2 := norm_birkhoffCoeff_mul_le α c q a l
    have he := Real.exp_pos (2 * π * |(l : ℝ)| * h')
    nlinarith
  have hs : Summable (fun l : ℤ => c * (‖birkhoffCoeff α q a l‖ *
      Real.exp (2 * π * |(l : ℝ)| * h')) + ‖birkhoffCoeff α r a l‖ *
        Real.exp (2 * π * |(l : ℝ)| * h')) := (hq.mul_left _).add hr
  have hS : WSummable (birkhoffCoeff α (c * q + r) a) h' :=
    Summable.of_nonneg_of_le (fun l => by positivity) hpt hs
  refine ⟨hS, ?_⟩
  unfold wnorm
  refine (Summable.tsum_le_tsum hpt hS hs).trans (le_of_eq ?_)
  rw [Summable.tsum_add (hq.mul_left _) hr, tsum_mul_left]

/-- Trivial bound `‖S_bφ - bφ̂(0)‖_{h(1-δ)} ≤ b K (1 + 2/c)`, `c = 2πhδ`. -/
lemma wnorm_trivial (α : ℝ) {h δ K : ℝ} {a : ℤ → ℂ} (hh : 0 < h) (hδ : 0 < δ)
    (hK : ∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) (b : ℕ) :
    WSummable (birkhoffCoeff α b a) (h * (1 - δ)) ∧
      wnorm (birkhoffCoeff α b a) (h * (1 - δ)) ≤ b * K * (1 + 2 / (2 * π * h * δ)) := by
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  set c := 2 * π * h * δ with hc
  have hcpos : 0 < c := by positivity
  have hpt : ∀ l : ℤ, ‖birkhoffCoeff α b a l‖ * Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ))) ≤
      b * K * Real.exp (-(c * |(l : ℝ)|)) := by
    intro l
    rw [norm_birkhoffCoeff]
    split_ifs with hl
    · simp; positivity
    · have hexp : Real.exp (2 * π * |(l : ℝ)| * (h * (1 - δ))) =
          Real.exp (2 * π * |(l : ℝ)| * h) * Real.exp (-(c * |(l : ℝ)|)) := by
        rw [← Real.exp_add, hc]; congr 1; ring
      rw [hexp]
      have h1 := hK l hl
      have h2 := norm_bmult_le α b l
      have he := Real.exp_pos (-(c * |(l : ℝ)|))
      have he2 := Real.exp_pos (2 * π * |(l : ℝ)| * h)
      calc ‖a l‖ * ‖bmult α b l‖ * (Real.exp (2 * π * |(l : ℝ)| * h) *
            Real.exp (-(c * |(l : ℝ)|)))
          = (‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h)) * ‖bmult α b l‖ *
            Real.exp (-(c * |(l : ℝ)|)) := by ring
        _ ≤ K * b * Real.exp (-(c * |(l : ℝ)|)) := by
          gcongr
        _ = _ := by ring
  obtain ⟨hsum, hle⟩ := summable_exp_neg_abs' hcpos
  have hg := hsum.mul_left ((b : ℝ) * K)
  have hS : WSummable (birkhoffCoeff α b a) (h * (1 - δ)) :=
    Summable.of_nonneg_of_le (fun l => by positivity) hpt hg
  refine ⟨hS, ?_⟩
  unfold wnorm
  refine (Summable.tsum_le_tsum hpt hS hg).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

lemma qN_mono (hα : Irrational α) {i j : ℕ} (hij : i ≤ j) : CAH.qN α i ≤ CAH.qN α j := by
  have := q_mono hα hij
  rw [← CAH.qN_cast hα, ← CAH.qN_cast hα] at this
  exact_mod_cast this

/-- **Ostrowski-type decomposition** `m = ∑_{s=u}^{v-1} c_s q_s + b` (`b < q_u`,
`c_s q_s ≤ min(m, q_{s+1})`) combined with the bounds `E_s` for `S_{q_s}`. -/
lemma decomp_bound (hα : Irrational α) {h δ K C U : ℝ} {a : ℤ → ℂ} (hh : 0 < h) (hδ : 0 < δ)
    (hK : ∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) (hC : 0 ≤ C)
    (u : ℕ)
    (hE : ∀ s, u ≤ s → WSummable (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ∧
      wnorm (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ≤
        C * K * ((s : ℝ) ^ 4 * CAH.q α s / CAH.q α (s + 1) + CAH.q α s / CAH.q α s ^ U)) :
    ∀ v m : ℕ, m < CAH.qN α v → WSummable (birkhoffCoeff α m a) (h * (1 - δ)) ∧
      wnorm (birkhoffCoeff α m a) (h * (1 - δ)) ≤
        CAH.q α u * K * (1 + 2 / (2 * π * h * δ)) +
          ∑ s ∈ Finset.Ico u v, C * K * ((s : ℝ) ^ 4 + min (m : ℝ) (CAH.q α (s + 1)) /
            CAH.q α s ^ U) := by
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hF : 0 ≤ 1 + 2 / (2 * π * h * δ) := by positivity
  have htriv : ∀ m : ℕ, m ≤ CAH.qN α u → WSummable (birkhoffCoeff α m a) (h * (1 - δ)) ∧
      wnorm (birkhoffCoeff α m a) (h * (1 - δ)) ≤ CAH.q α u * K * (1 + 2 / (2 * π * h * δ)) := by
    intro m hm
    obtain ⟨h1, h2⟩ := wnorm_trivial α hh hδ hK m
    refine ⟨h1, h2.trans ?_⟩
    have : (m : ℝ) ≤ CAH.q α u := by rw [← CAH.qN_cast hα]; exact_mod_cast hm
    gcongr
  have hterm0 : ∀ (m : ℕ) (s : ℕ), 0 ≤ C * K * ((s : ℝ) ^ 4 + min (m : ℝ) (CAH.q α (s + 1)) /
      CAH.q α s ^ U) := by
    intro m s
    have := CAH.q_pos hα (s + 1)
    have := Real.rpow_pos_of_pos (CAH.q_pos hα s) U
    have : 0 ≤ min (m : ℝ) (CAH.q α (s + 1)) := le_min (Nat.cast_nonneg _) (by linarith)
    positivity
  intro v
  induction v with
  | zero =>
    intro m hm
    rw [qN_zero] at hm
    obtain ⟨h1, h2⟩ := htriv m (by have := CAH.one_le_qN hα u; omega)
    exact ⟨h1, by simpa using h2⟩
  | succ v ih =>
    intro m hm
    by_cases hv : v < u
    · obtain ⟨h1, h2⟩ := htriv m (by have := qN_mono hα (show v + 1 ≤ u by omega); omega)
      refine ⟨h1, h2.trans ?_⟩
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    push Not at hv
    have hqv : 0 < CAH.qN α v := by have := CAH.one_le_qN hα v; omega
    set c := m / CAH.qN α v with hc
    set r := m % CAH.qN α v with hr
    have hmcr : c * CAH.qN α v + r = m := by rw [hc, hr, mul_comm]; exact Nat.div_add_mod m _
    have hrlt : r < CAH.qN α v := Nat.mod_lt _ hqv
    have hrm : r ≤ m := Nat.mod_le _ _
    obtain ⟨hsr, hwr⟩ := ih r hrlt
    obtain ⟨hsq, hwq⟩ := hE v hv
    obtain ⟨hsm, hwm⟩ := wnorm_decomp_le α a (h * (1 - δ)) c (CAH.qN α v) r hsq hsr
    rw [hmcr] at hsm hwm
    refine ⟨hsm, hwm.trans ?_⟩
    rw [Finset.sum_Ico_succ_top hv]
    -- the new block
    have hcq : (c : ℝ) * CAH.q α v ≤ m := by
      rw [← CAH.qN_cast hα]; exact_mod_cast (show c * CAH.qN α v ≤ m by omega)
    have hcq2 : (c : ℝ) * CAH.q α v ≤ CAH.q α (v + 1) := by
      have : c * CAH.qN α v ≤ CAH.qN α (v + 1) := by omega
      rw [← CAH.qN_cast hα, ← CAH.qN_cast hα]; exact_mod_cast this
    have hqv0 := CAH.q_pos hα v
    have hqv1 := CAH.q_pos hα (v + 1)
    have hqU := Real.rpow_pos_of_pos hqv0 U
    have hblock : (c : ℝ) * wnorm (birkhoffCoeff α (CAH.qN α v) a) (h * (1 - δ)) ≤
        C * K * ((v : ℝ) ^ 4 + min (m : ℝ) (CAH.q α (v + 1)) / CAH.q α v ^ U) := by
      have h1 : (c : ℝ) * wnorm (birkhoffCoeff α (CAH.qN α v) a) (h * (1 - δ)) ≤
          c * (C * K * ((v : ℝ) ^ 4 * CAH.q α v / CAH.q α (v + 1) + CAH.q α v / CAH.q α v ^ U)) :=
        mul_le_mul_of_nonneg_left hwq (Nat.cast_nonneg _)
      refine h1.trans ?_
      rw [show (c : ℝ) * (C * K * ((v : ℝ) ^ 4 * CAH.q α v / CAH.q α (v + 1) +
          CAH.q α v / CAH.q α v ^ U)) = C * K * ((v : ℝ) ^ 4 * ((c * CAH.q α v) / CAH.q α (v + 1)) +
          (c * CAH.q α v) / CAH.q α v ^ U) by ring]
      have e1 : (c : ℝ) * CAH.q α v / CAH.q α (v + 1) ≤ 1 := by
        rw [div_le_one hqv1]; exact hcq2
      have e2 : (c : ℝ) * CAH.q α v ≤ min (m : ℝ) (CAH.q α (v + 1)) := le_min hcq hcq2
      have hv4 : 0 ≤ (v : ℝ) ^ 4 := by positivity
      gcongr
      calc (v : ℝ) ^ 4 * ((c * CAH.q α v) / CAH.q α (v + 1)) ≤ (v : ℝ) ^ 4 * 1 :=
            mul_le_mul_of_nonneg_left e1 hv4
        _ = _ := mul_one _
    have hsum : ∑ s ∈ Finset.Ico u v, C * K * ((s : ℝ) ^ 4 + min (r : ℝ) (CAH.q α (s + 1)) /
        CAH.q α s ^ U) ≤ ∑ s ∈ Finset.Ico u v, C * K * ((s : ℝ) ^ 4 +
          min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ U) := by
      apply Finset.sum_le_sum; intro s _
      have := Real.rpow_pos_of_pos (CAH.q_pos hα s) U
      have hrm' : (r : ℝ) ≤ m := by exact_mod_cast hrm
      gcongr
    linarith

lemma sum_block_le {u N : ℕ} {CK Γ : ℝ} (G : ℕ → ℝ) (hCK : 0 ≤ CK) (hΓ : 0 ≤ Γ)
    (hG : ∀ s ∈ Finset.Ico u (N + 1), G s ≤ 1 + (if s = u then Γ else 0)) :
    ∑ s ∈ Finset.Ico u (N + 1), CK * ((s : ℝ) ^ 4 + G s) ≤
      CK * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1) + Γ) := by
  have h1 : ∀ s ∈ Finset.Ico u (N + 1), CK * ((s : ℝ) ^ 4 + G s) ≤
      CK * ((N : ℝ) ^ 4 + 1) + CK * (if s = u then Γ else 0) := by
    intro s hs
    have hsN : (s : ℝ) ≤ N := by
      have := (Finset.mem_Ico.1 hs).2; exact_mod_cast (show s ≤ N by omega)
    have : (s : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hsN 4
    have := hG s hs
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_ite_eq']
  have hcard : ((Finset.Ico u (N + 1)).card : ℝ) ≤ N + 1 := by
    rw [Nat.card_Ico]; exact_mod_cast (show N + 1 - u ≤ N + 1 by omega)
  have hN4 : 0 ≤ (N : ℝ) ^ 4 + 1 := by positivity
  have h2 : (Finset.Ico u (N + 1)).card • (CK * ((N : ℝ) ^ 4 + 1)) ≤
      CK * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1)) := by
    rw [nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right hcard (mul_nonneg hCK hN4)
    nlinarith
  have h3 : CK * (if u ∈ Finset.Ico u (N + 1) then Γ else 0) ≤ CK * Γ := by
    apply mul_le_mul_of_nonneg_left _ hCK; split_ifs <;> linarith
  linarith

lemma G_le_one (hα : Irrational α) {A U : ℝ} (hA : 1 ≤ A) (hAU : A ≤ U) (m s : ℕ)
    (h : CAH.q α (s + 1) ≤ CAH.q α s ^ A ∨ (m : ℝ) ≤ CAH.q α s) :
    min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ U ≤ 1 := by
  have hq1 := CAH.q_one_le hα s
  have hqU := Real.rpow_pos_of_pos (CAH.q_pos hα s) U
  rw [div_le_one hqU]
  rcases h with h | h
  · exact (min_le_right _ _).trans (h.trans (Real.rpow_le_rpow_of_exponent_le hq1 hAU))
  · refine (min_le_left _ _).trans (h.trans ?_)
    calc CAH.q α s = CAH.q α s ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

/-- Real-variable core of Corollary `cor4`. -/
lemma cor4_real {Y N D P E C : ℝ} (hY : 1 ≤ Y) (hN : 1 ≤ N) (hN5 : N ^ 5 ≤ D ^ 5 * Y)
    (hN2 : N ^ 2 ≤ D ^ 2 * Y) (hP : P ≤ Y ^ 2) (hE : 0 < E) (hC : 0 ≤ C)
    (hB : 1 + D ^ 2 / E + 5 * C * D ^ 5 ≤ Y) :
    P * (1 + N ^ 2 / E) + C * ((N + 1) * (N ^ 4 + 1)) ≤ Y ^ 4 := by
  have h1 : (N + 1) * (N ^ 4 + 1) ≤ 5 * N ^ 5 := by nlinarith [pow_le_pow_left₀ zero_le_one hN 4]
  have h2 : 1 + N ^ 2 / E ≤ (1 + D ^ 2 / E) * Y := by
    have : N ^ 2 / E ≤ D ^ 2 * Y / E := div_le_div_of_nonneg_right hN2 hE.le
    rw [add_mul, one_mul, div_mul_eq_mul_div]; linarith
  have hD2 : 0 ≤ D ^ 2 / E := by positivity
  have h3 : P * (1 + N ^ 2 / E) ≤ Y ^ 2 * ((1 + D ^ 2 / E) * Y) :=
    mul_le_mul hP h2 (by positivity) (by positivity)
  have h4 : C * ((N + 1) * (N ^ 4 + 1)) ≤ 5 * C * D ^ 5 * Y := by
    have := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hN5 (by norm_num)))
      hC
    linarith
  have hY3 : Y ≤ Y ^ 3 := by nlinarith
  have hCD : 0 ≤ 5 * C * D ^ 5 := by
    have : 0 ≤ D ^ 5 * Y := le_trans (by positivity) hN5
    have : 0 ≤ D ^ 5 := by nlinarith
    positivity
  have h5 : 5 * C * D ^ 5 * Y ≤ 5 * C * D ^ 5 * Y ^ 3 := mul_le_mul_of_nonneg_left hY3 hCD
  have h6 : (1 + D ^ 2 / E + 5 * C * D ^ 5) * Y ^ 3 ≤ Y * Y ^ 3 :=
    mul_le_mul_of_nonneg_right hB (by positivity)
  nlinarith

/-- **Corollary `cor4`** (coefficient form, `A = 2M`, `U = A⁵`).  Given `h_*, η > 0` and
`M > 1` there is `T₀` such that for every irrational `α`, every sequence `n_k` with the
properties of `dioph_bridge` (`IsAFKSeq α (2M) n`), every `k` with `Q_k ≥ T₀`, every `h ≥ h_*`,
`δ ≥ η/k²`, every `φ̂` with `|φ̂(l)| e^{2π|l|h} ≤ K` (`l ≠ 0`) and every `m ≤ Q_{k+1}`:
`‖S_mφ - mφ̂(0)‖_{h(1-δ)} ≤ K (Q̄_k Q_k^{-M} + Q̄_k^{1/M})`.

Deviations: the paper writes `lφ̂(0)` for `mφ̂(0)`; in Case 2 the decomposition runs up to
`s = n_{k+1}` (allowing `m = Q_{k+1}`); the "remainder" `b < q_u` is estimated by
`b K (1 + 2/(2πhδ))`, which carries a factor `O(k²)` that the paper absorbs silently (it is
harmless since `q_u ≤ Q̄_k^{1/(2M)}`). -/
theorem cor4 {hstar η M : ℝ} (hh : 0 < hstar) (hη : 0 < η) (hM : 1 < M) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ α : ℝ, Irrational α → ∀ n : ℕ → ℕ, IsAFKSeq α (2 * M) n →
      ∀ k : ℕ, T₀ ≤ CAH.q α (n k) →
      ∀ (h δ K : ℝ) (a : ℤ → ℂ), hstar ≤ h → η / (k : ℝ) ^ 2 ≤ δ →
      (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
      ∀ m : ℕ, m ≤ CAH.qN α (n (k + 1)) →
      WSummable (birkhoffCoeff α m a) (h * (1 - δ)) ∧
      wnorm (birkhoffCoeff α m a) (h * (1 - δ)) ≤
        K * (CAH.q α (n k + 1) * CAH.q α (n k) ^ (-M) + CAH.q α (n k + 1) ^ (1 / M)) := by
  have hM0 : 0 < M := by linarith
  have hA1 : 1 ≤ 2 * M := by linarith
  have hAU : 2 * M ≤ (2 * M) ^ 5 := le_self_pow₀ hA1 (by norm_num)
  have hUM : 0 < (2 * M) ^ 5 - M := by linarith
  have hρ0 : 0 < 1 / (2 * M) ^ 4 := by positivity
  have hρ1 : 1 / (2 * M) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hA1
  obtain ⟨C, hC, hden⟩ := denjoy_el hh hη ((2 * M) ^ 5)
  obtain ⟨T₁, hT₁2, hT₁⟩ := delta_ok hη hρ0
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (20 * M) / (2 * M) ^ 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + 3 / ε := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  obtain ⟨T₂, -, hT₂⟩ := exists_le_rpow (1 + D ^ 2 / (π * hstar * η) + 5 * C * D ^ 5)
    (show 0 < 1 / (4 * M) by positivity)
  obtain ⟨T₃, -, hT₃⟩ := exists_le_rpow C hUM
  refine ⟨max T₁ (max T₂ T₃), le_trans hT₁2 (le_max_left _ _), ?_⟩
  intro α hα n hn k hk h δ K a hh' hδ hK m hm
  have hk1' : T₁ ≤ CAH.q α (n k) := (le_max_left _ _).trans hk
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hhpos : 0 < h := by linarith
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h0
    · rw [hn.2.1, q_zero] at hk1'; linarith
    · exact h0
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hkn : k ≤ n k := hn.le_self k
  have hknr : (k : ℝ) ≤ n k := by exact_mod_cast hkn
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  have hδk : η / ((n k : ℕ) : ℝ) ^ 2 ≤ δ :=
    le_trans (div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)) hδ
  have hnn : n k < n (k + 1) := hn.1 (Nat.lt_succ_self k)
  set N := n (k + 1) with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
  set X := CAH.q α (n k + 1) with hX
  have hQX : CAH.q α (n k) ≤ X := CAH.q_le_succ hα (n k)
  have hX0 : 0 < X := CAH.q_pos hα _
  have hX1 : 1 ≤ X := CAH.q_one_le hα _
  have hXT₂ : T₂ ≤ X := (((le_max_left _ _).trans (le_max_right _ _)).trans hk).trans hQX
  have hQT₃ : T₃ ≤ CAH.q α (n k) := ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  -- the bounds `E_s`
  have hEgen : ∀ u : ℕ, k ≤ u → CAH.q α (n k) ^ (1 / (2 * M) ^ 4) ≤ CAH.q α u →
      ∀ s, u ≤ s → WSummable (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ∧
        wnorm (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ≤
          C * K * ((s : ℝ) ^ 4 * CAH.q α s / CAH.q α (s + 1) +
            CAH.q α s / CAH.q α s ^ (2 * M) ^ 5) := by
    intro u hku hρu s hus
    have hqus : CAH.q α u ≤ CAH.q α s := q_mono hα hus
    have h1 : 1 / Real.sqrt (CAH.q α s) ≤ 1 / Real.sqrt (CAH.q α u) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.2 (CAH.q_pos hα u)) (Real.sqrt_le_sqrt hqus)
    have hδ1 : 1 / Real.sqrt (CAH.q α s) ≤ δ :=
      h1.trans ((hT₁ α hα (n k) u hk1' hρu).trans hδk)
    have hsr : (k : ℝ) ≤ s := by exact_mod_cast (show k ≤ s by omega)
    have hδ2 : η / (10 * (s : ℝ) ^ 2) ≤ δ :=
      le_trans (div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)) hδ
    exact hden α hα s s le_rfl h δ K a hh' hδ1 hδ2 hK
  -- `m < q_{N+1}`
  have hmN : m < CAH.qN α (N + 1) := by
    obtain ⟨j, hj⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
    have := qN_lt_qN_succ hα j
    rw [hj] at hm ⊢
    exact lt_of_le_of_lt hm this
  have hmq : (m : ℝ) ≤ CAH.q α N := by rw [← CAH.qN_cast hα]; exact_mod_cast hm
  -- the factor `1 + 2/(2πhδ)`
  have hfac : 1 + 2 / (2 * π * h * δ) ≤ 1 + (N : ℝ) ^ 2 / (π * hstar * η) := by
    have h1 : η ≤ δ * (k : ℝ) ^ 2 := by rwa [div_le_iff₀ (by positivity)] at hδ
    have h2 : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hkN 2
    have h3 : 2 / (2 * π * h * δ) ≤ (N : ℝ) ^ 2 / (π * hstar * η) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : hstar * η ≤ h * (δ * (N : ℝ) ^ 2) :=
        mul_le_mul hh' (h1.trans (mul_le_mul_of_nonneg_left h2 hδ0.le)) hη.le hhpos.le
      have := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * π by positivity)
      nlinarith
    linarith
  -- powers of `Y = X^{1/(4M)}`
  set Y := X ^ (1 / (4 * M)) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hX1 (by positivity)
  have hY4 : Y ^ 4 = X ^ (1 / M) := by
    rw [hY, ← Real.rpow_mul_natCast hX0.le]; congr 1; push_cast
    field_simp
  have hY2 : Y ^ 2 = X ^ (1 / (2 * M)) := by
    rw [hY, ← Real.rpow_mul_natCast hX0.le]; congr 1; push_cast
    field_simp; ring
  have hNle : (N : ℝ) ≤ D * X ^ (1 / (20 * M)) := by
    have h1 := idx_le_rpow hα N hε0
    rw [← hD] at h1
    have h2 : CAH.q α N ≤ X ^ ((2 * M) ^ 4) := (hn.2.2 k).1
    have h3 : CAH.q α N ^ ε ≤ X ^ (1 / (20 * M)) := by
      have := Real.rpow_le_rpow (CAH.q_pos hα N).le h2 hε0.le
      rw [← Real.rpow_mul hX0.le, hε, show (2 * M) ^ 4 * (1 / (20 * M) / (2 * M) ^ 4) =
        1 / (20 * M) by field_simp] at this
      rw [hε]; exact this
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hD0.le)
  have hθ : (X ^ (1 / (20 * M))) ^ 5 = Y := by
    rw [← Real.rpow_mul_natCast hX0.le, hY]; congr 1; push_cast
    field_simp; ring
  have hN5 : (N : ℝ) ^ 5 ≤ D ^ 5 * Y := by
    have := pow_le_pow_left₀ (by linarith) hNle 5
    rwa [mul_pow, hθ] at this
  have hN2 : (N : ℝ) ^ 2 ≤ D ^ 2 * Y := by
    have := pow_le_pow_left₀ (by linarith) hNle 2
    rw [mul_pow] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← hθ]
    have h1 : 1 ≤ X ^ (1 / (20 * M)) := Real.one_le_rpow hX1 (by positivity)
    exact pow_le_pow_right₀ h1 (by norm_num)
  have hB := hT₂ X hXT₂
  rw [← hY] at hB
  have hreal := fun P (hP : P ≤ Y ^ 2) =>
    cor4_real hY1 hNr hN5 hN2 hP (show 0 < π * hstar * η by positivity) hC.le hB
  have hG := fun s (hs : CAH.q α (s + 1) ≤ CAH.q α s ^ (2 * M) ∨ (m : ℝ) ≤ CAH.q α s) =>
    G_le_one hα hA1 hAU m s hs
  have hCK : 0 ≤ C * K := by positivity
  have hP1 : 0 ≤ X * CAH.q α (n k) ^ (-M) := by
    have := Real.rpow_pos_of_pos (CAH.q_pos hα (n k)) (-M); positivity
  rcases (hn.2.2 k).2.2 with hbig | ⟨-, hb1, hb2⟩
  · -- Case 1: `Q̄_k ≥ Q_k^A`, `u = n_k`
    have hρu : CAH.q α (n k) ^ (1 / (2 * M) ^ 4) ≤ CAH.q α (n k) := by
      calc _ ≤ CAH.q α (n k) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (CAH.q_one_le hα _) hρ1
        _ = _ := Real.rpow_one _
    obtain ⟨hS, hW⟩ := decomp_bound hα hhpos hδ0 hK hC.le (n k) (hEgen (n k) hkn hρu) (N + 1) m hmN
    refine ⟨hS, hW.trans ?_⟩
    set Γ := X / CAH.q α (n k) ^ (2 * M) ^ 5 with hΓ
    have hQU := Real.rpow_pos_of_pos (CAH.q_pos hα (n k)) ((2 * M) ^ 5)
    have hΓ0 : 0 ≤ Γ := by positivity
    have hsum := sum_block_le (u := n k) (N := N) (CK := C * K) (Γ := Γ)
      (fun s => min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5) hCK hΓ0 (by
        intro s hs
        have hs' := Finset.mem_Ico.1 hs
        by_cases hsu : s = n k
        · subst hsu
          simp only [ite_true]
          have : min (m : ℝ) (CAH.q α (n k + 1)) / CAH.q α (n k) ^ (2 * M) ^ 5 ≤ Γ :=
            div_le_div_of_nonneg_right (min_le_right _ _) hQU.le
          linarith
        · simp only [hsu, ite_false, add_zero]
          apply hG
          by_cases hsN : s < N
          · left
            exact (hn.2.2 k).2.1 s (by omega) hsN
          · right
            rw [show s = N by omega]; exact hmq)
    have hP : CAH.q α (n k) ≤ Y ^ 2 := by
      rw [hY2]; exact le_rpow_inv_of_rpow_le (CAH.q_pos hα _) (by linarith) hbig
    have hfin := hreal _ hP
    have hCΓ : C * Γ ≤ X * CAH.q α (n k) ^ (-M) := by
      have h1 := hT₃ _ hQT₃
      rw [hΓ, show C * (X / CAH.q α (n k) ^ (2 * M) ^ 5) = X * (C / CAH.q α (n k) ^ (2 * M) ^ 5) by
        ring]
      apply mul_le_mul_of_nonneg_left _ hX0.le
      rw [div_le_iff₀ hQU, ← Real.rpow_add (CAH.q_pos hα _)]
      convert h1 using 2; ring
    have hq0 := CAH.q_pos hα (n k)
    calc CAH.q α (n k) * K * (1 + 2 / (2 * π * h * δ)) +
          ∑ s ∈ Finset.Ico (n k) (N + 1), C * K * ((s : ℝ) ^ 4 +
            min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5)
        ≤ CAH.q α (n k) * K * (1 + (N : ℝ) ^ 2 / (π * hstar * η)) +
          C * K * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1) + Γ) := by
          gcongr
      _ = K * (CAH.q α (n k) * (1 + (N : ℝ) ^ 2 / (π * hstar * η)) +
          C * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1))) + K * (C * Γ) := by ring
      _ ≤ K * Y ^ 4 + K * (X * CAH.q α (n k) ^ (-M)) := by gcongr
      _ = _ := by rw [hY4]; ring
  · -- Case 2: `(Q̄_{k-1}, Q_k)` and `(Q_k, Q_{k+1})` are bridges, `u = n_{k-1} + 1`
    obtain ⟨hsj1, hlo1, hhi1⟩ := hb1
    obtain ⟨hsj2, -, -⟩ := hb2
    have hku : k ≤ n (k - 1) + 1 := by have := hn.le_self (k - 1); omega
    have hql := CAH.q_pos hα (n (k - 1) + 1)
    have hρu := rpow_inv_le_of_le_rpow hql (CAH.q_pos hα _).le (by positivity) hhi1
    obtain ⟨hS, hW⟩ := decomp_bound hα hhpos hδ0 hK hC.le (n (k - 1) + 1)
      (hEgen _ hku hρu) (N + 1) m hmN
    refine ⟨hS, hW.trans ?_⟩
    have hsum := sum_block_le (u := n (k - 1) + 1) (N := N) (CK := C * K) (Γ := 0)
      (fun s => min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5) hCK le_rfl (by
        intro s hs
        have hs' := Finset.mem_Ico.1 hs
        simp only [ite_self, add_zero]
        apply hG
        by_cases hsN : s < N
        · left
          by_cases hsk : s < n k
          · exact hsj1 s hs'.1 hsk
          · exact hsj2 s (by omega) hsN
        · right
          rw [show s = N by omega]; exact hmq)
    have hP : CAH.q α (n (k - 1) + 1) ≤ Y ^ 2 := by
      rw [hY2]
      refine (le_rpow_inv_of_rpow_le hql (by linarith) hlo1).trans ?_
      exact Real.rpow_le_rpow (CAH.q_pos hα _).le hQX (by positivity)
    have hfin := hreal _ hP
    calc CAH.q α (n (k - 1) + 1) * K * (1 + 2 / (2 * π * h * δ)) +
          ∑ s ∈ Finset.Ico (n (k - 1) + 1) (N + 1), C * K * ((s : ℝ) ^ 4 +
            min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5)
        ≤ CAH.q α (n (k - 1) + 1) * K * (1 + (N : ℝ) ^ 2 / (π * hstar * η)) +
          C * K * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1) + 0) := by
          gcongr
      _ = K * (CAH.q α (n (k - 1) + 1) * (1 + (N : ℝ) ^ 2 / (π * hstar * η)) +
          C * (((N : ℝ) + 1) * ((N : ℝ) ^ 4 + 1))) := by ring
      _ ≤ K * Y ^ 4 := by gcongr
      _ ≤ _ := by rw [hY4]; exact mul_le_mul_of_nonneg_left (by linarith) hK0

lemma birkhoffCoeff_zero (α : ℝ) (a : ℤ → ℂ) : birkhoffCoeff α 0 a = 0 := by
  funext l; simp [birkhoffCoeff, bmult]

/-- Decomposition `m = ∑_{s < v} c_s q_s` with `c_s q_s ≤ min(m, q_{s+1})`, against arbitrary
block bounds `F s`. -/
lemma decomp_bound0 (hα : Irrational α) {a : ℤ → ℂ} {h' : ℝ} (F : ℕ → ℝ)
    (hF : ∀ s, WSummable (birkhoffCoeff α (CAH.qN α s) a) h' ∧
      wnorm (birkhoffCoeff α (CAH.qN α s) a) h' ≤ F s) :
    ∀ v m : ℕ, m < CAH.qN α v → WSummable (birkhoffCoeff α m a) h' ∧
      wnorm (birkhoffCoeff α m a) h' ≤
        ∑ s ∈ Finset.range v, min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s * F s := by
  intro v
  induction v with
  | zero =>
    intro m hm
    rw [qN_zero] at hm
    obtain rfl : m = 0 := by omega
    rw [birkhoffCoeff_zero]
    refine ⟨by simp [WSummable, summable_zero], by simp [wnorm]⟩
  | succ v ih =>
    intro m hm
    have hqv : 0 < CAH.qN α v := by have := CAH.one_le_qN hα v; omega
    set c := m / CAH.qN α v with hc
    set r := m % CAH.qN α v with hr
    have hmcr : c * CAH.qN α v + r = m := by rw [hc, hr, mul_comm]; exact Nat.div_add_mod m _
    have hrlt : r < CAH.qN α v := Nat.mod_lt _ hqv
    have hrm : r ≤ m := Nat.mod_le _ _
    obtain ⟨hsr, hwr⟩ := ih r hrlt
    obtain ⟨hsq, hwq⟩ := hF v
    obtain ⟨hsm, hwm⟩ := wnorm_decomp_le α a h' c (CAH.qN α v) r hsq hsr
    rw [hmcr] at hsm hwm
    refine ⟨hsm, hwm.trans ?_⟩
    rw [Finset.sum_range_succ]
    have hqv0 := CAH.q_pos hα v
    have hwq0 : 0 ≤ wnorm (birkhoffCoeff α (CAH.qN α v) a) h' :=
      tsum_nonneg (fun l => by positivity)
    have hF0 : 0 ≤ F v := hwq0.trans hwq
    have hcq : (c : ℝ) * CAH.q α v ≤ m := by
      rw [← CAH.qN_cast hα]; exact_mod_cast (show c * CAH.qN α v ≤ m by omega)
    have hcq2 : (c : ℝ) * CAH.q α v ≤ CAH.q α (v + 1) := by
      have : c * CAH.qN α v ≤ CAH.qN α (v + 1) := by omega
      rw [← CAH.qN_cast hα, ← CAH.qN_cast hα]; exact_mod_cast this
    have hc1 : (c : ℝ) ≤ min (m : ℝ) (CAH.q α (v + 1)) / CAH.q α v := by
      rw [le_div_iff₀ hqv0]; exact le_min hcq hcq2
    have hblock : (c : ℝ) * wnorm (birkhoffCoeff α (CAH.qN α v) a) h' ≤
        min (m : ℝ) (CAH.q α (v + 1)) / CAH.q α v * F v :=
      mul_le_mul hc1 hwq hwq0 (le_trans (Nat.cast_nonneg _) hc1)
    have hsum : ∑ s ∈ Finset.range v, min (r : ℝ) (CAH.q α (s + 1)) / CAH.q α s * F s ≤
        ∑ s ∈ Finset.range v, min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s * F s := by
      apply Finset.sum_le_sum; intro s _
      have hFs : 0 ≤ F s := le_trans (tsum_nonneg (fun l => by positivity)) (hF s).2
      have := CAH.q_pos hα s
      have hrm' : (r : ℝ) ≤ m := by exact_mod_cast hrm
      gcongr
    linarith

/-- Growth bounds on `N = n_{k+1}` in terms of `Y = Q̄_k^{1/(4M)}`. -/
lemma N_bounds (hα : Irrational α) {M : ℝ} (hM : 1 < M) {n : ℕ → ℕ}
    (hn : IsAFKSeq α (2 * M) n) (k : ℕ) :
    ((n (k + 1) : ℕ) : ℝ) ^ 5 ≤ (1 + 3 / (1 / (20 * M) / (2 * M) ^ 4)) ^ 5 *
        CAH.q α (n k + 1) ^ (1 / (4 * M)) ∧
      ((n (k + 1) : ℕ) : ℝ) ^ 2 ≤ (1 + 3 / (1 / (20 * M) / (2 * M) ^ 4)) ^ 2 *
        CAH.q α (n k + 1) ^ (1 / (4 * M)) := by
  have hM0 : 0 < M := by linarith
  set X := CAH.q α (n k + 1) with hX
  have hX0 : 0 < X := CAH.q_pos hα _
  have hX1 : 1 ≤ X := CAH.q_one_le hα _
  set ε := 1 / (20 * M) / (2 * M) ^ 4 with hε
  have hε0 : 0 < ε := by positivity
  set D := 1 + 3 / ε with hD
  have hD0 : 0 < D := by positivity
  set N := n (k + 1)
  have hNle : (N : ℝ) ≤ D * X ^ (1 / (20 * M)) := by
    have h1 := idx_le_rpow hα N hε0
    have h2 : CAH.q α N ≤ X ^ ((2 * M) ^ 4) := (hn.2.2 k).1
    have h3 : CAH.q α N ^ ε ≤ X ^ (1 / (20 * M)) := by
      have := Real.rpow_le_rpow (CAH.q_pos hα N).le h2 hε0.le
      rwa [← Real.rpow_mul hX0.le, hε, show (2 * M) ^ 4 * (1 / (20 * M) / (2 * M) ^ 4) =
        1 / (20 * M) by field_simp] at this
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hD0.le)
  have hθ : (X ^ (1 / (20 * M))) ^ 5 = X ^ (1 / (4 * M)) := by
    rw [← Real.rpow_mul_natCast hX0.le]; congr 1; push_cast; field_simp; ring
  have hN5 : (N : ℝ) ^ 5 ≤ D ^ 5 * X ^ (1 / (4 * M)) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 5
    rwa [mul_pow, hθ] at this
  refine ⟨hN5, ?_⟩
  have := pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 2
  rw [mul_pow] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← hθ]
  have h1 : 1 ≤ X ^ (1 / (20 * M)) := Real.one_le_rpow hX1 (by positivity)
  exact pow_le_pow_right₀ h1 (by norm_num)

lemma small_final_real {N K Φ P C D Y X Z TM R I : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hΦ : 0 ≤ Φ) (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hY : 1 ≤ Y) (hN5 : N ^ 5 ≤ D ^ 5 * Y)
    (hX : X ≤ TM * Z) (hZ : 0 ≤ Z) (hTM : 0 ≤ TM) (hR : 0 ≤ R) (hI : I ≤ K * Φ * X) :
    (N + 1) * (K * (Φ * P + C * (N ^ 4 + 1))) + I ≤
      (R + Φ * TM + (2 * Φ * P + 4 * C) * D ^ 5 + 1) * K * (Z + Y ^ 4) := by
  have hN4 : 1 ≤ N ^ 4 := one_le_pow₀ hN
  have h1 : (N + 1) * (Φ * P + C * (N ^ 4 + 1)) ≤ (2 * Φ * P + 4 * C) * N ^ 5 := by
    have hN5' : N ≤ N ^ 5 := le_self_pow₀ hN (by norm_num)
    have e : N ^ 5 = N * N ^ 4 := by ring
    have hΦP : 0 ≤ Φ * P := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hN4 hΦP, mul_le_mul_of_nonneg_left hN4 hC]
  have hY4' : Y ≤ Y ^ 4 := le_self_pow₀ hY (by norm_num)
  have h2 : N ^ 5 ≤ D ^ 5 * Y ^ 4 := hN5.trans (mul_le_mul_of_nonneg_left hY4' (by positivity))
  have hc0 : 0 ≤ 2 * Φ * P + 4 * C := by positivity
  have h3 : (N + 1) * (Φ * P + C * (N ^ 4 + 1)) ≤ (2 * Φ * P + 4 * C) * D ^ 5 * Y ^ 4 := by
    calc _ ≤ (2 * Φ * P + 4 * C) * N ^ 5 := h1
      _ ≤ (2 * Φ * P + 4 * C) * (D ^ 5 * Y ^ 4) := mul_le_mul_of_nonneg_left h2 hc0
      _ = _ := by ring
  have h4 : I ≤ K * (Φ * TM * Z) := by
    have := mul_le_mul_of_nonneg_left hX (show 0 ≤ K * Φ by positivity)
    nlinarith
  have hY40 : 0 ≤ Y ^ 4 := by positivity
  have hA0 : 0 ≤ (2 * Φ * P + 4 * C) * D ^ 5 := by positivity
  have hB0 : 0 ≤ Φ * TM := by positivity
  have h5 : (N + 1) * (Φ * P + C * (N ^ 4 + 1)) + Φ * TM * Z ≤
      (R + Φ * TM + (2 * Φ * P + 4 * C) * D ^ 5 + 1) * (Z + Y ^ 4) := by
    nlinarith [mul_nonneg hR hZ, mul_nonneg hR hY40, mul_nonneg hB0 hY40,
      mul_nonneg hA0 hZ]
  have h6 := mul_le_mul_of_nonneg_left h5 hK
  nlinarith

/-- Per-block bound used in `denjoy_small`. -/
lemma small_term_bound (hα : Irrational α) {M T T' K Φ C : ℝ} {n : ℕ → ℕ}
    (hn : IsAFKSeq α (2 * M) n) (k m : ℕ) (hmq : (m : ℝ) ≤ CAH.q α (n (k + 1)))
    (hkT : CAH.q α (n k) < T) (hTT' : T ≤ T') (hT'1 : 1 ≤ T') (hA1 : 1 ≤ 2 * M)
    (hAU : 2 * M ≤ (2 * M) ^ 5) (hK0 : 0 ≤ K) (hΦ1 : 1 ≤ Φ) (hC : 0 < C)
    (s : ℕ) (hs : s ∈ Finset.range (n (k + 1) + 1)) :
    min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s *
      (if CAH.q α s < T' then CAH.q α s * K * Φ else
        C * K * ((s : ℝ) ^ 4 * CAH.q α s / CAH.q α (s + 1) +
          CAH.q α s / CAH.q α s ^ (2 * M) ^ 5)) ≤
      K * (Φ * T' ^ (2 * M) + C * (((n (k + 1) : ℕ) : ℝ) ^ 4 + 1)) +
        (if s = n k then K * Φ * CAH.q α (n k + 1) else 0) := by
  set N := n (k + 1) with hN
  set X := CAH.q α (n k + 1) with hX
  have hnn : n k < N := hn.1 (Nat.lt_succ_self k)
  have hsbig : ∀ s, ¬ CAH.q α s < T' → n k < s := by
    intro s hs
    by_contra hc; push Not at hc
    have := q_mono hα hc
    exact hs (by linarith)
  have hsN : s ≤ N := by have := Finset.mem_range.1 hs; omega
  have hqs := CAH.q_pos hα s
  have hmin0 : 0 ≤ min (m : ℝ) (CAH.q α (s + 1)) :=
    le_min (Nat.cast_nonneg _) (CAH.q_pos hα _).le
  have hg0 : 0 ≤ K * (Φ * T' ^ (2 * M) + C * ((N : ℝ) ^ 4 + 1)) := by positivity
  by_cases hsT : CAH.q α s < T'
  · simp only [hsT, ite_true]
    have e : min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s * (CAH.q α s * K * Φ) =
        min (m : ℝ) (CAH.q α (s + 1)) * (K * Φ) := by field_simp
    rw [e]
    have hKΦ : 0 ≤ K * Φ := by positivity
    by_cases hsk : s = n k
    · simp only [hsk, ite_true]
      have : min (m : ℝ) (CAH.q α (n k + 1)) * (K * Φ) ≤ K * Φ * X := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) hKΦ
      linarith
    · simp only [hsk, ite_false, add_zero]
      have hmin : min (m : ℝ) (CAH.q α (s + 1)) ≤ T' ^ (2 * M) := by
        have hT'le : T' ≤ T' ^ (2 * M) := Real.self_le_rpow_of_one_le hT'1 hA1
        rcases lt_or_gt_of_ne hsk with hlt | hgt
        · have := q_mono hα (show s + 1 ≤ n k by omega)
          exact (min_le_right _ _).trans (by linarith)
        · by_cases hsN' : s < N
          · have h1 := (hn.2.2 k).2.1 s (by omega) hsN'
            have h2 : CAH.q α s ^ (2 * M) ≤ T' ^ (2 * M) :=
              Real.rpow_le_rpow hqs.le hsT.le (by linarith)
            exact (min_le_right _ _).trans (h1.trans h2)
          · have hsN2 : s = N := by omega
            have hqN : CAH.q α N < T' := hsN2 ▸ hsT
            exact (min_le_left _ _).trans (by linarith)
      have : min (m : ℝ) (CAH.q α (s + 1)) * (K * Φ) ≤ T' ^ (2 * M) * (K * Φ) :=
        mul_le_mul_of_nonneg_right hmin hKΦ
      have : T' ^ (2 * M) * (K * Φ) ≤ K * (Φ * T' ^ (2 * M) + C * ((N : ℝ) ^ 4 + 1)) := by
        have : 0 ≤ K * (C * ((N : ℝ) ^ 4 + 1)) := by positivity
        have e : T' ^ (2 * M) * (K * Φ) = K * (Φ * T' ^ (2 * M)) := by ring
        rw [e, mul_add]; linarith
      linarith
  · simp only [hsT, ite_false]
    have hks := hsbig s hsT
    simp only [show s ≠ n k by omega, ite_false, add_zero]
    have hqs1 := CAH.q_pos hα (s + 1)
    have hqU := Real.rpow_pos_of_pos hqs ((2 * M) ^ 5)
    have e : min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s * (C * K * ((s : ℝ) ^ 4 *
        CAH.q α s / CAH.q α (s + 1) + CAH.q α s / CAH.q α s ^ (2 * M) ^ 5)) =
        C * K * ((s : ℝ) ^ 4 * (min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α (s + 1)) +
          min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5) := by
      field_simp
    rw [e]
    have h1 : min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α (s + 1) ≤ 1 := by
      rw [div_le_one hqs1]; exact min_le_right _ _
    have h2 : (s : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsN) 4
    have h3 : min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5 ≤ 1 := by
      apply G_le_one hα hA1 hAU
      by_cases hsN' : s < N
      · left; exact (hn.2.2 k).2.1 s (by omega) hsN'
      · right; rw [show s = N by omega]; exact hmq
    have h4 : (s : ℝ) ^ 4 * (min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α (s + 1)) ≤ (N : ℝ) ^ 4 :=
      by
        have : 0 ≤ min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α (s + 1) := by positivity
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) s) 4]
    have hCK : 0 ≤ C * K := by positivity
    have : C * K * ((s : ℝ) ^ 4 * (min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α (s + 1)) +
        min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s ^ (2 * M) ^ 5) ≤
        C * K * ((N : ℝ) ^ 4 + 1) := mul_le_mul_of_nonneg_left (by linarith) hCK
    have : 0 ≤ K * (Φ * T' ^ (2 * M)) := by positivity
    nlinarith

/-- The estimates of Proposition `denjoy` for the (finitely many relevant) indices with
`Q_k < T`, with a constant depending on `T`. -/
lemma denjoy_small {hstar η M T : ℝ} (hh : 0 < hstar) (hη : 0 < η) (hM : 1 < M) (hT : 1 ≤ T) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ α : ℝ, Irrational α → ∀ n : ℕ → ℕ, IsAFKSeq α (2 * M) n →
      ∀ k : ℕ, 1 ≤ k → CAH.q α (n k) < T →
      ∀ (h K : ℝ) (a : ℤ → ℂ), hstar ≤ h →
      (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
      wnorm (birkhoffCoeff α (CAH.qN α (n k)) a) (h * (1 - η / (k : ℝ) ^ 2)) ≤
          C' * K * CAH.q α (n k) ^ (-M) ∧
      ∀ m : ℕ, m ≤ CAH.qN α (n (k + 1)) →
        wnorm (birkhoffCoeff α m a) (h * (1 - η / (k : ℝ) ^ 2)) ≤
          C' * K * (CAH.q α (n k + 1) * CAH.q α (n k) ^ (-M) +
            CAH.q α (n k + 1) ^ (1 / M)) := by
  have hM0 : 0 < M := by linarith
  have hA1 : 1 ≤ 2 * M := by linarith
  have hAU : 2 * M ≤ (2 * M) ^ 5 := le_self_pow₀ hA1 (by norm_num)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = π * hstar * η := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 + 3 * Real.log T := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκ]; have := Real.log_nonneg hT; linarith
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = 1 + κ ^ 2 / E := ⟨_, rfl⟩
  have hΦ1 : 1 ≤ Φ := by rw [hΦ]; have : 0 ≤ κ ^ 2 / E := by positivity
                         linarith
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ, T' = max T ((κ ^ 2 / η) ^ 2) := ⟨_, rfl⟩
  have hTT' : T ≤ T' := by rw [hT']; exact le_max_left _ _
  have hT'1 : 1 ≤ T' := hT.trans hTT'
  obtain ⟨C, hC, hden⟩ := denjoy_el hh hη ((2 * M) ^ 5)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + 3 / (1 / (20 * M) / (2 * M) ^ 4) := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  have hTM : 0 < T ^ M := Real.rpow_pos_of_pos (by linarith) M
  have hT'A : 1 ≤ T' ^ (2 * M) := Real.one_le_rpow hT'1 (by linarith)
  refine ⟨Φ * T * T ^ M + Φ * T ^ M + (2 * Φ * T' ^ (2 * M) + 4 * C) * D ^ 5 + 1,
    by positivity, ?_⟩
  intro α hα n hn k hk hkT h K a hh' hK
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hhpos : 0 < h := by linarith
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set δ := η / (k : ℝ) ^ 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set Q := CAH.q α (n k) with hQ
  have hQ0 : 0 < Q := CAH.q_pos hα _
  have hkκ : (k : ℝ) ≤ κ := by
    have h1 : (k : ℝ) ≤ n k := by exact_mod_cast hn.le_self k
    have h2 := idx_le_log hα (n k)
    have h3 : Real.log Q ≤ Real.log T := Real.log_le_log hQ0 hkT.le
    rw [hκ]; linarith
  have hfac : 1 + 2 / (2 * π * h * δ) ≤ Φ := by
    have e : 2 / (2 * π * h * δ) = (k : ℝ) ^ 2 / (π * h * η) := by
      rw [hδ]; field_simp
    rw [e, hΦ]
    have h1 : (k : ℝ) ^ 2 / (π * h * η) ≤ κ ^ 2 / (π * h * η) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) hkκ 2) (by positivity)
    have h2 : κ ^ 2 / (π * h * η) ≤ κ ^ 2 / E := by
      rw [hE]; apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left hh' pi_pos.le
      nlinarith
    linarith
  have hQM : 1 ≤ T ^ M * Q ^ (-M) := by
    rw [Real.rpow_neg hQ0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hQ0 M),
      one_mul]
    exact Real.rpow_le_rpow hQ0.le hkT.le hM0.le
  have hQM0 : 0 ≤ Q ^ (-M) := (Real.rpow_pos_of_pos hQ0 _).le
  refine ⟨?_, fun m hm => ?_⟩
  · -- `S_{Q_k}`: trivial bound
    obtain ⟨-, hw⟩ := wnorm_trivial α hhpos hδ0 hK (CAH.qN α (n k))
    rw [CAH.qN_cast hα] at hw
    refine hw.trans ?_
    calc Q * K * (1 + 2 / (2 * π * h * δ)) ≤ T * K * Φ := by gcongr
      _ ≤ T * K * Φ * (T ^ M * Q ^ (-M)) := by
          have : 0 ≤ T * K * Φ := by positivity
          nlinarith
      _ = (Φ * T * T ^ M) * K * Q ^ (-M) := by ring
      _ ≤ _ := by
          gcongr
          have : 0 ≤ Φ * T ^ M + (2 * Φ * T' ^ (2 * M) + 4 * C) * D ^ 5 := by positivity
          linarith
  · -- `S_m` for `m ≤ Q_{k+1}`
    set N := n (k + 1) with hN
    have hnn : n k < N := hn.1 (Nat.lt_succ_self k)
    have hN1 : 1 ≤ N := by omega
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    set X := CAH.q α (n k + 1) with hX
    have hX0 : 0 < X := CAH.q_pos hα _
    have hmN : m < CAH.qN α (N + 1) := by
      obtain ⟨j, hj⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
      have := qN_lt_qN_succ hα j
      rw [hj] at hm ⊢
      exact lt_of_le_of_lt hm this
    have hmq : (m : ℝ) ≤ CAH.q α N := by rw [← CAH.qN_cast hα]; exact_mod_cast hm
    -- block bounds
    let F : ℕ → ℝ := fun s => if CAH.q α s < T' then CAH.q α s * K * Φ else
      C * K * ((s : ℝ) ^ 4 * CAH.q α s / CAH.q α (s + 1) + CAH.q α s / CAH.q α s ^ (2 * M) ^ 5)
    have hsbig : ∀ s, ¬ CAH.q α s < T' → n k < s := by
      intro s hs
      by_contra hc; push Not at hc
      have := q_mono hα hc
      exact hs (by linarith)
    have hF : ∀ s, WSummable (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ∧
        wnorm (birkhoffCoeff α (CAH.qN α s) a) (h * (1 - δ)) ≤ F s := by
      intro s
      by_cases hs : CAH.q α s < T'
      · obtain ⟨h1, h2⟩ := wnorm_trivial α hhpos hδ0 hK (CAH.qN α s)
        rw [CAH.qN_cast hα] at h2
        refine ⟨h1, h2.trans ?_⟩
        simp only [F, hs, ite_true]
        have := CAH.q_pos hα s
        gcongr
      · simp only [F, hs, ite_false]
        have hks : k ≤ s := le_trans (hn.le_self k) (hsbig s hs).le
        have hksr : (k : ℝ) ≤ s := by exact_mod_cast hks
        have hδ1 : 1 / Real.sqrt (CAH.q α s) ≤ δ := by
          push Not at hs
          have hsq : κ ^ 2 / η ≤ Real.sqrt (CAH.q α s) := by
            rw [Real.le_sqrt (by positivity) (by linarith)]
            exact (le_max_right _ _).trans (hT' ▸ hs)
          have hsq0 : 0 < Real.sqrt (CAH.q α s) := Real.sqrt_pos.2 (CAH.q_pos hα s)
          rw [hδ, div_le_div_iff₀ hsq0 (by positivity), one_mul]
          rw [div_le_iff₀ hη] at hsq
          have : (k : ℝ) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by linarith) hkκ 2
          linarith
        have hδ2 : η / (10 * (s : ℝ) ^ 2) ≤ δ :=
          div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)
        exact hden α hα s s le_rfl h δ K a hh' hδ1 hδ2 hK
    obtain ⟨-, hW⟩ := decomp_bound0 hα F hF (N + 1) m hmN
    refine hW.trans ?_
    -- per-term bounds
    set g : ℕ → ℝ := fun s => K * (Φ * T' ^ (2 * M) + C * ((N : ℝ) ^ 4 + 1)) +
      (if s = n k then K * Φ * X else 0) with hg
    have hterm : ∀ s ∈ Finset.range (N + 1),
        min (m : ℝ) (CAH.q α (s + 1)) / CAH.q α s * F s ≤ g s := fun s hs =>
      small_term_bound hα hn k m hmq hkT hTT' hT'1 hA1 hAU hK0 hΦ1 hC s hs
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [g]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Finset.sum_ite_eq',
      nsmul_eq_mul]
    have hite : (if n k ∈ Finset.range (N + 1) then K * Φ * X else 0) ≤ K * Φ * X := by
      split_ifs <;> [exact le_rfl; positivity]
    obtain ⟨hN5, -⟩ := N_bounds hα hM hn k
    rw [← hD, ← hN, ← hX] at hN5
    have hY1 : 1 ≤ X ^ (1 / (4 * M)) := Real.one_le_rpow (CAH.q_one_le hα _) (by positivity)
    have hY4 : (X ^ (1 / (4 * M))) ^ 4 = X ^ (1 / M) := by
      rw [← Real.rpow_mul_natCast hX0.le]; congr 1; push_cast; field_simp
    have hXQ : X ≤ T ^ M * (X * Q ^ (-M)) := by
      calc X = X * 1 := (mul_one X).symm
        _ ≤ X * (T ^ M * Q ^ (-M)) := mul_le_mul_of_nonneg_left hQM hX0.le
        _ = _ := by ring
    have hfin := small_final_real (N := (N : ℝ)) (K := K) (Φ := Φ) (P := T' ^ (2 * M)) (C := C)
      (D := D) (Y := X ^ (1 / (4 * M))) (R := Φ * T * T ^ M) hNr hK0 (by linarith)
      (by linarith) hC.le hD0.le hY1 hN5 hXQ (by positivity) hTM.le (by positivity) hite
    rw [hY4] at hfin
    push_cast
    exact hfin

end Cor4

/-! ## Proposition `denjoy` -/

/-- **Proposition `denjoy`** (coefficient form).  Given `h_* > 0`, `η > 0` and `M > 1` there is
`C = C(h_*, η, M) > 0` such that for every irrational `α` there is a subsequence
`Q_k = q_{n_k}` of denominators (`Q̄_k = q_{n_k+1}`) with `Q_0 = 1` and, for every `k`:
* `Q_{k+1} ≤ Q̄_k^{16M⁴}`;
and, for `k > 0`, every `h ≥ h_*` and `φ̂` with `|φ̂(l)| e^{2π|l|h} ≤ K` (`l ≠ 0`), with
`h_k = h(1 - η/k²)`:
* `‖S_{Q_k}φ - Q_kφ̂(0)‖_{h_k} ≤ C K (Q_k^{-M} + Q̄_k^{-1+1/M})`;
* `‖S_mφ - mφ̂(0)‖_{h_k} ≤ C K (Q̄_k Q_k^{-M} + Q̄_k^{1/M})` for every `m ≤ Q_{k+1}`.

Here `‖·‖_{h'}` is the weighted coefficient norm `wnorm` (which dominates the sup norm on the
strip `|Im z| ≤ h'`, `norm_fourierC_le_wnorm`), `K` plays the role of `‖φ - φ̂(0)‖_h`.
Deviations: the paper's `‖S_lφ - lφ̂(0)‖ ≤ C‖φ - φ̂(0)‖(Q̄_kQ_k^{-M} + Q̄_k^{1/M})` is stated
exactly; the paper's restriction `η < 1` is not needed in coefficient form.  Internally the
subsequence uses `CD(A,A,A⁴)` bridges and `U = A⁵` (see `dioph_bridge`, `cor3`). -/
theorem denjoy {hstar η M : ℝ} (hh : 0 < hstar) (hη : 0 < η) (hM : 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, Irrational α → ∃ n : ℕ → ℕ, StrictMono n ∧ n 0 = 0 ∧
      ∀ k : ℕ, CAH.q α (n (k + 1)) ≤ CAH.q α (n k + 1) ^ (16 * M ^ 4) ∧
      (0 < k → ∀ (h K : ℝ) (a : ℤ → ℂ), hstar ≤ h →
        (∀ l : ℤ, l ≠ 0 → ‖a l‖ * Real.exp (2 * π * |(l : ℝ)| * h) ≤ K) →
        wnorm (birkhoffCoeff α (CAH.qN α (n k)) a) (h * (1 - η / (k : ℝ) ^ 2)) ≤
            C * K * (CAH.q α (n k) ^ (-M) + CAH.q α (n k + 1) ^ (-1 + 1 / M)) ∧
        ∀ m : ℕ, m ≤ CAH.qN α (n (k + 1)) →
          wnorm (birkhoffCoeff α m a) (h * (1 - η / (k : ℝ) ^ 2)) ≤
            C * K * (CAH.q α (n k + 1) * CAH.q α (n k) ^ (-M) +
              CAH.q α (n k + 1) ^ (1 / M))) := by
  obtain ⟨T₁, hT₁, h3⟩ := cor3_Q hh hη hM
  obtain ⟨T₂, hT₂, h4⟩ := cor4 hh hη hM
  obtain ⟨C', hC', hsmall⟩ := denjoy_small hh hη hM
    (show 1 ≤ max T₁ T₂ by linarith [le_max_left T₁ T₂])
  refine ⟨C' + 1, by positivity, fun α hα => ?_⟩
  obtain ⟨n, hn⟩ := exists_isAFKSeq hα (show 1 < 2 * M by linarith)
  refine ⟨n, hn.1, hn.2.1, fun k => ⟨?_, fun hk h K a hh' hK => ?_⟩⟩
  · rw [show (16 * M ^ 4 : ℝ) = (2 * M) ^ 4 by ring]; exact (hn.2.2 k).1
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 1 one_ne_zero)
  have hp1 : 0 ≤ CAH.q α (n k) ^ (-M) := (Real.rpow_pos_of_pos (CAH.q_pos hα _) _).le
  have hp2 : 0 ≤ CAH.q α (n k + 1) ^ (-1 + 1 / M) := (Real.rpow_pos_of_pos (CAH.q_pos hα _) _).le
  have hp3 : 0 ≤ CAH.q α (n k + 1) * CAH.q α (n k) ^ (-M) :=
    mul_nonneg (CAH.q_pos hα _).le hp1
  have hp4 : 0 ≤ CAH.q α (n k + 1) ^ (1 / M) := (Real.rpow_pos_of_pos (CAH.q_pos hα _) _).le
  have hmono : ∀ x : ℝ, 0 ≤ x → K * x ≤ (C' + 1) * K * x := by
    intro x hx; have := mul_nonneg hK0 hx; nlinarith
  by_cases hkT : max T₁ T₂ ≤ CAH.q α (n k)
  · refine ⟨?_, fun m hm => ?_⟩
    · exact (h3 α hα n hn k ((le_max_left _ _).trans hkT) h _ K a hh' le_rfl hK).trans
        (hmono _ (by positivity))
    · exact (h4 α hα n hn k ((le_max_right _ _).trans hkT) h _ K a hh' le_rfl hK m hm).2.trans
        (hmono _ (by positivity))
  · push Not at hkT
    obtain ⟨s1, s2⟩ := hsmall α hα n hn k hk hkT h K a hh' hK
    refine ⟨s1.trans ?_, fun m hm => (s2 m hm).trans ?_⟩
    · have := mul_nonneg hK0 hp2
      have := mul_nonneg hK0 hp1
      nlinarith
    · have := mul_nonneg hK0 (add_nonneg hp3 hp4)
      nlinarith

end Red.AFK
