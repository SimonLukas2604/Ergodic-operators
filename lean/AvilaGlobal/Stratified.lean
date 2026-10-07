/-
# Consequences: piecewise affinity, the dichotomy, and stratified analyticity
  (paper §1.2–1.3: Remark `omega real`, Corollary `alter`, Proposition `pluri`,
  Theorems `e`, `v`, `frequen`)

* `L_neg` — for `SL(2,ℝ)`-valued (real-symmetric) cocycles, `ε ↦ L(α, A_ε)` is even.
* `tendsto_accel` — the acceleration is a genuine one-sided limit (convexity).
* `accel_nonneg`, `isRegular_iff_accel_eq_zero` — Remark `omega real`.
* `L_piecewise_affine` — quantization makes `ε ↦ L(α, A_ε)` piecewise affine.
* `uh_imp_regular`, `uh_iff_regular` — the easy direction, and the full **Theorem
  `uniformly hyperbolic`**.
* `alter` — **Corollary `alter`**.
* `OmegaSet`, `Ldj` — the sets `Ω_{δ,j}` and the functions `L_{δ,j}`; `Ldj_eq` — well-defined.
* `pluri_mem` — second part of **Proposition `pluri`**; `pluri_open_analytic`,
  `pluri_open_smooth` — first part, for analytic families.
* `stratified_energy`, `stratified_potential`, `stratified_frequency` — **Theorems `e`, `v`,
  `frequen`**.
-/
import AvilaGlobal.UniformHyperbolicity
import AvilaGlobal.UHOpen
import AvilaGlobal.RegularUH
import AvilaGlobal.UHAnalytic

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate ContDiff
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

variable [hH : Hypotheses]
include hH

variable {δ : ℝ} {A : ℂ → M2} {α : ℝ}

/-! ### Helpers -/

lemma cshift_zero (A : ℂ → M2) : cshift A 0 = A := by
  funext z; simp [cshift]

lemma strip_mono {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) : strip δ₁ ⊆ strip δ₂ := fun _ hz =>
  lt_of_lt_of_le hz h

lemma IsAnalyticCocycle.mono (hA : IsAnalyticCocycle δ A) {δ' : ℝ} (h0 : 0 < δ') (h : δ' ≤ δ) :
    IsAnalyticCocycle δ' A :=
  ⟨h0, hA.holo.mono (strip_mono h), hA.periodic, fun z hz => hA.det_eq_one z (strip_mono h hz)⟩

lemma mapsTo_cshift {δ ε : ℝ} : MapsTo (fun z : ℂ => z + ε * I) (strip (δ - |ε|)) (strip δ) := by
  intro z hz
  simp only [strip, Set.mem_ofPred_eq, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
    I_re, mul_zero, add_zero] at hz ⊢
  calc |z.im + ε| ≤ |z.im| + |ε| := abs_add_le _ _
    _ < δ := by linarith

lemma mem_interior_Ioo_of_abs {δ ε : ℝ} (hε : |ε| < δ) : ε ∈ interior (Ioo (-δ) δ) := by
  rw [interior_Ioo]; exact abs_lt.mp hε

lemma int_eq_of_abs_lt {m n : ℤ} (h : |2 * Real.pi * m - 2 * Real.pi * n| < Real.pi) : m = n := by
  have h' : |(m : ℝ) - n| < 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    by_contra hc
    push Not at hc
    nlinarith [Real.pi_pos]
  rw [← Int.cast_sub, ← Int.cast_abs] at h'
  have : |m - n| < 1 := by exact_mod_cast h'
  rw [abs_lt] at this
  omega

/-- A function with constant derivative `c` on `(-r, r)` is affine there. -/
lemma affine_of_hasDerivAt {f : ℝ → ℝ} {c r : ℝ} (h : ∀ x, |x| < r → HasDerivAt f c x) :
    ∀ t, |t| < r → f t = f 0 + c * t := by
  intro t ht
  have ht' := abs_lt.mp ht
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg t) ht
  rcases lt_trichotomy t 0 with h0 | h0 | h0
  · obtain ⟨ξ, -, e⟩ := exists_hasDerivAt_eq_slope f (fun _ => c) h0
      (fun x hx => (h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)).continuousAt
        |>.continuousWithinAt)
      (fun x hx => h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    rw [eq_div_iff (sub_ne_zero.mpr h0.ne')] at e
    linarith
  · subst h0; simp
  · obtain ⟨ξ, -, e⟩ := exists_hasDerivAt_eq_slope f (fun _ => c) h0
      (fun x hx => (h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)).continuousAt
        |>.continuousWithinAt)
      (fun x hx => h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    rw [eq_div_iff (sub_ne_zero.mpr h0.ne')] at e
    linarith

/-- The right derivative of the convex function `ε ↦ L(α, A_ε)`. -/
lemma hasDerivWithinAt_rd (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    HasDerivWithinAt (L α A) (derivWithin (L α A) (Ioi ε) ε) (Ioi ε) ε :=
  (L_convexOn hA α).hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Ioo_of_abs hε)

lemma tendsto_slope_rd (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    Tendsto (slope (L α A) ε) (𝓝[>] ε) (𝓝 (derivWithin (L α A) (Ioi ε) ε)) :=
  (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (hasDerivWithinAt_rd hA α hε)

lemma tendsto_add_nhdsGT (ε : ℝ) : Tendsto (fun t : ℝ => t + ε) (𝓝[>] 0) (𝓝[>] ε) := by
  have hc : Continuous fun t : ℝ => t + ε := continuous_id.add continuous_const
  have h := (hc.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)).tendsto_nhdsWithin
    (t := Ioi ε) (fun t ht => by simp only [mem_Ioi] at ht ⊢; linarith)
  simpa using h

lemma tendsto_quot (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    Tendsto (fun t => (L α A (t + ε) - L α A ε) / (2 * Real.pi * t)) (𝓝[>] 0)
      (𝓝 (derivWithin (L α A) (Ioi ε) ε / (2 * Real.pi))) := by
  have h := ((tendsto_slope_rd hA α hε).comp (tendsto_add_nhdsGT ε)).div_const (2 * Real.pi)
  refine h.congr (fun t => ?_)
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_right]
  ring

lemma accel_cshift_eq (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    accel α (cshift A ε) = derivWithin (L α A) (Ioi ε) ε / (2 * Real.pi) := by
  have e : accel α (cshift A ε) = limUnder (𝓝[>] (0 : ℝ))
      (fun t => (L α A (t + ε) - L α A ε) / (2 * Real.pi * t)) := by
    simp only [accel, L_cshift, zero_add]
  rw [e, (tendsto_quot hA α hε).limUnder_eq]

lemma rd_eq (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    derivWithin (L α A) (Ioi ε) ε = 2 * Real.pi * accel α (cshift A ε) := by
  rw [accel_cshift_eq hA α hε]
  exact (mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)).symm

lemma accel_eq_rd (hA : IsAnalyticCocycle δ A) (α : ℝ) :
    accel α A = derivWithin (L α A) (Ioi 0) 0 / (2 * Real.pi) := by
  have := accel_cshift_eq hA α (ε := 0) (by simpa using hA.pos)
  rwa [cshift_zero] at this

/-- Between two points with the same right derivative `c`, `L` is affine with slope `c`. -/
lemma L_sub_eq_of_rd (hA : IsAnalyticCocycle δ A) (α : ℝ) {x y c : ℝ} (hx : |x| < δ)
    (hy : |y| < δ) (hxy : x < y) (hcx : derivWithin (L α A) (Ioi x) x = c)
    (hcy : derivWithin (L α A) (Ioi y) y = c) :
    L α A y - L α A x = c * (y - x) := by
  have hc := L_convexOn hA α
  have hxi := mem_interior_Ioo_of_abs hx
  have hyi := mem_interior_Ioo_of_abs hy
  have h1 := hc.rightDeriv_le_slope_of_mem_interior hxi (abs_lt.mp hy) hxy
  have h2 := hc.slope_le_leftDeriv_of_mem_interior (abs_lt.mp hx) hyi hxy
  have h3 := hc.leftDeriv_le_rightDeriv_of_mem_interior hyi
  have hs : slope (L α A) x y = c := le_antisymm (by linarith) (by linarith)
  rw [slope_def_field, div_eq_iff (sub_ne_zero.mpr hxy.ne')] at hs
  exact hs

lemma L_eq_of_accel_eq (hA : IsAnalyticCocycle δ A) {c x y : ℝ} (hx : x ∈ Ioo 0 δ)
    (hy : y ∈ Ioo 0 δ) (hcx : accel α (cshift A x) = c) (hcy : accel α (cshift A y) = c) :
    L α A x - 2 * Real.pi * c * x = L α A y - 2 * Real.pi * c * y := by
  have hx' : |x| < δ := by rw [abs_of_pos hx.1]; exact hx.2
  have hy' : |y| < δ := by rw [abs_of_pos hy.1]; exact hy.2
  have rx : derivWithin (L α A) (Ioi x) x = 2 * Real.pi * c := by rw [rd_eq hA α hx', hcx]
  have ry : derivWithin (L α A) (Ioi y) y = 2 * Real.pi * c := by rw [rd_eq hA α hy', hcy]
  rcases lt_trichotomy x y with h | h | h
  · have := L_sub_eq_of_rd hA α hx' hy' h rx ry; linarith
  · rw [h]
  · have := L_sub_eq_of_rd hA α hy' hx' h ry rx; linarith

lemma norm_map_conj (M : M2) : ‖M.map conj‖ = ‖M‖ := by
  simp [Matrix.linfty_opNorm_def]

omit hH in
/-- Real symmetry on the strip: `A(z̄) = conj A(z)` for `|Im z| < δ`. -/
def IsRealSymmetricOn (δ : ℝ) (A : ℂ → M2) : Prop := ∀ z ∈ strip δ, A (conj z) = (A z).map conj

lemma L_neg_of (hsym : IsRealSymmetricOn δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    L α A (-ε) = L α A ε := by
  have hs : ∀ x, shift A (-ε) x = (shift A ε x).map conj := by
    intro x
    simp only [shift]
    rw [← hsym _ (mem_strip_shift hε x)]
    congr 1
    apply Complex.ext <;> simp
  have hit : ∀ n x, iter α (shift A (-ε)) n x = (iter α (shift A ε) n x).map conj := by
    intro n x
    induction n with
    | zero => simp [iter]
    | succ n ih => rw [iter, iter, ih, hs, Matrix.map_mul]
  simp only [L, lyapunov, lyapSeq, hit, norm_map_conj]

/-- The family `p ↦ A_p` (`|p| < δ/2`) is a real-analytic family of cocycles on `|Im z| < δ/2`. -/
lemma cshift_family (hA : IsAnalyticCocycle δ A) :
    IsAnalyticCocycleFamily (δ / 2) (Ioo (-(δ / 2)) (δ / 2)) (fun p : ℝ => cshift A p) := by
  have hδ := hA.pos
  refine ⟨isOpen_Ioo, fun p hp => ?_, ?_⟩
  · have hp2 : |p| < δ / 2 := abs_lt.mpr hp
    exact (hA.cshift (by linarith)).mono (by linarith) (by linarith)
  · rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hp2 : |p| < δ / 2 := abs_lt.mpr hp
    have hw : z + p * I ∈ strip δ := mapsTo_cshift (δ := δ) (ε := p)
      (show z ∈ strip (δ - |p|) from (by have : |z.im| < δ / 2 := hz; linarith : |z.im| < δ - |p|))
    have hAw : AnalyticAt ℝ A (z + p * I) :=
      (hA.holo.analyticAt ((isOpen_strip δ).mem_nhds hw)).restrictScalars
    have h1 : AnalyticAt ℝ (fun q : ℝ × ℂ => (q.1 : ℂ)) (p, z) :=
      (Complex.ofRealCLM.analyticAt _).comp analyticAt_fst
    have hin : AnalyticAt ℝ (fun q : ℝ × ℂ => q.2 + (q.1 : ℂ) * I) (p, z) :=
      analyticAt_snd.add (h1.mul analyticAt_const)
    exact AnalyticAt.comp (g := A) (f := fun q : ℝ × ℂ => q.2 + (q.1 : ℂ) * I) hAw hin

/-! ### Real symmetry, the acceleration as a limit, piecewise affinity -/

/-- For real-symmetric `A`, `L(α, A_{-ε}) = L(α, A_ε)`. -/
theorem L_neg (hsym : IsRealSymmetric A) (α ε : ℝ) : L α A (-ε) = L α A ε :=
  L_neg_of (δ := |ε| + 1) (fun z _ => hsym z) α (by linarith)

/-- By convexity, the one-sided limit defining the acceleration exists (for any `α`). -/
theorem tendsto_accel (hA : IsAnalyticCocycle δ A) (α : ℝ) :
    Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0) (𝓝 (accel α A)) := by
  have h0 : |(0 : ℝ)| < δ := by simpa using hA.pos
  rw [accel_eq_rd hA α]
  simpa using tendsto_quot hA α h0

/-- The acceleration of a shifted cocycle is the right derivative of `ε ↦ L(α, A_ε)`, divided
by `2π`. -/
theorem accel_cshift (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ} (hε : |ε| < δ) :
    accel α (cshift A ε) = derivWithin (L α A) (Ici ε) ε / (2 * Real.pi) := by
  rw [accel_cshift_eq hA α hε, derivWithin_Ioi_eq_Ici]

lemma accel_nonneg_of (hA : IsAnalyticCocycle δ A) (hsym : IsRealSymmetricOn δ A) (α : ℝ) :
    0 ≤ accel α A := by
  have hc := L_convexOn hA α
  refine ge_of_tendsto (tendsto_accel hA α) ?_
  filter_upwards [Ioo_mem_nhdsGT hA.pos] with t ht
  have h1 : t ∈ Ioo (-δ) δ := ⟨by linarith [ht.1, ht.2], ht.2⟩
  have h2 : -t ∈ Ioo (-δ) δ := ⟨by linarith [ht.2], by linarith [ht.1, hA.pos]⟩
  have key := hc.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at key
  have e : (1 / 2 : ℝ) * t + 1 / 2 * (-t) = 0 := by ring
  rw [e, L_neg_of hsym α (ε := t) (by rw [abs_of_pos ht.1]; exact ht.2)] at key
  exact div_nonneg (by linarith) (mul_pos (by positivity) ht.1).le

/-- **Remark `omega real`** (first part): real-symmetric cocycles have `ω(α, A) ≥ 0`. -/
theorem accel_nonneg (hA : IsAnalyticCocycle δ A) (hsym : IsRealSymmetric A) (α : ℝ) :
    0 ≤ accel α A :=
  accel_nonneg_of hA (fun z _ => hsym z) α

/-- Quantization makes `ε ↦ L(α, A_ε)` piecewise affine with slopes in `2πℤ`: every
`ε ∈ (-δ, δ)` has a right neighbourhood on which it is affine with slope `2π ω(α, A_ε)`. -/
theorem L_piecewise_affine (hA : IsAnalyticCocycle δ A) (hα : Irrational α) {ε : ℝ}
    (hε : |ε| < δ) :
    ∃ η > 0, ∀ t ∈ Icc ε (ε + η),
      L α A t = L α A ε + 2 * Real.pi * accel α (cshift A ε) * (t - ε) := by
  have hc := L_convexOn hA α
  have hint : ∀ t, |t| < δ → ∃ m : ℤ, derivWithin (L α A) (Ioi t) t = 2 * Real.pi * m := by
    intro t ht
    obtain ⟨m, hm⟩ := (quantized (hA.cshift ht) hα).2
    exact ⟨m, by rw [rd_eq hA α ht, hm]⟩
  have hεi : ε ∈ interior (Ioo (-δ) δ) := mem_interior_Ioo_of_abs hε
  have hεS : ε ∈ Ioo (-δ) δ := abs_lt.mp hε
  obtain ⟨m, hm⟩ := hint ε hε
  have hev : ∀ᶠ s in 𝓝[>] ε, slope (L α A) ε s < derivWithin (L α A) (Ioi ε) ε + Real.pi ∧
      s ∈ Ioo ε δ :=
    ((tendsto_slope_rd hA α hε).eventually (eventually_lt_nhds (by linarith [Real.pi_pos]))).and
      (Ioo_mem_nhdsGT hεS.2)
  obtain ⟨s, hs1, hs2⟩ := hev.exists
  have hcont : ContinuousOn (L α A) (Ioo (-δ) δ) := hc.continuousOn isOpen_Ioo
  have hgc : ContinuousAt (fun t => slope (L α A) t s) ε := by
    simp only [slope_def_field]
    exact (continuousAt_const.sub (hcont.continuousAt (isOpen_Ioo.mem_nhds hεS))).div
      (continuousAt_const.sub continuousAt_id) (sub_pos.mpr hs2.1).ne'
  have hev2 : ∀ᶠ t in 𝓝 ε, slope (L α A) t s < derivWithin (L α A) (Ioi ε) ε + Real.pi :=
    hgc.eventually (eventually_lt_nhds hs1)
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.mp hev2
  have hη₁ : 0 < min r (s - ε) := lt_min hr (sub_pos.mpr hs2.1)
  have hmin1 := min_le_left r (s - ε)
  have hmin2 := min_le_right r (s - ε)
  have hmemS : ∀ t ∈ Ioo ε (ε + min r (s - ε)), t ∈ Ioo (-δ) δ := fun t ht =>
    ⟨by linarith [hεS.1, ht.1], by linarith [hs2.2, ht.2]⟩
  have hconst : ∀ t ∈ Ioo ε (ε + min r (s - ε)),
      derivWithin (L α A) (Ioi t) t = derivWithin (L α A) (Ioi ε) ε := by
    intro t ht
    have hts : t < s := by linarith [ht.2]
    have htS := hmemS t ht
    have hti : t ∈ interior (Ioo (-δ) δ) := by rwa [interior_Ioo]
    have h1 : derivWithin (L α A) (Ioi t) t ≤ slope (L α A) t s :=
      hc.rightDeriv_le_slope_of_mem_interior hti ⟨by linarith [htS.1], hs2.2⟩ hts
    have h2 : slope (L α A) t s < derivWithin (L α A) (Ioi ε) ε + Real.pi :=
      hrb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    have h3 : derivWithin (L α A) (Ioi ε) ε ≤ derivWithin (L α A) (Ioi t) t :=
      hc.monotoneOn_rightDeriv hεi hti ht.1.le
    obtain ⟨mt, hmt⟩ := hint t (abs_lt.mpr htS)
    rw [hmt] at h1 h3 ⊢
    rw [hm] at h2 h3 ⊢
    have hmm : mt = m := int_eq_of_abs_lt (abs_lt.mpr ⟨by linarith, by linarith⟩)
    rw [hmm]
  have hslope : ∀ t ∈ Ioo ε (ε + min r (s - ε)),
      slope (L α A) ε t = derivWithin (L α A) (Ioi ε) ε := by
    intro t ht
    have htS := hmemS t ht
    have hti : t ∈ interior (Ioo (-δ) δ) := by rwa [interior_Ioo]
    apply le_antisymm
    · calc slope (L α A) ε t ≤ derivWithin (L α A) (Iio t) t :=
            hc.slope_le_leftDeriv_of_mem_interior hεS hti ht.1
        _ ≤ derivWithin (L α A) (Ioi t) t := hc.leftDeriv_le_rightDeriv_of_mem_interior hti
        _ = _ := hconst t ht
    · exact hc.rightDeriv_le_slope_of_mem_interior hεi htS ht.1
  have hR := rd_eq hA α hε
  refine ⟨min r (s - ε) / 2, by linarith, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp
  · have := hslope t ⟨h, by linarith [ht.2]⟩
    rw [slope_def_field, div_eq_iff (sub_ne_zero.mpr h.ne'), hR] at this
    linarith

lemma isRegular_iff_of (hA : IsAnalyticCocycle δ A) (hsym : IsRealSymmetricOn δ A)
    (hα : Irrational α) : IsRegular α A ↔ accel α A = 0 := by
  have hδ := hA.pos
  constructor
  · rintro ⟨η, hη, a, b, h⟩
    have hm1 := min_le_left η δ
    have hm2 := min_le_right η δ
    have hη' : 0 < min η δ := lt_min hη hδ
    have hb : b = 0 := by
      have h1 := h (min η δ / 2) (by rw [abs_of_pos (by linarith)]; linarith)
      have h2 := h (-(min η δ / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      rw [L_neg_of hsym α (ε := min η δ / 2) (by rw [abs_of_pos (by linarith)]; linarith)] at h2
      have : b * min η δ = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith
    subst hb
    have hq := tendsto_accel hA α
    have : Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hη] with t ht
      have h1 := h t (by rw [abs_of_pos ht.1]; exact ht.2)
      have h0 := h 0 (by simpa using hη)
      rw [h1, h0]; simp
    exact tendsto_nhds_unique hq this
  · intro h0
    obtain ⟨η, hη, hη'⟩ := L_piecewise_affine hA hα (ε := 0) (by simpa using hδ)
    rw [cshift_zero, h0] at hη'
    have hm1 := min_le_left η δ
    have hm2 := min_le_right η δ
    refine ⟨min η δ, lt_min hη hδ, L α A 0, 0, fun ε hε => ?_⟩
    rcases le_or_gt 0 ε with h | h
    · have := hη' ε ⟨h, by rw [abs_of_nonneg h] at hε; linarith⟩
      simpa using this
    · have := hη' (-ε) ⟨by linarith, by rw [abs_of_neg h] at hε; linarith⟩
      rw [L_neg_of hsym α (ε := ε) (by linarith)] at this
      simpa using this

/-- **Remark `omega real`** (second part): for real-symmetric cocycles with irrational
frequency, regularity is equivalent to zero acceleration. -/
theorem isRegular_iff_accel_eq_zero (hA : IsAnalyticCocycle δ A) (hsym : IsRealSymmetric A)
    (hα : Irrational α) : IsRegular α A ↔ accel α A = 0 :=
  isRegular_iff_of hA (fun z _ => hsym z) hα

/-- The acceleration is upper semicontinuous (along `αₙ → α` irrational, `Aₙ → A` uniformly on
the strip). -/
theorem accel_usc (hA : IsAnalyticCocycle δ A) (hα : Irrational α) {αs : ℕ → ℝ}
    {As : ℕ → ℂ → M2} (hAs : ∀ n, IsAnalyticCocycle δ (As n)) (hαs' : ∀ n, Irrational (αs n))
    (hαs : Tendsto αs atTop (𝓝 α)) (hconv : TendstoUniformlyOn As A atTop (strip δ)) :
    ∀ᶠ n in atTop, accel (αs n) (As n) ≤ accel α A := by
  obtain ⟨k, hk⟩ := (quantized hA hα).2
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (L α A t - L α A 0) / (2 * Real.pi * t) < k + 1 / 2 ∧ t ∈ Ioo 0 δ :=
    ((tendsto_accel hA α).eventually (eventually_lt_nhds (by rw [hk]; linarith))).and
      (Ioo_mem_nhdsGT hA.pos)
  obtain ⟨ε₁, hq, hε₁⟩ := hev.exists
  have hε₁' : |ε₁| < δ := by rw [abs_of_pos hε₁.1]; exact hε₁.2
  have hconv' : TendstoUniformlyOn (fun n => cshift (As n) ε₁) (cshift A ε₁) atTop
      (strip (δ - |ε₁|)) :=
    (hconv.comp (fun z : ℂ => z + ε₁ * I)).mono (fun z hz => mapsTo_cshift hz)
  have hT1 := jks_continuity (hA.cshift hε₁') hα (fun n => (hAs n).cshift hε₁') hαs hconv'
  have hT0 := jks_continuity hA hα hAs hαs hconv
  simp only [L_cshift, zero_add] at hT1
  have hT : Tendsto (fun n => (L (αs n) (As n) ε₁ - L (αs n) (As n) 0) / (2 * Real.pi * ε₁))
      atTop (𝓝 ((L α A ε₁ - L α A 0) / (2 * Real.pi * ε₁))) := (hT1.sub hT0).div_const _
  filter_upwards [hT.eventually (eventually_lt_nhds hq)] with n hn
  obtain ⟨m, hm⟩ := (quantized (hAs n) (hαs' n)).2
  have hle : accel (αs n) (As n) ≤
      (L (αs n) (As n) ε₁ - L (αs n) (As n) 0) / (2 * Real.pi * ε₁) := by
    rw [accel_eq_rd (hAs n) (αs n)]
    have := (L_convexOn (hAs n) (αs n)).rightDeriv_le_slope_of_mem_interior
      (mem_interior_Ioo_of_abs (by simpa using (hAs n).pos)) (abs_lt.mp hε₁') hε₁.1
    rw [slope_def_field, sub_zero] at this
    have e : (L (αs n) (As n) ε₁ - L (αs n) (As n) 0) / (2 * Real.pi * ε₁) =
        (L (αs n) (As n) ε₁ - L (αs n) (As n) 0) / ε₁ / (2 * Real.pi) := by ring
    rw [e]
    gcongr
  rw [hm, hk]
  have hmk : (m : ℝ) < k + 1 := by rw [← hm]; linarith
  have : m < k + 1 := by exact_mod_cast hmk
  have : m ≤ k := by omega
  exact_mod_cast this

/-! ### Characterization of uniform hyperbolicity -/

/-- The "if" direction: uniformly hyperbolic cocycles (with irrational frequency) are regular. -/
theorem uh_imp_regular {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) (hUH : UH α A) : IsRegular α A := by
  have hδ := hA.pos
  have hfam := cshift_family hA
  have h0U : (0 : ℝ) ∈ Ioo (-(δ / 2)) (δ / 2) := ⟨by linarith, by linarith⟩
  have hUH0 : UH α (cshift A 0) := by rwa [cshift_zero]
  obtain ⟨W, hW, hWan⟩ := uh_analytic_family hfam α h0U hUH0
  have hfun : (fun p : ℝ => L α (cshift A p) 0) = L α A := by
    funext p; rw [L_cshift, zero_add]
  rw [hfun] at hWan
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  have han : ∀ t, |t| < min r δ → AnalyticAt ℝ (L α A) t := fun t ht =>
    hWan t (hrW (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact lt_of_lt_of_le ht (min_le_left _ _)))
  have hint : ∀ t, |t| < min r δ → ∃ m : ℤ, deriv (L α A) t = 2 * Real.pi * m := by
    intro t ht
    have htδ : |t| < δ := lt_of_lt_of_le ht (min_le_right _ _)
    obtain ⟨m, hm⟩ := (quantized (hA.cshift htδ) hα).2
    refine ⟨m, ?_⟩
    rw [← hm, ← rd_eq hA α htδ]
    exact ((han t ht).differentiableAt.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi t)).symm
  have hdc : ContinuousAt (deriv (L α A)) 0 :=
    (hWan.deriv 0 (mem_of_mem_nhds hW)).continuousAt
  obtain ⟨s, hs, hsb⟩ := Metric.continuousAt_iff.mp hdc Real.pi Real.pi_pos
  obtain ⟨m0, hm0⟩ := hint 0 (by simpa using lt_min hr hδ)
  have hconst : ∀ t, |t| < min s (min r δ) → HasDerivAt (L α A) (deriv (L α A) 0) t := by
    intro t ht
    have ht1 : |t| < min r δ := lt_of_lt_of_le ht (min_le_right _ _)
    have ht2 : |t| < s := lt_of_lt_of_le ht (min_le_left _ _)
    obtain ⟨mt, hmt⟩ := hint t ht1
    have hd := hsb (show dist t 0 < s by rw [Real.dist_eq, sub_zero]; exact ht2)
    rw [Real.dist_eq, hmt, hm0] at hd
    have hmm := int_eq_of_abs_lt hd
    have e : deriv (L α A) t = deriv (L α A) 0 := by rw [hmt, hm0, hmm]
    rw [← e]
    exact (han t ht1).differentiableAt.hasDerivAt
  exact ⟨min s (min r δ), lt_min hs (lt_min hr hδ), L α A 0, deriv (L α A) 0,
    fun ε hε => affine_of_hasDerivAt hconst ε hε⟩

/-- **Theorem (characterization of uniform hyperbolicity).**  If `L(α, A) > 0` then `(α, A)` is
regular iff it is uniformly hyperbolic. -/
theorem uh_iff_regular {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) (hpos : 0 < L α A 0) : IsRegular α A ↔ UH α A :=
  ⟨fun h => regular_pos_imp_uh hA hα h hpos, uh_imp_regular hA hα⟩


/-! ### Corollary `alter` -/

/-- **Corollary `alter`.**  For irrational `α` there is `ε₀ > 0` such that either
`L(α, A_ε) = 0` for all `0 < ε < ε₀` (and then `ω(α, A) = 0`), or `(α, A_ε)` is uniformly
hyperbolic for all `0 < ε < ε₀`. -/
theorem alter (hA : IsAnalyticCocycle δ A) (hα : Irrational α) :
    ∃ ε₀ > 0, ε₀ ≤ δ ∧
      ((∀ ε ∈ Ioo 0 ε₀, L α A ε = 0) ∧ accel α A = 0 ∨
        ∀ ε ∈ Ioo 0 ε₀, UH α (cshift A ε)) := by
  have hδ := hA.pos
  obtain ⟨η, hη, hη'⟩ := L_piecewise_affine hA hα (ε := 0) (by simpa using hδ)
  rw [cshift_zero] at hη'
  have hmem : ∀ ε ∈ Ioo 0 (min η δ), ε ∈ Icc 0 η ∧ |ε| < δ := fun ε hε =>
    ⟨⟨hε.1.le, hε.2.le.trans (min_le_left _ _)⟩,
      by rw [abs_of_pos hε.1]; exact hε.2.trans_le (min_le_right _ _)⟩
  have hφ : ∀ t ∈ Ioo 0 (min η δ),
      L α A t = L α A 0 + 2 * Real.pi * accel α A * t ∧ 0 ≤ L α A t := fun t ht =>
    ⟨by have := hη' t (by simpa using (hmem t ht).1); simpa using this,
      hA.L_nonneg α (hmem t ht).2⟩
  have he₀ : 0 < min η δ := lt_min hη hδ
  refine ⟨min η δ, he₀, min_le_right _ _, ?_⟩
  by_cases hall : ∀ ε ∈ Ioo 0 (min η δ), L α A ε = 0
  · left
    refine ⟨hall, ?_⟩
    have h1 := hall (min η δ / 2) ⟨by linarith, by linarith⟩
    have h2 := hall (min η δ / 4) ⟨by linarith, by linarith⟩
    rw [(hφ (min η δ / 2) ⟨by linarith, by linarith⟩).1] at h1
    rw [(hφ (min η δ / 4) ⟨by linarith, by linarith⟩).1] at h2
    have : accel α A * (Real.pi * min η δ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (mul_pos Real.pi_pos he₀).ne'
  · right
    push Not at hall
    obtain ⟨ε₁, hε₁, hne⟩ := hall
    intro ε hε
    have hposε : 0 < L α A ε := by
      by_contra hcon
      push Not at hcon
      have h0 : L α A ε = 0 := le_antisymm hcon (hφ ε hε).2
      have g1 := hφ (ε / 2) ⟨by linarith [hε.1], by linarith [hε.1, hε.2]⟩
      have g2 := hφ ((ε + min η δ) / 2) ⟨by linarith [hε.1, hε.2], by linarith [hε.2]⟩
      have gε := (hφ ε hε).1
      have g₁ := (hφ ε₁ hε₁).1
      have ha1 : accel α A * (Real.pi * ε) ≤ 0 := by linarith [g1.1, g1.2]
      have ha2 : 0 ≤ accel α A * (Real.pi * (min η δ - ε)) := by linarith [g2.1, g2.2]
      have hP1 : 0 < Real.pi * ε := mul_pos Real.pi_pos hε.1
      have hP2 : 0 < Real.pi * (min η δ - ε) := mul_pos Real.pi_pos (sub_pos.mpr hε.2)
      have ha0 : accel α A = 0 := le_antisymm (by nlinarith) (by nlinarith)
      have hL0 : L α A 0 = 0 := by rw [ha0] at gε; linarith
      exact hne (by rw [g₁, ha0, hL0]; ring)
    have hεδ := (hmem ε hε).2
    refine regular_pos_imp_uh (hA.cshift hεδ) hα ?_ (by rw [L_cshift, zero_add]; exact hposε)
    have hmin1 := min_le_left ε (min η δ - ε)
    have hmin2 := min_le_right ε (min η δ - ε)
    refine ⟨min ε (min η δ - ε), lt_min hε.1 (sub_pos.mpr hε.2),
      L α A 0 + 2 * Real.pi * accel α A * ε, 2 * Real.pi * accel α A, fun s hs => ?_⟩
    rw [L_cshift]
    have hs' := abs_lt.mp hs
    rw [(hφ (s + ε) ⟨by linarith, by linarith⟩).1]
    ring

/-! ### The sets `Ω_{δ,j}` and the functions `L_{δ,j}` -/

omit hH in
/-- `(α, A) ∈ Ω_{δ,j}`: some `0 < δ' < δ` has `(α, A_{δ'}) ∈ 𝒰ℋ` with acceleration `j`. -/
def OmegaSet (δ : ℝ) (j : ℤ) (α : ℝ) (A : ℂ → M2) : Prop :=
  ∃ δ' ∈ Ioo 0 δ, UH α (cshift A δ') ∧ accel α (cshift A δ') = j

omit hH in
open Classical in
/-- `L_{δ,j}(α, A) = L(α, A_{δ'}) - 2πjδ'` (and `0` off `Ω_{δ,j}`). -/
def Ldj (δ : ℝ) (j : ℤ) (α : ℝ) (A : ℂ → M2) : ℝ :=
  if h : OmegaSet δ j α A then L α A h.choose - 2 * Real.pi * j * h.choose else 0

/-- `L_{δ,j}` is well defined: any admissible `δ'` gives the same value. -/
theorem Ldj_eq (hA : IsAnalyticCocycle δ A) {j : ℤ} {δ' : ℝ} (hδ' : δ' ∈ Ioo 0 δ)
    (hUH : UH α (cshift A δ')) (hω : accel α (cshift A δ') = j) :
    Ldj δ j α A = L α A δ' - 2 * Real.pi * j * δ' := by
  have hO : OmegaSet δ j α A := ⟨δ', hδ', hUH, hω⟩
  simp only [Ldj, dif_pos hO]
  obtain ⟨h1, -, h3⟩ := Exists.choose_spec hO
  exact L_eq_of_accel_eq hA h1 hδ' h3 hω

/-- **Proposition `pluri`** (second part), for `j ≠ 0` (the case treated in the paper). -/
theorem pluri_mem_of_ne_zero (hA : IsAnalyticCocycle δ A) (hα : Irrational α) {j : ℤ}
    (hj0 : j ≠ 0) (hj : accel α A = j) :
    (∃ δ₀ > 0, ∀ δ' ∈ Ioo 0 δ₀, UH α (cshift A δ') ∧ accel α (cshift A δ') = j) ∧
      OmegaSet δ j α A ∧ L α A 0 = Ldj δ j α A := by
  have hδ := hA.pos
  obtain ⟨ε₀, hε₀, hε₀δ, hcase⟩ := alter hA hα
  have hUHall : ∀ ε ∈ Ioo 0 ε₀, UH α (cshift A ε) := by
    rcases hcase with ⟨-, h0⟩ | h
    · exact absurd (hj.symm.trans h0) (by exact_mod_cast hj0)
    · exact h
  obtain ⟨η, hη, hη'⟩ := L_piecewise_affine hA hα (ε := 0) (by simpa using hδ)
  rw [cshift_zero, hj] at hη'
  have haff : ∀ t ∈ Icc (0 : ℝ) η, L α A t = L α A 0 + 2 * Real.pi * j * t := by
    intro t ht; have := hη' t (by simpa using ht); simpa using this
  have hacc : ∀ δ' ∈ Ioo 0 η, accel α (cshift A δ') = j := by
    intro δ' hδ'
    have e : accel α (cshift A δ') = limUnder (𝓝[>] (0 : ℝ))
        (fun t => (L α A (t + δ') - L α A δ') / (2 * Real.pi * t)) := by
      simp only [accel, L_cshift, zero_add]
    rw [e]
    apply Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hδ'.2)] with t ht
    rw [haff (t + δ') ⟨by linarith [ht.1, hδ'.1], by linarith [ht.2]⟩,
      haff δ' ⟨hδ'.1.le, hδ'.2.le⟩, eq_div_iff (mul_pos (by positivity) ht.1).ne']
    ring
  have hd1 := min_le_left ε₀ η
  have hd2 := min_le_right ε₀ η
  have hδ₀ : 0 < min ε₀ η := lt_min hε₀ hη
  have h1 : ∀ δ' ∈ Ioo 0 (min ε₀ η), UH α (cshift A δ') ∧ accel α (cshift A δ') = j :=
    fun δ' hδ' => ⟨hUHall δ' ⟨hδ'.1, by linarith [hδ'.2]⟩, hacc δ' ⟨hδ'.1, by linarith [hδ'.2]⟩⟩
  have hd : min ε₀ η / 2 ∈ Ioo 0 (min ε₀ η) := ⟨by linarith, by linarith⟩
  have hdδ : min ε₀ η / 2 ∈ Ioo 0 δ := ⟨by linarith, by linarith⟩
  refine ⟨⟨min ε₀ η, hδ₀, h1⟩, ⟨min ε₀ η / 2, hdδ, (h1 _ hd).1, (h1 _ hd).2⟩, ?_⟩
  rw [Ldj_eq hA hdδ (h1 _ hd).1 (h1 _ hd).2, haff (min ε₀ η / 2) ⟨by linarith, by linarith⟩]
  ring

/-- **Proposition `pluri`** (second part): if `α` is irrational and `ω(α, A) = j ≠ 0`, then
`(α, A) ∈ Ω_{δ,j}`, with `(α, A_{δ'}) ∈ 𝒰ℋ` of acceleration `j` for all small `δ' > 0`, and
`L(α, A) = L_{δ,j}(α, A)`. -/
theorem pluri_mem (hA : IsAnalyticCocycle δ A) (hα : Irrational α) {j : ℤ}
    (hj : accel α A = j) (hj0 : j ≠ 0) :
    (∃ δ₀ > 0, ∀ δ' ∈ Ioo 0 δ₀, UH α (cshift A δ') ∧ accel α (cshift A δ') = j) ∧
      OmegaSet δ j α A ∧ L α A 0 = Ldj δ j α A :=
  pluri_mem_of_ne_zero hA hα hj0 hj

/-! ### Families of cocycles: openness, persistence of `Ω_{δ,j}`, stratifications -/

section Families

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Tube lemma: a continuous family of `1`-periodic functions on `U × {|Im z| < δ}` converges
uniformly on every smaller strip. -/
lemma tendstoUniformlyOn_family {Q : Type*} [TopologicalSpace Q] {U : Set Q} (hU : IsOpen U)
    {G : Q → ℂ → M2} {δ δ' : ℝ} (hδ' : δ' < δ)
    (hG : ContinuousOn (fun q : Q × ℂ => G q.1 q.2) (U ×ˢ strip δ))
    (hper : ∀ p ∈ U, ∀ z, G p (z + 1) = G p z) {p₀ : Q} (hp₀ : p₀ ∈ U) :
    TendstoUniformlyOn G (G p₀) (𝓝 p₀) (strip δ') := by
  intro u hu
  have hKc : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-δ') δ') := isCompact_Icc.reProdIm isCompact_Icc
  have hKs : (Icc (0 : ℝ) 1 ×ℂ Icc (-δ') δ') ⊆ strip δ := by
    intro z hz
    have h2 : z.im ∈ Icc (-δ') δ' := hz.2
    show |z.im| < δ
    rw [abs_lt]; constructor <;> linarith [h2.1, h2.2]
  obtain ⟨v, hv, hvK⟩ := hKc.mem_uniformity_of_prod (f := G)
    (hG.mono (prod_mono subset_rfl hKs)) hp₀ (tendsto_swap_uniformity hu)
  rw [hU.nhdsWithin_eq hp₀] at hv
  filter_upwards [hv, hU.mem_nhds hp₀] with p hp hpU
  intro z hz
  have hz' : |z.im| < δ' := hz
  rw [abs_lt] at hz'
  have hzK : z - (⌊z.re⌋ : ℂ) ∈ (Icc (0 : ℝ) 1 ×ℂ Icc (-δ') δ') := by
    refine ⟨?_, ?_⟩
    · show (z - (⌊z.re⌋ : ℂ)).re ∈ Icc (0 : ℝ) 1
      simp only [sub_re, intCast_re]
      constructor
      · linarith [Int.floor_le z.re]
      · linarith [Int.lt_floor_add_one z.re]
    · show (z - (⌊z.re⌋ : ℂ)).im ∈ Icc (-δ') δ'
      simp only [sub_im, intCast_im, sub_zero]
      exact ⟨hz'.1.le, hz'.2.le⟩
  have e1 : G p z = G p (z - (⌊z.re⌋ : ℂ)) := by
    rw [← periodic_int (hper p hpU) ⌊z.re⌋ (z - (⌊z.re⌋ : ℂ)), sub_add_cancel]
  have e2 : G p₀ z = G p₀ (z - (⌊z.re⌋ : ℂ)) := by
    rw [← periodic_int (hper p₀ hp₀) ⌊z.re⌋ (z - (⌊z.re⌋ : ℂ)), sub_add_cancel]
  rw [e1, e2]
  exact hvK p hp _ hzK

lemma tendstoUniformlyOn_seq {Q : Type*} [TopologicalSpace Q] {G : Q → ℂ → M2} {p₀ : Q}
    {s : Set ℂ} (h : TendstoUniformlyOn G (G p₀) (𝓝 p₀) s) {ps : ℕ → Q}
    (hps : Tendsto ps atTop (𝓝 p₀)) :
    TendstoUniformlyOn (fun n => G (ps n)) (G p₀) atTop s :=
  fun u hu => hps.eventually (h u hu)

lemma tendstoUniformly_shift_of {As : ℕ → ℂ → M2} {A : ℂ → M2} {δ ε : ℝ} (hε : |ε| < δ)
    (h : TendstoUniformlyOn As A atTop (strip δ)) :
    TendstoUniformly (fun n => shift (As n) ε) (shift A ε) atTop := by
  rw [← tendstoUniformlyOn_univ]
  exact (h.comp (fun x : ℝ => (x : ℂ) + ε * I)).mono (fun x _ => mem_strip_shift hε x)

/-- Shifting an analytic family: `(p, ε) ↦ A_p(· + iε)`. -/
lemma IsAnalyticCocycleFamily.shift_family {U : Set P} {Af : P → ℂ → M2}
    (hAf : IsAnalyticCocycleFamily δ U Af) {a b δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hab : ∀ ε ∈ Ioo a b, |ε| + δ₁ ≤ δ) :
    IsAnalyticCocycleFamily δ₁ (U ×ˢ Ioo a b) (fun q : P × ℝ => cshift (Af q.1) q.2) := by
  refine ⟨hAf.isOpen.prod isOpen_Ioo, fun q hq => ?_, ?_⟩
  · have h := hab q.2 hq.2
    exact ((hAf.cocycle q.1 hq.1).cshift (by linarith)).mono hδ₁ (by linarith)
  · rintro ⟨⟨p, ε⟩, z⟩ ⟨⟨hp, hε⟩, hz⟩
    have h := hab ε hε
    have hw : z + ε * I ∈ strip δ := mapsTo_cshift (δ := δ) (ε := ε)
      (show z ∈ strip (δ - |ε|) from
        (by have : |z.im| < δ₁ := hz; linarith : |z.im| < δ - |ε|))
    have hA := hAf.analytic (p, z + ε * I) ⟨hp, hw⟩
    have h1 : AnalyticAt ℝ (fun q : (P × ℝ) × ℂ => ((q.1.2 : ℝ) : ℂ)) ((p, ε), z) :=
      AnalyticAt.comp (g := ⇑Complex.ofRealCLM) (f := fun q : (P × ℝ) × ℂ => q.1.2)
        (Complex.ofRealCLM.analyticAt _) (AnalyticAt.comp (g := Prod.snd) (f := Prod.fst) analyticAt_snd analyticAt_fst)
    have hin : AnalyticAt ℝ (fun q : (P × ℝ) × ℂ => (q.1.1, q.2 + (q.1.2 : ℂ) * I))
        ((p, ε), z) :=
      AnalyticAt.prod (AnalyticAt.comp (g := Prod.fst) (f := Prod.fst) analyticAt_fst analyticAt_fst)
        (analyticAt_snd.add (h1.mul analyticAt_const))
    exact AnalyticAt.comp (g := fun q : P × ℂ => Af q.1 q.2)
      (f := fun q : (P × ℝ) × ℂ => (q.1.1, q.2 + (q.1.2 : ℂ) * I)) hA hin

/-- Analyticity of `p ↦ L(α, (A_p)_{δ'})` near a point where `(α, (A_{p₀})_{δ'}) ∈ 𝒰ℋ`. -/
lemma omega_analytic {U : Set P} {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af)
    {α : ℝ} {p₀ : P} (hp₀ : p₀ ∈ U) {δ' : ℝ} (hδ' : δ' ∈ Ioo 0 δ)
    (hUH0 : UH α (cshift (Af p₀) δ')) :
    AnalyticAt ℝ (fun p => L α (Af p) δ') p₀ := by
  have hm1 := min_le_left δ' (δ - δ')
  have hm2 := min_le_right δ' (δ - δ')
  have hρ : 0 < min δ' (δ - δ') := lt_min hδ'.1 (sub_pos.mpr hδ'.2)
  have hB := hAf.shift_family (a := δ' - min δ' (δ - δ') / 2) (b := δ' + min δ' (δ - δ') / 2)
    (δ₁ := (δ - δ') / 2) (by linarith [hδ'.2]) (fun ε hε => by
      rw [abs_of_pos (by linarith [hε.1])]; linarith [hε.2])
  have hq₀ : (p₀, δ') ∈ U ×ˢ Ioo (δ' - min δ' (δ - δ') / 2) (δ' + min δ' (δ - δ') / 2) :=
    ⟨hp₀, by linarith, by linarith⟩
  obtain ⟨W, hW, hWan⟩ := uh_analytic_family hB α hq₀ hUH0
  have hfun : (fun q : P × ℝ => L α (cshift (Af q.1) q.2) 0) = fun q => L α (Af q.1) q.2 := by
    funext q; rw [L_cshift, zero_add]
  rw [hfun] at hWan
  exact AnalyticAt.comp (g := fun q : P × ℝ => L α (Af q.1) q.2) (f := fun p : P => (p, δ'))
    (hWan _ (mem_of_mem_nhds hW)) (analyticAt_id.prod analyticAt_const)

/-- The heart of Proposition `pluri`: near a point of `Ω_{δ,j}` with witness `δ'`, uniform
hyperbolicity and acceleration `j` of `A_{δ'}` persist (jointly in the frequency, rational
frequencies included), and `L(α, A_{δ'})` is `C^∞`. -/
lemma omega_core {U : Set P} {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af) {j : ℤ}
    {α₀ : ℝ} {p₀ : P} (hp₀ : p₀ ∈ U) {δ' : ℝ} (hδ' : δ' ∈ Ioo 0 δ)
    (hUH0 : UH α₀ (cshift (Af p₀) δ')) (hacc0 : accel α₀ (cshift (Af p₀) δ') = j) :
    (∀ᶠ q in 𝓝 (α₀, p₀), q.2 ∈ U ∧ UH q.1 (cshift (Af q.2) δ') ∧
        accel q.1 (cshift (Af q.2) δ') = j) ∧
      ∃ W ∈ 𝓝 (α₀, p₀), ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (Af q.2) δ') W := by
  have hδ'' : |δ'| < δ := by rw [abs_of_pos hδ'.1]; exact hδ'.2
  have hm1 := min_le_left δ' (δ - δ')
  have hm2 := min_le_right δ' (δ - δ')
  have hρ : 0 < min δ' (δ - δ') := lt_min hδ'.1 (sub_pos.mpr hδ'.2)
  have hB := hAf.shift_family (a := δ' - min δ' (δ - δ') / 2) (b := δ' + min δ' (δ - δ') / 2)
    (δ₁ := (δ - δ') / 2) (by linarith [hδ'.2]) (fun ε hε => by
      rw [abs_of_pos (by linarith [hε.1])]; linarith [hε.2])
  have hq₀ : (p₀, δ') ∈ U ×ˢ Ioo (δ' - min δ' (δ - δ') / 2) (δ' + min δ' (δ - δ') / 2) :=
    ⟨hp₀, by linarith, by linarith⟩
  obtain ⟨W, hW, hWs⟩ := uh_smooth_family hB hq₀ hUH0
  have hfun : (fun q : ℝ × (P × ℝ) => L q.1 (cshift (Af q.2.1) q.2.2) 0) =
      fun q => L q.1 (Af q.2.1) q.2.2 := by
    funext q; rw [L_cshift, zero_add]
  rw [hfun] at hWs
  set Φ : ℝ × (P × ℝ) → ℝ := fun q => L q.1 (Af q.2.1) q.2.2 with hΦ
  have hW'o : IsOpen (interior W) := isOpen_interior
  have hW'm : (α₀, (p₀, δ')) ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  have hWs' : ContDiffOn ℝ ∞ Φ (interior W) := hWs.mono interior_subset
  have hdiff : ∀ q ∈ interior W, HasFDerivAt Φ (fderiv ℝ Φ q) q := fun q hq =>
    (((hWs'.differentiableOn (by simp)) q hq).differentiableAt (hW'o.mem_nhds hq)).hasFDerivAt
  have hfc : ContinuousOn (fderiv ℝ Φ) (interior W) :=
    hWs'.continuousOn_fderiv_of_isOpen hW'o (by simp)
  set emb : ℝ × P → ℝ × (P × ℝ) := fun q => (q.1, (q.2, δ')) with hemb_def
  have hemb : Continuous emb := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  set ψ : ℝ × P → ℝ := fun q => fderiv ℝ Φ (emb q) (0, (0, 1)) with hψ_def
  have hderiv : ∀ q : ℝ × P, emb q ∈ interior W →
      derivWithin (L q.1 (Af q.2)) (Ioi δ') δ' = ψ q := by
    intro q hq
    have h2 : HasDerivAt (fun ε : ℝ => (q.1, (q.2, ε))) ((0 : ℝ), ((0 : P), (1 : ℝ))) δ' :=
      (hasDerivAt_const δ' q.1).prodMk ((hasDerivAt_const δ' q.2).prodMk (hasDerivAt_id δ'))
    have h3 := (hdiff _ hq).comp_hasDerivAt (x := δ') h2
    exact h3.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi δ')
  have hψc : ∀ q, emb q ∈ interior W → ContinuousAt ψ q := fun q hq =>
    ((hfc.continuousAt (hW'o.mem_nhds hq)).comp hemb.continuousAt).clm_apply continuousAt_const
  have hψ0 : ψ (α₀, p₀) = 2 * Real.pi * j := by
    rw [← hderiv (α₀, p₀) hW'm, rd_eq (hAf.cocycle p₀ hp₀) α₀ hδ'', hacc0]
  have e1 : ∀ᶠ q in 𝓝 (α₀, p₀), emb q ∈ interior W :=
    hemb.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW'm)
  have e2 : ∀ᶠ q in 𝓝 (α₀, p₀), q.2 ∈ U :=
    continuous_snd.continuousAt.preimage_mem_nhds (hAf.isOpen.mem_nhds hp₀)
  have e3 : ∀ᶠ q in 𝓝 (α₀, p₀), dist (ψ q) (ψ (α₀, p₀)) < Real.pi :=
    (hψc _ hW'm).eventually (Metric.ball_mem_nhds _ Real.pi_pos)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (e1.and (e2.and e3))
  have hirr : ∀ q ∈ Metric.ball (α₀, p₀) r, Irrational q.1 → ψ q = 2 * Real.pi * j := by
    intro q hq hirr
    obtain ⟨h1, h2, h3⟩ := hball q hq
    obtain ⟨m, hm⟩ := (quantized ((hAf.cocycle q.2 h2).cshift hδ'') hirr).2
    have e : ψ q = 2 * Real.pi * m := by
      rw [← hderiv q h1, rd_eq (hAf.cocycle q.2 h2) q.1 hδ'', hm]
    rw [Real.dist_eq, e, hψ0] at h3
    rw [e, int_eq_of_abs_lt h3]
  have hall : ∀ q ∈ Metric.ball (α₀, p₀) r, ψ q = 2 * Real.pi * j := by
    intro q hq
    obtain ⟨as, has, hlim⟩ := mem_closure_iff_seq_limit.mp (dense_irrational q.1)
    have hlim2 : Tendsto (fun n => (as n, q.2)) atTop (𝓝 q) :=
      hlim.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => q.2) atTop (𝓝 q.2))
    have hev2 : ∀ᶠ n in atTop, ψ (as n, q.2) = 2 * Real.pi * j :=
      (hlim2.eventually (Metric.isOpen_ball.mem_nhds hq)).mono fun n hn => hirr _ hn (has n)
    exact tendsto_nhds_unique ((hψc q (hball q hq).1).tendsto.comp hlim2)
      (tendsto_const_nhds.congr' (hev2.mono fun n h => h.symm))
  have hUHev : ∀ᶠ q in 𝓝 (α₀, p₀), UH q.1 (cshift (Af q.2) δ') := by
    rw [eventually_iff_seq_eventually]
    intro qs hqs
    have hconvU := tendstoUniformlyOn_family hAf.isOpen (δ' := (δ' + δ) / 2)
      (by linarith [hδ'.2]) hAf.analytic.continuousOn (fun p hp => (hAf.cocycle p hp).periodic) hp₀
    have hps : Tendsto (fun n => (qs n).2) atTop (𝓝 p₀) := (continuous_snd.tendsto _).comp hqs
    have has : Tendsto (fun n => (qs n).1) atTop (𝓝 α₀) := (continuous_fst.tendsto _).comp hqs
    have hR := tendstoUniformly_shift_of (ε := δ')
      (by rw [abs_of_pos hδ'.1]; linarith [hδ'.2]) (tendstoUniformlyOn_seq hconvU hps)
    have e : ∀ X : ℂ → M2, shift (cshift X δ') 0 = shift X δ' := fun X => by
      rw [shift_cshift, zero_add]
    have hSL : IsSLCocycle (shift (cshift (Af p₀) δ') 0) := by
      rw [e]; exact (hAf.cocycle p₀ hp₀).isSLCocycle_shift hδ''
    exact uh_open (As := fun n => cshift (Af (qs n).2) δ') hSL hUH0
      ((hps.eventually (hAf.isOpen.mem_nhds hp₀)).mono fun n hn => by
        rw [e]; exact (hAf.cocycle _ hn).isSLCocycle_shift hδ'')
      has (by simp only [e]; exact hR)
  refine ⟨?_, emb ⁻¹' interior W, hemb.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW'm), ?_⟩
  · filter_upwards [Metric.ball_mem_nhds (α₀, p₀) hr, hUHev] with q hq hUHq
    obtain ⟨h1, h2, h3⟩ := hball q hq
    refine ⟨h2, hUHq, ?_⟩
    have e := hall q hq
    rw [← hderiv q h1, rd_eq (hAf.cocycle q.2 h2) q.1 hδ''] at e
    exact mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) e
  · have hc : ContDiff ℝ ∞ emb := contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    have h := hWs'.comp (s := emb ⁻¹' interior W) hc.contDiffOn (fun q hq => hq)
    have e : (Φ ∘ emb) = fun q : ℝ × P => L q.1 (Af q.2) δ' := by
      funext q; rfl
    rw [e] at h
    exact h

end Families

/-- **Proposition `pluri`** (first part, at fixed frequency): for a real-analytic family of
cocycles, `{p | (α, A_p) ∈ Ω_{δ,j}}` is open and `p ↦ L_{δ,j}(α, A_p)` is real-analytic on
it. -/
theorem pluri_open_analytic {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set P}
    {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af) (α : ℝ) (j : ℤ) :
    IsOpen {p | p ∈ U ∧ OmegaSet δ j α (Af p)} ∧
      AnalyticOnNhd ℝ (fun p => Ldj δ j α (Af p)) {p | p ∈ U ∧ OmegaSet δ j α (Af p)} := by
  have key : ∀ p₀ ∈ {p | p ∈ U ∧ OmegaSet δ j α (Af p)}, ∃ δ' ∈ Ioo 0 δ,
      (∀ᶠ p in 𝓝 p₀, p ∈ U ∧ UH α (cshift (Af p) δ') ∧ accel α (cshift (Af p) δ') = j) ∧
        AnalyticAt ℝ (fun p => L α (Af p) δ') p₀ := by
    rintro p₀ ⟨hp₀, δ', hδ', hUH0, hacc0⟩
    refine ⟨δ', hδ', ?_, omega_analytic hAf hp₀ hδ' hUH0⟩
    have h := (omega_core hAf hp₀ hδ' hUH0 hacc0).1
    have hc : Continuous fun p : P => (α, p) := continuous_const.prodMk continuous_id
    exact hc.continuousAt.eventually h
  have hopen : IsOpen {p | p ∈ U ∧ OmegaSet δ j α (Af p)} := by
    rw [isOpen_iff_mem_nhds]
    intro p₀ hp₀
    obtain ⟨δ', hδ', hev, -⟩ := key p₀ hp₀
    filter_upwards [hev] with p hp
    exact ⟨hp.1, δ', hδ', hp.2.1, hp.2.2⟩
  refine ⟨hopen, fun p₀ hp₀ => ?_⟩
  obtain ⟨δ', hδ', hev, han⟩ := key p₀ hp₀
  have han2 : AnalyticAt ℝ (fun p => L α (Af p) δ' - 2 * Real.pi * j * δ') p₀ :=
    han.sub analyticAt_const
  refine han2.congr ?_
  filter_upwards [hev] with p hp
  exact (Ldj_eq (hAf.cocycle p hp.1) hδ' hp.2.1 hp.2.2).symm

/-- **Proposition `pluri`** (first part, jointly in the frequency): `{(α, p) | (α, A_p) ∈ Ω_{δ,j}}`
is open and `(α, p) ↦ L_{δ,j}(α, A_p)` is `C^∞` on it. -/
theorem pluri_open_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set P}
    {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af) (j : ℤ) :
    IsOpen {q : ℝ × P | q.2 ∈ U ∧ OmegaSet δ j q.1 (Af q.2)} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × P => Ldj δ j q.1 (Af q.2))
        {q : ℝ × P | q.2 ∈ U ∧ OmegaSet δ j q.1 (Af q.2)} := by
  have key : ∀ q₀ ∈ {q : ℝ × P | q.2 ∈ U ∧ OmegaSet δ j q.1 (Af q.2)}, ∃ δ' ∈ Ioo 0 δ,
      (∀ᶠ q in 𝓝 q₀, q.2 ∈ U ∧ UH q.1 (cshift (Af q.2) δ') ∧
          accel q.1 (cshift (Af q.2) δ') = j) ∧
        ∃ W ∈ 𝓝 q₀, ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (Af q.2) δ') W := by
    rintro ⟨α₀, p₀⟩ ⟨hp₀, δ', hδ', hUH0, hacc0⟩
    exact ⟨δ', hδ', omega_core hAf hp₀ hδ' hUH0 hacc0⟩
  have hopen : IsOpen {q : ℝ × P | q.2 ∈ U ∧ OmegaSet δ j q.1 (Af q.2)} := by
    rw [isOpen_iff_mem_nhds]
    intro q₀ hq₀
    obtain ⟨δ', hδ', hev, -⟩ := key q₀ hq₀
    filter_upwards [hev] with q hq
    exact ⟨hq.1, δ', hδ', hq.2.1, hq.2.2⟩
  refine ⟨hopen, fun q₀ hq₀ => ?_⟩
  obtain ⟨δ', hδ', hev, W, hW, hWs⟩ := key q₀ hq₀
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (Af q.2) δ' - 2 * Real.pi * j * δ') W :=
    hWs.sub contDiffOn_const
  refine ((hg.contDiffAt hW).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with q hq
  exact Ldj_eq (hAf.cocycle q.2 hq.1) hδ' hq.2.1 hq.2.2

/-! ### Stratifications -/

/-- Compressing a decreasing sequence of relatively closed sets with empty intersection into a
stratification (removing repetitions): every stratum is contained in a "stratum" of `F`. -/
theorem exists_stratification {T : Type*} [TopologicalSpace T] {X : Set T} (F : ℕ → Set T)
    (h0 : F 0 = X) (hclosed : ∀ i, ∃ C, IsClosed C ∧ F i = C ∩ X)
    (hanti : ∀ i, F (i + 1) ⊆ F i) (hinter : ⋂ i, F i = ∅) :
    ∃ S, IsStratification X S ∧ ∀ i, ∃ m, stratum S i ⊆ stratum F m := by
  classical
  have hmono : Antitone F := antitone_nat_of_succ_le hanti
  let next : ℕ → ℕ := fun a => if h : ∃ n, a < n ∧ F n ≠ F a then Nat.find h else a + 1
  have P1 : ∀ a, a < next a := by
    intro a
    simp only [next]
    split_ifs with h
    · exact (Nat.find_spec h).1
    · omega
  have P2 : ∀ a n, a ≤ n → n < next a → F n = F a := by
    intro a n han hn
    simp only [next] at hn
    split_ifs at hn with h
    · rcases eq_or_lt_of_le han with rfl | han'
      · rfl
      · have := Nat.find_min h hn
        push Not at this
        exact this han'
    · have : n = a := by omega
      rw [this]
  have P3 : ∀ a, F a ≠ ∅ → F (next a) ≠ F a := by
    intro a ha
    simp only [next]
    split_ifs with h
    · exact (Nat.find_spec h).2
    · exfalso
      push Not at h
      apply ha
      apply Set.eq_empty_of_subset_empty
      rw [← hinter]
      refine Set.subset_iInter fun i => ?_
      rcases le_or_gt i a with hi | hi
      · exact hmono hi
      · rw [h i hi]
  let k : ℕ → ℕ := fun i => next^[i] 0
  have hk : ∀ i, k (i + 1) = next (k i) := fun i => Function.iterate_succ_apply' next i 0
  have hki : ∀ i, i ≤ k i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => rw [hk]; have := P1 (k i); omega
  have hX : ∀ i, F i ⊆ X := fun i => by rw [← h0]; exact hmono (Nat.zero_le i)
  refine ⟨fun i => F (k i), ⟨?_, fun i => hX _, fun i => hclosed _, fun i => ?_,
    fun i hi => ?_, ?_⟩, fun i => ?_⟩
  · show F (next^[0] 0) = X
    simpa using h0
  · show F (k (i + 1)) ⊆ F (k i)
    rw [hk]; exact hmono (P1 _).le
  · show F (k (i + 1)) ≠ F (k i)
    rw [hk]; exact P3 _ hi
  · apply Set.eq_empty_of_subset_empty
    rw [← hinter]
    exact Set.iInter_mono fun i => hmono (hki i)
  · refine ⟨next (k i) - 1, ?_⟩
    have h1 := P1 (k i)
    have e1 : next (k i) - 1 + 1 = next (k i) := by omega
    have e2 : F (next (k i) - 1) = F (k i) := P2 _ _ (by omega) (by omega)
    show F (k i) \ F (k (i + 1)) ⊆ F (next (k i) - 1) \ F (next (k i) - 1 + 1)
    rw [e1, e2, hk]

lemma AnalyticOnSet.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {Y Y' : Set E} (h : AnalyticOnSet f Y) (hY : Y' ⊆ Y) : AnalyticOnSet f Y' := fun p hp => by
  obtain ⟨U, hU, g, hg, hfg⟩ := h p (hY hp)
  exact ⟨U, hU, g, hg, fun y hy => hfg y ⟨hY hy.1, hy.2⟩⟩

lemma SmoothOnSet.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {Y Y' : Set E} (h : SmoothOnSet f Y) (hY : Y' ⊆ Y) : SmoothOnSet f Y' := fun p hp => by
  obtain ⟨U, hU, g, hg, hfg⟩ := h p (hY hp)
  exact ⟨U, hU, g, hg, fun y hy => hfg y ⟨hY hy.1, hy.2⟩⟩

lemma accel_eq_of_bounds (hA : IsAnalyticCocycle δ A) (hα : Irrational α) {k : ℤ}
    (h1 : (k : ℝ) ≤ accel α A) (h2 : accel α A < k + 1) : accel α A = k := by
  obtain ⟨m, hm⟩ := (quantized hA hα).2
  rw [hm] at h1 h2 ⊢
  have a : k ≤ m := by exact_mod_cast h1
  have b : m < k + 1 := by exact_mod_cast h2
  have : m = k := by omega
  rw [this]

/-- Schwarz reflection: a real-analytic potential satisfies `v(z̄) = conj v(z)` on its strip. -/
lemma reflect_potential {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) :
    ∀ z ∈ strip δ, v (conj z) = conj (v z) := by
  have hopen := isOpen_strip δ
  have hconjS : ∀ z ∈ strip δ, conj z ∈ strip δ := fun z hz => by
    show |(conj z).im| < δ
    rw [conj_im, abs_neg]; exact hz
  have hwd : DifferentiableOn ℂ (conj ∘ v ∘ conj) (strip δ) := by
    intro z hz
    have hd := ((hv.holo (conj z) (hconjS z hz)).differentiableAt
      (hopen.mem_nhds (hconjS z hz))).hasDerivAt.conj_conj
    rw [conj_conj] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hconv : Convex ℝ (strip δ) := by
    have e : strip δ = Complex.im ⁻¹' Ioo (-δ) δ := by
      ext z; simp only [strip, mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
    rw [e]
    exact (convex_Ioo _ _).linear_preimage Complex.imLm
  have h1 : AnalyticOnNhd ℂ v (strip δ) := hv.holo.analyticOnNhd hopen
  have h2 : AnalyticOnNhd ℂ (conj ∘ v ∘ conj) (strip δ) := hwd.analyticOnNhd hopen
  have h0 : (0 : ℂ) ∈ strip δ := by show |(0 : ℂ).im| < δ; simpa using hv.pos
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), v z = (conj ∘ v ∘ conj) z := by
    rw [Filter.frequently_iff]
    intro S hS
    obtain ⟨r, hr, hrS⟩ := Metric.mem_nhdsWithin_iff.mp hS
    refine ⟨((r / 2 : ℝ) : ℂ), hrS ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    · simp only [Function.comp_apply, Complex.conj_ofReal]
      exact (Complex.conj_eq_iff_im.mpr (hv.real _)).symm
  have heq := h1.eqOn_of_preconnected_of_frequently_eq h2 hconv.isPreconnected h0 hfr
  intro z hz
  have := heq (hconjS z hz)
  simp only [Function.comp_apply, conj_conj] at this
  exact this

lemma schr_sym {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) (E : ℝ) :
    IsRealSymmetricOn δ (schr (eShift E v)) := by
  intro z hz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schr, eShift, reflect_potential hv z hz]

lemma analyticAt_schr_aux {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c : X → ℂ}
    {x : X} (hc : AnalyticAt ℝ c x) : AnalyticAt ℝ (fun y => (!![c y, -1; 1, 0] : M2)) x := by
  let T : ℂ →L[ℝ] M2 :=
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (!![1, 0; 0, 0] : M2)).restrictScalars ℝ
  have hform : (fun y => (!![c y, -1; 1, 0] : M2)) = fun y => T (c y) + !![0, -1; 1, 0] := by
    funext y; ext i j; fin_cases i <;> fin_cases j <;> simp [T]
  rw [hform]
  exact ((T.analyticAt _).comp hc).add analyticAt_const

lemma schr_family_energy {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) :
    IsAnalyticCocycleFamily δ (univ : Set ℝ) (fun E => schr (eShift E v)) := by
  refine ⟨isOpen_univ, fun E _ => hv.schr E, ?_⟩
  rintro ⟨E, z⟩ ⟨-, hz⟩
  show AnalyticAt ℝ (fun q : ℝ × ℂ => schr (eShift q.1 v) q.2) (E, z)
  have hvz : AnalyticAt ℝ (fun q : ℝ × ℂ => v q.2) (E, z) :=
    AnalyticAt.comp (g := v) (f := Prod.snd)
      (hv.holo.analyticAt ((isOpen_strip δ).mem_nhds hz)).restrictScalars analyticAt_snd
  have hE : AnalyticAt ℝ (fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ)) (E, z) :=
    AnalyticAt.comp (g := ⇑Complex.ofRealCLM) (f := Prod.fst) (Complex.ofRealCLM.analyticAt _)
      analyticAt_fst
  exact analyticAt_schr_aux (c := fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ) - v q.2) (hE.sub hvz)

lemma schr_family {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set P}
    {v : P → ℂ → ℂ} (hv : IsAnalyticFamily δ U v) :
    IsAnalyticCocycleFamily δ (U ×ˢ univ) (fun q : P × ℝ => schr (eShift q.2 (v q.1))) := by
  refine ⟨hv.isOpen.prod isOpen_univ, fun q hq => (hv.pot q.1 hq.1).schr q.2, ?_⟩
  rintro ⟨⟨p, E⟩, z⟩ ⟨⟨hp, -⟩, hz⟩
  show AnalyticAt ℝ (fun q : (P × ℝ) × ℂ => schr (eShift q.1.2 (v q.1.1)) q.2) ((p, E), z)
  have hvq : AnalyticAt ℝ (fun q : (P × ℝ) × ℂ => v q.1.1 q.2) ((p, E), z) :=
    AnalyticAt.comp (g := fun q : P × ℂ => v q.1 q.2) (f := fun q : (P × ℝ) × ℂ => (q.1.1, q.2))
      (hv.analytic (p, z) ⟨hp, hz⟩) (AnalyticAt.prod (AnalyticAt.comp (g := Prod.fst) (f := Prod.fst) analyticAt_fst analyticAt_fst) analyticAt_snd)
  have hE : AnalyticAt ℝ (fun q : (P × ℝ) × ℂ => ((q.1.2 : ℝ) : ℂ)) ((p, E), z) :=
    AnalyticAt.comp (g := ⇑Complex.ofRealCLM) (f := fun q : (P × ℝ) × ℂ => q.1.2)
      (Complex.ofRealCLM.analyticAt _) (AnalyticAt.comp (g := Prod.snd) (f := Prod.fst) analyticAt_snd analyticAt_fst)
  exact analyticAt_schr_aux (c := fun q : (P × ℝ) × ℂ => ((q.1.2 : ℝ) : ℂ) - v q.1.1 q.2)
    (hE.sub hvq)

/-- Stratified analyticity for a real-analytic family of real-symmetric cocycles at a fixed
irrational frequency (the proof of Theorems `e` and `v`). -/
theorem stratified_family_analytic {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af)
    (hsym : ∀ p ∈ U, IsRealSymmetricOn δ (Af p)) (hα : Irrational α) :
    IsAnalyticStratified (fun p => L α (Af p) 0) U := by
  classical
  have hcoc := hAf.cocycle
  have hcoc2 : ∀ p ∈ U, IsAnalyticCocycle (δ / 2) (Af p) := fun p hp =>
    (hcoc p hp).mono (by linarith [(hcoc p hp).pos]) (by linarith [(hcoc p hp).pos])
  have hconv : ∀ p ∈ U, TendstoUniformlyOn Af (Af p) (𝓝 p) (strip (δ / 2)) := fun p hp =>
    tendstoUniformlyOn_family hAf.isOpen (by linarith [(hcoc p hp).pos])
      hAf.analytic.continuousOn (fun p hp => (hcoc p hp).periodic) hp
  have hnn : ∀ p ∈ U, 0 ≤ accel α (Af p) := fun p hp =>
    accel_nonneg_of (hcoc p hp) (hsym p hp) α
  have huh : ∀ p ∈ U, UH α (Af p) → ∀ᶠ p' in 𝓝 p, UH α (Af p') := by
    intro p hp hUH
    rw [eventually_iff_seq_eventually]
    intro ps hps
    have h0 : |(0 : ℝ)| < δ / 2 := by simpa using (hcoc2 p hp).pos
    exact uh_open (αs := fun _ => α) (As := fun n => Af (ps n)) ((hcoc p hp).isSLCocycle_shift
      (by simpa using (hcoc p hp).pos)) hUH
      ((hps.eventually (hAf.isOpen.mem_nhds hp)).mono fun n hn =>
        (hcoc _ hn).isSLCocycle_shift (by simpa using (hcoc _ hn).pos))
      tendsto_const_nhds
      (tendstoUniformly_shift_of h0 (tendstoUniformlyOn_seq (hconv p hp) hps))
  have husc : ∀ p ∈ U, ∀ ps : ℕ → P, (∀ n, ps n ∈ U) → Tendsto ps atTop (𝓝 p) →
      ∀ᶠ n in atTop, accel α (Af (ps n)) ≤ accel α (Af p) := fun p hp ps hpsU hps =>
    accel_usc (αs := fun _ => α) (hcoc2 p hp) hα (fun n => hcoc2 _ (hpsU n)) (fun _ => hα)
      tendsto_const_nhds (tendstoUniformlyOn_seq (hconv p hp) hps)
  have contOn : ContinuousOn (fun p => L α (Af p) 0) U := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
    intro ps hps
    have hU' : ∀ n, (if ps n ∈ U then ps n else p) ∈ U := fun n => by
      split_ifs with h
      · exact h
      · exact hp
    have hev : ∀ᶠ n in atTop, (if ps n ∈ U then ps n else p) = ps n :=
      (hps.eventually (hAf.isOpen.mem_nhds hp)).mono fun n hn => if_pos hn
    have hps2 : Tendsto (fun n => if ps n ∈ U then ps n else p) atTop (𝓝 p) :=
      hps.congr' (hev.mono fun n h => h.symm)
    have := jks_continuity (αs := fun _ => α) (hcoc2 p hp) hα (fun n => hcoc2 _ (hU' n))
      tendsto_const_nhds (tendstoUniformlyOn_seq (hconv p hp) hps2)
    refine this.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp_apply, hn]
  let F : ℕ → Set P := fun i =>
    {p | p ∈ U ∧ (i ≠ 0 → ¬ UH α (Af p)) ∧ (i : ℝ) - 1 ≤ accel α (Af p)}
  have hF0 : F 0 = U := by
    ext p
    constructor
    · exact fun h => h.1
    · intro hp
      exact ⟨hp, fun h => absurd rfl h, by have := hnn p hp; push_cast; linarith⟩
  have hFanti : ∀ i, F (i + 1) ⊆ F i := fun i p hp =>
    ⟨hp.1, fun _ => hp.2.1 (Nat.succ_ne_zero i), by
      have := hp.2.2; push_cast at this ⊢; linarith⟩
  have hFcl : ∀ i, ∃ C, IsClosed C ∧ F i = C ∩ U := by
    intro i
    refine ⟨closure (F i), isClosed_closure, ?_⟩
    ext p
    constructor
    · intro hp; exact ⟨subset_closure hp, hp.1⟩
    · rintro ⟨hcl, hpU⟩
      obtain ⟨ps, hpsF, hps⟩ := mem_closure_iff_seq_limit.mp hcl
      refine ⟨hpU, fun hi hUH => ?_, ?_⟩
      · obtain ⟨n, hn⟩ := (hps.eventually (huh p hpU hUH)).exists
        exact (hpsF n).2.1 hi hn
      · obtain ⟨n, hn⟩ := (husc p hpU ps (fun n => (hpsF n).1) hps).exists
        linarith [(hpsF n).2.2]
  have hFinter : ⋂ i, F i = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    have h := (mem_iInter.mp hp) (⌈accel α (Af p)⌉₊ + 2)
    have h2 := h.2.2
    push_cast at h2
    linarith [Nat.le_ceil (accel α (Af p))]
  obtain ⟨S, hS, hSF⟩ := exists_stratification F hF0 hFcl hFanti hFinter
  refine ⟨contOn, S, hS, fun i => ?_⟩
  obtain ⟨m, hm⟩ := hSF i
  refine AnalyticOnSet.mono ?_ hm
  rcases m with _ | _ | j
  · intro p hp
    have hUH : UH α (Af p) := by
      by_contra h
      exact hp.2 ⟨hp.1.1, fun _ => h, by have := hnn p hp.1.1; push_cast; linarith⟩
    obtain ⟨W, hW, hWan⟩ := uh_analytic_family hAf α hp.1.1 hUH
    exact ⟨W, hW, _, hWan, fun y _ => rfl⟩
  · intro p _
    refine ⟨univ, univ_mem, fun _ => 0, analyticOnNhd_const, fun y hy => ?_⟩
    have hyS := hy.1
    have hyU : y ∈ U := hyS.1.1
    have hyUH : ¬ UH α (Af y) := hyS.1.2.1 (by omega)
    have hlt : accel α (Af y) < 1 := by
      by_contra h
      push Not at h
      exact hyS.2 ⟨hyU, fun _ => hyUH, by push_cast; linarith⟩
    have h0 : accel α (Af y) = 0 := by
      have := accel_eq_of_bounds (k := 0) (hcoc y hyU) hα (by simpa using hnn y hyU)
        (by simpa using hlt)
      simpa using this
    have hreg := (isRegular_iff_of (hcoc y hyU) (hsym y hyU) hα).mpr h0
    show L α (Af y) 0 = 0
    by_contra hne
    have hpos : 0 < L α (Af y) 0 := lt_of_le_of_ne
      ((hcoc y hyU).L_nonneg α (by simpa using (hcoc y hyU).pos)) (Ne.symm hne)
    exact hyUH (regular_pos_imp_uh (hcoc y hyU) hα hreg hpos)
  · intro p hp
    have hacc : ∀ y ∈ stratum F (j + 1 + 1), y ∈ U ∧ accel α (Af y) = ((j : ℤ) + 1 : ℤ) := by
      intro y hy
      have hyU : y ∈ U := hy.1.1
      refine ⟨hyU, accel_eq_of_bounds (hcoc y hyU) hα ?_ ?_⟩
      · have := hy.1.2.2; push_cast at this ⊢; linarith
      · by_contra h
        push Not at h
        exact hy.2 ⟨hyU, fun _ => hy.1.2.1 (by omega), by push_cast at h ⊢; linarith⟩
    obtain ⟨hpU, hpacc⟩ := hacc p hp
    have hj0 : ((j : ℤ) + 1 : ℤ) ≠ 0 := by omega
    have hmem := (pluri_mem_of_ne_zero (hcoc p hpU) hα hj0 hpacc).2.1
    obtain ⟨hΩo, hΩa⟩ := pluri_open_analytic hAf α ((j : ℤ) + 1)
    refine ⟨_, hΩo.mem_nhds ⟨hpU, hmem⟩, _, hΩa, fun y hy => ?_⟩
    obtain ⟨hyU, hyacc⟩ := hacc y hy.1
    exact (pluri_mem_of_ne_zero (hcoc y hyU) hα hj0 hyacc).2.2

/-- Stratified smoothness, jointly in the (irrational) frequency (the proof of Theorem
`frequen`). -/
theorem stratified_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {Af : P → ℂ → M2} (hAf : IsAnalyticCocycleFamily δ U Af)
    (hsym : ∀ p ∈ U, IsRealSymmetricOn δ (Af p)) :
    IsSmoothStratified (fun q : ℝ × P => L q.1 (Af q.2) 0) ({a | Irrational a} ×ˢ U) := by
  classical
  set X : Set (ℝ × P) := {a | Irrational a} ×ˢ U with hXdef
  have hcoc := hAf.cocycle
  have hcoc2 : ∀ p ∈ U, IsAnalyticCocycle (δ / 2) (Af p) := fun p hp =>
    (hcoc p hp).mono (by linarith [(hcoc p hp).pos]) (by linarith [(hcoc p hp).pos])
  have hconv : ∀ p ∈ U, TendstoUniformlyOn Af (Af p) (𝓝 p) (strip (δ / 2)) := fun p hp =>
    tendstoUniformlyOn_family hAf.isOpen (by linarith [(hcoc p hp).pos])
      hAf.analytic.continuousOn (fun p hp => (hcoc p hp).periodic) hp
  have hnn : ∀ q ∈ X, 0 ≤ accel q.1 (Af q.2) := fun q hq =>
    accel_nonneg_of (hcoc q.2 hq.2) (hsym q.2 hq.2) q.1
  have huh : ∀ q ∈ X, UH q.1 (Af q.2) → ∀ᶠ q' in 𝓝 q, UH q'.1 (Af q'.2) := by
    intro q hq hUH
    rw [eventually_iff_seq_eventually]
    intro qs hqs
    have hps : Tendsto (fun n => (qs n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hqs
    have has : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hqs
    have h0 : |(0 : ℝ)| < δ / 2 := by simpa using (hcoc2 q.2 hq.2).pos
    exact uh_open (As := fun n => Af (qs n).2)
      ((hcoc q.2 hq.2).isSLCocycle_shift (by simpa using (hcoc q.2 hq.2).pos)) hUH
      ((hps.eventually (hAf.isOpen.mem_nhds hq.2)).mono fun n hn =>
        (hcoc _ hn).isSLCocycle_shift (by simpa using (hcoc _ hn).pos))
      has (tendstoUniformly_shift_of h0 (tendstoUniformlyOn_seq (hconv q.2 hq.2) hps))
  have husc : ∀ q ∈ X, ∀ qs : ℕ → ℝ × P, (∀ n, qs n ∈ X) → Tendsto qs atTop (𝓝 q) →
      ∀ᶠ n in atTop, accel (qs n).1 (Af (qs n).2) ≤ accel q.1 (Af q.2) := by
    intro q hq qs hqsX hqs
    have hps : Tendsto (fun n => (qs n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hqs
    have has : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hqs
    exact accel_usc (hcoc2 q.2 hq.2) hq.1 (fun n => hcoc2 _ (hqsX n).2) (fun n => (hqsX n).1)
      has (tendstoUniformlyOn_seq (hconv q.2 hq.2) hps)
  have contOn : ContinuousOn (fun q : ℝ × P => L q.1 (Af q.2) 0) X := by
    intro q hq
    rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
    intro qs hqs
    have hqs' : Tendsto qs atTop (𝓝 q) := (tendsto_nhdsWithin_iff.mp hqs).1
    have hqsX : ∀ᶠ n in atTop, qs n ∈ X := (tendsto_nhdsWithin_iff.mp hqs).2
    have hX' : ∀ n, (if qs n ∈ X then qs n else q) ∈ X := fun n => by
      split_ifs with h
      · exact h
      · exact hq
    have hev : ∀ᶠ n in atTop, (if qs n ∈ X then qs n else q) = qs n :=
      hqsX.mono fun n hn => if_pos hn
    have hqs2 : Tendsto (fun n => if qs n ∈ X then qs n else q) atTop (𝓝 q) :=
      hqs'.congr' (hev.mono fun n h => h.symm)
    have hps : Tendsto (fun n => (if qs n ∈ X then qs n else q).2) atTop (𝓝 q.2) :=
      (continuous_snd.tendsto _).comp hqs2
    have has : Tendsto (fun n => (if qs n ∈ X then qs n else q).1) atTop (𝓝 q.1) :=
      (continuous_fst.tendsto _).comp hqs2
    have := jks_continuity (hcoc2 q.2 hq.2) hq.1 (fun n => hcoc2 _ (hX' n).2) has
      (tendstoUniformlyOn_seq (hconv q.2 hq.2) hps)
    refine this.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp_apply, hn]
  let F : ℕ → Set (ℝ × P) := fun i =>
    {q | q ∈ X ∧ (i ≠ 0 → ¬ UH q.1 (Af q.2)) ∧ (i : ℝ) - 1 ≤ accel q.1 (Af q.2)}
  have hF0 : F 0 = X := by
    ext q
    constructor
    · exact fun h => h.1
    · intro hq
      exact ⟨hq, fun h => absurd rfl h, by have := hnn q hq; push_cast; linarith⟩
  have hFanti : ∀ i, F (i + 1) ⊆ F i := fun i q hq =>
    ⟨hq.1, fun _ => hq.2.1 (Nat.succ_ne_zero i), by
      have := hq.2.2; push_cast at this ⊢; linarith⟩
  have hFcl : ∀ i, ∃ C, IsClosed C ∧ F i = C ∩ X := by
    intro i
    refine ⟨closure (F i), isClosed_closure, ?_⟩
    ext q
    constructor
    · intro hq; exact ⟨subset_closure hq, hq.1⟩
    · rintro ⟨hcl, hqX⟩
      obtain ⟨qs, hqsF, hqs⟩ := mem_closure_iff_seq_limit.mp hcl
      refine ⟨hqX, fun hi hUH => ?_, ?_⟩
      · obtain ⟨n, hn⟩ := (hqs.eventually (huh q hqX hUH)).exists
        exact (hqsF n).2.1 hi hn
      · obtain ⟨n, hn⟩ := (husc q hqX qs (fun n => (hqsF n).1) hqs).exists
        linarith [(hqsF n).2.2]
  have hFinter : ⋂ i, F i = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    have h := (mem_iInter.mp hq) (⌈accel q.1 (Af q.2)⌉₊ + 2)
    have h2 := h.2.2
    push_cast at h2
    linarith [Nat.le_ceil (accel q.1 (Af q.2))]
  obtain ⟨S, hS, hSF⟩ := exists_stratification F hF0 hFcl hFanti hFinter
  refine ⟨contOn, S, hS, fun i => ?_⟩
  obtain ⟨m, hm⟩ := hSF i
  refine SmoothOnSet.mono ?_ hm
  rcases m with _ | _ | j
  · rintro ⟨α₀, p₀⟩ hq
    have hUH : UH α₀ (Af p₀) := by
      by_contra h
      exact hq.2 ⟨hq.1.1, fun _ => h, by have := hnn _ hq.1.1; push_cast; linarith⟩
    obtain ⟨W, hW, hWs⟩ := uh_smooth_family hAf hq.1.1.2 hUH
    exact ⟨W, hW, _, hWs, fun y _ => rfl⟩
  · intro q _
    refine ⟨univ, univ_mem, fun _ => 0, contDiffOn_const, fun y hy => ?_⟩
    have hyS := hy.1
    have hyX : y ∈ X := hyS.1.1
    have hyUH : ¬ UH y.1 (Af y.2) := hyS.1.2.1 (by omega)
    have hlt : accel y.1 (Af y.2) < 1 := by
      by_contra h
      push Not at h
      exact hyS.2 ⟨hyX, fun _ => hyUH, by push_cast; linarith⟩
    have h0 : accel y.1 (Af y.2) = 0 := by
      have := accel_eq_of_bounds (k := 0) (hcoc y.2 hyX.2) hyX.1 (by simpa using hnn y hyX)
        (by simpa using hlt)
      simpa using this
    have hreg := (isRegular_iff_of (hcoc y.2 hyX.2) (hsym y.2 hyX.2) hyX.1).mpr h0
    show L y.1 (Af y.2) 0 = 0
    by_contra hne
    have hpos : 0 < L y.1 (Af y.2) 0 := lt_of_le_of_ne
      ((hcoc y.2 hyX.2).L_nonneg y.1 (by simpa using (hcoc y.2 hyX.2).pos)) (Ne.symm hne)
    exact hyUH (regular_pos_imp_uh (hcoc y.2 hyX.2) hyX.1 hreg hpos)
  · intro q hq
    have hacc : ∀ y ∈ stratum F (j + 1 + 1),
        y ∈ X ∧ accel y.1 (Af y.2) = ((j : ℤ) + 1 : ℤ) := by
      intro y hy
      have hyX : y ∈ X := hy.1.1
      refine ⟨hyX, accel_eq_of_bounds (hcoc y.2 hyX.2) hyX.1 ?_ ?_⟩
      · have := hy.1.2.2; push_cast at this ⊢; linarith
      · by_contra h
        push Not at h
        exact hy.2 ⟨hyX, fun _ => hy.1.2.1 (by omega), by push_cast at h ⊢; linarith⟩
    obtain ⟨hqX, hqacc⟩ := hacc q hq
    have hj0 : ((j : ℤ) + 1 : ℤ) ≠ 0 := by omega
    have hmem := (pluri_mem_of_ne_zero (hcoc q.2 hqX.2) hqX.1 hj0 hqacc).2.1
    obtain ⟨hΩo, hΩs⟩ := pluri_open_smooth hAf ((j : ℤ) + 1)
    refine ⟨_, hΩo.mem_nhds ⟨hqX.2, hmem⟩, _, hΩs, fun y hy => ?_⟩
    obtain ⟨hyX, hyacc⟩ := hacc y hy.1
    exact (pluri_mem_of_ne_zero (hcoc y.2 hyX.2) hyX.1 hj0 hyacc).2.2

/-! ### Stratified analyticity -/

/-- **Theorem `v`** (stratified analyticity in the potential).  For irrational `α` and a
real-analytic family `v_λ`, `(λ, E) ↦ L(α, A^{(E - v_λ)})` is `C^ω`-stratified on `U × ℝ`. -/
theorem stratified_potential {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set P}
    {v : P → ℂ → ℂ} (hv : IsAnalyticFamily δ U v) (hα : Irrational α) :
    IsAnalyticStratified (fun q : P × ℝ => LE α (v q.1) q.2) (U ×ˢ univ) := by
  have := stratified_family_analytic (schr_family hv)
    (fun q hq => schr_sym (hv.pot q.1 hq.1) q.2) hα
  exact this

/-- **Theorem `e`** (stratified analyticity in the energy).  For irrational `α` and a real-analytic
potential `v`, `E ↦ L(E)` is `C^ω`-stratified on `ℝ`. -/
theorem stratified_energy {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) (hα : Irrational α) :
    IsAnalyticStratified (LE α v) univ := by
  have := stratified_family_analytic (schr_family_energy hv) (fun E _ => schr_sym hv E) hα
  exact this

/-- **Theorem `frequen`.**  For a real-analytic family `v_λ`, `(α, λ, E) ↦ L(α, A^{(E - v_λ)})` is
`C^∞`-stratified on `(ℝ \ ℚ) × U × ℝ`. -/
theorem stratified_frequency {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set P}
    {v : P → ℂ → ℂ} (hv : IsAnalyticFamily δ U v) :
    IsSmoothStratified (fun q : ℝ × P × ℝ => LE q.1 (v q.2.1) q.2.2)
      ({a : ℝ | Irrational a} ×ˢ U ×ˢ univ) := by
  have := stratified_family_smooth (schr_family hv)
    (fun q hq => schr_sym (hv.pot q.1 hq.1) q.2)
  exact this

end AvilaGlobal
