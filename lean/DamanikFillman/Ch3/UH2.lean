/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.1: uniform exponential growth excludes bounded orbits (Theorem 3.8.2, (a) ⇒ (c))

Main results:
* `DF.Cocycle.stable_line` — for products `Tₘ = Aₘ ⋯ A₁` in `SL(2, ℂ)` with `‖Aₘ‖ ≤ Q` and
  `‖Tₘ‖ ≥ c Rᵐ`, the phase-aligned almost most contracted directions converge to a unit vector
  `s` with `‖Tₘ s‖ ≤ 4/‖Tₘ‖ + ‖Tₘ‖ K R^{-2m}`, and every unit vector with bounded forward orbit is
  at most as large as `s` along the orbit (it is a multiple of `s`);
* `DF.Cocycle.not_boundedOrbit_of_uniformExpGrowth` — **Theorem 3.8.2, (a) ⇒ (c)**;
* `DF.Cocycle.uniformExpGrowth_iff_not_boundedOrbit` — **Theorem 3.8.2, (a) ⟺ (c)**.

The proof of (a) ⇒ (c) follows the book's argument for `Λˢ(ω₀) ≠ Λᵘ(ω₀)`: along the orbit of
the point `ω₀` carrying a bounded orbit, let `ρ` be the optimal uniform growth rate and
`R = ρ^{3/4}`; there are windows `[a, a + p]` of arbitrary length on which the growth is at most
`R^{3p/2}`. On such a window the (forward) stable direction at `ω_a` is contracted by `A_p(ω_a)`
and the (backward) stable direction at `ω_{a+p}` is contracted by `A_{-p}(ω_{a+p})`; for the
vectors `vₖ = A_k(ω₀) v` of the bounded orbit this gives `‖v_{a+p}‖ ≤ ‖v_a‖/2 ≤ ‖v_{a+p}‖/4`,
a contradiction. Real cocycles are handled by complexification.
-/
import DamanikFillman.Ch3.UH
import DamanikFillman.Ch3.Ruelle

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace

namespace DF

namespace Cocycle

/-- Convergence of the stable directions for products with uniform exponential growth. -/
theorem stable_line {T A : ℕ → M2} (hdet : ∀ n, (A n).det = 1) (hTdet : ∀ n, (T n).det = 1)
    (hTsucc : ∀ n, T (n + 1) = A (n + 1) * T n) {Q c R : ℝ} (hQ : ∀ n, ‖A n‖ ≤ Q) (hc : 0 < c)
    (hR : 1 < R) (hgrow : ∀ n, c * R ^ n ≤ ‖T n‖) :
    ∃ s : C2, ‖s‖ = 1 ∧
      (∀ n, ‖actC (T n) s‖ ≤ 4 / ‖T n‖ +
        ‖T n‖ * (160 * Q ^ 2 / c ^ 2 / (1 - (R⁻¹) ^ 2) * ((R⁻¹) ^ 2) ^ n)) ∧
      ∀ x : C2, ‖x‖ = 1 → (∃ M, ∀ n, ‖actC (T n) x‖ ≤ M) →
        ∀ n, ‖actC (T n) x‖ ≤ ‖actC (T n) s‖ := by
  have ht1 : ∀ n, 1 ≤ ‖T n‖ := fun n => one_le_norm_of_det_eq_one (hTdet n)
  have ha1 : ∀ n, 1 ≤ ‖A n‖ := fun n => one_le_norm_of_det_eq_one (hdet n)
  have hback : ∀ n, adjugate (A (n + 1)) * T (n + 1) = T n := by
    intro n; rw [hTsucc, ← mul_assoc, adjugate_mul, hdet, one_smul, one_mul]
  -- small vectors and aligned phases
  choose u hu1 hu using fun n => small_vector (T n) (hTdet n)
  choose ph hph1 hph using exists_phase
  set w : ℕ → C2 := fun n => Nat.rec (motive := fun _ => C2) (u 0)
    (fun k wk => ph wk (u (k + 1)) • u (k + 1)) n with hwdef
  have hw0 : w 0 = u 0 := rfl
  have hws : ∀ n, w (n + 1) = ph (w n) (u (n + 1)) • u (n + 1) := fun n => rfl
  have hw1 : ∀ n, ‖w n‖ = 1 := by
    intro n; cases n with
    | zero => rw [hw0, hu1]
    | succ n => rw [hws, norm_smul, hph1, hu1, one_mul]
  have hwT : ∀ n, ‖T n‖ * ‖actC (T n) (w n)‖ ≤ 4 := by
    intro n; cases n with
    | zero => rw [hw0]; exact hu 0
    | succ n => rw [hws, actC_smul, norm_smul, hph1, one_mul]; exact hu _
  have hwT' : ∀ n, ‖actC (T n) (w n)‖ ≤ 4 / ‖T n‖ := fun n => by
    rw [le_div_iff₀ (by linarith [ht1 n]), mul_comm]; exact hwT n
  have hperp : ∀ n, ‖T n‖ / 4 ≤ ‖actC (T n) (perp (w n))‖ := by
    intro n
    have h1 := one_le_norm_mul_perp (hTdet n) (hw1 n)
    have h2 := hwT n
    have h3 : 0 ≤ ‖actC (T n) (perp (w n))‖ := norm_nonneg _
    nlinarith [norm_nonneg (actC (T n) (w n)), ht1 n]
  -- the angle bound
  set δ : ℕ → ℝ := fun n => ‖det2 (w n) (w (n + 1))‖
  have hδ : ∀ n, δ n ≤ 80 * ‖A (n + 1)‖ ^ 2 / ‖T n‖ ^ 2 := by
    intro n
    set a := ‖A (n + 1)‖
    set t := ‖T n‖
    have ht0 : 0 < t := by linarith [ht1 n]
    have hy : ‖actC (T n) (w (n + 1))‖ ≤ 16 * a ^ 2 / t := by
      have e1 : actC (T n) (w (n + 1)) = actC (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1))) := by
        rw [← actC_mul, hback]
      have e2 := norm_actC_le (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1)))
      have e3 := norm_adjugate_le (A (n + 1))
      have e4 := hwT' (n + 1)
      have e5 : t ≤ 2 * a * ‖T (n + 1)‖ := by
        have := norm_mul_le (adjugate (A (n + 1))) (T (n + 1))
        rw [hback] at this
        nlinarith [norm_nonneg (T (n + 1))]
      have hT1 : 0 < ‖T (n + 1)‖ := by linarith [ht1 (n + 1)]
      rw [e1]
      calc ‖actC (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1)))‖
          ≤ 2 * a * (4 / ‖T (n + 1)‖) :=
            e2.trans (mul_le_mul e3 e4 (norm_nonneg _) (by positivity))
        _ ≤ 16 * a ^ 2 / t := by
            rw [mul_div_assoc', div_le_div_iff₀ hT1 ht0]
            nlinarith [ha1 (n + 1)]
    have hx := hwT' n
    have key := norm_det2_mul_le (T := T n) (v := w (n + 1)) (hw1 n)
    rw [hw1 (n + 1), one_mul] at key
    have hp := one_le_norm_mul_perp (hTdet n) (hw1 n)
    -- `δ ≤ δ ‖T x^⊥‖ ‖T x‖ ≤ (‖T y‖ + ‖T x‖) ‖T x‖`
    have hδ1 : δ n ≤ (‖actC (T n) (w (n + 1))‖ + ‖actC (T n) (w n)‖) * ‖actC (T n) (w n)‖ := by
      have hd0 : 0 ≤ δ n := norm_nonneg _
      calc δ n ≤ δ n * (‖actC (T n) (w n)‖ * ‖actC (T n) (perp (w n))‖) := by nlinarith
        _ = (δ n * ‖actC (T n) (perp (w n))‖) * ‖actC (T n) (w n)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right key (norm_nonneg _)
    have ha : 1 ≤ a := ha1 (n + 1)
    calc δ n ≤ (16 * a ^ 2 / t + 4 / t) * (4 / t) := by
          refine hδ1.trans (mul_le_mul (add_le_add hy hx) hx (norm_nonneg _) (by positivity))
      _ ≤ 80 * a ^ 2 / t ^ 2 := by
          have : (16 * a ^ 2 / t + 4 / t) * (4 / t) = (64 * a ^ 2 + 16) / t ^ 2 := by
            field_simp; ring
          rw [this]
          gcongr
          nlinarith
  -- increments of `w`
  have hinc : ∀ n, dist (w n) (w (n + 1)) ≤ 2 * δ n := by
    intro n
    have hr : ⟪w n, w (n + 1)⟫_ℂ = ((‖⟪w n, u (n + 1)⟫_ℂ‖ : ℝ) : ℂ) := by
      rw [hws]; exact hph _ _
    have hr' : ‖⟪w n, w (n + 1)⟫_ℂ‖ = ‖⟪w n, u (n + 1)⟫_ℂ‖ := by rw [hr]; simp
    have hsq := norm_sq_decomp (w n) (w (n + 1)) (hw1 n)
    rw [hw1 (n + 1), hr'] at hsq
    have hr0 : 0 ≤ ‖⟪w n, u (n + 1)⟫_ℂ‖ := norm_nonneg _
    have hr1 : ‖⟪w n, u (n + 1)⟫_ℂ‖ ≤ 1 := by nlinarith [norm_nonneg (det2 (w n) (w (n + 1)))]
    have hd : dist (w n) (w (n + 1)) ^ 2 = 2 - 2 * ‖⟪w n, u (n + 1)⟫_ℂ‖ := by
      rw [dist_eq_norm, @norm_sub_sq ℂ, hw1 n, hw1 (n + 1), hr]
      simp
      try ring
    have hδn : δ n ^ 2 = 1 - ‖⟪w n, u (n + 1)⟫_ℂ‖ ^ 2 := by
      simp only [δ]; linarith
    have : dist (w n) (w (n + 1)) ^ 2 ≤ (2 * δ n) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 this
  -- geometric decay of `δ`
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ 0)
  set ρ := (R⁻¹) ^ 2 with hρdef
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    have : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    have h0 : 0 < R⁻¹ := by positivity
    nlinarith
  have hδg : ∀ n, 0 ≤ n → δ n ≤ 80 * Q ^ 2 / c ^ 2 * ρ ^ n := by
    intro n _
    refine (hδ n).trans ?_
    have ht : c * R ^ n ≤ ‖T n‖ := hgrow n
    have hcR : 0 < c * R ^ n := by positivity
    have hρn : ρ ^ n = ((R ^ n)⁻¹) ^ 2 := by rw [hρdef, ← pow_mul, ← inv_pow, ← pow_mul, mul_comm]
    have hTpos : 0 < ‖T n‖ := hcR.trans_le ht
    rw [hρn, div_le_iff₀ (by positivity : 0 < ‖T n‖ ^ 2)]
    have h1 : 80 * ‖A (n + 1)‖ ^ 2 ≤ 80 * Q ^ 2 := by
      have := hQ (n + 1)
      have := norm_nonneg (A (n + 1))
      nlinarith
    have h2 : (c * R ^ n) ^ 2 ≤ ‖T n‖ ^ 2 := pow_le_pow_left₀ hcR.le ht 2
    have h3 : 80 * Q ^ 2 / c ^ 2 * ((R ^ n)⁻¹) ^ 2 * (c * R ^ n) ^ 2 = 80 * Q ^ 2 := by
      field_simp
    nlinarith [sq_nonneg Q, (by positivity : 0 ≤ 80 * Q ^ 2 / c ^ 2 * ((R ^ n)⁻¹) ^ 2)]
  obtain ⟨hδsum, hδtail⟩ := geom_tail (N := 0) (fun n => norm_nonneg _) hρ0 hρ1 hδg
  have hcauchy : CauchySeq w :=
    cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun n => dist_nonneg) hinc
      (hδsum.mul_left 2))
  obtain ⟨s, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hs1 : ‖s‖ = 1 := by
    have := (continuous_norm.tendsto s).comp hlim
    simp only [comp_def, hw1] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hdist : ∀ n, dist (w n) s ≤ 160 * Q ^ 2 / c ^ 2 / (1 - ρ) * ρ ^ n := by
    intro n
    refine (dist_le_tsum_of_dist_le_of_tendsto (fun n => 2 * δ n) hinc (hδsum.mul_left 2) hlim n).trans ?_
    rw [tsum_mul_left]
    have := hδtail n (Nat.zero_le n)
    have h1ρ : 0 < 1 - ρ := by linarith
    calc 2 * ∑' m, δ (n + m) ≤ 2 * (80 * Q ^ 2 / c ^ 2 * ρ ^ n / (1 - ρ)) := by linarith
      _ = _ := by ring
  have hsbound : ∀ n, ‖actC (T n) s‖ ≤ 4 / ‖T n‖ +
      ‖T n‖ * (160 * Q ^ 2 / c ^ 2 / (1 - ρ) * ρ ^ n) := by
    intro n
    have : actC (T n) s = actC (T n) (w n) - actC (T n) (w n - s) := by rw [actC_sub]; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add (hwT' n) ?_)
    refine (norm_actC_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← dist_eq_norm]; exact hdist n
  refine ⟨s, hs1, hsbound, fun x hx hxb n => ?_⟩
  -- a vector with bounded forward orbit is a multiple of `s`
  have hκ : det2 s x = 0 := by
    by_contra hne
    have hκ : 0 < ‖det2 s x‖ := norm_pos_iff.2 hne
    obtain ⟨M, hM⟩ := hxb
    have hT : Tendsto (fun n => ‖T n‖) atTop atTop :=
      tendsto_atTop_mono hgrow ((tendsto_pow_atTop_atTop_of_one_lt hR).const_mul_atTop hc)
    have hd : Tendsto (fun n => dist (w n) s) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hlim
    have hev1 : ∀ᶠ n in atTop, ‖det2 s x‖ / 2 ≤ ‖det2 (w n) x‖ := by
      filter_upwards [hd.eventually (gt_mem_nhds (half_pos hκ))] with n hn
      have e1 : ‖det2 s x - det2 (w n) x‖ ≤ dist (w n) s * ‖x‖ := by
        rw [det2_sub_left, dist_comm, dist_eq_norm]; exact norm_det2_le _ _
      have e2 := norm_sub_norm_le (det2 s x) (det2 (w n) x)
      rw [hx, mul_one] at e1
      linarith
    obtain ⟨n, hn1, hn2⟩ := (hev1.and (hT.eventually (eventually_ge_atTop
      (16 * (M + 4) / ‖det2 s x‖ + 4)))).exists
    have key := norm_det2_mul_le (T := T n) (v := x) (hw1 n)
    have e1 := hperp n
    have e2 := hwT' n
    have e3 := hM n
    rw [hx, one_mul] at key
    have ht0 : 0 < ‖T n‖ := by linarith [ht1 n]
    have e4 : ‖det2 s x‖ / 2 * (‖T n‖ / 4) ≤ ‖det2 (w n) x‖ * ‖actC (T n) (perp (w n))‖ :=
      mul_le_mul hn1 e1 (by positivity) (norm_nonneg _)
    have e5 : 4 / ‖T n‖ ≤ 4 := by
      rw [div_le_iff₀ ht0]; nlinarith [ht1 n]
    have e6 : 16 * (M + 4) ≤ ‖det2 s x‖ * (‖T n‖ - 4) := by
      have h := (div_le_iff₀ hκ).1 (by linarith : 16 * (M + 4) / ‖det2 s x‖ ≤ ‖T n‖ - 4)
      linarith
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    nlinarith
  have hxs : x = ⟪s, x⟫_ℂ • s := by
    have := decomp s x hs1
    rw [hκ, zero_smul, add_zero] at this
    exact this
  rw [hxs, actC_smul, norm_smul]
  have : ‖⟪s, x⟫_ℂ‖ ≤ 1 := (norm_inner_le_norm _ _).trans (by rw [hs1, hx, one_mul])
  exact mul_le_of_le_one_left (norm_nonneg _) this

/-! ### Complexification -/

/-- The complexification of a real `2 × 2` matrix. -/
def cplx (M : M2R) : M2 := (Complex.ofRealHom).mapMatrix M

lemma cplx_apply (M : M2R) (i j : Fin 2) : cplx M i j = (M i j : ℂ) := rfl

lemma cplx_mul (M N : M2R) : cplx (M * N) = cplx M * cplx N := map_mul _ _ _

lemma cplx_det (M : M2R) : (cplx M).det = (M.det : ℂ) := (RingHom.map_det _ _).symm

lemma cplx_adjugate (M : M2R) : cplx (adjugate M) = adjugate (cplx M) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cplx_apply, adjugate_fin_two]

lemma adjugate_adjugate_two (M : M2) : adjugate (adjugate M) = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two]

/-- The complexification of a real vector. -/
def vC (v : EuclideanSpace ℝ (Fin 2)) : C2 := WithLp.toLp 2 (fun i => (v i : ℂ))

lemma vC_apply (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : vC v i = (v i : ℂ) := rfl

lemma norm_vC (v : EuclideanSpace ℝ (Fin 2)) : ‖vC v‖ = ‖v‖ := by
  have h1 := normsq_C2 (vC v)
  have h2 : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [vC_apply, Complex.norm_real] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)

lemma act_apply (B : M2R) (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    act B v i = B i 0 * v 0 + B i 1 * v 1 := by
  simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma actC_cplx (B : M2R) (v : EuclideanSpace ℝ (Fin 2)) : actC (cplx B) (vC v) = vC (act B v) := by
  ext i; simp only [actC_apply, vC_apply, act_apply, cplx_apply]; push_cast; ring

lemma norm_le_norm_cplx (B : M2R) : ‖B‖ ≤ ‖cplx B‖ := by
  show ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B‖ ≤ ‖cplx B‖
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have := norm_actC_le (cplx B) (vC v)
  rw [actC_cplx, norm_vC, norm_vC] at this
  exact this

lemma norm_entry_le_R (M : M2R) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  have h := sq_norm_col_le_R M j
  have hi : ‖M i j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [sq_nonneg ‖M 0 j‖,
      sq_nonneg ‖M 1 j‖]
  nlinarith [norm_nonneg (M i j), norm_nonneg M]

lemma norm_cplx_le (B : M2R) : ‖cplx B‖ ≤ 2 * ‖B‖ :=
  norm_le_of_entries _ (norm_nonneg _) fun i j => by
    rw [cplx_apply, Complex.norm_real]; exact norm_entry_le_R _ _ _

/-! ### Theorem 3.8.2, (a) ⇒ (c) -/

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Theorem 3.8.2, (a) ⇒ (c)**: a continuous `SL(2, ℝ)` cocycle with uniform exponential growth
has no bounded orbit. -/
theorem not_boundedOrbit_of_uniformExpGrowth (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : UniformExpGrowth T A) : ¬ BoundedOrbit T A := by
  classical
  obtain ⟨C, hC, l, hl, hgrowR⟩ := h
  rintro ⟨ω0, v, hv1, hvb⟩
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hBadd : ∀ (n m : ℤ) ω, B (n + m) ω = B m (tp n ω) * B n ω := fun n m ω => iterZ_add n m ω
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hBn : ∀ n ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
    | succ i ih =>
      intro ω
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul,
        show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
    | pred i ih =>
      intro ω
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
        show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
  -- complexification
  set Bc : ℤ → X → M2 := fun n ω => cplx (B n ω : M2R) with hBcdef
  have hBcdet : ∀ n ω, (Bc n ω).det = 1 := fun n ω => by
    simp only [Bc]; rw [cplx_det, (B n ω).2]; simp
  have hBcup : ∀ n ω, ‖Bc n ω‖ ≤ 2 * Q ^ n.natAbs := fun n ω =>
    (norm_cplx_le _).trans (by linarith [hBn n ω])
  have hBcinv : ∀ (p : ℤ) ω, Bc (-p) (tp p ω) = adjugate (Bc p ω) := by
    intro p ω
    show cplx ((iterZ T.toEquiv A (-p) (tpow T.toEquiv p ω) : SL2R) : M2R) =
      adjugate (cplx ((iterZ T.toEquiv A p ω : SL2R) : M2R))
    rw [← iterZ_inv, Matrix.SpecialLinearGroup.coe_inv, cplx_adjugate]
  have hadj1 : ∀ (p : ℤ) ω, ‖Bc (-p) (tp p ω)‖ ≤ 2 * ‖Bc p ω‖ := fun p ω => by
    rw [hBcinv]; exact norm_adjugate_le _
  have hadj2 : ∀ (p : ℤ) ω, ‖Bc p ω‖ ≤ 2 * ‖Bc (-p) (tp p ω)‖ := fun p ω => by
    rw [hBcinv]; conv_lhs => rw [← adjugate_adjugate_two (Bc p ω)]
    exact norm_adjugate_le _
  -- the orbit
  set ω' : ℤ → X := fun k => tp k ω0 with hω'def
  have hω'add : ∀ k m : ℤ, ω' (k + m) = tp m (ω' k) := fun k m => tpow_add k m ω0
  -- the optimal growth rate along the orbit
  set G : Set ℝ := {r | 1 < r ∧ ∃ c > 0, ∀ k n : ℤ, c * r ^ n.natAbs ≤ ‖Bc n (ω' k)‖}
  have hlG : l ∈ G := ⟨hl, C, hC, fun k n => (hgrowR n (ω' k)).trans (norm_le_norm_cplx _)⟩
  have hGQ : ∀ r ∈ G, r ≤ Q := by
    rintro r ⟨hr1, c, hc, hcr⟩
    by_contra hrQ
    push Not at hrQ
    have hQpos : 0 < Q := by linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / c) ((one_lt_div hQpos).2 hrQ)
    have h1 := (hcr 0 n).trans (hBcup n (ω' 0))
    rw [Int.natAbs_natCast] at h1
    have h2 : c * (r / Q) ^ n ≤ 2 := by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]; linarith
    rw [div_lt_iff₀ hc] at hn
    linarith
  have hGbdd : BddAbove G := ⟨Q, hGQ⟩
  set ρ := sSup G
  have hlρ : l ≤ ρ := le_csSup hGbdd hlG
  have hρ1 : 1 < ρ := by linarith
  set R := ρ ^ ((3 : ℝ) / 4) with hRdef
  have hR1 : 1 < R := Real.one_lt_rpow hρ1 (by norm_num)
  have hRρ : R < ρ := by
    have := Real.rpow_lt_rpow_of_exponent_lt hρ1 (show (3 : ℝ) / 4 < 1 by norm_num)
    simpa using this
  obtain ⟨c, hc, hcR⟩ : ∃ c > 0, ∀ k n : ℤ, c * R ^ n.natAbs ≤ ‖Bc n (ω' k)‖ := by
    obtain ⟨r, ⟨hr1, c, hc, hcr⟩, hRr⟩ := exists_lt_of_lt_csSup ⟨l, hlG⟩ hRρ
    refine ⟨c, hc, fun k n => le_trans ?_ (hcr k n)⟩
    gcongr
  set S := R ^ ((3 : ℝ) / 2) with hSdef
  have hS1 : 1 < S := Real.one_lt_rpow hR1 (by norm_num)
  have hSρ : ρ < S := by
    have : S = ρ ^ ((9 : ℝ) / 8) := by
      rw [hSdef, hRdef, ← Real.rpow_mul (by linarith)]; norm_num
    rw [this]
    have := Real.rpow_lt_rpow_of_exponent_lt hρ1 (show (1 : ℝ) < 9 / 8 by norm_num)
    simpa using this
  have hSR : S < R ^ 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt hR1 (show (3 : ℝ) / 2 < 2 by norm_num)
    simpa [hSdef] using this
  have hSnot : ∀ c' > 0, ∃ k n : ℤ, ‖Bc n (ω' k)‖ < c' * S ^ n.natAbs := by
    intro c' hc'
    by_contra hcon
    push Not at hcon
    have := le_csSup hGbdd (show S ∈ G from ⟨hS1, c', hc', hcon⟩)
    linarith
  -- the smallness threshold
  have hR0 : 0 < R := by linarith
  have hρ' : (R⁻¹) ^ 2 < 1 := by
    have : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR1
    have h0 : 0 < R⁻¹ := by positivity
    nlinarith
  set K := 160 * (2 * Q) ^ 2 / c ^ 2 / (1 - (R⁻¹) ^ 2) with hKdef
  have hK0 : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  have hb : S * (R⁻¹) ^ 2 < 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]; exact hSR
  have hsmall : Tendsto (fun p : ℕ => 4 / (c * R ^ p) + 2 * S ^ p * (K * ((R⁻¹) ^ 2) ^ p))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ => 4 / (c * R ^ p)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop_atTop_of_one_lt hR1).const_mul_atTop hc)
    have h2 : Tendsto (fun p : ℕ => 2 * K * (S * (R⁻¹) ^ 2) ^ p) atTop (𝓝 (2 * K * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hb).const_mul _
    rw [mul_zero] at h2
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun p => by rw [mul_pow]; ring
  obtain ⟨p1, hp1⟩ := eventually_atTop.1 (hsmall.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  -- a window of near-minimal growth
  obtain ⟨a, p, hp, hwin1, hwin2⟩ : ∃ a : ℤ, ∃ p : ℕ, p1 ≤ p ∧ ‖Bc p (ω' a)‖ ≤ 2 * S ^ p ∧
      ‖Bc (-(p : ℤ)) (ω' (a + p))‖ ≤ 2 * S ^ p := by
    have hc' : 0 < (S ^ p1)⁻¹ / 2 := by positivity
    obtain ⟨k, n, hkn⟩ := hSnot _ hc'
    have hc'le : ∀ q : ℕ, (S ^ p1)⁻¹ / 2 * S ^ q ≤ S ^ q := by
      intro q
      have : (S ^ p1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1.le)
      have : 0 < S ^ q := by positivity
      nlinarith
    have hp1n : p1 ≤ n.natAbs := by
      by_contra hlt
      push Not at hlt
      have h1 : 1 ≤ ‖Bc n (ω' k)‖ := one_le_norm_of_det_eq_one (hBcdet n _)
      have h2 : S ^ n.natAbs ≤ S ^ p1 := pow_le_pow_right₀ hS1.le hlt.le
      have h3 : (S ^ p1)⁻¹ / 2 * S ^ n.natAbs ≤ 1 / 2 := by
        have : (S ^ p1)⁻¹ * S ^ n.natAbs ≤ 1 := by
          rw [inv_mul_le_iff₀ (by positivity), mul_one]; exact h2
        linarith
      linarith
    have hkn' : ‖Bc n (ω' k)‖ ≤ S ^ n.natAbs := hkn.le.trans (hc'le _)
    rcases Int.natAbs_eq n with hn | hn
    · refine ⟨k, n.natAbs, hp1n, ?_, ?_⟩
      · rw [← hn]; linarith [pow_pos (zero_lt_one.trans hS1) n.natAbs]
      · rw [hω'add]
        have := hadj1 (n.natAbs : ℤ) (ω' k)
        rw [← hn] at this ⊢
        linarith
    · refine ⟨k - n.natAbs, n.natAbs, hp1n, ?_, ?_⟩
      · have := hadj2 (n.natAbs : ℤ) (ω' (k - n.natAbs))
        rw [← hω'add, sub_add_cancel, ← hn] at this
        linarith
      · rw [sub_add_cancel, ← hn]
        linarith [pow_pos (zero_lt_one.trans hS1) n.natAbs]
  -- the bounded orbit
  set vk : ℤ → C2 := fun k => vC (act (B k ω0 : M2R) v) with hvkdef
  have hvk_shift : ∀ (k m : ℤ), actC (Bc m (ω' k)) (vk k) = vk (k + m) := by
    intro k m
    simp only [vk, Bc]
    rw [actC_cplx, ← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, hBadd]
  have hvk0 : vk 0 = vC v := by
    simp only [vk]; rw [hB0, Matrix.SpecialLinearGroup.coe_one, act_one]
  have hvk_pos : ∀ k, 0 < ‖vk k‖ := by
    intro k
    rcases eq_or_lt_of_le (norm_nonneg (vk k)) with h0 | h0
    · exfalso
      have h1 := hvk_shift k (-k)
      have hz : actC (Bc (-k) (ω' k)) 0 = 0 := by simp [actC]
      rw [norm_eq_zero.1 h0.symm, hz, add_neg_cancel, hvk0] at h1
      have := congrArg norm h1
      rw [norm_zero, norm_vC, hv1] at this
      norm_num at this
    · exact h0
  have hvk_le : ∀ k, ‖vk k‖ ≤ 1 := fun k => by simp only [vk]; rw [norm_vC]; exact hvb k
  -- contraction estimate from `stable_line`
  have hcontr : ∀ (Tm Am : ℕ → M2) (z : ℤ → ℤ), (∀ n, (Am n).det = 1) → (∀ n, (Tm n).det = 1) →
      (∀ n, Tm (n + 1) = Am (n + 1) * Tm n) → (∀ n, ‖Am n‖ ≤ 2 * Q) →
      (∀ n, c * R ^ n ≤ ‖Tm n‖) → ‖Tm p‖ ≤ 2 * S ^ p → ∀ k0 : ℤ,
      (∀ m : ℕ, actC (Tm m) (vk k0) = vk (z m)) → ‖vk (z p)‖ ≤ ‖vk k0‖ / 2 := by
    intro Tm Am z hAd hTd hTs hAQ hTg hwin k0 hz
    obtain ⟨s, hs1, hsb, hsx⟩ := stable_line hAd hTd hTs hAQ hc hR1 hTg
    have hk0 := hvk_pos k0
    set x : C2 := ((‖vk k0‖⁻¹ : ℝ) : ℂ) • vk k0
    have hx1 : ‖x‖ = 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk0),
        inv_mul_cancel₀ hk0.ne']
    have hxm : ∀ m : ℕ, ‖actC (Tm m) x‖ = ‖vk k0‖⁻¹ * ‖vk (z m)‖ := by
      intro m
      rw [actC_smul, hz, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hk0)]
    have hxb : ∃ M, ∀ m : ℕ, ‖actC (Tm m) x‖ ≤ M := ⟨‖vk k0‖⁻¹, fun m => by
      rw [hxm]
      exact mul_le_of_le_one_right (inv_pos.2 hk0).le (hvk_le _)⟩
    have h1 := hsx x hx1 hxb p
    have h2 := hsb p
    have hTp : 0 < ‖Tm p‖ := lt_of_lt_of_le (by positivity) (hTg p)
    have h3 : 4 / ‖Tm p‖ ≤ 4 / (c * R ^ p) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (hTg p)
    have h4 : ‖Tm p‖ * (160 * (2 * Q) ^ 2 / c ^ 2 / (1 - (R⁻¹) ^ 2) * ((R⁻¹) ^ 2) ^ p) ≤
        2 * S ^ p * (K * ((R⁻¹) ^ 2) ^ p) :=
      mul_le_mul_of_nonneg_right hwin (by positivity)
    have h5 := hp1 p hp
    rw [hxm] at h1
    have h6 : ‖vk k0‖⁻¹ * ‖vk (z p)‖ ≤ 1 / 2 := by linarith
    rw [inv_mul_le_iff₀ hk0] at h6
    linarith
  -- forward window
  have hfwd : ‖vk (a + p)‖ ≤ ‖vk a‖ / 2 := by
    refine hcontr (fun m => Bc m (ω' a)) (fun m => cplx (A (tp ((m : ℤ) - 1) (ω' a)) : M2R))
      (fun m => a + m) (fun m => by rw [cplx_det, (A _).2]; simp) (fun m => hBcdet _ _)
      (fun m => ?_) (fun m => (norm_cplx_le _).trans (by linarith [hQA (tp ((m : ℤ) - 1) (ω' a))]))
      (fun m => by have := hcR a m; rwa [Int.natAbs_natCast] at this) hwin1 a
      (fun m => by rw [hvk_shift])
    show cplx (B ((m + 1 : ℕ) : ℤ) (ω' a) : M2R) =
      cplx (A (tp (((m + 1 : ℕ) : ℤ) - 1) (ω' a)) : M2R) * cplx (B (m : ℤ) (ω' a) : M2R)
    rw [show (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) by push_cast; ring,
      show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring,
      show B ((m : ℤ) + 1) (ω' a) = A (tp m (ω' a)) * B m (ω' a) from iterZ_succ _ _,
      Matrix.SpecialLinearGroup.coe_mul, cplx_mul]
  -- backward window
  have hbwd : ‖vk a‖ ≤ ‖vk (a + p)‖ / 2 := by
    have := hcontr (fun m => Bc (-(m : ℤ)) (ω' (a + p)))
      (fun m => cplx (((A (tp (-(m : ℤ)) (ω' (a + p))))⁻¹ : SL2R) : M2R))
      (fun m => a + p + -(m : ℤ)) (fun m => by rw [cplx_det, (_ : SL2R).2]; simp)
      (fun m => hBcdet _ _) (fun m => ?_)
      (fun m => (norm_cplx_le _).trans (by linarith [hQAi (tp (-(m : ℤ)) (ω' (a + p)))]))
      (fun m => by have := hcR (a + p) (-(m : ℤ)); rwa [Int.natAbs_neg, Int.natAbs_natCast] at this)
      hwin2 (a + p) (fun m => by rw [hvk_shift])
    · rwa [show a + (p : ℤ) + -(p : ℤ) = a by ring] at this
    · show cplx (B (-((m + 1 : ℕ) : ℤ)) (ω' (a + p)) : M2R) =
        cplx (((A (tp (-((m + 1 : ℕ) : ℤ)) (ω' (a + p))))⁻¹ : SL2R) : M2R) *
          cplx (B (-(m : ℤ)) (ω' (a + p)) : M2R)
      rw [show -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 by push_cast; ring,
        show B (-(m : ℤ) - 1) (ω' (a + p)) = (A (tp (-(m : ℤ) - 1) (ω' (a + p))))⁻¹ *
          B (-(m : ℤ)) (ω' (a + p)) from iterZ_pred _ _,
        Matrix.SpecialLinearGroup.coe_mul, cplx_mul]
  have := hvk_pos (a + p)
  linarith

/-- **Theorem 3.8.2, (a) ⟺ (c)**: a continuous `SL(2, ℝ)` cocycle over a homeomorphism of a
compact metric space exhibits uniform exponential growth iff it has no bounded orbit. -/
theorem uniformExpGrowth_iff_not_boundedOrbit (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) : UniformExpGrowth T A ↔ ¬ BoundedOrbit T A :=
  ⟨not_boundedOrbit_of_uniformExpGrowth T A hA, uniformExpGrowth_of_not_boundedOrbit T A hA⟩

end Cocycle

end DF
