/-
# Arithmetic of gap labels

Formalization of the elementary arithmetic cores in S. Becker, *Self-dual perturbations of the
critical almost Mathieu operator: Dry Ten Martini and Hausdorff dimension*
(`spectral_gaps_and_dimension.tex`):

* §5, Lemma `gap:lem:cluster-trace` (l.6527–6603): the integer identification
  `Mq + mp = 0`, `m = sq`, `τ(P_n) = q|δ|` from an affine trace with rational limit zero and the
  relative asymptotic `τ(P_n) = q|δ|(1 + o(1))` (A).
* §5, Lemma `gap:lem:absolute-label` (l.6607–6641): the absolute affine label
  `N(p/q+δ) = r/q + m₀δ`, the congruence `m₀p ≡ r (mod q)`, the bound `|m₀| ≤ 2/Δ`, and the
  slope change `sq` across one cluster (B).
* §5, Proposition `gap:prop:infinite-exponent` (l.6643–6742): the final label computation
  `r/q + n(α − p/q) = {nα}` and `m₀ ≡ n (mod q)` (C); the supply of convergents with
  `0 < |α − p/q| < e^{-Dq}` when `β(α) = ∞`, and the level-count bound (D).
* §3, Proposition `gap:prop:transfer` (l.3265–3312): the contradiction step of the proof, as a
  statement of real analysis (E).
* §3, proof of Theorem `gap:thm:comparison` (l.3227–3238): the energy reversal `r ↦ 1 − r`
  permutes `Λ_α` (F).

The operator-algebraic inputs (affine-label formula, trace asymptotics, IDS transfer) are
hypotheses here; what is proved is exactly the arithmetic/real-analytic deduction in the paper.
-/
import Mathlib
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open Filter Topology Set

namespace SGD

namespace LabelArithmetic

/-! ## Auxiliary facts -/

/-- For `s = ±1`, the one-sided punctured neighbourhood filter `𝓝[{δ | 0 < sδ}] 0` is
nontrivial. (Auxiliary for Lemmas `gap:lem:cluster-trace` and `gap:lem:absolute-label`.) -/
theorem oneSided_neBot {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] (0 : ℝ)).NeBot := by
  rcases hs with rfl | rfl
  · have : {δ : ℝ | 0 < ((1 : ℤ) : ℝ) * δ} = Ioi 0 := by ext δ; simp
    rw [this]; infer_instance
  · have : {δ : ℝ | 0 < ((-1 : ℤ) : ℝ) * δ} = Iio 0 := by ext δ; simp
    rw [this]; infer_instance

/-- Points of the one-sided interval `0 < sδ < Δ` lie eventually in the one-sided
neighbourhood filter. (Auxiliary.) -/
theorem eventually_oneSided_interval {s : ℤ} {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ᶠ δ in 𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] (0 : ℝ), 0 < (s : ℝ) * δ ∧ (s : ℝ) * δ < Δ := by
  have h1 : ∀ᶠ δ in 𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] (0 : ℝ), 0 < (s : ℝ) * δ :=
    self_mem_nhdsWithin
  have h2 : ∀ᶠ δ in 𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] (0 : ℝ), (s : ℝ) * δ < Δ := by
    apply nhdsWithin_le_nhds
    have hc : Continuous fun δ : ℝ => (s : ℝ) * δ := continuous_const.mul continuous_id
    have : ∀ᶠ δ in 𝓝 (0 : ℝ), (s : ℝ) * δ < Δ :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hΔ)
    exact this
  exact h1.and h2

/-- For `s = ±1` and `0 < sδ`, one has `|δ| = sδ`. (Auxiliary.) -/
theorem abs_eq_sign_mul {s : ℤ} (hs : s = 1 ∨ s = -1) {δ : ℝ} (h : 0 < (s : ℝ) * δ) :
    |δ| = (s : ℝ) * δ := by
  rcases hs with rfl | rfl
  · simp only [Int.cast_one, one_mul] at h ⊢; exact abs_of_pos h
  · simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_pos] at h ⊢; exact abs_of_neg h

/-- If `q ∣ m p` with `gcd(p,q) = 1` then `q ∣ m`. (Auxiliary.) -/
theorem dvd_of_dvd_mul_coprime {p m : ℤ} {q : ℕ} (hpq : Int.gcd p q = 1)
    (h : (q : ℤ) ∣ m * p) : (q : ℤ) ∣ m := by
  have hc : IsCoprime (q : ℤ) p := (Int.isCoprime_iff_gcd_eq_one.mpr hpq).symm
  exact hc.dvd_of_dvd_mul_right h

/-! ## A. Exact trace of a cluster (Lemma `gap:lem:cluster-trace`) -/

/-- **Lemma 5.x (`gap:lem:cluster-trace`), integer identification (l.6595–6602).**
Let `gcd(p,q) = 1`, `q ≥ 1`, `s ∈ {1,-1}`, `Δ > 0`, and let the trace of the cluster
projection be affine with fixed integers on the one-sided interval,
`τ(P_n) = M + m a` with `a = p/q + δ`, `0 < sδ < Δ` (continuous-field affine-label formula).
If the rational limit is zero, `M + m p/q = 0`, and the relative asymptotic
`τ(P_n)/(q|δ|) → 1` holds as `sδ → 0⁺`, then `m = s q`, `M = -s p`, and
`τ(P_n) = q|δ|` on the whole interval `0 < sδ < Δ`. -/
theorem cluster_trace_exact {p : ℤ} {q : ℕ} (hq : 1 ≤ q) (hpq : Int.gcd p q = 1)
    {s : ℤ} (hs : s = 1 ∨ s = -1) {Δ : ℝ} (hΔ : 0 < Δ) {M m : ℤ} (τ : ℝ → ℝ)
    (haff : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      τ δ = M + m * ((p : ℝ) / q + δ))
    (hlim0 : (M : ℝ) + m * ((p : ℝ) / q) = 0)
    (hasymp : Tendsto (fun δ => τ δ / ((q : ℝ) * |δ|))
      (𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] 0) (𝓝 1)) :
    m = s * q ∧ M = -(s * p) ∧
      ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ → τ δ = q * |δ| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- `Mq + mp = 0`
  have hint : M * (q : ℤ) + m * p = 0 := by
    have : (M : ℝ) * q + m * p = 0 := by
      field_simp at hlim0; linarith
    exact_mod_cast this
  -- `m = k q`
  obtain ⟨k, hk⟩ : (q : ℤ) ∣ m := by
    apply dvd_of_dvd_mul_coprime hpq
    exact ⟨-M, by linarith⟩
  -- on the interval, `τ = m δ`
  have hτ : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ → τ δ = m * δ := by
    intro δ h1 h2
    rw [haff δ h1 h2]; linear_combination hlim0
  -- the ratio is eventually the constant `k s`
  have hev : ∀ᶠ δ in 𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] (0 : ℝ),
      τ δ / ((q : ℝ) * |δ|) = (k : ℝ) * s := by
    filter_upwards [eventually_oneSided_interval hΔ] with δ ⟨h1, h2⟩
    have habs := abs_eq_sign_mul hs h1
    have hs2 : (s : ℝ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hsδ : (s : ℝ) * δ ≠ 0 := h1.ne'
    rw [hτ δ h1 h2, habs, hk, div_eq_iff (mul_ne_zero hq0.ne' hsδ)]
    push_cast
    linear_combination (-((k : ℝ) * q * δ)) * hs2
  have := oneSided_neBot hs
  have hks : (k : ℝ) * s = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)) hasymp
  have hks' : k * s = 1 := by exact_mod_cast hks
  have hk' : k = s := by
    rcases hs with rfl | rfl <;> omega
  have hm : m = s * q := by rw [hk, hk']; ring
  refine ⟨hm, ?_, ?_⟩
  · have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have h0 : (M + s * p) * q = 0 := by rw [hm] at hint; linear_combination hint
    have := (mul_eq_zero.mp h0).resolve_right hqz
    linarith
  · intro δ h1 h2
    rw [hτ δ h1 h2, abs_eq_sign_mul hs h1, hm]; push_cast; ring

/-- Non-vacuity check for `cluster_trace_exact`: the model trace `τ(δ) = q|δ|` satisfies all
hypotheses with `m = sq`, `M = -sp` (here `p = 1`, `q = 2`, `s = 1`). -/
example : ∃ τ : ℝ → ℝ,
    (∀ δ : ℝ, 0 < ((1 : ℤ) : ℝ) * δ → ((1 : ℤ) : ℝ) * δ < 1 →
      τ δ = ((-1 : ℤ) : ℝ) + ((2 : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((2 : ℕ) : ℝ) + δ)) ∧
    Tendsto (fun δ => τ δ / (((2 : ℕ) : ℝ) * |δ|))
      (𝓝[{δ : ℝ | 0 < ((1 : ℤ) : ℝ) * δ}] 0) (𝓝 1) := by
  refine ⟨fun δ => 2 * δ, fun δ _ _ => by push_cast; ring, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < ((1 : ℤ) : ℝ) * δ)
  simp at hδ
  rw [abs_of_pos hδ]; push_cast; field_simp

/-! ## B. Absolute gap labels (Lemma `gap:lem:absolute-label`) -/

/-- **Lemma 5.x (`gap:lem:absolute-label`), eq. `gap:eq:absolute-affine` (l.6606–6626).**
Let `gcd(p,q) = 1`, `q ≥ 1`, `s ∈ {1,-1}`, `Δ > 0`. Suppose the IDS of a connected gap branch is
affine with fixed integers, `N(p/q+δ) = M + m₀(p/q+δ)` for `0 < sδ < Δ`, takes values in
`[0,1]` there, and has one-sided rational limit `r/q`. Then
`Mq + m₀p = r`, `m₀p ≡ r (mod q)`, `N(p/q+δ) = r/q + m₀δ` and `|m₀| ≤ 2/Δ`. -/
theorem absolute_label {p : ℤ} {q : ℕ} (hq : 1 ≤ q) {s : ℤ} (hs : s = 1 ∨ s = -1)
    {Δ : ℝ} (hΔ : 0 < Δ) {M m₀ r : ℤ} (N : ℝ → ℝ)
    (haff : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      N ((p : ℝ) / q + δ) = M + m₀ * ((p : ℝ) / q + δ))
    (hrange : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ → N ((p : ℝ) / q + δ) ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun δ => N ((p : ℝ) / q + δ))
      (𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] 0) (𝓝 ((r : ℝ) / q))) :
    M * q + m₀ * p = r ∧ m₀ * p ≡ r [ZMOD q] ∧
      (∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
        N ((p : ℝ) / q + δ) = (r : ℝ) / q + m₀ * δ) ∧
      |(m₀ : ℝ)| ≤ 2 / Δ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have := oneSided_neBot hs
  -- the affine function tends to `M + m₀ p/q`
  have hlim' : Tendsto (fun δ => N ((p : ℝ) / q + δ))
      (𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] 0) (𝓝 ((M : ℝ) + m₀ * ((p : ℝ) / q))) := by
    have hc : Tendsto (fun δ : ℝ => (M : ℝ) + m₀ * ((p : ℝ) / q + δ))
        (𝓝[{δ : ℝ | 0 < (s : ℝ) * δ}] 0) (𝓝 ((M : ℝ) + m₀ * ((p : ℝ) / q + 0))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((continuous_const.add (continuous_const.mul
        (continuous_const.add continuous_id))).tendsto 0)
    simp only [add_zero] at hc
    apply hc.congr'
    filter_upwards [eventually_oneSided_interval hΔ] with δ ⟨h1, h2⟩
    exact (haff δ h1 h2).symm
  have hr : (r : ℝ) / q = M + m₀ * ((p : ℝ) / q) := tendsto_nhds_unique hlim hlim'
  have hint : M * (q : ℤ) + m₀ * p = r := by
    have : (M : ℝ) * q + m₀ * p = r := by
      field_simp at hr; linarith
    exact_mod_cast this
  have hcong : m₀ * p ≡ r [ZMOD q] := by
    rw [Int.ModEq, ← hint]; simp
  have hform : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      N ((p : ℝ) / q + δ) = (r : ℝ) / q + m₀ * δ := by
    intro δ h1 h2; rw [haff δ h1 h2, hr]; ring
  refine ⟨hint, hcong, hform, ?_⟩
  -- `r/q ∈ [0,1]` as a limit of values in `[0,1]`
  have hrI : (r : ℝ) / q ∈ Icc (0 : ℝ) 1 := by
    apply isClosed_Icc.mem_of_tendsto hlim
    filter_upwards [eventually_oneSided_interval hΔ] with δ ⟨h1, h2⟩
    exact hrange δ h1 h2
  -- evaluate at `δ = sΔ/2`
  have hs2 : (s : ℝ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hss : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> norm_num
  set δ := (s : ℝ) * Δ / 2 with hδ
  have h1 : 0 < (s : ℝ) * δ := by rw [hδ]; nlinarith
  have h2 : (s : ℝ) * δ < Δ := by rw [hδ]; nlinarith
  have hN := hrange δ h1 h2
  rw [hform δ h1 h2] at hN
  have hbd : |(m₀ : ℝ) * δ| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hN.1, hN.2, hrI.1, hrI.2]
  have : |(m₀ : ℝ) * δ| = |(m₀ : ℝ)| * (Δ / 2) := by
    rw [hδ, abs_mul, mul_div_assoc, abs_mul, hss, abs_of_pos (by linarith : (0 : ℝ) < Δ / 2)]
    ring
  rw [this] at hbd
  rw [le_div_iff₀ hΔ]; linarith

/-- **Lemma 5.x (`gap:lem:absolute-label`), last assertion (l.6621–6626).**
Crossing one cluster of exact trace `q|δ|` (Lemma `gap:lem:cluster-trace`) upwards in energy
changes the integer slope by `sq`: if `N_lower(p/q+δ) = r/q + m_l δ`, `N_upper(p/q+δ) = r'/q + m_u δ`
and `N_upper − N_lower = q|δ|` on `0 < sδ < Δ`, then `r' = r` and `m_u = m_l + sq`. -/
theorem slope_change_across_cluster {p : ℤ} {q : ℕ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    {Δ : ℝ} (hΔ : 0 < Δ) {r r' m_l m_u : ℤ} (Nl Nu : ℝ → ℝ)
    (hl : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      Nl ((p : ℝ) / q + δ) = (r : ℝ) / q + m_l * δ)
    (hu : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      Nu ((p : ℝ) / q + δ) = (r' : ℝ) / q + m_u * δ)
    (hcl : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      Nu ((p : ℝ) / q + δ) - Nl ((p : ℝ) / q + δ) = q * |δ|) :
    (r' : ℝ) / q = (r : ℝ) / q ∧ m_u = m_l + s * q := by
  have hs2 : (s : ℝ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  -- the difference is `(r'-r)/q + (m_u - m_l) δ = s q δ` at two points
  have key : ∀ δ : ℝ, 0 < (s : ℝ) * δ → (s : ℝ) * δ < Δ →
      ((r' : ℝ) / q - r / q) + ((m_u : ℝ) - m_l - s * q) * δ = 0 := by
    intro δ h1 h2
    have := hcl δ h1 h2
    rw [hu δ h1 h2, hl δ h1 h2, abs_eq_sign_mul hs h1] at this
    linear_combination this
  have e1 := key ((s : ℝ) * Δ / 2) (by nlinarith) (by nlinarith)
  have e2 := key ((s : ℝ) * Δ / 4) (by nlinarith) (by nlinarith)
  have hsl : ((m_u : ℝ) - m_l - s * q) * ((s : ℝ) * Δ / 4) = 0 := by linarith
  have hsne : (s : ℝ) * Δ / 4 ≠ 0 := by
    intro h; have : (s : ℝ) * s * Δ = 0 := by linarith [congrArg ((s : ℝ) * ·) h]
    rw [hs2] at this; linarith
  have hm : (m_u : ℝ) - m_l - s * q = 0 := (mul_eq_zero.mp hsl).resolve_right hsne
  refine ⟨?_, ?_⟩
  · rw [hm, zero_mul, add_zero] at e1; linarith
  · have : (m_u : ℝ) = m_l + s * q := by linarith
    exact_mod_cast this

/-! ## C. The final label computation (Proposition `gap:prop:infinite-exponent`) -/

/-- **Proposition 5.x (`gap:prop:infinite-exponent`), choice of the rational index
(l.6720–6723).** For `gcd(p,q) = 1` and `0 < |n| < q`, the index `r = np − q⌊np/q⌋ = np mod q`
lies in `{1, …, q−1}`. -/
theorem label_index_mem {p n : ℤ} {q : ℕ} (hpq : Int.gcd p q = 1) (hn : n ≠ 0)
    (hnq : |n| < q) : 1 ≤ n * p % q ∧ n * p % q ≤ q - 1 := by
  have hq : (0 : ℤ) < q := lt_of_le_of_lt (abs_nonneg n) hnq
  refine ⟨?_, ?_⟩
  · have hnn : 0 ≤ n * p % q := Int.emod_nonneg _ hq.ne'
    rcases hnn.lt_or_eq with h | h
    · omega
    · exfalso
      have hd : (q : ℤ) ∣ n * p := Int.dvd_of_emod_eq_zero h.symm
      have hdn : (q : ℤ) ∣ n := dvd_of_dvd_mul_coprime hpq hd
      have := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdn)
      omega
  · have := Int.emod_lt_of_pos (n * p) hq; omega

/-- **Proposition 5.x (`gap:prop:infinite-exponent`), the IDS of the indicated cut
(l.6736–6742).** Let `gcd(p,q) = 1`, `n ≠ 0`, `|n| < q`, `|n(α − p/q)| < 1/q`, and
`r = np mod q`. Then
`r/q + n(α − p/q) = nα − ⌊np/q⌋ = {nα}`. -/
theorem label_eq_fract {α : ℝ} {p n : ℤ} {q : ℕ} (hpq : Int.gcd p q = 1) (hn : n ≠ 0)
    (hnq : |n| < q) (hclose : |(n : ℝ) * (α - p / q)| < 1 / q) :
    ((n * p % q : ℤ) : ℝ) / q + n * (α - p / q) = n * α - ⌊((n * p : ℤ) : ℝ) / q⌋ ∧
      ((n * p % q : ℤ) : ℝ) / q + n * (α - p / q) = Int.fract (n * α) := by
  have hqz : (0 : ℤ) < q := lt_of_le_of_lt (abs_nonneg n) hnq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqz
  obtain ⟨h1, h2⟩ := label_index_mem hpq hn hnq
  have hdiv : ((n * p % q : ℤ) : ℝ) = n * p - q * ((n * p / q : ℤ) : ℝ) := by
    have := Int.emod_def (n * p) q
    rw [this]; push_cast; ring
  have heq : ((n * p % q : ℤ) : ℝ) / q + n * (α - p / q) = n * α - ((n * p / q : ℤ) : ℝ) := by
    rw [hdiv]; field_simp; ring
  have hr0 : (0 : ℝ) ≤ ((n * p % q : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ n * p % q)
  have hrq : ((n * p % q : ℤ) : ℝ) < q := by
    have : n * p % q < (q : ℤ) := by omega
    exact_mod_cast this
  have hfl : ⌊((n * p : ℤ) : ℝ) / q⌋ = n * p / q := by
    rw [Int.floor_eq_iff]
    have hsplit : ((n * p : ℤ) : ℝ) / q = ((n * p / q : ℤ) : ℝ) + ((n * p % q : ℤ) : ℝ) / q := by
      rw [hdiv]; field_simp; push_cast; ring
    rw [hsplit]
    have h0 : 0 ≤ ((n * p % q : ℤ) : ℝ) / q := div_nonneg hr0 hq0.le
    have h1' : ((n * p % q : ℤ) : ℝ) / q < 1 := (div_lt_one hq0).mpr hrq
    constructor <;> linarith
  refine ⟨by rw [heq, hfl], ?_⟩
  -- `⌊nα⌋ = np / q`
  have hr1 : (1 : ℝ) ≤ ((n * p % q : ℤ) : ℝ) := by exact_mod_cast h1
  have hr2 : ((n * p % q : ℤ) : ℝ) ≤ q - 1 := by
    have : ((n * p % q : ℤ) : ℝ) ≤ ((q : ℤ) : ℝ) - 1 := by exact_mod_cast h2
    simpa using this
  have hlo : 1 / (q : ℝ) ≤ ((n * p % q : ℤ) : ℝ) / q := by
    rw [div_le_div_iff_of_pos_right hq0]; exact hr1
  have hhi : ((n * p % q : ℤ) : ℝ) / q ≤ 1 - 1 / q := by
    rw [div_le_iff₀ hq0, sub_mul, one_div_mul_cancel hq0.ne']; linarith
  have habs := abs_lt.mp hclose
  have hfloor : ⌊(n : ℝ) * α⌋ = n * p / q := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith [heq, habs.1, habs.2]
  rw [Int.fract, hfloor, heq]

/-- **Proposition 5.x (`gap:prop:infinite-exponent`), congruence of the reference slope
(l.6726–6729).** If `gcd(p,q) = 1`, `m₀p ≡ r (mod q)` and `r = np mod q`, then
`m₀ ≡ n (mod q)`; hence `n = m₀ + jq` for an integer `j` (the ladder index is `j/s`), and for
`δ = α − p/q` the indicated cut has IDS `r/q + (m₀ + jq)δ = {nα}` (under the hypotheses of
`label_eq_fract`). -/
theorem slope_congr_and_ladder {α : ℝ} {p n m₀ : ℤ} {q : ℕ} (hpq : Int.gcd p q = 1)
    (hn : n ≠ 0) (hnq : |n| < q) (hclose : |(n : ℝ) * (α - p / q)| < 1 / q)
    (hm₀ : m₀ * p ≡ n * p % q [ZMOD q]) :
    m₀ ≡ n [ZMOD q] ∧ ∃ j : ℤ, n = m₀ + j * q ∧
      ((n * p % q : ℤ) : ℝ) / q + ((m₀ : ℝ) + j * q) * (α - p / q) = Int.fract (n * α) := by
  have hcong : m₀ * p ≡ n * p [ZMOD q] := hm₀.trans (Int.mod_modEq _ _)
  have hd : (q : ℤ) ∣ (n - m₀) * p := by
    have := (Int.ModEq.dvd hcong); rw [sub_mul]; exact this
  have hdn : (q : ℤ) ∣ n - m₀ := dvd_of_dvd_mul_coprime hpq hd
  obtain ⟨j, hj⟩ := hdn
  refine ⟨(Int.modEq_iff_dvd.mpr ⟨j, hj⟩), j, by linarith, ?_⟩
  have hn' : (n : ℝ) = m₀ + j * q := by
    have : n = m₀ + j * q := by linarith
    exact_mod_cast this
  rw [← hn']
  exact (label_eq_fract hpq hn hnq hclose).2

/-! ## D. Convergent supply when `β(α) = ∞` -/

/-- The continued-fraction denominators of `α` satisfy `q_n ≥ 1`. (Auxiliary.) -/
theorem one_le_cfDen (α : ℝ) (n : ℕ) : 1 ≤ AMO.cfDen α n := by
  have hmono : Monotone fun k => (GenContFract.of α).dens k :=
    monotone_nat_of_le_succ fun k => GenContFract.of_den_mono
  have := hmono (Nat.zero_le n)
  simp only [GenContFract.zeroth_den_eq_one] at this
  exact this

/-- **Proposition 5.x (`gap:prop:infinite-exponent`), supply of convergents (l.6716–6719).**
If `α` is irrational and `β(α) = ∞`, then for every `D` there are infinitely many convergents
`p_n/q_n` with `0 < |α − p_n/q_n| < e^{-D q_n}`: for every `D : ℝ` and `N : ℕ` there is `n ≥ N`
with this property. -/
theorem exists_convergent_of_beta_eq_top {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α = ⊤)
    (D : ℝ) (N : ℕ) :
    ∃ n ≥ N, 0 < |α - (GenContFract.of α).convs n| ∧
      |α - (GenContFract.of α).convs n| < Real.exp (-(D * AMO.cfDen α n)) := by
  have hfreq : ∃ᶠ j in atTop,
      ENNReal.ofReal (|D| + 1) < ENNReal.ofReal (Real.log (AMO.cfDen α (j + 1)) / AMO.cfDen α j) :=
    Filter.frequently_lt_of_lt_limsup (by isBoundedDefault)
      (by have h := hβ; unfold AMO.beta at h; rw [h]; exact ENNReal.ofReal_lt_top)
  obtain ⟨n, hn, hnN⟩ := (hfreq.and_eventually (eventually_ge_atTop N)).exists
  refine ⟨n, hnN, ?_, ?_⟩
  · -- the convergent is rational, `α` is not
    obtain ⟨c, hc⟩ := GenContFract.exists_rat_eq_nth_conv (K := ℝ) α n
    rw [abs_pos, sub_ne_zero, hc]
    exact hα.ne_rat c
  · have hnt : ¬(GenContFract.of α).TerminatedAt n := by
      intro h
      have : (GenContFract.of α).Terminates := ⟨n, h⟩
      obtain ⟨c, hc⟩ := (GenContFract.terminates_iff_rat α).mp this
      exact hα.ne_rat c hc
    have happ := GenContFract.abs_sub_convs_le hnt
    have hqn := one_le_cfDen α n
    have hqn1 := one_le_cfDen α (n + 1)
    have hlt := (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1
    -- `log q_{n+1} > (|D|+1) q_n ≥ D q_n`
    have hqpos : (0 : ℝ) < AMO.cfDen α n := by linarith
    have hlog : D * AMO.cfDen α n < Real.log (AMO.cfDen α (n + 1)) := by
      rw [lt_div_iff₀ hqpos] at hlt
      nlinarith [le_abs_self D]
    have hexp : Real.exp (D * AMO.cfDen α n) < AMO.cfDen α (n + 1) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < AMO.cfDen α (n + 1))]
      exact Real.exp_lt_exp.mpr hlog
    calc |α - (GenContFract.of α).convs n|
        ≤ 1 / ((GenContFract.of α).dens n * (GenContFract.of α).dens (n + 1)) := happ
      _ ≤ 1 / AMO.cfDen α (n + 1) := by
          unfold AMO.cfDen at hqn hqn1 ⊢
          apply one_div_le_one_div_of_le (by linarith)
          nlinarith
      _ < 1 / Real.exp (D * AMO.cfDen α n) :=
          one_div_lt_one_div_of_lt (Real.exp_pos _) hexp
      _ = Real.exp (-(D * AMO.cfDen α n)) := by rw [Real.exp_neg, one_div]

/-- **Proposition 5.x (`gap:prop:infinite-exponent`), level count (l.6669–6672).**
If the reference slope satisfies `|m| ≤ 2e^{bq}` with `b ≥ 0`, `q ≥ 1`, and `|n| < q`, then the
number `|n − m|/q` of cluster crossings needed to reach slope `n` satisfies
`|n − m|/q < e^{(b+3)q}`. -/
theorem level_count_bound {b : ℝ} (hb : 0 ≤ b) {q : ℕ} (hq : 1 ≤ q) {n m : ℤ}
    (hm : |(m : ℝ)| ≤ 2 * Real.exp (b * q)) (hn : |n| < q) :
    |((n : ℝ) - m)| / q < Real.exp ((b + 3) * q) := by
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hn' : |(n : ℝ)| < q := by exact_mod_cast hn
  have he1 : 1 ≤ Real.exp (b * q) := Real.one_le_exp (by positivity)
  have he3 : (3 : ℝ) < Real.exp 3 := by
    have := Real.add_one_lt_exp (by norm_num : (3 : ℝ) ≠ 0); linarith
  have he3q : Real.exp 3 ≤ Real.exp (3 * q) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp ((b + 3) * q) = Real.exp (b * q) * Real.exp (3 * q) := by
    rw [← Real.exp_add]; ring_nf
  rw [div_lt_iff₀ (by linarith), hsplit]
  calc |((n : ℝ) - m)| ≤ |(n : ℝ)| + |(m : ℝ)| := abs_sub _ _
    _ < q + 2 * Real.exp (b * q) := by linarith
    _ ≤ q * Real.exp (b * q) + 2 * q * Real.exp (b * q) := by nlinarith
    _ = 3 * Real.exp (b * q) * q := by ring
    _ < Real.exp 3 * Real.exp (b * q) * q := by
        have := mul_pos (by linarith : (0:ℝ) < Real.exp (b * q)) (by linarith : (0:ℝ) < q)
        nlinarith
    _ ≤ Real.exp (b * q) * Real.exp (3 * q) * q := by
        have := mul_pos (by linarith : (0:ℝ) < Real.exp (b * q)) (by linarith : (0:ℝ) < q)
        nlinarith

/-! ## E. The transfer contradiction (Proposition `gap:prop:transfer`) -/

/-- **Proposition 3.x (`gap:prop:transfer`), contradiction step (l.3295–3310).**
Abstract form of the case `u = v = E₀` in the proof. Data: the transferred spectral set `Σ`
(spectrum of `H_R`), its IDS `N` (`= N_R`), continuous `b, g`, the comparison IDS family
`Nb b' = N_{b'}` (each monotone) with spectra `spec b' = spec H_{b'}`, and the transfer
identities `g(E) ∈ spec H_{b(E)}`, `N_R(E) = N_{b(E)}(g(E))` on `Σ`
(eq. `gap:eq:spectral-ids-transfer`). The comparison input (Theorem `gap:thm:comparison` plus
the uniform Neumann bound): numbers `c < d` and a neighbourhood `U` of `b(E₀)` such that for
`b' ∈ U`, `[c,d]` lies in the resolvent of `H_{b'}` and `N_{b'} = ℓ` on `[c,d]`. Finally,
spectral points `E_j^± → E₀` with `N_R(E_j^-) < ℓ < N_R(E_j^+)`. These are incompatible.

Only continuity of `b, g` at `E₀` and monotonicity of each `N_{b'}` are used; as in the paper,
no monotonicity of `g` is needed. -/
theorem transfer_contradiction (Sig : Set ℝ) (N b g : ℝ → ℝ) (Nb : ℝ → ℝ → ℝ)
    (spec : ℝ → Set ℝ) (E₀ ℓ c d : ℝ) (U : Set ℝ)
    (hb : ContinuousAt b E₀) (hg : ContinuousAt g E₀)
    (hmono : ∀ b', Monotone (Nb b'))
    (htrans : ∀ E ∈ Sig, g E ∈ spec (b E) ∧ N E = Nb (b E) (g E))
    (hcd : c < d) (hU : U ∈ 𝓝 (b E₀))
    (hgap : ∀ b' ∈ U, ∀ t ∈ Icc c d, t ∉ spec b' ∧ Nb b' t = ℓ)
    (Em Ep : ℕ → ℝ) (hEmS : ∀ j, Em j ∈ Sig) (hEpS : ∀ j, Ep j ∈ Sig)
    (hEm : Tendsto Em atTop (𝓝 E₀)) (hEp : Tendsto Ep atTop (𝓝 E₀))
    (hNm : ∀ j, N (Em j) < ℓ) (hNp : ∀ j, ℓ < N (Ep j)) : False := by
  -- for large `j`, `b(E_j^±) ∈ U`, hence `g(E_j^-) < c` and `g(E_j^+) > d`
  have hbU : ∀ {E : ℕ → ℝ}, Tendsto E atTop (𝓝 E₀) → ∀ᶠ j in atTop, b (E j) ∈ U :=
    fun hE => (hb.tendsto.comp hE) hU
  have hlow : ∀ᶠ j in atTop, g (Em j) < c := by
    filter_upwards [hbU hEm] with j hj
    by_contra hc
    push_neg at hc
    obtain ⟨hspec, hN⟩ := htrans _ (hEmS j)
    by_cases hd : g (Em j) ≤ d
    · exact (hgap _ hj _ ⟨hc, hd⟩).1 hspec
    · push_neg at hd
      have := hmono (b (Em j)) hd.le
      rw [(hgap _ hj d ⟨hcd.le, le_rfl⟩).2] at this
      have := hNm j; linarith
  have hhigh : ∀ᶠ j in atTop, d < g (Ep j) := by
    filter_upwards [hbU hEp] with j hj
    by_contra hd
    push_neg at hd
    obtain ⟨hspec, hN⟩ := htrans _ (hEpS j)
    by_cases hc : c ≤ g (Ep j)
    · exact (hgap _ hj _ ⟨hc, hd⟩).1 hspec
    · push_neg at hc
      have := hmono (b (Ep j)) hc.le
      rw [(hgap _ hj c ⟨le_rfl, hcd.le⟩).2] at this
      have := hNp j; linarith
  -- continuity of `g` gives `g(E₀) ≤ c < d ≤ g(E₀)`
  have h1 : g E₀ ≤ c :=
    le_of_tendsto (hg.tendsto.comp hEm) (hlow.mono fun _ h => h.le)
  have h2 : d ≤ g E₀ :=
    ge_of_tendsto (hg.tendsto.comp hEp) (hhigh.mono fun _ h => h.le)
  linarith

/-! ## F. Energy reversal permutes the labels -/

/-- The label set `Λ_α = {{nα} : n ∈ ℤ, n ≠ 0}` of gap labels. -/
def labelSet (α : ℝ) : Set ℝ := {x | ∃ n : ℤ, n ≠ 0 ∧ Int.fract (n * α) = x}

/-- **Proof of Theorem 3.x (`gap:thm:comparison`), energy reversal (l.3232–3238).**
For irrational `α`, the label map `r ↦ 1 − r` permutes `Λ_α`: `1 − {nα} = {(−n)α}`. -/
theorem one_sub_mem_labelSet_iff {α : ℝ} (hα : Irrational α) (x : ℝ) :
    1 - x ∈ labelSet α ↔ x ∈ labelSet α := by
  have key : ∀ n : ℤ, n ≠ 0 → Int.fract (((-n : ℤ) : ℝ) * α) = 1 - Int.fract (n * α) := by
    intro n hn
    have hirr : Irrational ((n : ℝ) * α) := hα.intCast_mul hn
    have hne : Int.fract ((n : ℝ) * α) ≠ 0 := by
      intro h
      rw [Int.fract, sub_eq_zero] at h
      exact hirr.ne_int _ h
    rw [Int.cast_neg, neg_mul]
    exact Int.fract_neg hne
  constructor
  · rintro ⟨n, hn, hx⟩
    refine ⟨-n, neg_ne_zero.mpr hn, ?_⟩
    rw [key n hn, hx]; ring
  · rintro ⟨n, hn, rfl⟩
    exact ⟨-n, neg_ne_zero.mpr hn, key n hn⟩

/-- **Energy reversal (`gap:thm:comparison`, l.3232–3238), set form.** For irrational `α`,
`(r ↦ 1 − r)(Λ_α) = Λ_α`. -/
theorem image_one_sub_labelSet {α : ℝ} (hα : Irrational α) :
    (fun r => 1 - r) '' labelSet α = labelSet α := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (one_sub_mem_labelSet_iff hα y).mpr hy
  · intro hx
    refine ⟨1 - x, (one_sub_mem_labelSet_iff hα x).mpr (by simpa using hx), by ring⟩

end LabelArithmetic

end SGD
