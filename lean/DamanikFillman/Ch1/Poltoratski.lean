/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.10 (pp. 93–103): Poltoratski's theorem.

# Main definitions

* `DF.borelTransformDensity μ f z = ∫ f(x) / (x - z) dμ(x)` — the Borel transform `F_{fμ}` of the
  (signed) measure `fμ` (1.10.1).

# Main results

* `DF.besicovitch_covering_real` — Theorem 1.10.2 (Besicovitch covering theorem in `ℝ`), derived
  from Mathlib's general Besicovitch theorem (the constant `N` is not made explicit);
* `DF.tendsto_poisson_ratio` — a comparison principle: if `ν(B(E,r))/μ(B(E,r)) → L` and
  `D^-_μ(E) > 0`, then `Im F_ν(E + iε) / Im F_μ(E + iε) → L`;
* `DF.ae_tendsto_im_ratio` — Lemma 1.10.3, (1.10.12): `Im F_{fμ} / Im F_μ → f` `μ`-a.e.;
* `DF.ae_singularPart_tendsto_im_ratio_zero` — Lemma 1.10.3, (1.10.13);
* `DF.tendsto_eps_mul_borelTransformDensity`, `DF.tendsto_ratio_of_atom` — Exercise 1.10.4:
  `ε F_{fμ}(E + iε) → i f(E) μ({E})` and `F_{fμ}/F_μ → f(E)` at every atom `E`;
* `DF.poltoratski_of_pure_point` — Theorem 1.10.1 when `μ_s` is pure point (proved);
* `DF.poltoratski_of_lipschitz` — Theorem 1.10.1 for Lipschitz `f` (proved);
* `DF.poltoratski_corollary` — Theorem 1.10.4, derived from Theorem 1.10.1.

# Statements

* `DF.PoltoratskiStatement` — Theorem 1.10.1 (Poltoratski's theorem) in general.  It is proved
  in `DamanikFillman.Ch1.PoltoratskiProof` (`DF.poltoratskiStatement_holds`), following the
  Jakšić–Last argument with the rank-one perturbation replaced by explicit Herglotz functions.

# Deviation in the proof of Lemma 1.10.3

Instead of the maximal-function / covering argument of the book, we use Mathlib's
differentiation theorem for arbitrary locally finite measures (itself based on the Besicovitch
covering theorem), `Besicovitch.ae_tendsto_rnDeriv`, together with a layer-cake comparison of
Poisson integrals (`DF.lintegral_poisson_ball_le`).
-/
import DamanikFillman.Ch1.BorelBoundary

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-! ## Theorem 1.10.2: the Besicovitch covering theorem on the line -/

/-- Theorem 1.10.2 (Besicovitch covering theorem in `ℝ`): there is a universal `N` such that every
family of nondegenerate closed intervals `[c_i - r_i, c_i + r_i]` with bounded radii admits `N`
subfamilies, each consisting of pairwise disjoint intervals (hence countable), which together
cover all the centres. -/
theorem besicovitch_covering_real : ∃ N : ℕ, ∀ (ι : Type) (c r : ι → ℝ), (∀ i, 0 < r i) →
    BddAbove (range r) →
    ∃ s : Fin N → Set ι, (∀ k, (s k).PairwiseDisjoint fun i => closedBall (c i) (r i)) ∧
      (∀ k, (s k).Countable) ∧ range c ⊆ ⋃ k, ⋃ i ∈ s k, closedBall (c i) (r i) := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, fun ι c r hr hbdd => ?_⟩
  obtain ⟨R, hR⟩ := hbdd
  let q : Besicovitch.BallPackage ι ℝ :=
    { c := c, r := r, rpos := hr, r_bound := R, r_le := fun i => hR (mem_range_self i) }
  obtain ⟨s, hdisj, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  refine ⟨s, hdisj, fun k => ?_, ?_⟩
  · refine (hdisj k).countable_of_nonempty_interior fun i _ => ?_
    refine ⟨c i, ?_⟩
    rw [Real.closedBall_eq_Icc, interior_Icc]
    have := hr i
    constructor <;> linarith
  · refine hcov.trans ?_
    gcongr
    exact ball_subset_closedBall

/-! ## Borel transforms of densities -/

/-- The Borel transform `F_{fμ}(z) = ∫ f(x) / (x - z) dμ(x)` of the signed measure `fμ`
(cf. (1.10.1)). -/
def borelTransformDensity (μ : Measure ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x, (f x : ℂ) * ((x : ℂ) - z)⁻¹ ∂μ

lemma integrable_density_inv_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x => (f x : ℂ) * ((x : ℂ) - z)⁻¹) μ := by
  refine (hf.ofReal (𝕜 := ℂ)).mul_of_top_left ?_
  exact memLp_top_of_bound (continuous_inv_sub hz).aestronglyMeasurable (1 / |z.im|)
    (Eventually.of_forall fun x => norm_inv_sub_le x hz)

/-- `Im F_{fμ}(E + iε) = π ∫ f(x) P_ε(x - E) dμ(x)` (cf. (1.10.14)). -/
lemma borelTransformDensity_im (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (borelTransformDensity μ f (E + ε * I)).im =
      Real.pi * ∫ x, f x * poissonKernel ε (x - E) ∂μ := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε.ne'
  unfold borelTransformDensity
  have h := integral_im (integrable_density_inv_sub μ hf hz)
  simp only [RCLike.im_to_complex] at h
  rw [← h, ← integral_const_mul]
  congr 1; ext x
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, inv_sub_im,
    poissonKernel]
  field_simp

lemma borelTransformDensity_one (μ : Measure ℝ) (z : ℂ) :
    borelTransformDensity μ (fun _ => 1) z = borelTransform μ z := by
  simp [borelTransformDensity, borelTransform]

lemma borelTransformDensity_congr_ae (μ : Measure ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[μ] g) (z : ℂ) :
    borelTransformDensity μ f z = borelTransformDensity μ g z := by
  unfold borelTransformDensity
  exact integral_congr_ae (h.mono fun x hx => by simp [hx])

/-! ## Comparison of Poisson integrals: ratios -/

/-- An open ball is the increasing union of closed balls. -/
lemma ball_eq_iUnion_closedBall (E : ℝ) {r : ℝ} (hr : 0 < r) :
    ball E r = ⋃ n : ℕ, closedBall E (r * ((n + 1) / (n + 2))) := by
  ext x
  simp only [mem_ball, mem_iUnion, mem_closedBall]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist x E))
    refine ⟨n, ?_⟩
    have hd : 0 < r - dist x E := by linarith
    have h1 : r / (r - dist x E) < n + 2 := by linarith
    rw [div_lt_iff₀ hd] at h1
    have : r * ((n + 1) / (n + 2)) = r - r / (n + 2) := by field_simp; ring
    rw [this]
    have : r / (n + 2) ≤ r - dist x E := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · rintro ⟨n, hn⟩
    refine lt_of_le_of_lt hn ?_
    have : ((n : ℝ) + 1) / (n + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith

lemma monotone_closedBall_radii (E r : ℝ) (hr : 0 ≤ r) :
    Monotone fun n : ℕ => closedBall E (r * ((n + 1) / (n + 2))) := by
  intro m n hmn
  apply closedBall_subset_closedBall
  apply mul_le_mul_of_nonneg_left _ hr
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Closed-ball comparison implies open-ball comparison. -/
lemma ball_le_of_closedBall_le {μ ν : Measure ℝ} {E u : ℝ} {a : ℝ≥0∞}
    (h : ∀ r, 0 < r → r < u → ν (closedBall E r) ≤ a * μ (closedBall E r)) :
    ∀ r, 0 < r → r < u → ν (ball E r) ≤ a * μ (ball E r) := by
  intro r hr hru
  rw [ball_eq_iUnion_closedBall E hr, (monotone_closedBall_radii E r hr.le).measure_iUnion,
    (monotone_closedBall_radii E r hr.le).measure_iUnion, ENNReal.mul_iSup]
  refine iSup_mono fun n => h _ ?_ ?_
  · positivity
  · have : ((n : ℝ) + 1) / (n + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith

lemma poissonInt_ne_top (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poissonInt μ E ε ≠ ∞ := by
  rw [poissonInt_eq μ E hε]; exact ENNReal.ofReal_ne_top

/-- The basic estimate behind the ratio comparison: if `ν ≤ a μ` on small closed balls around `E`,
then `π⁻¹ Im F_ν ≤ a π⁻¹ Im F_μ + O(ε)`. -/
lemma poisson_toReal_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {E u a : ℝ}
    (hu : 0 < u) (ha : 0 ≤ a)
    (h : ∀ r, 0 < r → r < u → ν (closedBall E r) ≤ ENNReal.ofReal a * μ (closedBall E r)) :
    ∃ r₀ > 0, ∀ ε, 0 < ε → (poissonInt ν E ε).toReal ≤
      a * (poissonInt μ E ε).toReal + ε / (Real.pi * r₀ ^ 2) * ν.real univ := by
  refine ⟨u / 2, by positivity, fun ε hε => ?_⟩
  have hball : ∀ r, 0 < r → r ≤ u / 2 → ν (ball E r) ≤ ENNReal.ofReal a * μ (ball E r) :=
    fun r hr hrr => ball_le_of_closedBall_le h r hr (by linarith)
  have hle : poissonInt ν E ε ≤ ENNReal.ofReal a * poissonInt μ E ε +
      ENNReal.ofReal (ε / (Real.pi * (u / 2) ^ 2)) * ν univ := by
    rw [poissonInt, ← lintegral_add_compl _ (measurableSet_ball (x := E) (ε := u / 2))]
    gcongr
    · calc ∫⁻ x in ball E (u / 2), ENNReal.ofReal (poissonKernel ε (x - E)) ∂ν
          ≤ ENNReal.ofReal a * ∫⁻ x in ball E (u / 2),
              ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ :=
            lintegral_poisson_ball_le hε ENNReal.ofReal_ne_top hball
        _ ≤ ENNReal.ofReal a * poissonInt μ E ε := by
            gcongr; exact setLIntegral_le_lintegral _ _
    · exact lintegral_poisson_compl_le ν hε (by positivity)
  have hfin : ENNReal.ofReal a * poissonInt μ E ε +
      ENNReal.ofReal (ε / (Real.pi * (u / 2) ^ 2)) * ν univ ≠ ∞ := by
    apply ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (poissonInt_ne_top μ E hε), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (poissonInt_ne_top μ E hε))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

/-- If `D^-_μ(E) > 0`, the Poisson integral of `μ` at `E` stays bounded away from `0`. -/
lemma exists_poisson_lower_bound {μ : Measure ℝ} [IsFiniteMeasure μ] {E : ℝ}
    (hpos : 0 < lowerDeriv μ E) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ (poissonInt μ E ε).toReal := by
  obtain ⟨c', hc'0, hc'lt⟩ := exists_between (hpos.trans_le (lowerDeriv_le_liminf_poisson μ E))
  set c'' := min c' 1
  have hc''lt : c'' < liminf (poissonInt μ E) (𝓝[>] 0) := lt_of_le_of_lt (min_le_left _ _) hc'lt
  have hc''0 : 0 < c'' := lt_min hc'0 one_pos
  have hc''top : c'' ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨c''.toReal, ENNReal.toReal_pos hc''0.ne' hc''top, ?_⟩
  filter_upwards [eventually_lt_of_lt_liminf hc''lt, self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
  exact ENNReal.toReal_mono (poissonInt_ne_top μ E hε0) hε.le

lemma tendsto_eps_div_const (C c : ℝ) :
    Tendsto (fun ε : ℝ => ε * C / c) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => ε * C / c) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Comparison principle for ratios of Poisson integrals: if
`ν(B̄(E, r)) / μ(B̄(E, r)) → L` as `r ↓ 0` and `D^-_μ(E) > 0`, then
`Im F_ν(E + iε) / Im F_μ(E + iε) → L` (stated for the normalized Poisson integrals). -/
theorem tendsto_poisson_ratio {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E L : ℝ} (hL : 0 ≤ L)
    (hlim : Tendsto (fun r => ν (closedBall E r) / μ (closedBall E r)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal L)))
    (hpos : 0 < lowerDeriv μ E) :
    Tendsto (fun ε => (poissonInt ν E ε).toReal / (poissonInt μ E ε).toReal) (𝓝[>] 0)
      (𝓝 L) := by
  obtain ⟨c, hc, hcev⟩ := exists_poisson_lower_bound hpos
  rw [tendsto_order]
  constructor
  · intro b hb
    rcases lt_or_ge b 0 with hb0 | hb0
    · filter_upwards [hcev, self_mem_nhdsWithin] with ε hε hε0
      exact lt_of_lt_of_le hb0 (div_nonneg ENNReal.toReal_nonneg (hc.le.trans hε))
    obtain ⟨b', hbb', hb'L⟩ := exists_between hb
    have hb'pos : 0 < b' := lt_of_le_of_lt hb0 hbb'
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal b' < ν (closedBall E r) / μ (closedBall E r) :=
      hlim.eventually (lt_mem_nhds ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hb'L))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    have hu0 : (0 : ℝ) < u := hu
    have hcmp : ∀ r, 0 < r → r < u →
        μ (closedBall E r) ≤ ENNReal.ofReal (1 / b') * ν (closedBall E r) := by
      intro r hr hru
      have h1 := (hsub ⟨hr, hru⟩ : ENNReal.ofReal b' < _)
      have h2 : ENNReal.ofReal b' * μ (closedBall E r) ≤ ν (closedBall E r) := by
        rcases eq_or_ne (μ (closedBall E r)) 0 with h0 | h0
        · rw [h0, mul_zero]; exact bot_le
        · exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top _ _))).1 h1.le
      calc μ (closedBall E r) = ENNReal.ofReal (1 / b') * (ENNReal.ofReal b' * μ (closedBall E r)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hb'pos.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    obtain ⟨r₀, hr₀, hest⟩ := poisson_toReal_le hu0 (by positivity) hcmp
    have hsmall := tendsto_eps_div_const (b' * (μ.real univ / (Real.pi * r₀ ^ 2))) c
    have hev2 := hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < b' - b by linarith))
    filter_upwards [hcev, hev2, self_mem_nhdsWithin] with ε hε hε2 hε0
    have hε0' : (0 : ℝ) < ε := hε0
    have hpμ : 0 < (poissonInt μ E ε).toReal := hc.trans_le hε
    have h1 := hest ε hε0'
    rw [lt_div_iff₀ hpμ]
    have h3 : ε * (b' * (μ.real univ / (Real.pi * r₀ ^ 2))) / (poissonInt μ E ε).toReal ≤
        ε * (b' * (μ.real univ / (Real.pi * r₀ ^ 2))) / c := by
      apply div_le_div_of_nonneg_left _ hc hε
      have := measureReal_nonneg (μ := μ) (s := univ)
      positivity
    have h4 : ε * (b' * (μ.real univ / (Real.pi * r₀ ^ 2))) / (poissonInt μ E ε).toReal <
        b' - b := lt_of_le_of_lt h3 hε2
    rw [div_lt_iff₀ hpμ] at h4
    have h5 : ε / (Real.pi * r₀ ^ 2) * μ.real univ =
        ε * (μ.real univ / (Real.pi * r₀ ^ 2)) := by ring
    rw [h5] at h1
    have h6 : b' * (poissonInt μ E ε).toReal ≤ (poissonInt ν E ε).toReal +
        b' * (ε * (μ.real univ / (Real.pi * r₀ ^ 2))) := by
      have := mul_le_mul_of_nonneg_left h1 hb'pos.le
      rw [mul_add, ← mul_assoc, mul_one_div_cancel hb'pos.ne', one_mul] at this
      linarith
    nlinarith
  · intro a ha
    obtain ⟨a', hLa', ha'a⟩ := exists_between ha
    have ha'pos : 0 ≤ a' := hL.trans hLa'.le
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (closedBall E r) / μ (closedBall E r) < ENNReal.ofReal a' :=
      hlim.eventually (gt_mem_nhds ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hLa'))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    have hu0 : (0 : ℝ) < u := hu
    have hcmp : ∀ r, 0 < r → r < u →
        ν (closedBall E r) ≤ ENNReal.ofReal a' * μ (closedBall E r) := by
      intro r hr hru
      have h1 := (hsub ⟨hr, hru⟩ : _ < ENNReal.ofReal a')
      exact (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
        (Or.inl (measure_ne_top _ _))).1 h1.le
    obtain ⟨r₀, hr₀, hest⟩ := poisson_toReal_le hu0 ha'pos hcmp
    have hsmall := tendsto_eps_div_const (ν.real univ / (Real.pi * r₀ ^ 2)) c
    have hev2 := hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < a - a' by linarith))
    filter_upwards [hcev, hev2, self_mem_nhdsWithin] with ε hε hε2 hε0
    have hε0' : (0 : ℝ) < ε := hε0
    have hpμ : 0 < (poissonInt μ E ε).toReal := hc.trans_le hε
    have h1 := hest ε hε0'
    rw [div_lt_iff₀ hpμ]
    have h3 : ε * (ν.real univ / (Real.pi * r₀ ^ 2)) / (poissonInt μ E ε).toReal ≤
        ε * (ν.real univ / (Real.pi * r₀ ^ 2)) / c := by
      apply div_le_div_of_nonneg_left _ hc hε
      have := measureReal_nonneg (μ := ν) (s := univ)
      positivity
    have h4 : ε * (ν.real univ / (Real.pi * r₀ ^ 2)) / (poissonInt μ E ε).toReal < a - a' :=
      lt_of_le_of_lt h3 hε2
    rw [div_lt_iff₀ hpμ] at h4
    have h5 : ε / (Real.pi * r₀ ^ 2) * ν.real univ =
        ε * (ν.real univ / (Real.pi * r₀ ^ 2)) := by ring
    rw [h5] at h1
    nlinarith

/-! ## `μ`-a.e. positivity of the lower derivative -/

/-- For `μ`-a.e. `E`, the derivative `D_μ(E)` exists and is positive (possibly infinite). -/
theorem ae_lowerDeriv_pos (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ (E : ℝ) ∂μ, 0 < lowerDeriv μ E := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume μ, Measure.rnDeriv_lt_top volume μ]
    with E hE hlt
  have hinv := tendsto_inv_iff.2 hE
  have h2 : Tendsto (fun r => μ (closedBall E r) / ENNReal.ofReal (2 * r)) (𝓝[>] 0)
      (𝓝 (volume.rnDeriv μ E)⁻¹) := by
    refine hinv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [volume_closedBall_ofReal]
    rw [ENNReal.inv_div (Or.inr ENNReal.ofReal_ne_top)
      (Or.inr (by simpa using (by linarith : (0 : ℝ) < 2 * r)))]
  rw [(hasMeasDeriv_of_closedBall h2).lowerDeriv_eq]
  exact ENNReal.inv_pos.2 hlt.ne

/-! ## Lemma 1.10.3 -/

/-- For a nonnegative integrable `g`, the normalized Poisson integral of `gμ`. -/
lemma poissonInt_withDensity (μ : Measure ℝ) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g μ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (poissonInt (μ.withDensity fun x => ENNReal.ofReal (g x)) E ε).toReal =
      ∫ x, g x * poissonKernel ε (x - E) ∂μ := by
  have hint : Integrable (fun x => g x * poissonKernel ε (x - E)) μ := by
    refine hgi.mul_of_top_left ?_
    exact memLp_top_of_bound ((continuous_poissonKernel hε).comp
      (continuous_sub_right E)).aestronglyMeasurable (1 / (Real.pi * ε))
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (poissonKernel_nonneg hε.le _)]; exact poissonKernel_le hε _)
  have hm2 : Measurable fun x => ENNReal.ofReal (poissonKernel ε (x - E)) :=
    ((measurable_poissonKernel ε).comp (measurable_id.sub_const E)).ennreal_ofReal
  rw [poissonInt, lintegral_withDensity_eq_lintegral_mul _ hgm.ennreal_ofReal hm2]
  have hpt : ∀ x, ((fun x => ENNReal.ofReal (g x)) *
      fun x => ENNReal.ofReal (poissonKernel ε (x - E))) x =
      ENNReal.ofReal (g x * poissonKernel ε (x - E)) := fun x => by
    simp only [Pi.mul_apply]; rw [ENNReal.ofReal_mul (hg0 x)]
  rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => mul_nonneg (hg0 x) (poissonKernel_nonneg hε.le _)),
    ENNReal.toReal_ofReal (integral_nonneg fun x =>
      mul_nonneg (hg0 x) (poissonKernel_nonneg hε.le _))]

/-- Lemma 1.10.3 for nonnegative measurable densities. -/
lemma ae_tendsto_poisson_ratio_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g μ) :
    ∀ᵐ (E : ℝ) ∂μ, Tendsto (fun ε => (∫ x, g x * poissonKernel ε (x - E) ∂μ) /
      (poissonInt μ E ε).toReal) (𝓝[>] 0) (𝓝 (g E)) := by
  set ν := μ.withDensity fun x => ENNReal.ofReal (g x)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hgi.2
  have hrn : ν.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (g x) :=
    Measure.rnDeriv_withDensity μ (by fun_prop)
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν μ, hrn, ae_lowerDeriv_pos μ] with E hE hrnE hpos
  rw [hrnE] at hE
  refine (tendsto_poisson_ratio (hg0 E) hE hpos).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [poissonInt_withDensity μ hgm hg0 hgi E hε]

lemma borelTransform_im_eq_poissonInt (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (borelTransform μ (E + ε * I)).im = Real.pi * (poissonInt μ E ε).toReal := by
  rw [poissonInt_eq μ E hε, ENNReal.toReal_ofReal
    (div_nonneg (borelTransform_im_nonneg μ E hε) Real.pi_pos.le)]
  field_simp

lemma integrable_mul_poisson (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Integrable (fun x => g x * poissonKernel ε (x - E)) μ :=
  hg.mul_of_top_left (memLp_top_of_bound ((continuous_poissonKernel hε).comp
    (continuous_sub_right E)).aestronglyMeasurable (1 / (Real.pi * ε))
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (poissonKernel_nonneg hε.le _)]; exact poissonKernel_le hε _))

/-- Lemma 1.10.3, (1.10.12): for real `f ∈ L¹(μ)`,
`Im F_{fμ}(E + iε) / Im F_μ(E + iε) → f(E)` for `μ`-a.e. `E`. -/
theorem ae_tendsto_im_ratio (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) :
    ∀ᵐ (E : ℝ) ∂μ, Tendsto (fun ε : ℝ => (borelTransformDensity μ f (E + ε * I)).im /
      (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 (f E)) := by
  -- reduce to a measurable representative
  set f' := hf.1.mk f
  have hf'm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[μ] f' := hf.1.ae_eq_mk
  have hf'i : Integrable f' μ := hf.congr hff'
  set fp : ℝ → ℝ := fun x => max (f' x) 0
  set fn : ℝ → ℝ := fun x => max (-f' x) 0
  have hfpm : Measurable fp := hf'm.max measurable_const
  have hfnm : Measurable fn := hf'm.neg.max measurable_const
  have hfpi : Integrable fp μ := hf'i.pos_part
  have hfni : Integrable fn μ := hf'i.neg_part
  filter_upwards [ae_tendsto_poisson_ratio_nonneg μ hfpm (fun x => le_max_right _ _) hfpi,
    ae_tendsto_poisson_ratio_nonneg μ hfnm (fun x => le_max_right _ _) hfni, hff'] with E hp hn hE
  have hlim := hp.sub hn
  have hfE : fp E - fn E = f E := by
    simp only [fp, fn, hE]
    rcases le_total 0 (f' E) with h | h
    · simp [h]
    · simp [h]
  rw [hfE] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [borelTransformDensity_congr_ae μ hff', borelTransformDensity_im μ hf'i E hε,
    borelTransform_im_eq_poissonInt μ E hε, mul_div_mul_left _ _ Real.pi_ne_zero, ← sub_div,
    ← integral_sub (integrable_mul_poisson μ hfpi hε E) (integrable_mul_poisson μ hfni hε E)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [fp, fn]
  rcases le_total 0 (f' x) with h | h
  · simp [h]
  · simp [h]

/-- Lemma 1.10.3, (1.10.13): for any finite measure `ν`,
`Im F_ν(E + iε) / Im F_μ(E + iε) → 0` for a.e. `E` with respect to the part of `μ` singular with
respect to `ν`. -/
theorem ae_singularPart_tendsto_im_ratio_zero (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    ∀ᵐ (E : ℝ) ∂(μ.singularPart ν), Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im /
      (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 0) := by
  have hac : μ.singularPart ν ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le μ ν)
  -- `ν.rnDeriv μ = 0` a.e. for the part of `μ` singular to `ν`
  obtain ⟨s, hsm, hs0, hsc⟩ := Measure.mutuallySingular_singularPart μ ν
  have hzero : ∀ᵐ (E : ℝ) ∂(μ.singularPart ν), ν.rnDeriv μ E = 0 := by
    have h1 : ∫⁻ x in sᶜ, ν.rnDeriv μ x ∂μ = 0 := by
      rw [← withDensity_apply _ hsm.compl]
      exact le_antisymm ((Measure.withDensity_rnDeriv_le ν μ _).trans hsc.le) bot_le
    rw [lintegral_eq_zero_iff (Measure.measurable_rnDeriv ν μ)] at h1
    have h2 := hac.ae_le (ae_restrict_iff' hsm.compl |>.1 h1)
    have h3 : ∀ᵐ (E : ℝ) ∂(μ.singularPart ν), E ∈ sᶜ := by
      rw [ae_iff]; simpa using hs0
    filter_upwards [h2, h3] with E hE hEs using hE hEs
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν μ), hzero,
    hac.ae_le (ae_lowerDeriv_pos μ)] with E hE hE0 hpos
  rw [hE0, ← ENNReal.ofReal_zero] at hE
  refine (tendsto_poisson_ratio le_rfl hE hpos).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [borelTransform_im_eq_poissonInt μ E hε, borelTransform_im_eq_poissonInt ν E hε,
    mul_div_mul_left _ _ Real.pi_ne_zero]

/-! ## Exercise 1.10.4: atoms -/

/-- Exercise 1.10.4(a) for densities: `ε F_{fμ}(E + iε) → i f(E) μ({E})`. -/
theorem tendsto_eps_mul_borelTransformDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (E : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * borelTransformDensity μ f (E + ε * I)) (𝓝[>] 0)
      (𝓝 (I * (f E : ℂ) * (μ.real {E} : ℂ))) := by
  have hrw : ∀ ε : ℝ, (ε : ℂ) * borelTransformDensity μ f (E + ε * I) =
      ∫ x, (f x : ℂ) * ((ε : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹) ∂μ := fun ε => by
    unfold borelTransformDensity; rw [← integral_const_mul]; congr 1; ext x; ring
  simp_rw [hrw]
  have hlim : ∫ x, ({E} : Set ℝ).indicator (fun x => (f x : ℂ) * I) x ∂μ =
      I * (f E : ℂ) * (μ.real {E} : ℂ) := by
    rw [integral_indicator (measurableSet_singleton E)]
    simp [Measure.real]; ring
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using (ne_of_gt hε)
    exact ((hf.ofReal (𝕜 := ℂ)).1.mul
      ((continuous_inv_sub hz).const_smul (ε : ℂ)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun x => ?_
    have hε' : (0 : ℝ) < ε := hε
    have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε'.ne'
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hε'.le]
    have : ε * ‖((x : ℂ) - (E + ε * I))⁻¹‖ ≤ 1 := by
      calc ε * ‖((x : ℂ) - (E + ε * I))⁻¹‖ ≤ ε * (1 / |(E + ε * I : ℂ).im|) :=
            mul_le_mul_of_nonneg_left (norm_inv_sub_le x hz) hε'.le
        _ = 1 := by simp [abs_of_pos hε', hε'.ne']
    calc ‖f x‖ * (ε * ‖((x : ℂ) - (E + ε * I))⁻¹‖) ≤ ‖f x‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x = E
    · subst hx
      simp only [indicator_of_mem (mem_singleton x)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
      field_simp
      ring_nf
      simp [I_sq]
    · rw [indicator_of_notMem (by simpa using hx)]
      have hc : ContinuousAt (fun ε : ℝ => (f x : ℂ) * ((ε : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹))
          0 := by
        have h0 : ((x : ℂ) - (E + ((0 : ℝ) : ℂ) * I)) ≠ 0 := by
          simpa [sub_eq_zero] using (Complex.ofReal_injective.ne hx)
        exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.mul (by fun_prop) (ContinuousAt.inv₀ (by fun_prop) h0))
      have := hc.tendsto
      simp only [Complex.ofReal_zero, zero_mul, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds

/-- Exercise 1.10.4(b): at every atom `E` of `μ`, `F_{fμ}(E + iε) / F_μ(E + iε) → f(E)`. -/
theorem tendsto_ratio_of_atom (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) {E : ℝ} (hE : μ {E} ≠ 0) :
    Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
      (𝓝[>] 0) (𝓝 (f E : ℂ)) := by
  have hE' : (μ.real {E} : ℂ) ≠ 0 := by
    have : μ.real {E} ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]; exact ⟨hE, measure_ne_top _ _⟩
    exact_mod_cast this
  have h1 := tendsto_eps_mul_borelTransformDensity μ hf E
  have h2 := tendsto_eps_mul_borelTransform μ E
  have h3 := h1.div h2 (mul_ne_zero I_ne_zero hE')
  have hval : I * (f E : ℂ) * (μ.real {E} : ℂ) / (I * (μ.real {E} : ℂ)) = f E := by
    field_simp
  rw [hval] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ this]

/-! ## Theorem 1.10.1 for Lipschitz densities -/

/-- Theorem 1.10.1 for Lipschitz `f`: here the elementary estimate
`|F_{fμ}(z) - f(E) F_μ(z)| ≤ L μ(ℝ)` combined with `Im F_μ(E + iε) → ∞` (`μ_s`-a.e., (1.9.24))
suffices.  (The content of Poltoratski's theorem is the extension to all of `L¹(μ)`.) -/
theorem poltoratski_of_lipschitz (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hfi : Integrable f μ) :
    ∀ᵐ (E : ℝ) ∂(μ.singularPart volume),
      Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
        (𝓝[>] 0) (𝓝 (f E : ℂ)) := by
  have h := singularPart_not_tendsto_atTop μ
  have h' : ∀ᵐ (E : ℝ) ∂(μ.singularPart volume),
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop := by
    rw [ae_iff]; exact h
  filter_upwards [h'] with E hE
  set C : ℝ := L * μ.real univ
  -- the key estimate
  have hdiff : ∀ ε : ℝ, 0 < ε →
      ‖borelTransformDensity μ f (E + ε * I) - f E * borelTransform μ (E + ε * I)‖ ≤ C := by
    intro ε hε
    have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε.ne'
    have heq : borelTransformDensity μ f (E + ε * I) - f E * borelTransform μ (E + ε * I) =
        ∫ x, ((f x - f E : ℝ) : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹ ∂μ := by
      unfold borelTransformDensity borelTransform
      rw [← integral_const_mul, ← integral_sub (integrable_density_inv_sub μ hfi hz)
        ((integrable_inv_sub μ hz).const_mul _)]
      congr 1; ext x; push_cast; ring
    rw [heq]
    calc ‖∫ x, ((f x - f E : ℝ) : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹ ∂μ‖
        ≤ ∫ _x, (L : ℝ) ∂μ := by
          refine norm_integral_le_of_norm_le (integrable_const _)
            (Eventually.of_forall fun x => ?_)
          rw [norm_mul, Complex.norm_real, norm_inv]
          have hne : ((x : ℂ) - (E + ε * I)) ≠ 0 := by
            intro h0; have := congrArg Complex.im h0; simp at this; linarith
          have hpos : 0 < ‖(x : ℂ) - (E + ε * I)‖ := norm_pos_iff.2 hne
          have h1 : ‖f x - f E‖ ≤ L * |x - E| := by
            have := hf.dist_le_mul x E; rwa [Real.dist_eq, Real.dist_eq] at this
          have h2 : |x - E| ≤ ‖(x : ℂ) - (E + ε * I)‖ := by
            have := Complex.abs_re_le_norm ((x : ℂ) - (E + ε * I)); simpa using this
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]
          calc ‖f x - f E‖ ≤ L * |x - E| := h1
            _ ≤ L * ‖(x : ℂ) - (E + ε * I)‖ := by gcongr
      _ = C := by rw [integral_const, smul_eq_mul, mul_comm]
  -- conclude
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hinv : Tendsto (fun ε : ℝ => C / (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 0) :=
    hE.const_div_atTop C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hinv
  filter_upwards [hE.eventually (eventually_gt_atTop 0), self_mem_nhdsWithin] with ε hpos hε
  have hF0 : borelTransform μ (E + ε * I) ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have : borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I) - f E =
      (borelTransformDensity μ f (E + ε * I) - f E * borelTransform μ (E + ε * I)) /
        borelTransform μ (E + ε * I) := by
    field_simp
  rw [this, norm_div]
  have hle : (borelTransform μ (E + ε * I)).im ≤ ‖borelTransform μ (E + ε * I)‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  calc _ ≤ C / ‖borelTransform μ (E + ε * I)‖ := by
        gcongr; exact hdiff ε hε
    _ ≤ C / (borelTransform μ (E + ε * I)).im := by
        apply div_le_div_of_nonneg_left (by positivity) hpos hle

/-! ## Theorem 1.10.1 (statement), its pure point case, and Theorem 1.10.4 -/

/-- Theorem 1.10.1 (Poltoratski), recorded as a statement: for a finite compactly supported
measure `μ` and real `f ∈ L¹(μ)`, `F_{fμ}(E + iε) / F_μ(E + iε) → f(E)` for `μ_s`-a.e. `E`. -/
def PoltoratskiStatement : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ → (∃ R : ℝ, μ (Icc (-R) R)ᶜ = 0) →
    ∀ f : ℝ → ℝ, Integrable f μ →
      ∀ᵐ (E : ℝ) ∂(μ.singularPart volume),
        Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
          (𝓝[>] 0) (𝓝 (f E : ℂ))

/-- Theorem 1.10.1 in the case where the singular part of `μ` is pure point (i.e. `μ_sc = 0`):
proved directly via Exercise 1.10.4. -/
theorem poltoratski_of_pure_point (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpp : μ.singularPart volume {E | μ {E} = 0} = 0) {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∀ᵐ (E : ℝ) ∂(μ.singularPart volume),
      Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
        (𝓝[>] 0) (𝓝 (f E : ℂ)) := by
  have h : ∀ᵐ (E : ℝ) ∂(μ.singularPart volume), μ {E} ≠ 0 := by
    rw [ae_iff]; simpa using hpp
  filter_upwards [h] with E hE using tendsto_ratio_of_atom μ hf hE

lemma borelTransformDensity_indicator {ρ σ : Measure ℝ} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    {T : Set ℝ} (hT : MeasurableSet T) (hρ : ρ Tᶜ = 0) (hσ : σ T = 0) {z : ℂ} (hz : z.im ≠ 0) :
    borelTransformDensity (ρ + σ) (T.indicator 1) z = borelTransform ρ z := by
  unfold borelTransformDensity borelTransform
  have : (fun x : ℝ => ((T.indicator (1 : ℝ → ℝ) x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) =
      T.indicator (fun x : ℝ => ((x : ℂ) - z)⁻¹) := by
    ext x
    by_cases hx : x ∈ T <;> simp [hx]
  rw [this, integral_indicator hT, Measure.restrict_add,
    integral_add_measure ((integrable_inv_sub ρ hz).restrict) ((integrable_inv_sub σ hz).restrict),
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hρ),
    Measure.restrict_eq_zero.2 hσ, integral_zero_measure, add_zero]

/-- Theorem 1.10.4, derived from Poltoratski's theorem: if `ρ, σ` are finite compactly supported
measures and `ρ` is singular with respect to both `σ` and Lebesgue measure, then
`F_σ(E + iε) / F_ρ(E + iε) → 0` for `ρ`-a.e. `E`. -/
theorem poltoratski_corollary (hP : PoltoratskiStatement) (ρ σ : Measure ℝ) [IsFiniteMeasure ρ]
    [IsFiniteMeasure σ] (hρc : ∃ R : ℝ, ρ (Icc (-R) R)ᶜ = 0) (hσc : ∃ R : ℝ, σ (Icc (-R) R)ᶜ = 0)
    (hρσ : ρ ⟂ₘ σ) (hρL : ρ ⟂ₘ volume) :
    ∀ᵐ (E : ℝ) ∂ρ, Tendsto (fun ε : ℝ => borelTransform σ (E + ε * I) / borelTransform ρ (E + ε * I))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨s, hsm, hρs, hσs⟩ := hρσ
  set μ := ρ + σ
  have hμc : ∃ R : ℝ, μ (Icc (-R) R)ᶜ = 0 := by
    obtain ⟨R₁, h₁⟩ := hρc
    obtain ⟨R₂, h₂⟩ := hσc
    refine ⟨max R₁ R₂, ?_⟩
    have hsub : ∀ R, R ≤ max R₁ R₂ → (Icc (-max R₁ R₂) (max R₁ R₂))ᶜ ⊆ (Icc (-R) R)ᶜ := by
      intro R hR
      exact compl_subset_compl.2 (Icc_subset_Icc (by linarith) hR)
    simp only [μ, Measure.add_apply]
    rw [measure_mono_null (hsub R₁ (le_max_left _ _)) h₁,
      measure_mono_null (hsub R₂ (le_max_right _ _)) h₂, add_zero]
  -- `ρ` is absolutely continuous with respect to `μ_s`
  have hρle : ρ ≤ μ.singularPart volume := by
    simp only [μ]
    rw [Measure.singularPart_add, Measure.singularPart_eq_self.2 hρL]
    exact Measure.le_add_right le_rfl
  have hac : ρ ≪ μ.singularPart volume := Measure.absolutelyContinuous_of_le hρle
  have hT := hP μ inferInstance hμc (sᶜ.indicator 1)
    ((integrable_const (1 : ℝ)).indicator hsm.compl)
  have hS := hP μ inferInstance hμc (s.indicator 1) ((integrable_const (1 : ℝ)).indicator hsm)
  have hmem : ∀ᵐ (E : ℝ) ∂ρ, E ∈ sᶜ := by rw [ae_iff]; simpa using hρs
  by_cases hμ0 : μ = 0
  · have : ρ = 0 := by
      have h1 : ρ ≤ μ := Measure.le_add_right le_rfl
      rw [hμ0] at h1
      exact le_antisymm h1 (Measure.zero_le _)
    rw [this]; simp
  filter_upwards [hac.ae_le hT, hac.ae_le hS, hmem] with E hET hES hEs
  rw [indicator_of_mem hEs] at hET
  rw [indicator_of_notMem (by simpa using hEs)] at hES
  have h := hES.div hET (by simp)
  simp only [Pi.one_apply, Complex.ofReal_one, Complex.ofReal_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε.ne'
  have hzpos : 0 < (E + ε * I : ℂ).im := by simpa using hε
  have hρT : borelTransformDensity μ (sᶜ.indicator 1) (E + ε * I) = borelTransform ρ (E + ε * I) :=
    borelTransformDensity_indicator hsm.compl (by simpa using hρs) hσs hz
  have hσS : borelTransformDensity μ (s.indicator 1) (E + ε * I) = borelTransform σ (E + ε * I) := by
    have := borelTransformDensity_indicator (ρ := σ) (σ := ρ) hsm (by simpa using hσs) hρs hz
    rwa [add_comm] at this
  have hFμ : borelTransform μ (E + ε * I) ≠ 0 := by
    intro h0
    have := borelTransform_im_pos μ hμ0 hzpos
    rw [h0] at this; simp at this
  simp only [Pi.div_apply]
  rw [hρT, hσS, div_div_div_cancel_right₀ hFμ]

end DF
