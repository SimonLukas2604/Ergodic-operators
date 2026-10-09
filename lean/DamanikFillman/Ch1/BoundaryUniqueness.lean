/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1: Theorem 1.9.4(e), uniqueness of Borel transforms from boundary values.

# Main results

* `DF.BoundaryUniq.eq_zero_of_tendsto` — a bounded holomorphic function on the upper half-plane
  whose vertical limits vanish on a set of positive Lebesgue measure vanishes identically;
* `DF.boundaryUniquenessStatement_holds` — Theorem 1.9.4(e): two Borel transforms whose boundary
  values agree on a set of positive Lebesgue measure coincide;
* `DF.acPart_pos_of_reflectionless'` — Exercise 1.11.2, unconditionally.

The book deduces (e) from the factorization theory of `H^∞`.  We give a direct proof: for a
bounded holomorphic `H` which is small (`‖H‖ ≤ s`) at height `δ` above a compact set `J ⊂ ℝ`,
the function `K(w) = H(w + iδ) exp(-i k F_J(w))` (with `F_J` the Borel transform of `Leb|_J`,
so that `‖exp(-i k F_J)‖ = exp(k Im F_J)`) stays bounded by `sup ‖H‖` on every line `Im w = η`
as `η ↓ 0`; by Phragmén–Lindelöf, `‖H(z + iδ)‖ ≤ (sup ‖H‖) exp(-k Im F_J(z))`.  Since
`Im F_J(z)` is bounded below in terms of `Leb(J)`, letting `k → ∞` gives `H(z) = 0`.  This is
applied to `H = (F_ν + i)⁻¹ - (F_μ + i)⁻¹`.
-/
import DamanikFillman.Ch1.BorelBoundary
import DamanikFillman.Ch1.PoltoratskiRemling
import Mathlib.Analysis.Complex.PhragmenLindelof

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

namespace BoundaryUniq

/-- Phragmén–Lindelöf on the half-plane `{η ≤ Im z}`: a bounded holomorphic function which is
bounded by `C` on the line `Im z = η` is bounded by `C` above it. -/
lemma norm_le_of_line {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | 0 < z.im}) {η M C : ℝ}
    (hη : 0 < η) (hM : ∀ z : ℂ, η ≤ z.im → ‖f z‖ ≤ M) (hC : ∀ t : ℝ, ‖f (t + η * I)‖ ≤ C)
    {z : ℂ} (hz : η ≤ z.im) : ‖f z‖ ≤ C := by
  set g : ℂ → ℂ := fun w => f (I * w + η * I) with hg
  have him_g : ∀ w : ℂ, (I * w + η * I).im = w.re + η := fun w => by simp
  have hgd : DifferentiableOn ℂ g {w | -η < w.re} := by
    refine hf.comp (by fun_prop) fun w hw => ?_
    simp only [mem_setOf_eq] at hw ⊢
    rw [him_g]; linarith
  have hcl : DiffContOnCl ℂ g {w | 0 < w.re} := by
    refine DifferentiableOn.diffContOnCl (hgd.mono ?_)
    rw [closure_setOfPred_lt_re]
    intro w hw
    simp only [mem_setOf_eq] at hw ⊢
    linarith
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[Bornology.cobounded ℂ ⊓ 𝓟 {w | 0 < w.re}] fun w => Real.exp (B * ‖w‖ ^ c) := by
    refine ⟨1, by norm_num, 0, Asymptotics.IsBigO.of_bound M ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    simp only [mem_setOf_eq] at hw
    exact hM _ (by rw [him_g]; linarith)
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖g x‖ :=
    ⟨M, eventually_map.2 ((eventually_ge_atTop 0).mono fun x hx =>
      hM _ (by rw [him_g, ofReal_re]; linarith))⟩
  have hI : ∀ x : ℝ, ‖g (x * I)‖ ≤ C := fun x => by
    have e : I * ((x : ℂ) * I) + (η : ℂ) * I = ((-x : ℝ) : ℂ) + η * I := by
      push_cast; linear_combination (x : ℂ) * I_sq
    show ‖f (I * ((x : ℂ) * I) + (η : ℂ) * I)‖ ≤ C
    rw [e]
    exact hC (-x)
  have hre0 : 0 ≤ (-I * (z - η * I)).re := by simp; linarith
  have key := PhragmenLindelof.right_half_plane_of_bounded_on_real hcl hexp hre hI hre0
  have e2 : I * (-I * (z - η * I)) + η * I = z := by
    linear_combination (-(z - η * I)) * I_sq
  have e3 : g (-I * (z - η * I)) = f z := by
    show f (I * (-I * (z - η * I)) + η * I) = f z
    rw [e2]
  rwa [e3] at key

variable {J : Set ℝ}

lemma im_le_pi (hJ : volume J ≠ ∞) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (borelTransform (volume.restrict J) (E + ε * I)).im ≤ Real.pi := by
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJ
  rw [borelTransform_im_eq_poisson _ E hε.ne']
  have h1 : ∫ x in J, poissonKernel ε (x - E) ≤ ∫ x, poissonKernel ε (x - E) :=
    setIntegral_le_integral (integrable_poissonKernel_volume hε E)
      (Eventually.of_forall fun x => poissonKernel_nonneg hε.le _)
  rw [integral_poissonKernel hε E] at h1
  exact mul_le_of_le_one_right Real.pi_pos.le h1

lemma im_le_far (hJ : volume J ≠ ∞) (hJm : MeasurableSet J) (E : ℝ) {ε r : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (hfar : ∀ t ∈ J, r ≤ |t - E|) :
    (borelTransform (volume.restrict J) (E + ε * I)).im ≤ volume.real J * ε / r ^ 2 := by
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJ
  rw [borelTransform_im_eq_poisson _ E hε.ne']
  have h1 : ∫ x in J, poissonKernel ε (x - E) ≤ ∫ _ in J, ε / (Real.pi * r ^ 2) :=
    integral_mono_ae (integrable_poissonKernel _ hε E) (integrable_const _)
      ((ae_restrict_iff' hJm).2 (Eventually.of_forall fun x hx =>
        poissonKernel_le_of_le hε hr (hfar x hx)))
  rw [setIntegral_const, smul_eq_mul] at h1
  have := hr.ne'
  have := Real.pi_pos.ne'
  calc Real.pi * ∫ x in J, poissonKernel ε (x - E)
      ≤ Real.pi * (volume.real J * (ε / (Real.pi * r ^ 2))) :=
        mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    _ = volume.real J * ε / r ^ 2 := by field_simp

lemma le_im (hJ : volume J ≠ ∞) (hJm : MeasurableSet J) {R : ℝ} (hJR : J ⊆ Icc (-R) R)
    (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    volume.real J * ε / ((R + |E|) ^ 2 + ε ^ 2) ≤
      (borelTransform (volume.restrict J) (E + ε * I)).im := by
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJ
  rw [borelTransform_im_eq_poisson _ E hε.ne']
  have h1 : ∫ _ in J, ε / (Real.pi * ((R + |E|) ^ 2 + ε ^ 2)) ≤
      ∫ x in J, poissonKernel ε (x - E) :=
    integral_mono_ae (integrable_const _) (integrable_poissonKernel _ hε E)
      ((ae_restrict_iff' hJm).2 (Eventually.of_forall fun x hx => by
        have hx' : |x - E| ≤ R + |E| :=
          abs_le.2 ⟨by linarith [le_abs_self E, (hJR hx).1], by linarith [neg_abs_le E, (hJR hx).2]⟩
        have hsq : (x - E) ^ 2 ≤ (R + |E|) ^ 2 := by
          rw [← sq_abs (x - E)]; exact pow_le_pow_left₀ (abs_nonneg _) hx' 2
        unfold poissonKernel
        exact div_le_div_of_nonneg_left hε.le (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)))
  rw [setIntegral_const, smul_eq_mul] at h1
  have hD : (R + |E|) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have := Real.pi_pos.ne'
  calc volume.real J * ε / ((R + |E|) ^ 2 + ε ^ 2)
      = Real.pi * (volume.real J * (ε / (Real.pi * ((R + |E|) ^ 2 + ε ^ 2)))) := by
        field_simp
    _ ≤ Real.pi * ∫ x in J, poissonKernel ε (x - E) :=
        mul_le_mul_of_nonneg_left h1 Real.pi_pos.le

lemma norm_point_le (u v : ℝ) : ‖(u : ℂ) + v * I‖ ≤ |u| + |v| :=
  (norm_add_le _ _).trans (by simp [norm_mul])

/-- **Uniqueness for bounded holomorphic functions**: a bounded holomorphic function on the upper
half-plane whose vertical limits vanish on a set of positive Lebesgue measure is zero. -/
theorem eq_zero_of_tendsto {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H {z | 0 < z.im}) {M : ℝ}
    (hM : ∀ z : ℂ, 0 < z.im → ‖H z‖ ≤ M) {A : Set ℝ} (hA : 0 < volume A)
    (hlim : ∀ E ∈ A, Tendsto (fun ε : ℝ => H (E + ε * I)) (𝓝[>] 0) (𝓝 0))
    {z : ℂ} (hz : 0 < z.im) : H z = 0 := by
  have hHc : ContinuousOn H {z | 0 < z.im} := hH.continuousOn
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by rw [hM']; positivity
  have hM1 : ∀ w : ℂ, 0 < w.im → ‖H w‖ ≤ M' := fun w hw =>
    (hM w hw).trans (by rw [hM']; linarith [le_abs_self M])
  have hline : ∀ δ : ℝ, 0 < δ → Continuous fun t : ℝ => ‖H (t + δ * I)‖ := by
    intro δ hδ
    refine continuous_norm.comp (hHc.comp_continuous (by fun_prop) fun t => ?_)
    simpa using hδ
  -- a bounded piece of `A` of positive measure
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 < volume (A ∩ Icc (-R) R) := by
    by_contra h
    push_neg at h
    have h0 : volume (⋃ n : ℕ, A ∩ Icc (-(n : ℝ)) n) = 0 :=
      measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)
    have hsub : A ⊆ ⋃ n : ℕ, A ∩ Icc (-(n : ℝ)) n := by
      intro x hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact mem_iUnion.2 ⟨n, hx, (abs_le.1 hn).1, (abs_le.1 hn).2⟩
    exact hA.ne' (measure_mono_null hsub h0)
  set a : ℝ≥0∞ := volume (A ∩ Icc (-R) R) with ha
  have ha_top : a ≠ ∞ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := -R) (b := R)).ne
      (measure_mono inter_subset_right)
  set a' : ℝ := a.toReal with ha'
  have ha'pos : 0 < a' := ENNReal.toReal_pos hR.ne' ha_top
  set c : ℝ := a' / 2 * (z.im / ((R + |z.re|) ^ 2 + z.im ^ 2)) with hc
  have hden : 0 < (R + |z.re|) ^ 2 + z.im ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
  have hcpos : 0 < c := mul_pos (half_pos ha'pos) (div_pos hz hden)
  -- the main estimate
  have key : ∀ k : ℕ, ‖H z‖ ≤ M' * Real.exp (-(k * c)) := by
    intro k
    set s : ℝ := M' * Real.exp (-(k * Real.pi)) / 4 with hs
    have hspos : 0 < s := div_pos (mul_pos hM'pos (Real.exp_pos _)) (by norm_num)
    -- the compact sets where `H` is small near the boundary
    set J : ℕ → Set ℝ := fun n => Icc (-R) R ∩
      ⋂ δ ∈ Ioo (0 : ℝ) (1 / (n + 1)), {t : ℝ | ‖H (t + δ * I)‖ ≤ s} with hJ
    have hJclosed : ∀ n, IsClosed (J n) := fun n =>
      isClosed_Icc.inter (isClosed_biInter fun δ hδ => isClosed_le (hline δ hδ.1) continuous_const)
    have hJmono : Monotone J := by
      intro n m hnm t ht
      refine ⟨ht.1, mem_iInter₂.2 fun δ hδ => (mem_iInter₂.1 ht.2) δ ⟨hδ.1, hδ.2.trans_le ?_⟩⟩
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hcover : A ∩ Icc (-R) R ⊆ ⋃ n, J n := by
      intro t ht
      have h1 := (hlim t ht.1).eventually (closedBall_mem_nhds (0 : ℂ) hspos)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
      obtain ⟨ε, hε, hεP⟩ := h1
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine mem_iUnion.2 ⟨n, ht.2, mem_iInter₂.2 fun δ hδ => ?_⟩
      have := hεP (y := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ.1]; exact hδ.2.trans hn)
        hδ.1
      simpa using this
    have hsup : a ≤ ⨆ n, volume (J n) := by
      rw [← hJmono.measure_iUnion (μ := volume)]
      exact measure_mono hcover
    obtain ⟨n, hn⟩ : ∃ n, a / 2 < volume (J n) :=
      lt_iSup_iff.1 ((ENNReal.half_lt_self hR.ne' ha_top).trans_le hsup)
    set J0 := J n with hJ0
    have hJ0sub : J0 ⊆ Icc (-R) R := inter_subset_left
    have hJ0c : IsCompact J0 := isCompact_Icc.of_isClosed_subset (hJclosed n) hJ0sub
    have hJ0m : MeasurableSet J0 := (hJclosed n).measurableSet
    have hJ0fin : volume J0 ≠ ∞ := hJ0c.measure_lt_top.ne
    set vJ : ℝ := volume.real J0 with hvJdef
    have hvJ0 : 0 ≤ vJ := measureReal_nonneg
    have hvJ : a' / 2 ≤ vJ := by
      have h1 := ENNReal.toReal_mono hJ0fin hn.le
      rw [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h1
      exact h1
    have : IsFiniteMeasure (volume.restrict J0) := isFiniteMeasure_restrict.2 hJ0fin
    set F : ℂ → ℂ := borelTransform (volume.restrict J0) with hF
    have hFim_pi : ∀ w : ℂ, 0 < w.im → (F w).im ≤ Real.pi := fun w hw => by
      have := im_le_pi hJ0fin w.re hw
      rwa [← eq_re_add_im_mul_I] at this
    have hFz : c ≤ (F z).im := by
      have h1 := le_im hJ0fin hJ0m hJ0sub z.re hz
      rw [← eq_re_add_im_mul_I] at h1
      calc c = a' / 2 * (z.im / ((R + |z.re|) ^ 2 + z.im ^ 2)) := rfl
        _ ≤ vJ * (z.im / ((R + |z.re|) ^ 2 + z.im ^ 2)) :=
          mul_le_mul_of_nonneg_right hvJ (div_pos hz hden).le
        _ = vJ * z.im / ((R + |z.re|) ^ 2 + z.im ^ 2) := (mul_div_assoc _ _ _).symm
        _ ≤ (F z).im := h1
    -- the estimate at height `δ`
    have hδbound : ∀ δ ∈ Ioo (0 : ℝ) (1 / (n + 1)),
        ‖H (z + δ * I)‖ ≤ M' * Real.exp (-(k * c)) := by
      intro δ hδ
      have hsmall : ∀ t ∈ J0, ‖H (t + δ * I)‖ ≤ s := fun t ht => (mem_iInter₂.1 ht.2) δ hδ
      set V : Set ℝ := {t | ‖H (t + δ * I)‖ < 2 * s} with hV
      have hVo : IsOpen V := isOpen_lt (hline δ hδ.1) continuous_const
      have hJV : J0 ⊆ V := fun t ht => lt_of_le_of_lt (hsmall t ht) (by linarith)
      obtain ⟨r, hr, hrV⟩ := hJ0c.exists_thickening_subset_open hVo hJV
      -- uniform continuity of `H` near the relevant segment
      set ρ : ℝ := R + r + δ + 1 with hρ
      set Q : Set ℂ := closedBall 0 ρ ∩ {w | δ ≤ w.im} with hQdef
      have hQc : IsCompact Q :=
        (isCompact_closedBall 0 ρ).inter_right (isClosed_le continuous_const continuous_im)
      have hQ : Q ⊆ {w | 0 < w.im} := fun w hw => lt_of_lt_of_le hδ.1 hw.2
      obtain ⟨η1, hη1, hUC⟩ := Metric.uniformContinuousOn_iff.1
        (hQc.uniformContinuousOn_of_continuous (hHc.mono hQ)) s hspos
      -- the auxiliary function
      set K : ℂ → ℂ := fun w => H (w + δ * I) * Complex.exp (-(I * k * F w)) with hK
      have hnormK : ∀ w, ‖K w‖ = ‖H (w + δ * I)‖ * Real.exp (k * (F w).im) := by
        intro w
        simp only [hK, norm_mul, Complex.norm_exp]
        congr 2
        simp only [neg_re, mul_re, mul_im, I_re, I_im, natCast_re, natCast_im]
        ring
      have hKd : DifferentiableOn ℂ K {w | 0 < w.im} := by
        have h1 : DifferentiableOn ℂ (fun w => H (w + δ * I)) {w | 0 < w.im} := by
          refine hH.comp (by fun_prop) fun w hw => ?_
          simp only [mem_setOf_eq] at hw ⊢
          have : (w + (δ : ℂ) * I).im = w.im + δ := by simp
          linarith [hδ.1]
        have h2 : DifferentiableOn ℂ F {w | 0 < w.im} := differentiableOn_borelTransform _
        exact h1.mul ((h2.const_mul (I * k)).neg.cexp)
      have hglob : ∀ w : ℂ, 0 < w.im → ‖K w‖ ≤ M' * Real.exp (k * Real.pi) := by
        intro w hw
        rw [hnormK]
        have hw' : 0 < (w + δ * I).im := by simp; linarith [hδ.1]
        exact mul_le_mul (hM1 _ hw')
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hFim_pi w hw) (Nat.cast_nonneg k)))
          (Real.exp_pos _).le hM'pos.le
      -- bound on the line `Im w = η`
      have hline_bd : ∀ η : ℝ, 0 < η → η < η1 → η ≤ 1 → ∀ t : ℝ,
          ‖K (t + η * I)‖ ≤ M' * Real.exp (k * (vJ * η / r ^ 2)) := by
        intro η hη hηη1 hη1' t
        have hexp1 : 1 ≤ Real.exp (k * (vJ * η / r ^ 2)) :=
          Real.one_le_exp (mul_nonneg (Nat.cast_nonneg k)
            (div_nonneg (mul_nonneg hvJ0 hη.le) (sq_nonneg r)))
        have e : (t : ℂ) + η * I + δ * I = (t : ℂ) + ((η + δ : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hnormK, e]
        by_cases ht : t ∈ thickening r J0
        · -- near `J0`: `H` is small there
          obtain ⟨t', ht'J, ht'd⟩ := mem_thickening_iff.1 ht
          have htV : ‖H (t + δ * I)‖ < 2 * s := hrV ht
          have ht' : |t'| ≤ R := abs_le.2 ⟨(hJ0sub ht'J).1, (hJ0sub ht'J).2⟩
          rw [Real.dist_eq] at ht'd
          have ht_abs : |t| ≤ R + r := by
            have h1 : |t| ≤ |t - t'| + |t'| := by
              have := abs_add_le (t - t') t'
              rwa [sub_add_cancel] at this
            linarith
          have hmem1 : (t : ℂ) + δ * I ∈ Q := by
            refine ⟨?_, by simp⟩
            rw [mem_closedBall, dist_zero_right]
            refine (norm_point_le t δ).trans ?_
            rw [abs_of_pos hδ.1]; linarith
          have hmem2 : (t : ℂ) + ((η + δ : ℝ) : ℂ) * I ∈ Q := by
            refine ⟨?_, by simp; linarith⟩
            rw [mem_closedBall, dist_zero_right]
            refine (norm_point_le t (η + δ)).trans ?_
            rw [abs_of_pos (show (0 : ℝ) < η + δ by linarith [hδ.1])]; linarith
          have hd : dist ((t : ℂ) + δ * I) ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I) < η1 := by
            rw [dist_eq_norm]
            have e2 : (t : ℂ) + δ * I - ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I) =
                ((-η : ℝ) : ℂ) * I := by push_cast; ring
            rw [e2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_neg, abs_of_pos hη]
            exact hηη1
          have h3 := hUC _ hmem1 _ hmem2 hd
          rw [dist_eq_norm] at h3
          have hHle : ‖H ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I)‖ ≤ 3 * s := by
            have := norm_sub_norm_le (H ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I)) (H (t + δ * I))
            rw [norm_sub_rev] at this
            linarith
          have hW := hFim_pi ((t : ℂ) + η * I) (by simpa using hη)
          have hcancel : Real.exp (-(k * Real.pi)) * Real.exp (k * Real.pi) = 1 := by
            rw [← Real.exp_add]; simp
          calc ‖H ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I)‖ * Real.exp (k * (F (t + η * I)).im)
              ≤ 3 * s * Real.exp (k * Real.pi) :=
                mul_le_mul hHle (Real.exp_le_exp.2
                  (mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg k))) (Real.exp_pos _).le
                  (by positivity)
            _ = 3 / 4 * M' * (Real.exp (-(k * Real.pi)) * Real.exp (k * Real.pi)) := by
                rw [hs]; ring
            _ = 3 / 4 * M' := by rw [hcancel, mul_one]
            _ ≤ M' := by linarith
            _ ≤ M' * Real.exp (k * (vJ * η / r ^ 2)) := le_mul_of_one_le_right hM'pos.le hexp1
        · -- far from `J0`: the Poisson integral of `J0` is small there
          have hfar : ∀ t' ∈ J0, r ≤ |t' - t| := by
            intro t' ht'
            by_contra hlt
            push Not at hlt
            exact ht (mem_thickening_iff.2 ⟨t', ht', by rw [Real.dist_eq, abs_sub_comm]; exact hlt⟩)
          have hW := im_le_far hJ0fin hJ0m t hη hr hfar
          have hpos : 0 < ((t : ℂ) + ((η + δ : ℝ) : ℂ) * I).im := by
            simp; linarith [hδ.1]
          exact mul_le_mul (hM1 _ hpos)
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg k)))
            (Real.exp_pos _).le hM'pos.le
      -- Phragmén–Lindelöf and `η → 0`
      have hKz : ‖K z‖ ≤ M' := by
        have hlimη : Tendsto (fun η : ℝ => M' * Real.exp (k * (vJ * η / r ^ 2))) (𝓝[>] 0)
            (𝓝 M') := by
          have : Continuous fun η : ℝ => M' * Real.exp (k * (vJ * η / r ^ 2)) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlimη ?_
        filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hη1 one_pos) hz)] with η hη
        have h1 : η < η1 := lt_of_lt_of_le hη.2 ((min_le_left _ _).trans (min_le_left _ _))
        have h2 : η ≤ 1 := (lt_of_lt_of_le hη.2 ((min_le_left _ _).trans (min_le_right _ _))).le
        have h3 : η ≤ z.im := (lt_of_lt_of_le hη.2 (min_le_right _ _)).le
        exact norm_le_of_line hKd hη.1 (fun w hw => hglob w (hη.1.trans_le hw))
          (hline_bd η hη.1 h1 h2) h3
      have h1 : ‖H (z + δ * I)‖ ≤ M' * Real.exp (-(k * (F z).im)) := by
        rw [hnormK] at hKz
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
        exact hKz
      exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left hFz (Nat.cast_nonneg k)))) hM'pos.le)
    -- let `δ → 0`
    have hcz : ContinuousAt H z :=
      hHc.continuousAt ((isOpen_lt continuous_const continuous_im).mem_nhds hz)
    have ht : Tendsto (fun δ : ℝ => z + δ * I) (𝓝[>] 0) (𝓝 z) := by
      have : Continuous fun δ : ℝ => z + δ * I := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ((continuous_norm.tendsto _).comp (hcz.tendsto.comp ht)) ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (n + 1))] with δ hδ
    exact hδbound δ hδ
  have hlim0 : Tendsto (fun k : ℕ => M' * Real.exp (-(k * c))) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => -((k : ℝ) * c)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hcpos)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul M'
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim0 key)

lemma borelTransform_im_nonneg' (ρ : Measure ℝ) [IsFiniteMeasure ρ] {w : ℂ} (hw : 0 < w.im) :
    0 ≤ (borelTransform ρ w).im := by
  have := borelTransform_im_nonneg ρ w.re hw
  rwa [← eq_re_add_im_mul_I] at this

lemma add_I_ne_zero {w : ℂ} (hw : 0 ≤ w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma norm_inv_add_I_le {w : ℂ} (hw : 0 ≤ w.im) : ‖(w + I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  have h := abs_im_le_norm (w + I)
  simp only [add_im, I_im] at h
  rw [abs_of_pos (by linarith)] at h
  linarith

end BoundaryUniq

open BoundaryUniq in
/-- **Theorem 1.9.4(e)**: two Borel transforms whose boundary values agree on a set of positive
Lebesgue measure coincide. -/
theorem boundaryUniquenessStatement_holds : BoundaryUniquenessStatement := by
  intro μ ν hμ hν A hA hlim z hz
  set H : ℂ → ℂ := fun w => (borelTransform ν w + I)⁻¹ - (borelTransform μ w + I)⁻¹ with hH
  have hHd : DifferentiableOn ℂ H {w | 0 < w.im} := by
    refine (((differentiableOn_borelTransform ν).add_const I).inv fun w hw => ?_).sub
      (((differentiableOn_borelTransform μ).add_const I).inv fun w hw => ?_)
    · exact add_I_ne_zero (borelTransform_im_nonneg' ν hw)
    · exact add_I_ne_zero (borelTransform_im_nonneg' μ hw)
  have hHb : ∀ w : ℂ, 0 < w.im → ‖H w‖ ≤ 2 := fun w hw => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_inv_add_I_le (borelTransform_im_nonneg' ν hw)
    have h2 := norm_inv_add_I_le (borelTransform_im_nonneg' μ hw)
    linarith
  have hHlim : ∀ E ∈ A, Tendsto (fun ε : ℝ => H (E + ε * I)) (𝓝[>] 0) (𝓝 0) := by
    intro E hE
    obtain ⟨w, h1, h2⟩ := hlim E hE
    have hw : 0 ≤ w.im := by
      refine ge_of_tendsto ((continuous_im.tendsto w).comp h1) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact borelTransform_im_nonneg μ E hε
    have hne := add_I_ne_zero hw
    have := ((h2.add_const I).inv₀ hne).sub ((h1.add_const I).inv₀ hne)
    rw [sub_self] at this
    exact this
  have h0 := eq_zero_of_tendsto hHd hHb hA hHlim hz
  have h1 : (borelTransform ν z + I)⁻¹ = (borelTransform μ z + I)⁻¹ := sub_eq_zero.1 h0
  have h2 := add_right_cancel (inv_inj.1 h1)
  exact h2.symm

/-- Exercise 1.11.2, unconditionally: a nonzero measure reflectionless on `Σ` has absolutely
continuous part charging every subset of `Σ` of positive Lebesgue measure. -/
theorem acPart_pos_of_reflectionless' (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    {S : Set ℝ} (hSm : MeasurableSet S) (hrefl : IsReflectionless μ S) {Q : Set ℝ} (hQ : Q ⊆ S)
    (hQpos : 0 < volume Q) : 0 < volume.withDensity (μ.rnDeriv volume) Q :=
  acPart_pos_of_reflectionless boundaryUniquenessStatement_holds μ hμ hSm hrefl hQ hQpos

end DF
