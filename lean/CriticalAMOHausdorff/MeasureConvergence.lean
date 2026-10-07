/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Convergence of the measure of the spectrum  (paper §6, Theorem 1.3, eq. (1.5))

Paper references (`Arxiv_version-5.tex`):
* §6 (`sectionproofmeasure`, tex l. 1027–1064): the proof of Theorem 1.3 (`measure`):
  `|σ(M_{v,b,p_n/q_n})| → |σ(M_{v,b,α})|` when `b` has a zero;
* the sets `w_m = [E_1^m - r_n, E_2^m + r_n]` (6.2) (`wm`) and the covering argument:
  `volume_le_liminf_of_cover`;
* the inequality `|σ(M_α)| ≥ limsup |σ(M_{p_n/q_n})|` (6.1), obtained in the paper from
  Hausdorff continuity of the spectrum [AS1983, El82].  We *prove* the needed Hausdorff
  continuity from the (symmetric) AMS estimate (5.7) `cgeneral`
  (`sigmaM_convergents_subset_cthickening`), and the measure upper semicontinuity under
  Hausdorff convergence (`limsup_volume_le_of_cthickening`);
* "another proof of Theorem 1.2" (tex l. 1062–1064): `volume_eq_zero_of_small_bands`.

## External inputs (explicit hypotheses, not proved here)
* `RationalBands v b α` (Floquet–Bloch theory for periodic Jacobi matrices, used at
  tex l. 1037–1040): for each `n`, `σ(M_{v,b,p_n/q_n})` is a union of at most `q_n`
  closed intervals `[E_1^m, E_2^m]`.
* In `volume_eq_zero_of_small_bands`: the bound `|σ(M_{v,b,p_n/q_n})| ≤ C/q_n` (for the
  critical almost Mathieu operator this is Last's bound [L], via
  `|σ(M_{2p_n/q_n})| = |σ(M_{0, 2 sin 2π(·), p_n/q_n})|`).

The abstract measure statements are proved completely; there is no `sorry` in this file.
-/
import CriticalAMOHausdorff.GapContinuity

noncomputable section

open MeasureTheory Filter Topology Set L2

namespace CAH

/-! ### Abstract measure theory -/

/-- **The covering step of §6 (tex l. 1041–1056).** If `K ⊆ ⋃_{m < N_n} [E_1^m - r_n,
E_2^m + r_n]` and `N_n r_n → 0`, then `|K| ≤ liminf_n |⋃_{m < N_n} [E_1^m, E_2^m]|`. -/
theorem volume_le_liminf_of_cover {K : Set ℝ} {N : ℕ → ℕ} {E1 E2 : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n)
    (hcov : ∀ n, K ⊆ ⋃ m ∈ Finset.range (N n), Icc (E1 n m - r n) (E2 n m + r n))
    (hNr : Tendsto (fun n => (N n : ℝ) * r n) atTop (𝓝 0)) :
    volume K ≤
      liminf (fun n => volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m))) atTop := by
  have hstep : ∀ n, volume K ≤ volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m)) +
      ENNReal.ofReal (2 * ((N n : ℝ) * r n)) := by
    intro n
    set A := ⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m)
    set B := ⋃ m ∈ Finset.range (N n),
      (Icc (E1 n m - r n) (E1 n m) ∪ Icc (E2 n m) (E2 n m + r n))
    have hsub : K ⊆ A ∪ B := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.1 (hcov n hx)
      by_cases h1 : x < E1 n m
      · exact Or.inr (mem_iUnion₂.2 ⟨m, hm, Or.inl ⟨hxm.1, h1.le⟩⟩)
      by_cases h2 : E2 n m < x
      · exact Or.inr (mem_iUnion₂.2 ⟨m, hm, Or.inr ⟨h2.le, hxm.2⟩⟩)
      push_neg at h1 h2
      exact Or.inl (mem_iUnion₂.2 ⟨m, hm, ⟨h1, h2⟩⟩)
    have hB : volume B ≤ ENNReal.ofReal (2 * ((N n : ℝ) * r n)) := by
      calc volume B ≤ ∑ m ∈ Finset.range (N n),
            volume (Icc (E1 n m - r n) (E1 n m) ∪ Icc (E2 n m) (E2 n m + r n)) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ m ∈ Finset.range (N n), ENNReal.ofReal (2 * r n) := by
            refine Finset.sum_le_sum (fun m _ => (measure_union_le _ _).trans (le_of_eq ?_))
            rw [Real.volume_Icc, Real.volume_Icc, sub_sub_cancel, add_sub_cancel_left,
              ← ENNReal.ofReal_add (hr n) (hr n), two_mul]
        _ = ENNReal.ofReal (2 * ((N n : ℝ) * r n)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1
            ring
    calc volume K ≤ volume (A ∪ B) := measure_mono hsub
      _ ≤ volume A + volume B := measure_union_le _ _
      _ ≤ _ := by gcongr
  have hg : Tendsto (fun n => ENNReal.ofReal (2 * ((N n : ℝ) * r n))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * ((N n : ℝ) * r n)) atTop (𝓝 0) := by
      simpa using hNr.const_mul 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    rw [ENNReal.ofReal_zero] at this
    exact this
  calc volume K ≤ liminf (fun n => volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m)) +
        ENNReal.ofReal (2 * ((N n : ℝ) * r n))) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hstep)
    _ = _ := ENNReal.liminf_add_of_right_tendsto_zero hg _

/-- **Upper semicontinuity of the measure under Hausdorff convergence.** If `K` is compact
and `K_n ⊆ cthickening ρ_n K` eventually with `ρ_n → 0`, then `limsup |K_n| ≤ |K|`. -/
theorem limsup_volume_le_of_cthickening {K : Set ℝ} (hK : IsCompact K) {Kn : ℕ → Set ℝ}
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, Kn n ⊆ Metric.cthickening (ρ n) K) :
    limsup (fun n => volume (Kn n)) atTop ≤ volume K := by
  have ht : Tendsto (fun n => volume (Metric.cthickening (ρ n) K)) atTop (𝓝 (volume K)) :=
    (tendsto_measure_cthickening_of_isCompact hK).comp hρ
  calc limsup (fun n => volume (Kn n)) atTop
      ≤ limsup (fun n => volume (Metric.cthickening (ρ n) K)) atTop :=
        limsup_le_limsup (h.mono fun n hn => measure_mono hn)
    _ = volume K := ht.limsup_eq

/-- **Abstract Theorem 1.3.** Covering (6.2) with `N_n r_n → 0`, together with
`limsup |K_n| ≤ |K|` (6.1), gives `|K_n| → |K|`. -/
theorem tendsto_volume_of_cover {K : Set ℝ} {N : ℕ → ℕ} {E1 E2 : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n)
    (hcov : ∀ n, K ⊆ ⋃ m ∈ Finset.range (N n), Icc (E1 n m - r n) (E2 n m + r n))
    (hNr : Tendsto (fun n => (N n : ℝ) * r n) atTop (𝓝 0))
    (hsup : limsup (fun n => volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m))) atTop
      ≤ volume K) :
    Tendsto (fun n => volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m))) atTop
      (𝓝 (volume K)) :=
  tendsto_of_le_liminf_of_limsup_le (volume_le_liminf_of_cover hr hcov hNr) hsup

/-- **Abstract "another proof of Theorem 1.2".** Under the covering hypotheses, if
`|K_n| ≤ C/Q_n` with `Q_n → ∞`, then `|K| = 0`. -/
theorem volume_eq_zero_of_cover {K : Set ℝ} {N : ℕ → ℕ} {E1 E2 : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n)
    (hcov : ∀ n, K ⊆ ⋃ m ∈ Finset.range (N n), Icc (E1 n m - r n) (E2 n m + r n))
    (hNr : Tendsto (fun n => (N n : ℝ) * r n) atTop (𝓝 0)) {C : ℝ} {Q : ℕ → ℝ}
    (hQ : Tendsto Q atTop atTop)
    (hsmall : ∀ n, volume (⋃ m ∈ Finset.range (N n), Icc (E1 n m) (E2 n m)) ≤
      ENNReal.ofReal (C / Q n)) :
    volume K = 0 := by
  have h0 : Tendsto (fun n => ENNReal.ofReal (C / Q n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => C / Q n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hQ
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hc
    rw [ENNReal.ofReal_zero] at this
    exact this
  refine le_antisymm ?_ zero_le
  calc volume K ≤ liminf (fun n => volume (⋃ m ∈ Finset.range (N n),
        Icc (E1 n m) (E2 n m))) atTop := volume_le_liminf_of_cover hr hcov hNr
    _ ≤ liminf (fun n => ENNReal.ofReal (C / Q n)) atTop :=
        liminf_le_liminf (Eventually.of_forall hsmall)
    _ = 0 := h0.liminf_eq

/-! ### Boundedness of the spectra -/

lemma norm_jacobi_le {v b : ℝ → ℝ} {Mv Mb : ℝ} (hMv : ∀ x, |v x| ≤ Mv)
    (hMb : ∀ x, |b x| ≤ Mb) (α θ : ℝ) : ‖jacobi v b α θ‖ ≤ 2 * Mb + Mv := by
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb 0)
  have hMv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0)
  unfold jacobi
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_add_le
    (weightedShift (fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ)) (Equiv.addRight (-1)))
    (weightedShift (fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ)) (Equiv.addRight 1))
  have e1 := norm_weightedShift_le (σ := Equiv.addRight (-1 : ℤ)) hMb0
    (c := fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ)) (fun n => by simpa using hMb _)
  have e2 := norm_weightedShift_le (σ := Equiv.addRight (1 : ℤ)) hMb0
    (c := fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ)) (fun n => by simpa using hMb _)
  have e3 := norm_weightedShift_le (σ := Equiv.refl ℤ) hMv0
    (c := fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ)) (fun n => by simpa using hMv _)
  linarith

/-- `σ(M_{v,b,α}) ⊆ [-R, R]` with `R = 2 sup|b| + sup|v|`. -/
lemma sigmaM_subset_Icc {v b : ℝ → ℝ} {Mv Mb : ℝ} (hMv : ∀ x, |v x| ≤ Mv)
    (hMb : ∀ x, |b x| ≤ Mb) (α : ℝ) :
    sigmaM v b α ⊆ Icc (-(2 * Mb + Mv)) (2 * Mb + Mv) := by
  refine closure_minimal (fun E hE => ?_) isClosed_Icc
  obtain ⟨θ, hθ⟩ := mem_iUnion.1 hE
  have h1 : algebraMap ℝ ℂ E ∈ spectrum ℂ (jacobi v b α θ) :=
    (spectrum.algebraMap_mem_iff ℂ).2 hθ
  have h2 := spectrum.norm_le_norm_of_mem h1
  have h3 : |E| ≤ 2 * Mb + Mv := by
    have : ‖algebraMap ℝ ℂ E‖ = |E| := by simp
    rw [← this]; exact h2.trans (norm_jacobi_le hMv hMb α θ)
  exact abs_le.1 h3

lemma isCompact_sigmaM {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (α : ℝ) :
    IsCompact (sigmaM v b α) := by
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mb, hMb⟩ := hb
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (sigmaM_subset_Icc hMv hMb α)

/-! ### Theorem 1.3 -/

/-- **External input (Floquet–Bloch theory, tex l. 1037–1040).** For every `n`, the
spectrum `σ(M_{v,b,p_n/q_n})` of the periodic problem is a union of at most `q_n` closed
intervals `[E_1^m, E_2^m]`. -/
def RationalBands (v b : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ n : ℕ, ∃ (N : ℕ) (E1 E2 : ℕ → ℝ), (N : ℝ) ≤ q α n ∧
    sigmaM v b (p α n / q α n) = ⋃ m ∈ Finset.range N, Icc (E1 m) (E2 m)

/-- **Hausdorff continuity, one side (replacing [AS1983, El82]).**  By the symmetric
estimate (5.7), `σ(M_{p_n/q_n})` lies in the `C|α - p_n/q_n|^{1/2}`-neighbourhood of
`σ(M_α)`. -/
theorem sigmaM_convergents_subset_cthickening {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    {Kb Kv : ℝ} (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable) {α : ℝ}
    (hα : Irrational α) :
    ∃ C : ℝ, ∀ n : ℕ, sigmaM v b (p α n / q α n) ⊆
      Metric.cthickening (C * √|α - p α n / q α n|) (sigmaM v b α) := by
  obtain ⟨C, -, hC⟩ := cgeneral hv hb hKb hKv hLb hLv hZ
  refine ⟨C, fun n E hE => ?_⟩
  have h1 : |p α n / q α n - α| ≤ 1 := by rw [abs_sub_comm]; exact abs_sub_pq_le_one hα n
  have h2 := hC _ α h1 E hE
  rw [abs_sub_comm] at h2
  obtain ⟨E', hE', hd⟩ := exists_mem_sigmaM_of_infDist_le hv hb h2
  exact Metric.mem_cthickening_of_dist_le E E' _ _ hE' (by rw [Real.dist_eq]; exact hd)

/-- **(6.1).** `limsup |σ(M_{v,b,p_n/q_n})| ≤ |σ(M_{v,b,α})|`. -/
theorem limsup_volume_sigmaM_le {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    {Kb Kv : ℝ} (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable) {α : ℝ}
    (hα : Irrational α) :
    limsup (fun n => volume (sigmaM v b (p α n / q α n))) atTop ≤ volume (sigmaM v b α) := by
  obtain ⟨C, hC⟩ := sigmaM_convergents_subset_cthickening hv hb hKb hKv hLb hLv hZ hα
  refine limsup_volume_le_of_cthickening (isCompact_sigmaM hv hb α) ?_
    (Eventually.of_forall hC)
  have := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_abs_sub_pq hα)).const_mul C
  simpa using this

/-- **Theorem 1.3 (`measure`), eq. (1.5).** Let `v, b` be bounded and Lipschitz, `b`
`1`-periodic with a zero and countably many zeros, and `α` irrational.  Assuming the band
structure `RationalBands v b α` of the periodic spectra (external input, Floquet theory),
`|σ(M_{v,b,p_n/q_n})| → |σ(M_{v,b,α})|`. -/
theorem measure_convergence {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hzero : ∃ x₀, b x₀ = 0) {α : ℝ} (hα : Irrational α)
    (hbands : RationalBands v b α) :
    Tendsto (fun n => volume (sigmaM v b (p α n / q α n))) atTop
      (𝓝 (volume (sigmaM v b α))) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_
    (limsup_volume_sigmaM_le hv hb hKb hKv hLb hLv hZ hα)
  choose N E1 E2 hNq hEq using hbands
  set K := sigmaM v b α
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mb, hMb⟩ := hb
  have hv' : BddFun v := ⟨Mv, hMv⟩
  have hb' : BddFun b := ⟨Mb, hMb⟩
  set R := 2 * Mb + Mv
  have hKne : K.Nonempty := sigmaM_nonempty hv' hb' α
  -- `r_n = sup_{E ∈ K} dist(E, σ(M_{p_n/q_n}))`, as in (5.9)
  set r : ℕ → ℝ := fun n =>
    sSup ((fun E => Metric.infDist E (sigmaM v b (p α n / q α n))) '' K) with hrdef
  have hbdd : ∀ n, BddAbove ((fun E => Metric.infDist E (sigmaM v b (p α n / q α n))) '' K) := by
    intro n
    refine ⟨2 * R, ?_⟩
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨y, hy⟩ := sigmaM_nonempty hv' hb' (p α n / q α n)
    have h1 := sigmaM_subset_Icc hMv hMb α hE
    have h2 := sigmaM_subset_Icc hMv hMb _ hy
    refine (Metric.infDist_le_dist_of_mem hy).trans ?_
    rw [Real.dist_eq]
    simp only [mem_Icc] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hle_r : ∀ n, ∀ E ∈ K, Metric.infDist E (sigmaM v b (p α n / q α n)) ≤ r n :=
    fun n E hE => le_csSup (hbdd n) ⟨E, hE, rfl⟩
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    obtain ⟨E, hE⟩ := hKne
    exact Metric.infDist_nonneg.trans (hle_r n E hE)
  have hcov : ∀ n, K ⊆ ⋃ m ∈ Finset.range (N n), Icc (E1 n m - r n) (E2 n m + r n) := by
    intro n E hE
    obtain ⟨E', hE', hd⟩ := exists_mem_sigmaM_of_infDist_le hv' hb' (hle_r n E hE)
    rw [hEq n] at hE'
    obtain ⟨m, hm, hm'⟩ := mem_iUnion₂.1 hE'
    refine mem_iUnion₂.2 ⟨m, hm, ?_⟩
    rw [abs_le] at hd
    exact ⟨by linarith [hm'.1], by linarith [hm'.2]⟩
  -- `N_n r_n ≤ q_n r_n → 0` by (5.9) and `|α - p_n/q_n| ≤ 1/q_n²`
  have hNr : Tendsto (fun n => (N n : ℝ) * r n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev := csingular_convergents hv' hb' hKb hKv hLb hLv hZ hper hzero hα (ε / 2)
      (by positivity)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
    refine ⟨n₀, fun n hn => ?_⟩
    have hrn : r n ≤ ε / 2 * √|α - p α n / q α n| :=
      csSup_le (hKne.image _) (by rintro _ ⟨E, hE, rfl⟩; exact hn₀ n hn E hE)
    have hq1 := (SGD.cfGrowth hα).one_le n
    have hsq : √|α - p α n / q α n| ≤ 1 / q α n := by
      have := Real.sqrt_le_sqrt (abs_sub_pq_le hα n)
      rwa [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq (by linarith)] at this
    have hN : (N n : ℝ) ≤ q α n := hNq n
    have hN0 : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hN0 (hr0 n))]
    calc (N n : ℝ) * r n ≤ q α n * (ε / 2 * (1 / q α n)) := by
          apply mul_le_mul hN (hrn.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))
            (hr0 n) (by linarith)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have h := volume_le_liminf_of_cover hr0 hcov hNr
  refine h.trans (le_of_eq ?_)
  congr 1
  funext n
  rw [hEq n]

/-- **Another proof of Theorem 1.2 (tex l. 1062–1064).** If moreover
`|σ(M_{v,b,p_n/q_n})| ≤ C/q_n` (for the critical AMO: Last's bound [L], external input),
then `|σ(M_{v,b,α})| = 0`. -/
theorem volume_eq_zero_of_small_bands {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    {Kb Kv : ℝ} (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hzero : ∃ x₀, b x₀ = 0) {α : ℝ} (hα : Irrational α)
    (hbands : RationalBands v b α) {C : ℝ}
    (hsmall : ∀ n, volume (sigmaM v b (p α n / q α n)) ≤ ENNReal.ofReal (C / q α n)) :
    volume (sigmaM v b α) = 0 := by
  have ht := measure_convergence hv hb hKb hKv hLb hLv hZ hper hzero hα hbands
  have h0 : Tendsto (fun n => ENNReal.ofReal (C / q α n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => C / q α n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (SGD.cfGrowth hα).tendsto_atTop
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hc
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact le_antisymm (le_of_tendsto_of_tendsto' ht h0 hsmall) zero_le

end CAH
