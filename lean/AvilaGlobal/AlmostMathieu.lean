/-
# Almost Mathieu computations and the Example Theorem  (paper, Appendix A and §1.2)

Throughout, `v(x) = 2 cos 2πx`.

* `am1` — **Theorem `am1`**: `L(α, A^{(E - λv)}_ε) = max(L(α, A^{(E-λv)}), log λ + 2πε)` for
  `ε ≥ 0`.
* `am2` — **Corollary `am2`** (Aubry–André formula, [BJ1]): `L ≥ max(0, log λ)`, with equality
  iff `E ∈ Σ_{α,λv}`.
* `example_theorem` — **Example Theorem**: for `λ > 1`, `w` real-analytic and `ε` small,
  `E ↦ L(E)` restricted to the spectrum of `2λ cos 2πx + εw(x)` is positive and real-analytic.
  (The paper writes "for `ε` small enough, for every `α`"; its proof fixes `α` first, and we
  state that form.)
-/
import AvilaGlobal.Stratified
import AvilaGlobal.Johnson

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

variable [hH : Hypotheses]
include hH

omit hH in
/-- The almost Mathieu potential `v(z) = 2 cos 2πz`. -/
def amPot : ℂ → ℂ := fun z => 2 * Complex.cos (2 * Real.pi * z)
omit hH in
/-- `λ v`. -/
def amPotScaled (lam : ℝ) : ℂ → ℂ := fun z => lam * amPot z

lemma amPot_isRealAnalyticPotential (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IsRealAnalyticPotential δ (amPotScaled lam) := by
  refine ⟨hδ, ?_, ?_, ?_⟩
  · have : Differentiable ℂ (amPotScaled lam) := by
      unfold amPotScaled amPot; fun_prop
    exact this.differentiableOn
  · intro z
    simp only [amPotScaled, amPot, mul_add, mul_one, Complex.cos_add_two_pi]
  · intro x
    have h : (Complex.cos (2 * Real.pi * (x : ℂ))).im = 0 := by
      have : (2 * (Real.pi : ℂ) * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact Complex.cos_ofReal_im _
    simp [amPotScaled, amPot, Complex.mul_im, h]

lemma amPotScaled_conj (lam : ℝ) (z : ℂ) : amPotScaled lam (conj z) = conj (amPotScaled lam z) := by
  have h : conj (2 * (Real.pi : ℂ) * z) = 2 * Real.pi * conj z := by simp [map_ofNat]
  simp only [amPotScaled, amPot]
  rw [map_mul, map_mul, Complex.conj_ofReal, ← Complex.cos_conj, h, map_ofNat]

/-- The Schrödinger cocycle of a conjugation-symmetric potential is real-symmetric. -/
lemma schr_isRealSymmetric {v : ℂ → ℂ} (hv : ∀ z, v (conj z) = conj (v z)) (E : ℝ) :
    IsRealSymmetric (schr (eShift E v)) := by
  intro z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schr, eShift, hv]

/-- Iterated invariance of a line field. -/
lemma iter_mulVec_inv {α : ℝ} {B : ℝ → M2} {u : ℝ → (Fin 2 → ℂ)}
    (hinv : ∀ x, ∃ c : ℂ, B x *ᵥ u x = c • u (x + α)) :
    ∀ m : ℕ, ∀ x, ∃ c : ℂ, iter α B m x *ᵥ u x = c • u (x + m * α) := by
  intro m
  induction m with
  | zero => intro x; exact ⟨1, by simp [iter]⟩
  | succ m ih =>
    intro x
    obtain ⟨c, hc⟩ := ih x
    obtain ⟨c', hc'⟩ := hinv (x + m * α)
    refine ⟨c * c', ?_⟩
    rw [iter, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hc', smul_smul]
    congr 2
    push_cast; ring

/-- A uniformly hyperbolic `SL(2)` cocycle has positive Lyapunov exponent. -/
theorem lyapunov_pos_of_isUH {α : ℝ} {B : ℝ → M2} (hB : IsSLCocycle B) (h : IsUH α B) :
    0 < lyapunov α B := by
  obtain ⟨u, s, hu, -, hup, -, hu0, -, hinv, -, n, hn, hexp⟩ := h
  -- uniform expansion constant
  set f : ℝ → ℝ := fun x => ‖iter α B n x *ᵥ u x‖ / ‖u x‖ with hf
  have hfc : Continuous f :=
    (((continuous_iter hB.continuous n).matrix_mulVec hu).norm).div hu.norm
      (fun x => norm_ne_zero_iff.mpr (hu0 x))
  have hfp : Function.Periodic f 1 := by
    intro x; simp only [hf, iter_periodic hB.periodic n x, hup x]
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0 : ℝ) 1)
    ⟨0, by simp⟩ hfc.continuousOn
  set c := f x₀
  have hc1 : 1 < c := by
    have h1 := (hexp x₀).2
    have hpos : 0 < ‖u x₀‖ := norm_pos_iff.mpr (hu0 x₀)
    simp only [c, hf]
    rw [one_lt_div hpos]; exact h1
  have hcge : ∀ x, c * ‖u x‖ ≤ ‖iter α B n x *ᵥ u x‖ := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hfp.exists_mem_Ico₀ one_pos x
    have : c ≤ f x := by rw [hxy]; exact hmin (Ico_subset_Icc_self hy)
    have hpos : 0 < ‖u x‖ := norm_pos_iff.mpr (hu0 x)
    rw [hf] at this
    simp only at this
    rwa [le_div_iff₀ hpos] at this
  -- growth along multiples of `n`
  have hgrow : ∀ k : ℕ, ∀ x, c ^ k * ‖u x‖ ≤ ‖iter α B (n * k) x *ᵥ u x‖ := by
    intro k
    induction k with
    | zero => intro x; simp [iter]
    | succ k ih =>
      intro x
      obtain ⟨μ, hμ⟩ := iter_mulVec_inv hinv (n * k) x
      have e : n * (k + 1) = n * k + n := by ring
      rw [e, iter_add, ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul, norm_smul]
      have h2 := hcge (x + ((n * k : ℕ) : ℝ) * α)
      have h3 := ih x
      rw [hμ, norm_smul] at h3
      calc c ^ (k + 1) * ‖u x‖ = c * (c ^ k * ‖u x‖) := by ring
        _ ≤ c * (‖μ‖ * ‖u (x + ((n * k : ℕ) : ℝ) * α)‖) :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = ‖μ‖ * (c * ‖u (x + ((n * k : ℕ) : ℝ) * α)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hnorm : ∀ k : ℕ, ∀ x, c ^ k ≤ ‖iter α B (n * k) x‖ := by
    intro k x
    have hpos : 0 < ‖u x‖ := norm_pos_iff.mpr (hu0 x)
    have := (hgrow k x).trans (Matrix.linfty_opNorm_mulVec _ _)
    exact le_of_mul_le_mul_right this hpos
  have hseq : ∀ k : ℕ, (k : ℝ) * Real.log c ≤ lyapSeq α B (n * k) := by
    intro k
    have : ∫ x in (0 : ℝ)..1, (k : ℝ) * Real.log c ≤ lyapSeq α B (n * k) := by
      refine intervalIntegral.integral_mono_on zero_le_one (by simp)
        ((hB.continuous_log_norm_iter (n * k)).intervalIntegrable _ _) (fun x _ => ?_)
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (hnorm k x)
    simpa using this
  have hT := hB.tendsto_lyapunov (α := α)
  have hmul : Tendsto (fun k : ℕ => n * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hT' := hT.comp hmul
  have hlow : Real.log c / n ≤ lyapunov α B := by
    refine ge_of_tendsto hT' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [Function.comp]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ hn' (by push_cast; positivity)]
    have := hseq k
    push_cast
    nlinarith
  have : 0 < Real.log c / n := div_pos (Real.log_pos hc1) (by exact_mod_cast hn)
  linarith

/-- A uniformly hyperbolic analytic cocycle has positive Lyapunov exponent. -/
theorem L_pos_of_UH {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ} (h : UH α A) :
    0 < L α A 0 :=
  lyapunov_pos_of_isUH (hA.isSLCocycle_shift (by simpa using hA.pos)) h


/-! ### Helpers on real-analytic potentials -/

lemma IsRealAnalyticPotential.mono {δ δ' : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v)
    (h0 : 0 < δ') (h : δ' ≤ δ) : IsRealAnalyticPotential δ' v :=
  ⟨h0, hv.holo.mono (fun z hz => lt_of_lt_of_le hz h), hv.periodic, hv.real⟩

lemma isPreconnected_strip (δ : ℝ) : IsPreconnected (strip δ) := by
  have : strip δ = {c : ℂ | c.im < δ} ∩ {c : ℂ | -δ < c.im} := by
    ext z; simp only [strip, Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]; tauto
  rw [this]
  exact ((convex_halfSpace_im_lt δ).inter (convex_halfSpace_im_gt (-δ))).isPreconnected

lemma conj_mem_strip {δ : ℝ} {z : ℂ} (hz : z ∈ strip δ) : conj z ∈ strip δ := by
  simpa [strip] using hz

/-- A real-analytic potential satisfies `w(z̄) = conj (w z)` on its strip (identity theorem). -/
lemma IsRealAnalyticPotential.conj_eq {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w) :
    ∀ z ∈ strip δ, w (conj z) = conj (w z) := by
  set g : ℂ → ℂ := fun z => conj (w (conj z)) with hg
  have hgd : DifferentiableOn ℂ g (strip δ) := by
    intro z hz
    have h1 : DifferentiableAt ℂ w (conj z) :=
      hw.holo.differentiableAt ((isOpen_strip δ).mem_nhds (conj_mem_strip hz))
    have h2 : DifferentiableAt ℂ (conj ∘ w ∘ conj) z := by
      rw [differentiableAt_conj_conj_iff]; exact h1
    exact h2.differentiableWithinAt
  have hA1 : AnalyticOnNhd ℂ w (strip δ) := hw.holo.analyticOnNhd (isOpen_strip δ)
  have hA2 : AnalyticOnNhd ℂ g (strip δ) := hgd.analyticOnNhd (isOpen_strip δ)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), w z = g z := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rw [Complex.ofReal_zero] at this
        exact this
      · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact hpos.ne'
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    simp only [hg, Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.mpr (hw.real _)).symm
  have h0 : (0 : ℂ) ∈ strip δ := by simp [strip, hw.pos]
  have heq := hA1.eqOn_of_preconnected_of_frequently_eq hA2 (isPreconnected_strip δ) h0 hfreq
  intro z hz
  have := heq (conj_mem_strip hz)
  simpa [hg] using this

/-- Replace `w` off its strip by `0`: this makes it conjugation-symmetric everywhere. -/
lemma IsRealAnalyticPotential.symmetrize {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w) :
    ∃ w' : ℂ → ℂ, IsRealAnalyticPotential δ w' ∧ (∀ z, w' (conj z) = conj (w' z)) ∧
      ∀ z ∈ strip δ, w' z = w z := by
  classical
  refine ⟨Set.indicator (strip δ) w, ⟨hw.pos, ?_, ?_, ?_⟩, ?_,
    fun z hz => Set.indicator_of_mem hz w⟩
  · exact hw.holo.congr (fun z hz => Set.indicator_of_mem hz w)
  · intro z
    have hm : z + 1 ∈ strip δ ↔ z ∈ strip δ := by simp [strip]
    by_cases h : z ∈ strip δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h), hw.periodic]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  · intro x
    have hx : (x : ℂ) ∈ strip δ := by simp [strip, hw.pos]
    rw [Set.indicator_of_mem hx]; exact hw.real x
  · intro z
    have hm : conj z ∈ strip δ ↔ z ∈ strip δ := by simp [strip]
    by_cases h : z ∈ strip δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h), hw.conj_eq z h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h')), map_zero]

/-- A real-analytic potential is bounded on every smaller strip. -/
lemma IsRealAnalyticPotential.exists_bound {δ δ' : ℝ} {w : ℂ → ℂ}
    (hw : IsRealAnalyticPotential δ w) (h : δ' < δ) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ strip δ', ‖w z‖ ≤ C := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) '' (Icc (0 : ℝ) 1 ×ˢ Icc (-δ') δ')
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKs : K ⊆ strip δ := by
    rintro _ ⟨p, ⟨-, hp⟩, rfl⟩
    simp only [strip, Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add]
    rw [abs_lt]; constructor <;> linarith [hp.1, hp.2]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hw.holo.continuousOn.mono hKs)
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hper : Function.Periodic w 1 := hw.periodic
  have hz' : |z.im| < δ' := hz
  have hmem : z - ((⌊z.re⌋ : ℤ) : ℂ) * 1 ∈ K := by
    refine ⟨(z.re - ⌊z.re⌋, z.im), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact sub_nonneg.mpr (Int.floor_le _)
    · linarith [Int.lt_floor_add_one z.re]
    · linarith [neg_abs_le z.im]
    · linarith [le_abs_self z.im]
    · apply Complex.ext <;> simp
  have := hC _ hmem
  rw [hper.sub_int_mul_eq] at this
  exact this.trans (le_max_left _ _)

/-! ### A bound for the spectrum -/

/-- `Σ_{α,v} ⊆ [-(2 + M), 2 + M]` if `|v| ≤ M` on the real line. -/
lemma abs_le_of_mem_Sigma {α : ℝ} {v : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hv : ∀ t : ℝ, ‖v t‖ ≤ M)
    {E : ℝ} (hE : E ∈ Sigma α v) : |E| ≤ 2 + M := by
  have : Nontrivial (L2 ℤ) := ⟨⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, fun h => by
    have := congrArg (fun u : L2 ℤ => u 0) h
    simp at this⟩⟩
  have h1 := spectrum.norm_le_norm_of_mem (show (E : ℂ) ∈ spectrum ℂ (schrOp α v 0) from hE)
  have hb : ∀ (c : ℤ → ℂ) (σ : ℤ ≃ ℤ) (K : ℝ), 0 ≤ K → (∀ i, ‖c i‖ ≤ K) →
      ‖L2.weightedShift c σ‖ ≤ K := fun c σ K hK h => L2.norm_weightedShift_le hK h
  have h2 : ‖schrOp α v 0‖ ≤ 1 + 1 + M := by
    unfold schrOp jacobi
    exact norm_add₃_le.trans (add_le_add (add_le_add
      (hb _ _ _ zero_le_one (fun i => by simp)) (hb _ _ _ zero_le_one (fun i => by simp)))
      (hb _ _ _ hM (fun i => hv _)))
  have h3 : ‖(E : ℂ)‖ = |E| := by simp
  linarith

/-! ### The matrix `[[d, 0], [0, 0]]` -/

lemma norm_mat00_le (d : ℂ) : ‖(!![d, 0; 0, 0] : M2)‖ ≤ ‖d‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖(!![d, 0; 0, 0] : M2) i j‖₊) ≤ ‖d‖₊ := by
    apply Finset.sup_le
    intro i _
    fin_cases i <;> simp [Fin.sum_univ_two]
  exact_mod_cast this

/-! ### Consequences of the formula of Theorem `am1` -/

lemma le_L_of_formula {α : ℝ} {A : ℂ → M2} {c : ℝ}
    (h1 : ∀ ε, 0 ≤ ε → L α A ε = max (L α A 0) (c + 2 * Real.pi * ε)) : c ≤ L α A 0 := by
  have := le_max_right (L α A 0) (c + 2 * Real.pi * 0)
  rw [← h1 0 le_rfl] at this
  linarith

lemma accel_le_one_of_formula {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) {c : ℝ}
    (h1 : ∀ ε, 0 ≤ ε → L α A ε = max (L α A 0) (c + 2 * Real.pi * ε)) : accel α A ≤ 1 := by
  have hc := le_L_of_formula h1
  refine le_of_tendsto (quantized hA hα).1 ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hd : 0 < 2 * Real.pi * ε := mul_pos (mul_pos two_pos Real.pi_pos) hε'
  rw [div_le_one hd, h1 ε hε'.le]
  have := max_le (show L α A 0 ≤ L α A 0 + 2 * Real.pi * ε by linarith)
    (show c + 2 * Real.pi * ε ≤ L α A 0 + 2 * Real.pi * ε by linarith)
  linarith

/-- The abstract core of Corollary `am2`. -/
lemma am2_core {α : ℝ} (hα : Irrational α) {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    (hsym : IsRealSymmetric A) {c : ℝ}
    (h1 : ∀ ε, 0 ≤ ε → L α A ε = max (L α A 0) (c + 2 * Real.pi * ε)) {P : Prop}
    (hP : ¬ P ↔ UH α A) : max 0 c ≤ L α A 0 ∧ (L α A 0 = max 0 c ↔ P) := by
  have hlog := le_L_of_formula h1
  have hnn : 0 ≤ L α A 0 := hA.L_nonneg α (by simpa using hA.pos)
  refine ⟨max_le hnn hlog, ⟨fun heq => ?_, fun hE => ?_⟩⟩
  · by_contra hE
    have huh := hP.mp hE
    have hpos : 0 < L α A 0 := L_pos_of_UH hA huh
    obtain ⟨η, hη, a, b, hab⟩ := uh_imp_regular hA hα huh
    have hL0 : L α A 0 = c := by
      rcases le_total 0 c with h | h
      · rw [heq, max_eq_right h]
      · rw [max_eq_left h] at heq; linarith
    have e1 := hab (η / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    have e2 := hab (-(η / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    have e0 := hab 0 (by simpa using hη)
    rw [L_neg hsym] at e2
    have hb : b * η = 0 := by linarith
    have hb0 : b = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · linarith
    subst hb0
    have hmax := le_max_right (L α A 0) (c + 2 * Real.pi * (η / 2))
    rw [← h1 (η / 2) (by linarith)] at hmax
    have := mul_pos Real.pi_pos hη
    linarith
  · by_contra hne
    have hgt : max 0 c < L α A 0 := lt_of_le_of_ne (max_le hnn hlog) (Ne.symm hne)
    have hpos : 0 < L α A 0 := lt_of_le_of_lt (le_max_left _ _) hgt
    have hlt : c < L α A 0 := lt_of_le_of_lt (le_max_right _ _) hgt
    have key : ∀ t, 0 ≤ t → t < (L α A 0 - c) / (2 * Real.pi) → L α A t = L α A 0 := by
      intro t ht htl
      rw [h1 t ht]
      apply max_eq_left
      rw [lt_div_iff₀ (by positivity)] at htl
      linarith
    have hreg : IsRegular α A := by
      refine ⟨(L α A 0 - c) / (2 * Real.pi), div_pos (by linarith) (by positivity),
        L α A 0, 0, fun ε hε => ?_⟩
      rcases le_total 0 ε with h | h
      · rw [key ε h (lt_of_le_of_lt (le_abs_self ε) hε)]; ring
      · have e := L_neg hsym α (-ε)
        rw [neg_neg] at e
        rw [e, key (-ε) (by linarith) (lt_of_le_of_lt (neg_le_abs ε) hε)]; ring
    exact hP.mpr ((uh_iff_regular hA hα hpos).mp hreg) hE

/-! ### Proof of Theorem `am1` -/

lemma norm_schrMat_le (a : ℂ) : ‖(!![a, -1; 1, 0] : M2)‖ ≤ ‖a‖ + 1 := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖(!![a, -1; 1, 0] : M2) i j‖₊) ≤
      ‖a‖₊ + 1 := by
    apply Finset.sup_le
    intro i _
    fin_cases i <;> simp [Fin.sum_univ_two]
  exact_mod_cast this

/-- On the line `Im z = ε ≥ 0`, `|E - λ v(z)|` is `λ e^{2πε}` up to an error `|E| + λ`. -/
lemma am_entry_bounds {lam : ℝ} (hlam : 0 < lam) (E : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    lam * Real.exp (2 * Real.pi * ε) - (|E| + lam) ≤ ‖(E : ℂ) - amPotScaled lam (x + ε * I)‖ ∧
      ‖(E : ℂ) - amPotScaled lam (x + ε * I)‖ ≤ lam * Real.exp (2 * Real.pi * ε) + (|E| + lam) := by
  have hsplit : amPotScaled lam (x + ε * I) =
      lam * Complex.exp (2 * Real.pi * (x + ε * I) * I) +
        lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I) := by
    simp only [amPotScaled, amPot, Complex.two_cos]; ring
  have hX : ‖Complex.exp (2 * Real.pi * (x + ε * I) * I)‖ = Real.exp (-(2 * Real.pi * ε)) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hY : ‖Complex.exp (-(2 * Real.pi * (x + ε * I)) * I)‖ = Real.exp (2 * Real.pi * ε) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hX1 : Real.exp (-(2 * Real.pi * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg Real.pi_pos.le hε
    linarith
  have hlamn : ‖(lam : ℂ)‖ = lam := by simp [abs_of_pos hlam]
  rw [hsplit]
  have nX : ‖(lam : ℂ) * Complex.exp (2 * Real.pi * (x + ε * I) * I)‖ ≤ lam := by
    rw [norm_mul, hlamn, hX]; exact mul_le_of_le_one_right hlam.le hX1
  have nY : ‖(lam : ℂ) * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I)‖ =
      lam * Real.exp (2 * Real.pi * ε) := by
    rw [norm_mul, hlamn, hY]
  have hEn : ‖(E : ℂ)‖ = |E| := by simp
  constructor
  · have h1 := norm_sub_le ((E : ℂ) - lam * Complex.exp (2 * Real.pi * (x + ε * I) * I))
      ((E : ℂ) - (lam * Complex.exp (2 * Real.pi * (x + ε * I) * I) +
        lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I)))
    have e : ((E : ℂ) - lam * Complex.exp (2 * Real.pi * (x + ε * I) * I)) -
        ((E : ℂ) - (lam * Complex.exp (2 * Real.pi * (x + ε * I) * I) +
          lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I))) =
        lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I) := by ring
    rw [e, nY] at h1
    have h3 := norm_sub_le (E : ℂ) (lam * Complex.exp (2 * Real.pi * (x + ε * I) * I))
    linarith
  · have h2 := norm_sub_le (E : ℂ) (lam * Complex.exp (2 * Real.pi * (x + ε * I) * I) +
      lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I))
    have h3 := norm_add_le ((lam : ℂ) * Complex.exp (2 * Real.pi * (x + ε * I) * I))
      (lam * Complex.exp (-(2 * Real.pi * (x + ε * I)) * I))
    linarith

/-- Upper bound `L(α, A_ε) ≤ log (λ e^{2πε} + |E| + λ + 1)`. -/
lemma am_L_upper {α : ℝ} {lam : ℝ} (hlam : 0 < lam) (E : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    L α (schr (eShift E (amPotScaled lam))) ε ≤
      Real.log (lam * Real.exp (2 * Real.pi * ε) + (|E| + lam + 1)) := by
  have hA := (amPot_isRealAnalyticPotential lam (show (0 : ℝ) < |ε| + 1 by positivity)).schr E
  have hS := hA.isSLCocycle_shift (ε := ε) (by linarith)
  have h1 := hS.lyapunov_le (α := α) 1 one_ne_zero
  have hρ0 : 0 < lam * Real.exp (2 * Real.pi * ε) := mul_pos hlam (Real.exp_pos _)
  have hint : lyapSeq α (shift (schr (eShift E (amPotScaled lam))) ε) 1 ≤
      ∫ _ in (0 : ℝ)..1, Real.log (lam * Real.exp (2 * Real.pi * ε) + (|E| + lam + 1)) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hS.continuous_log_norm_iter 1).intervalIntegrable _ _) (by simp) (fun x _ => ?_)
    have hpos := hS.one_le_norm_iter (α := α) 1 x
    refine Real.log_le_log (by linarith) ?_
    have hit : iter α (shift (schr (eShift E (amPotScaled lam))) ε) 1 x =
        !![(E : ℂ) - amPotScaled lam (x + ε * I), -1; 1, 0] := by
      simp [iter, shift, schr, eShift]
    rw [hit]
    refine (norm_schrMat_le _).trans ?_
    have := (am_entry_bounds hlam E hε x).2
    linarith
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hint
  simp only [Nat.cast_one, div_one] at h1
  exact h1.trans hint

/-- Lower bound via an invariant cone: `log (λ e^{2πε} - |E| - λ - 1) ≤ L(α, A_ε)`. -/
lemma am_L_lower {α : ℝ} {lam : ℝ} (hlam : 0 < lam) (E : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 1 ≤ lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1)) :
    Real.log (lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1)) ≤
      L α (schr (eShift E (amPotScaled lam))) ε := by
  have hA := (amPot_isRealAnalyticPotential lam (show (0 : ℝ) < |ε| + 1 by positivity)).schr E
  have hS := hA.isSLCocycle_shift (ε := ε) (by linarith)
  have hBx : ∀ y : ℝ, shift (schr (eShift E (amPotScaled lam))) ε y =
      !![(E : ℂ) - amPotScaled lam (y + ε * I), -1; 1, 0] := by
    intro y; simp [shift, schr, eShift]
  have hm0 : (0 : ℝ) ≤ lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1) := by linarith
  have hcone : ∀ n : ℕ, ∀ x,
      ‖iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 1 0‖ ≤
        ‖iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 0‖ ∧
      (lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1)) ^ n ≤
        ‖iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 0‖ := by
    intro n
    induction n with
    | zero => intro x; simp [iter]
    | succ n ih =>
      intro x
      obtain ⟨h1, h2⟩ := ih x
      have ha := (am_entry_bounds hlam E hε (x + n * α)).1
      have e0 : iter α (shift (schr (eShift E (amPotScaled lam))) ε) (n + 1) x 0 0 =
          ((E : ℂ) - amPotScaled lam ((x + n * α : ℝ) + ε * I)) *
            iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 0 -
            iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 1 0 := by
        rw [iter, hBx, Matrix.mul_apply, Fin.sum_univ_two]
        simp [sub_eq_add_neg]
      have e1 : iter α (shift (schr (eShift E (amPotScaled lam))) ε) (n + 1) x 1 0 =
          iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 0 := by
        rw [iter, hBx, Matrix.mul_apply, Fin.sum_univ_two]
        simp
      rw [e0, e1]
      generalize ((E : ℂ) - amPotScaled lam ((x + n * α : ℝ) + ε * I)) = a at ha ⊢
      generalize iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 0 = p at h1 h2 ⊢
      generalize iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 1 0 = q at h1 h2 ⊢
      have hlow : ‖a‖ * ‖p‖ - ‖q‖ ≤ ‖a * p - q‖ := by
        have := norm_sub_norm_le (a * p) q
        rwa [norm_mul] at this
      have hp0 := norm_nonneg p
      have hk : 1 * ‖p‖ ≤ (‖a‖ - 1) * ‖p‖ := mul_le_mul_of_nonneg_right (by linarith) hp0
      constructor
      · linarith
      · rw [pow_succ]
        have := mul_le_mul h2 (show lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1) ≤
          ‖a‖ - 1 by linarith) hm0 hp0
        linarith
  have hnorm : ∀ n x, (lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1)) ^ n ≤
      ‖iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x‖ := by
    intro n x
    have := row_sum_le_norm (iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x) 0
    linarith [(hcone n x).2,
      norm_nonneg (iter α (shift (schr (eShift E (amPotScaled lam))) ε) n x 0 1)]
  have hseq : ∀ n : ℕ, (n : ℝ) * Real.log (lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1))
      ≤ lyapSeq α (shift (schr (eShift E (amPotScaled lam))) ε) n := by
    intro n
    have : ∫ _ in (0 : ℝ)..1,
        (n : ℝ) * Real.log (lam * Real.exp (2 * Real.pi * ε) - (|E| + lam + 1)) ≤
          lyapSeq α (shift (schr (eShift E (amPotScaled lam))) ε) n := by
      refine intervalIntegral.integral_mono_on zero_le_one (by simp)
        ((hS.continuous_log_norm_iter n).intervalIntegrable _ _) (fun x _ => ?_)
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos (by linarith) n) (hnorm n x)
    simpa using this
  have hT := hS.tendsto_lyapunov (α := α)
  show _ ≤ lyapunov α (shift (schr (eShift E (amPotScaled lam))) ε)
  refine ge_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  linarith [hseq n]

lemma mul_one_add_div {ρ K : ℝ} (hρ : ρ ≠ 0) (s : ℝ) : ρ * (1 + s * (K / ρ)) = ρ + s * K := by
  rw [mul_add, mul_one, mul_left_comm, mul_div_cancel₀ K hρ]

/-- From two-sided logarithmic bounds, `L(α, A_ε) - 2πε → log λ` as `ε → ∞`. -/
lemma tendsto_of_log_bounds {F : ℝ → ℝ} {lam K : ℝ} (hlam : 0 < lam) (hK : 1 ≤ K)
    (hup : ∀ t, 0 ≤ t → F t ≤ Real.log (lam * Real.exp (2 * Real.pi * t) + K))
    (hlow : ∀ t, 0 ≤ t → 1 ≤ lam * Real.exp (2 * Real.pi * t) - K →
      Real.log (lam * Real.exp (2 * Real.pi * t) - K) ≤ F t) :
    Tendsto (fun t => F t - 2 * Real.pi * t) atTop (𝓝 (Real.log lam)) := by
  have hρpos : ∀ t : ℝ, 0 < lam * Real.exp (2 * Real.pi * t) :=
    fun t => mul_pos hlam (Real.exp_pos _)
  have hlogρ : ∀ t : ℝ,
      Real.log (lam * Real.exp (2 * Real.pi * t)) = Real.log lam + 2 * Real.pi * t := fun t => by
    rw [Real.log_mul hlam.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hρ : Tendsto (fun t : ℝ => lam * Real.exp (2 * Real.pi * t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi))).const_mul_atTop hlam
  have hu : Tendsto (fun t : ℝ => K / (lam * Real.exp (2 * Real.pi * t))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hρ
  have hl : ∀ s : ℝ, Tendsto (fun t : ℝ => Real.log lam +
      Real.log (1 + s * (K / (lam * Real.exp (2 * Real.pi * t))))) atTop
        (𝓝 (Real.log lam)) := by
    intro s
    have h1 : Tendsto (fun t : ℝ => 1 + s * (K / (lam * Real.exp (2 * Real.pi * t)))) atTop
        (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (hu.const_mul s)
      simpa using this
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    have := (tendsto_const_nhds (x := Real.log lam)).add h2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hl (-1)) (hl 1) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0, hρ.eventually_ge_atTop (2 * K)] with t ht hρt
    have hρt' := hρpos t
    have h := hlow t ht (by linarith)
    have hpos1 : 0 < 1 + -1 * (K / (lam * Real.exp (2 * Real.pi * t))) := by
      have : K / (lam * Real.exp (2 * Real.pi * t)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hρt']; linarith
      linarith
    have e : lam * Real.exp (2 * Real.pi * t) - K =
        lam * Real.exp (2 * Real.pi * t) * (1 + -1 * (K / (lam * Real.exp (2 * Real.pi * t)))) := by
      rw [mul_one_add_div hρt'.ne']; ring
    rw [e, Real.log_mul hρt'.ne' hpos1.ne', hlogρ] at h
    linarith
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hρt' := hρpos t
    have h := hup t ht
    have hpos1 : 0 < 1 + 1 * (K / (lam * Real.exp (2 * Real.pi * t))) := by
      have := div_pos (by linarith : (0 : ℝ) < K) hρt'
      linarith
    have e : lam * Real.exp (2 * Real.pi * t) + K =
        lam * Real.exp (2 * Real.pi * t) * (1 + 1 * (K / (lam * Real.exp (2 * Real.pi * t)))) := by
      rw [mul_one_add_div hρt'.ne']; ring
    rw [e, Real.log_mul hρt'.ne' hpos1.ne', hlogρ] at h
    linarith

/-- The real-analysis core of Theorem `am1`: an even convex function, piecewise affine with
slopes in `2πℤ` and asymptotic to `c + 2πε`, equals `max (f 0) (c + 2πε)` on `[0, ∞)`. -/
lemma am1_core {f : ℝ → ℝ} {c : ℝ} (heven : ∀ t, f (-t) = f t)
    (hsl : ∀ x y z, x < y → y < z → (f y - f x) * (z - y) ≤ (f z - f y) * (y - x))
    (haff : ∀ t, 0 < t → ∃ η > 0, ∃ k : ℤ, f (t + η) = f t + 2 * Real.pi * k * η)
    (hlim : Tendsto (fun t => f t - 2 * Real.pi * t) atTop (𝓝 c)) {ε : ℝ} (hε : 0 ≤ ε) :
    f ε = max (f 0) (c + 2 * Real.pi * ε) := by
  have hpi := Real.pi_pos
  have hmin : ∀ t, 0 ≤ t → f 0 ≤ f t := by
    intro t ht
    rcases ht.eq_or_lt with h | h
    · rw [← h]
    · have h1 := hsl (-t) 0 t (by linarith) h
      rw [heven] at h1
      by_contra hc
      push_neg at hc
      have := mul_pos (sub_pos.mpr hc) h
      linarith
  have hslope : ∀ s t, s < t → f t - f s ≤ 2 * Real.pi * (t - s) := by
    intro s t hst
    by_contra hcon
    push_neg at hcon
    have hDpos : 0 < f t - f s - 2 * Real.pi * (t - s) := by linarith
    have hG : ∀ᶠ T in atTop, f T - 2 * Real.pi * T < c + 1 :=
      hlim.eventually (gt_mem_nhds (by linarith))
    have hlin : Tendsto (fun T : ℝ => (f t - f s - 2 * Real.pi * (t - s)) * (T + -t)) atTop
        atTop :=
      Tendsto.const_mul_atTop hDpos (tendsto_atTop_add_const_right atTop (-t) tendsto_id)
    obtain ⟨T, ⟨hGT, htT⟩, hMT⟩ := ((hG.and (eventually_gt_atTop t)).and
      (hlin.eventually_gt_atTop ((c + 1 - (f t - 2 * Real.pi * t)) * (t - s)))).exists
    have h := hsl s t T hst htT
    have h2 : (f T - 2 * Real.pi * T) * (t - s) < (c + 1) * (t - s) :=
      mul_lt_mul_of_pos_right hGT (by linarith)
    linarith
  have hGc : ∀ t, c ≤ f t - 2 * Real.pi * t := by
    intro t
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop t] with T hT
    have := hslope t T hT
    linarith
  have hlow : max (f 0) (c + 2 * Real.pi * ε) ≤ f ε :=
    max_le (hmin ε hε) (by linarith [hGc ε])
  refine le_antisymm ?_ hlow
  rcases hε.eq_or_lt with h0 | hpos
  · rw [← h0]; exact le_max_left _ _
  · obtain ⟨η, hη, k, hk⟩ := haff ε hpos
    rcases le_or_gt k 0 with hk0 | hk1
    · have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      have h := hsl 0 ε (ε + η) hpos (by linarith)
      rw [hk] at h
      have h3 : (k : ℝ) * (2 * Real.pi * η * ε) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hk0' (mul_pos (mul_pos (mul_pos two_pos hpi) hη) hpos).le
      have h4 : (f ε - f 0) * η ≤ 0 := by linarith
      have h5 : f ε ≤ f 0 := by
        by_contra hc
        push_neg at hc
        have := mul_pos (sub_pos.mpr hc) hη
        linarith
      exact h5.trans (le_max_left _ _)
    · have hk1' : (1 : ℝ) ≤ k := by
        have : (1 : ℤ) ≤ k := by omega
        exact_mod_cast this
      have hGε : f ε - 2 * Real.pi * ε ≤ c := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [eventually_gt_atTop (ε + η)] with T hT
        have h := hsl ε (ε + η) T (by linarith) hT
        rw [hk] at h
        have h7 : (2 * Real.pi * k * (T - (ε + η))) * η ≤
            (f T - (f ε + 2 * Real.pi * k * η)) * η := by linarith
        have h6 := le_of_mul_le_mul_right h7 hη
        have h8 : 2 * Real.pi * (T - ε) * 1 ≤ 2 * Real.pi * (T - ε) * k :=
          mul_le_mul_of_nonneg_left hk1' (mul_nonneg (by linarith) (by linarith))
        linarith
      linarith [le_max_right (f 0) (c + 2 * Real.pi * ε)]

/-- **Theorem `am1`.** -/
theorem am1 {α : ℝ} (hα : Irrational α) {lam : ℝ} (hlam : 0 < lam) (E : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    L α (schr (eShift E (amPotScaled lam))) ε =
      max (L α (schr (eShift E (amPotScaled lam))) 0) (Real.log lam + 2 * Real.pi * ε) := by
  have hAδ : ∀ δ > 0, IsAnalyticCocycle δ (schr (eShift E (amPotScaled lam))) :=
    fun δ hδ => (amPot_isRealAnalyticPotential lam hδ).schr E
  have hsym : IsRealSymmetric (schr (eShift E (amPotScaled lam))) :=
    schr_isRealSymmetric (amPotScaled_conj lam) E
  refine am1_core (f := L α (schr (eShift E (amPotScaled lam)))) (fun t => L_neg hsym α t)
    ?_ ?_ ?_ hε
  · intro x y z hxy hyz
    have hc := L_convexOn (hAδ (|x| + |z| + 1) (by positivity)) α
    have hx : x ∈ Ioo (-(|x| + |z| + 1)) (|x| + |z| + 1) := by
      constructor <;> linarith [neg_abs_le x, le_abs_self x, abs_nonneg z]
    have hz : z ∈ Ioo (-(|x| + |z| + 1)) (|x| + |z| + 1) := by
      constructor <;> linarith [neg_abs_le z, le_abs_self z, abs_nonneg x]
    have := hc.slope_mono_adjacent hx hz hxy hyz
    rwa [div_le_div_iff₀ (by linarith) (by linarith)] at this
  · intro t ht
    have hA := hAδ (|t| + 1) (by positivity)
    obtain ⟨η, hη, haff⟩ := L_piecewise_affine hA hα (ε := t) (by linarith)
    obtain ⟨k, hk⟩ := (quantized (hA.cshift (ε := t) (by linarith)) hα).2
    refine ⟨η, hη, k, ?_⟩
    rw [haff (t + η) ⟨by linarith, le_rfl⟩, hk]
    ring
  · exact tendsto_of_log_bounds hlam (by linarith [abs_nonneg E] : (1 : ℝ) ≤ |E| + lam + 1)
      (fun t ht => am_L_upper hlam E ht) (fun t ht hm => am_L_lower hlam E ht hm)

/-- **Corollary `am2`** (Aubry–André formula). -/
theorem am2 {α : ℝ} (hα : Irrational α) {lam : ℝ} (hlam : 0 < lam) (E : ℝ) :
    max 0 (Real.log lam) ≤ LE α (amPotScaled lam) E ∧
      (LE α (amPotScaled lam) E = max 0 (Real.log lam) ↔ E ∈ Sigma α (amPotScaled lam)) := by
  have hv := amPot_isRealAnalyticPotential lam one_pos
  exact am2_core hα (hv.schr E) (schr_isRealSymmetric (amPotScaled_conj lam) E)
    (fun ε hε => am1 hα hlam E hε) (johnson hv hα E)

/-! ### The Example Theorem -/

omit hH in
/-- `v_ε = λ v + ε w`. -/
def vPert (lam ε : ℝ) (w : ℂ → ℂ) : ℂ → ℂ := fun z => amPotScaled lam z + ε * w z

lemma vPert_pot {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w) (lam ε : ℝ) :
    IsRealAnalyticPotential δ (vPert lam ε w) := by
  have h0 := amPot_isRealAnalyticPotential lam hw.pos
  refine ⟨hw.pos, h0.holo.add ((differentiableOn_const _).mul hw.holo), fun z => ?_, fun x => ?_⟩
  · simp only [vPert, h0.periodic, hw.periodic]
  · simp [vPert, Complex.add_im, Complex.mul_im, h0.real x, hw.real x]

lemma Sigma_congr {α : ℝ} {v v' : ℂ → ℂ} (h : ∀ x : ℝ, v x = v' x) :
    Sigma α v = Sigma α v' := by
  ext E
  simp only [Sigma, schrOp, jacobi, h, Set.mem_ofPred_eq]

lemma LE_congr {α : ℝ} {v v' : ℂ → ℂ} (h : ∀ x : ℝ, v x = v' x) : LE α v = LE α v' := by
  funext E
  have : shift (schr (eShift E v)) 0 = shift (schr (eShift E v')) 0 := by
    funext x
    simp only [shift, schr, eShift, Complex.ofReal_zero, zero_mul, add_zero, h]
  simp only [LE, L, this]

/-- The energy family `E ↦ A^{(E - v)}` is a real-analytic family of analytic cocycles. -/
lemma energyFamily {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) :
    IsAnalyticCocycleFamily δ univ (fun E : ℝ => schr (eShift E v)) := by
  refine ⟨isOpen_univ, fun E _ => hv.schr E, ?_⟩
  have hform : (fun q : ℝ × ℂ => schr (eShift q.1 v) q.2) =
      fun q => ((q.1 : ℂ) - v q.2) • (!![1, 0; 0, 0] : M2) + !![0, -1; 1, 0] := by
    funext q; ext i j; fin_cases i <;> fin_cases j <;> simp [schr, eShift]
  rw [hform]
  rintro ⟨E, z⟩ ⟨-, hz⟩
  have hvz : AnalyticAt ℂ v z := hv.holo.analyticOnNhd (isOpen_strip δ) z hz
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℂ => (q.1 : ℂ)) (E, z) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℂ)).analyticAt _
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℂ => v q.2) (E, z) :=
    (hvz.restrictScalars (𝕜 := ℝ)).comp analyticAt_snd
  exact ((h1.sub h2).smul analyticAt_const).add analyticAt_const

/-- The compactness part of the paper's Lemma: for `ε` small, every `E ∈ Σ_{α,v_ε}` has
`L > 0` and `ω ≤ 1`. -/
theorem example_key {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ strip δ, ‖w z‖ ≤ C) {lam : ℝ} (hlam : 1 < lam) {α : ℝ}
    (hα : Irrational α) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ → ∀ E ∈ Sigma α (vPert lam ε w),
      0 < LE α (vPert lam ε w) E ∧ accel α (schr (eShift E (vPert lam ε w))) ≤ 1 := by
  have hlam0 : 0 < lam := by linarith
  have hδ := hw.pos
  have hV : ∀ ε, IsRealAnalyticPotential δ (vPert lam ε w) := fun ε => vPert_pot hw lam ε
  obtain ⟨C₀, hC₀0, hC₀⟩ := (amPot_isRealAnalyticPotential lam
    (by linarith : (0 : ℝ) < δ + 1)).exists_bound (by linarith : δ < δ + 1)
  by_contra hcon
  push_neg at hcon
  choose es hes Es hEs hbad using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hR : ∀ n, Es n ∈ Icc (-(2 + (C₀ + C))) (2 + (C₀ + C)) := by
    intro n
    have hes1 : |es n| ≤ 1 := by
      refine (hes n).le.trans ?_
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hb : ∀ t : ℝ, ‖vPert lam (es n) w t‖ ≤ C₀ + C := by
      intro t
      have ht : (t : ℂ) ∈ strip δ := by simp [strip, hδ]
      calc ‖vPert lam (es n) w t‖
          ≤ ‖amPotScaled lam t‖ + ‖((es n : ℝ) : ℂ) * w t‖ := norm_add_le _ _
        _ ≤ C₀ + 1 * C := by
          gcongr
          · exact hC₀ _ ht
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul hes1 (hC _ ht) (norm_nonneg _) zero_le_one
        _ = C₀ + C := by ring
    exact abs_le.mp (abs_le_of_mem_Sigma (by linarith) hb (hEs n))
  obtain ⟨E, -, φ, hφ, hEφ⟩ := isCompact_Icc.tendsto_subseq hR
  have hes0 : Tendsto es atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hes n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hesφ : Tendsto (es ∘ φ) atTop (𝓝 0) := hes0.comp hφ.tendsto_atTop
  have hA : IsAnalyticCocycle δ (schr (eShift E (amPotScaled lam))) :=
    (amPot_isRealAnalyticPotential lam hδ).schr E
  have hAs : ∀ k, IsAnalyticCocycle δ (schr (eShift (Es (φ k)) (vPert lam (es (φ k)) w))) :=
    fun k => (hV _).schr _
  have hconv : TendstoUniformlyOn
      (fun k => schr (eShift (Es (φ k)) (vPert lam (es (φ k)) w)))
      (schr (eShift E (amPotScaled lam))) atTop (strip δ) := by
    refine Metric.tendstoUniformlyOn_iff.mpr ?_
    intro η hη
    have h1 : Tendsto (fun k => |E - Es (φ k)| + |es (φ k)| * C) atTop (𝓝 0) := by
      have a : Tendsto (fun k => |E - Es (φ k)|) atTop (𝓝 0) := by
        have := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => E) atTop (𝓝 E)).sub hEφ).abs
        simpa using this
      have b : Tendsto (fun k => |es (φ k)| * C) atTop (𝓝 0) := by
        simpa using hesφ.abs.mul_const C
      simpa using a.add b
    filter_upwards [h1.eventually (gt_mem_nhds hη)] with k hk
    intro z hz
    rw [dist_eq_norm]
    have hd : schr (eShift E (amPotScaled lam)) z -
        schr (eShift (Es (φ k)) (vPert lam (es (φ k)) w)) z =
        !![(E : ℂ) - Es (φ k) + es (φ k) * w z, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [schr, eShift, vPert] <;> ring
    rw [hd]
    refine (norm_mat00_le _).trans_lt (lt_of_le_of_lt ?_ hk)
    calc ‖(E : ℂ) - Es (φ k) + es (φ k) * w z‖
        ≤ ‖(E : ℂ) - Es (φ k)‖ + ‖((es (φ k) : ℝ) : ℂ) * w z‖ := norm_add_le _ _
      _ ≤ |E - Es (φ k)| + |es (φ k)| * C := by
        gcongr
        · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg _)
  have hform : ∀ ε, 0 ≤ ε → L α (schr (eShift E (amPotScaled lam))) ε =
      max (L α (schr (eShift E (amPotScaled lam))) 0) (Real.log lam + 2 * Real.pi * ε) :=
    fun ε hε => am1 hα hlam0 E hε
  have hLA : 0 < L α (schr (eShift E (amPotScaled lam))) 0 :=
    lt_of_lt_of_le (Real.log_pos hlam) (le_L_of_formula hform)
  have hacc := accel_le_one_of_formula hA hα hform
  have hjks := jks_continuity hA hα hAs tendsto_const_nhds hconv
  have husc := accel_usc hA hα hAs (fun _ => hα) tendsto_const_nhds hconv
  obtain ⟨k, hk1, hk2⟩ := ((hjks.eventually (lt_mem_nhds hLA)).and husc).exists
  exact (not_lt.mpr (le_trans hk2 hacc)) (hbad (φ k) hk1)

/-- The rest of the paper's Lemma and the conclusion via Proposition `pluri`, for a
conjugation-symmetric `w`. -/
theorem example_main {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w)
    (hsym : ∀ z, w (conj z) = conj (w z)) {lam : ℝ} {α : ℝ} (hα : Irrational α) (ε : ℝ)
    (hkey : ∀ E ∈ Sigma α (vPert lam ε w),
      0 < LE α (vPert lam ε w) E ∧ accel α (schr (eShift E (vPert lam ε w))) ≤ 1) :
    (∀ E ∈ Sigma α (vPert lam ε w), 0 < LE α (vPert lam ε w) E) ∧
      AnalyticOnSet (LE α (vPert lam ε w)) (Sigma α (vPert lam ε w)) := by
  have hV := vPert_pot hw lam ε
  have hVsym : ∀ z, vPert lam ε w (conj z) = conj (vPert lam ε w z) := by
    intro z; simp [vPert, amPotScaled_conj, hsym]
  have hone : ∀ E ∈ Sigma α (vPert lam ε w),
      accel α (schr (eShift E (vPert lam ε w))) = ((1 : ℤ) : ℝ) := by
    intro E hE
    obtain ⟨hpos, hle⟩ := hkey E hE
    have hA := hV.schr E
    have hsE := schr_isRealSymmetric hVsym E
    have hnn := accel_nonneg hA hsE α
    obtain ⟨k, hk⟩ := (quantized hA hα).2
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hreg := (isRegular_iff_accel_eq_zero hA hsE hα).mpr (by simpa using hk)
      exact ((johnson hV hα E).mpr ((uh_iff_regular hA hα hpos).mp hreg)) hE
    have h1 : (k : ℝ) ≤ 1 := by rw [← hk]; exact hle
    have h2 : (0 : ℝ) ≤ k := by rw [← hk]; exact hnn
    have : k = 1 := by
      have : k ≤ 1 := by exact_mod_cast h1
      have : 0 ≤ k := by exact_mod_cast h2
      omega
    rw [hk, this]
  have hfam := energyFamily hV
  obtain ⟨hopen, hana⟩ := pluri_open_analytic hfam α 1
  refine ⟨fun E hE => (hkey E hE).1, ?_⟩
  intro p hp
  have hmem := pluri_mem (hV.schr p) hα (hone p hp) one_ne_zero
  refine ⟨_, hopen.mem_nhds ⟨trivial, hmem.2.1⟩, _, hana, ?_⟩
  rintro y ⟨hy, -⟩
  exact (pluri_mem (hV.schr y) hα (hone y hy) one_ne_zero).2.2

/-- **Example Theorem.** -/
theorem example_theorem {δ : ℝ} {w : ℂ → ℂ} (hw : IsRealAnalyticPotential δ w) {lam : ℝ}
    (hlam : 1 < lam) {α : ℝ} (hα : Irrational α) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      let vε : ℂ → ℂ := fun z => amPotScaled lam z + ε * w z
      (∀ E ∈ Sigma α vε, 0 < LE α vε E) ∧ AnalyticOnSet (LE α vε) (Sigma α vε) := by
  obtain ⟨w₁, hw₁, hsym₁, hagree⟩ := hw.symmetrize
  have hδ := hw.pos
  have hw₂ : IsRealAnalyticPotential (δ / 2) w₁ := hw₁.mono (by linarith) (by linarith)
  obtain ⟨C, hC0, hC⟩ := hw₁.exists_bound (show δ / 2 < δ by linarith)
  obtain ⟨ε₀, hε₀, hkey⟩ := example_key hw₂ hC0 hC hlam hα
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  have hreal : ∀ x : ℝ, (fun z => amPotScaled lam z + ε * w z) (x : ℂ) = vPert lam ε w₁ x := by
    intro x
    have hx : (x : ℂ) ∈ strip δ := by simp [strip, hδ]
    simp only [vPert, hagree x hx]
  show (∀ E ∈ Sigma α (fun z => amPotScaled lam z + ε * w z),
      0 < LE α (fun z => amPotScaled lam z + ε * w z) E) ∧
    AnalyticOnSet (LE α (fun z => amPotScaled lam z + ε * w z))
      (Sigma α (fun z => amPotScaled lam z + ε * w z))
  rw [Sigma_congr (v := fun z => amPotScaled lam z + ε * w z) hreal,
    LE_congr (v := fun z => amPotScaled lam z + ε * w z) hreal]
  exact example_main hw₂ hsym₁ hα ε (hkey ε hε)

end AvilaGlobal
