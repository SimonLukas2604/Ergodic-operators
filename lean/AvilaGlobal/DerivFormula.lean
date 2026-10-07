import AvilaGlobal.UHOpen
import AvilaGlobal.UniformHyperbolicity

/-!
# The derivative of the Lyapunov exponent on `𝒰ℋ`  (Avila, *Global theory I*, §3.2)

`derivFormula_proof : DerivFormulaClaim`, proved directly, without `[Hypotheses]`, for every
frequency `α` and continuous `A`, `w`.

* `DerivFormulaAux.lyap_of_split`: `L(α, X) = ∫ log |ℓ|` when `X` has continuous invariant
  directions `u, s` with `X u = ℓ u(·+α)` and `|ℓ| ≥ 1`.
* `DerivFormulaAux.adapt_frame`: rescaling the frame `B` by `diag(φ, φ⁻¹)` (an adapted metric)
  makes the expanding multiplier satisfy `|λ| ≥ ρ > 1` pointwise, without changing `ulc(B⁻¹MB)`.
* `DerivFormulaAux.graphs_exist`: invariant unstable/stable graphs of size `≤ r` for a
  perturbation of a diagonal hyperbolic cocycle (graph transform `UHOpenAux.graph_fixed`).
* `DerivFormulaAux.core`: with `r = κ|t|`, `λ_t = λ(1 + t·ulc(B⁻¹wB) + o(t))` uniformly, hence
  the derivative.
-/

noncomputable section
open scoped Matrix.Norms.Operator
open Matrix Filter Topology Complex Set Function

namespace AvilaGlobal
open AMO

namespace DerivFormulaAux
open UHOpenAux

lemma norm_M2_le_entries (M : M2) {K : ℝ} (hK : 0 ≤ K) (h : ∀ i j, ‖M i j‖ ≤ K) :
    ‖M‖ ≤ 2 * K := by
  have hrow : ∀ i, ‖M i 0‖ + ‖M i 1‖ ≤ 2 * K := fun i => by linarith [h i 0, h i 1]
  rw [linfty_opNorm_def]
  have : ((Finset.univ : Finset (Fin 2)).sup fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) ≤
      ⟨2 * K, by positivity⟩ := by
    refine Finset.sup_le fun i _ => ?_
    refine NNReal.coe_le_coe.1 ?_
    change _ ≤ 2 * K
    simpa [Fin.sum_univ_two] using hrow i
  exact_mod_cast this

lemma entry_le_mulVec (M : M2) (i j : Fin 2) :
    ‖M i j‖ ≤ ‖M *ᵥ Pi.single j 1‖ := by
  have : (M *ᵥ Pi.single j 1) i = M i j := by
    simp [Matrix.mulVec_single]
  rw [← this]; exact norm_le_pi_norm _ i

lemma per_pos_min {g : ℝ → ℝ} (hg : Continuous g) (hp : Periodic g 1) {b : ℝ}
    (hb : ∀ x, b < g x) : ∃ c > b, ∀ x, c ≤ g x := by
  obtain ⟨c, hc, h⟩ := per_max_lt (g := fun x => -g x) hg.neg (fun x => by simp [hp x])
    (b := -b) (fun x => by linarith [hb x])
  exact ⟨-c, by linarith, fun x => by linarith [h x]⟩

lemma integral_shift_per {f : ℝ → ℝ} (hp : Periodic f 1) (a : ℝ) :
    ∫ x in (0 : ℝ)..1, f (x + a) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right f, zero_add, add_comm (1 : ℝ)]
  have := hp.intervalIntegral_add_eq a 0
  rw [zero_add] at this
  exact this

/-- Products along the orbit. -/
def oprod (α : ℝ) (ℓ : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∏ k ∈ Finset.range n, ℓ (x + k * α)

lemma iter_mulVec_inv {α : ℝ} {X : ℝ → M2} {u : ℝ → Fin 2 → ℂ} {ℓ : ℝ → ℂ}
    (hu : ∀ x, X x *ᵥ u x = ℓ x • u (x + α)) (n : ℕ) (x : ℝ) :
    iter α X n x *ᵥ u x = oprod α ℓ n x • u (x + n * α) := by
  induction n with
  | zero => simp [iter, oprod]
  | succ n ih =>
    have e : oprod α ℓ (n + 1) x = ℓ (x + n * α) * oprod α ℓ n x := by
      simp only [oprod, Finset.prod_range_succ]; ring
    rw [iter, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hu, smul_smul, e, mul_comm]
    congr 2
    push_cast; ring

/-- **Lyapunov exponent from an invariant splitting.** -/
theorem lyap_of_split {α : ℝ} {X : ℝ → M2} (hX : IsSLCocycle X) {u s : ℝ → Fin 2 → ℂ}
    {ℓ m : ℝ → ℂ} (huc : Continuous u) (hup : Periodic u 1) (hsc : Continuous s)
    (hsp : Periodic s 1) (hℓc : Continuous ℓ) (hℓp : Periodic ℓ 1)
    (hu : ∀ x, X x *ᵥ u x = ℓ x • u (x + α)) (hs : ∀ x, X x *ᵥ s x = m x • s (x + α))
    (hcr : ∀ x, cr (u x) (s x) ≠ 0) (hℓ : ∀ x, 1 ≤ ‖ℓ x‖) :
    lyapunov α X = ∫ x in (0 : ℝ)..1, Real.log ‖ℓ x‖ := by
  -- bounds
  obtain ⟨Ku, hKu⟩ := per_bound huc hup
  obtain ⟨Ks, hKs⟩ := per_bound hsc hsp
  have hcrc : Continuous fun x => ‖cr (u x) (s x)‖ :=
    (continuous_cr.comp (huc.prodMk hsc)).norm
  obtain ⟨c0, hc0pos, hc0⟩ := per_pos_min hcrc (fun x => by simp only [hup x, hsp x])
    (b := 0) (fun x => norm_pos_iff.2 (hcr x))
  have hu0 : ∀ x, u x ≠ 0 := fun x h => hcr x (by simp [h, cr])
  obtain ⟨cu, hcupos, hcu⟩ := per_pos_min huc.norm (fun x => by simp only [hup x])
    (b := 0) (fun x => norm_pos_iff.2 (hu0 x))
  have hKu0 : 0 < Ku := hcupos.trans_le ((hcu 0).trans (hKu 0))
  have hKs0 : 0 ≤ Ks := (norm_nonneg _).trans (hKs 0)
  set Λ := oprod α ℓ with hΛ
  set Mm := oprod α m with hMm
  have hΛ1 : ∀ n x, 1 ≤ ‖Λ n x‖ := by
    intro n x
    simp only [hΛ, oprod, norm_prod]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ]
      have := hℓ (x + n * α)
      nlinarith
  have hiu := iter_mulVec_inv hu
  have his := iter_mulVec_inv hs
  -- the stable multiplier is bounded
  have hM : ∀ n x, ‖Mm n x‖ ≤ 2 * Ku * Ks / c0 := by
    intro n x
    have e := cr_mulVec (iter α X n x) (u x) (s x)
    rw [det_iter hX.det_eq_one, one_mul, hiu, his, cr_smul_left, cr_smul_right] at e
    have h1 : ‖Λ n x‖ * ‖Mm n x‖ * ‖cr (u (x + n * α)) (s (x + n * α))‖ = ‖cr (u x) (s x)‖ := by
      rw [← e]; simp; ring
    have h2 := norm_cr_le (u x) (s x)
    have h3 := hc0 (x + n * α)
    have h4 : ‖cr (u x) (s x)‖ ≤ 2 * Ku * Ks := by
      have := mul_le_mul (hKu x) (hKs x) (norm_nonneg _) hKu0.le
      nlinarith
    rw [le_div_iff₀ hc0pos]
    have h5 : ‖Mm n x‖ * c0 ≤ ‖Λ n x‖ * ‖Mm n x‖ * ‖cr (u (x + n * α)) (s (x + n * α))‖ := by
      have := mul_le_mul (hΛ1 n x) h3 hc0pos.le (norm_nonneg _)
      nlinarith [norm_nonneg (Mm n x)]
    linarith
  -- upper bound for the iterate
  set C1 : ℝ := 2 * Ks / c0 * Ku + 2 * Ku / c0 * (2 * Ku * Ks / c0) * Ks with hC1
  have hC1nn : 0 ≤ C1 := by positivity
  have hup' : ∀ n x, ‖iter α X n x‖ ≤ 2 * (C1 * ‖Λ n x‖) := by
    intro n x
    apply norm_M2_le_entries _ (by have := hΛ1 n x; positivity)
    intro i j
    refine (entry_le_mulVec _ i j).trans ?_
    set e : Fin 2 → ℂ := Pi.single j 1
    have he : ‖e‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
      by_cases hk : k = j
      · subst hk; simp [e]
      · simp [e, hk]
    rw [decomp (hcr x) e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hiu, his,
      smul_smul, smul_smul]
    have hp : ‖cr e (s x) / cr (u x) (s x)‖ ≤ 2 * Ks / c0 := by
      rw [norm_div]
      refine div_le_div₀ (by positivity) ?_ hc0pos (hc0 x)
      refine (norm_cr_le _ _).trans ?_
      have := mul_le_mul he (hKs x) (norm_nonneg _) zero_le_one
      linarith
    have hq : ‖cr (u x) e / cr (u x) (s x)‖ ≤ 2 * Ku / c0 := by
      rw [norm_div]
      refine div_le_div₀ (by positivity) ?_ hc0pos (hc0 x)
      refine (norm_cr_le _ _).trans ?_
      have := mul_le_mul (hKu x) he (norm_nonneg _) hKu0.le
      linarith
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_mul, norm_mul]
    have hΛ1' := hΛ1 n x
    have t1 : ‖cr e (s x) / cr (u x) (s x)‖ * ‖Λ n x‖ * ‖u (x + n * α)‖ ≤
        2 * Ks / c0 * ‖Λ n x‖ * Ku := by
      gcongr; exact hKu _
    have t2 : ‖cr (u x) e / cr (u x) (s x)‖ * ‖Mm n x‖ * ‖s (x + n * α)‖ ≤
        2 * Ku / c0 * (2 * Ku * Ks / c0) * Ks := by
      gcongr
      · exact hM n x
      · exact hKs _
    have t3 : 2 * Ku / c0 * (2 * Ku * Ks / c0) * Ks ≤
        2 * Ku / c0 * (2 * Ku * Ks / c0) * Ks * ‖Λ n x‖ := by
      have : 0 ≤ 2 * Ku / c0 * (2 * Ku * Ks / c0) * Ks := by positivity
      nlinarith
    rw [hC1]; nlinarith
  -- lower bound
  have hlow : ∀ n x, cu / Ku * ‖Λ n x‖ ≤ ‖iter α X n x‖ := by
    intro n x
    have h1 := Matrix.linfty_opNorm_mulVec (iter α X n x) (u x)
    rw [hiu, norm_smul] at h1
    have h2 := hcu (x + n * α)
    have h3 := hKu x
    rw [div_mul_eq_mul_div, div_le_iff₀ hKu0]
    have : cu * ‖Λ n x‖ ≤ ‖Λ n x‖ * ‖u (x + ↑n * α)‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    nlinarith [norm_nonneg (iter α X n x), norm_nonneg (Λ n x)]
  -- log comparison
  have hC1pos : 0 < 2 * C1 := by
    have := hlow 0 0; have := hup' 0 0; have := hΛ1 0 0
    have : 0 < cu / Ku := by positivity
    nlinarith
  set C2 : ℝ := |Real.log (2 * C1)| + |Real.log (cu / Ku)| with hC2
  have hlog : ∀ n x, |Real.log ‖iter α X n x‖ - Real.log ‖Λ n x‖| ≤ C2 := by
    intro n x
    have hΛp : 0 < ‖Λ n x‖ := zero_lt_one.trans_le (hΛ1 n x)
    have hcp : 0 < cu / Ku := by positivity
    have a1 : Real.log ‖iter α X n x‖ ≤ Real.log (2 * C1) + Real.log ‖Λ n x‖ := by
      rw [← Real.log_mul hC1pos.ne' hΛp.ne']
      exact Real.log_le_log (zero_lt_one.trans_le (hX.one_le_norm_iter n x))
        (by have := hup' n x; linarith)
    have a2 : Real.log (cu / Ku) + Real.log ‖Λ n x‖ ≤ Real.log ‖iter α X n x‖ := by
      rw [← Real.log_mul hcp.ne' hΛp.ne']
      exact Real.log_le_log (by positivity) (hlow n x)
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log (cu / Ku)); have := abs_nonneg (Real.log (2 * C1)); linarith
    · have := le_abs_self (Real.log (2 * C1)); have := abs_nonneg (Real.log (cu / Ku)); linarith
  -- integral of the Birkhoff sums
  set I := ∫ x in (0 : ℝ)..1, Real.log ‖ℓ x‖
  have hlc : Continuous fun x => Real.log ‖ℓ x‖ :=
    hℓc.norm.log (fun x => (zero_lt_one.trans_le (hℓ x)).ne')
  have hlp : Periodic (fun x => Real.log ‖ℓ x‖) 1 := fun x => by simp only [hℓp x]
  have hΛlog : ∀ n x, Real.log ‖Λ n x‖ = ∑ k ∈ Finset.range n, Real.log ‖ℓ (x + k * α)‖ := by
    intro n x
    simp only [hΛ, oprod, norm_prod]
    exact Real.log_prod (fun k _ => (zero_lt_one.trans_le (hℓ _)).ne')
  have hΛc : ∀ n, Continuous fun x => Real.log ‖Λ n x‖ := by
    intro n
    simp_rw [hΛlog]
    exact continuous_finsetSum _ fun k _ => hlc.comp (continuous_id.add continuous_const)
  have hint : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, Real.log ‖Λ n x‖ = n * I := by
    intro n
    simp_rw [hΛlog]
    rw [intervalIntegral.integral_finsetSum (f := fun (k : ℕ) x => Real.log ‖ℓ (x + k * α)‖) (fun k _ =>
      (hlc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)]
    simp_rw [integral_shift_per hlp]
    simp [I]
  have hseq : ∀ n : ℕ, |lyapSeq α X n - n * I| ≤ C2 := by
    intro n
    rw [← hint n, lyapSeq, ← intervalIntegral.integral_sub
      ((hX.continuous_log_norm_iter n).intervalIntegrable _ _) ((hΛc n).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := C2)
      (f := fun x => Real.log ‖iter α X n x‖ - Real.log ‖Λ n x‖)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hlog n x)
    simpa [Real.norm_eq_abs] using this
  have hlim : Tendsto (fun n : ℕ => lyapSeq α X n / n) atTop (𝓝 I) := by
    have h0 : Tendsto (fun n : ℕ => (lyapSeq α X n - n * I) / n) atTop (𝓝 0) := by
      have hl : Tendsto (fun n : ℕ => C2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul C2
      refine squeeze_zero_norm (fun n => ?_) hl
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (hseq n) (by positivity)
    have h1 := h0.add_const I
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp
    ring
  exact tendsto_nhds_unique hX.tendsto_lyapunov hlim


lemma exp_sub_le : ∀ ε > 0, ∃ δ > 0, ∀ X : M2, ‖X‖ < δ →
    ‖NormedSpace.exp X - 1 - X‖ ≤ ε * ‖X‖ := by
  intro ε hε
  have h := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := M2)).isLittleO.def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := hball (y := X) (by simpa [dist_eq_norm] using hX)
  simp only [NormedSpace.exp_zero, sub_zero, one_apply_eq_self] at this
  exact this

lemma graph_scaled {a b c d : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hd : Continuous d) (hap : Periodic a 1) (hbp : Periodic b 1) (hcp : Periodic c 1)
    (hdp : Periodic d 1) (β : ℝ) {r : ℝ} (hr : 0 < r)
    (h1 : ∀ x, r * ‖b x‖ + ‖c x‖ / r + ‖d x‖ < ‖a x‖)
    (h2 : ∀ x, ‖a x * d x - b x * c x‖ < (‖a x‖ - r * ‖b x‖) ^ 2) :
    ∃ χ : ℝ → ℂ, Continuous χ ∧ Periodic χ 1 ∧ (∀ x, ‖χ x‖ ≤ r) ∧
      ∀ x, χ (x + β) * (a x + b x * χ x) = c x + d x * χ x := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨ψ, hψc, hψp, hψb, hψ⟩ := graph_fixed (a := a) (b := fun x => (r : ℂ) * b x)
    (c := fun x => c x / r) (d := d) ha (continuous_const.mul hb) (hc.div_const _) hd hap
    (fun x => by simp only [hbp x]) (fun x => by simp only [hcp x]) hdp β
    (fun x => by
      simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      linarith [h1 x])
    (fun x => by
      have e : a x * d x - (r : ℂ) * b x * (c x / r) = a x * d x - b x * c x := by
        field_simp
      simp only [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact h2 x)
  refine ⟨fun x => (r : ℂ) * ψ x, continuous_const.mul hψc, fun x => by simp only [hψp x],
    fun x => ?_, fun x => ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have := hψb x
    nlinarith
  · have := hψ x
    have e : (r : ℂ) * ψ (x + β) * (a x + b x * ((r : ℂ) * ψ x)) =
        (r : ℂ) * (ψ (x + β) * (a x + (r : ℂ) * b x * ψ x)) := by ring
    rw [e, this]
    field_simp


lemma continuous_inv_of_det {B : ℝ → M2} (hBc : Continuous B) (hBd : ∀ x, (B x).det = 1) :
    Continuous fun x => (B x)⁻¹ := by
  have : (fun x => (B x)⁻¹) = fun x => (B x).adjugate := funext fun x => by
    rw [Matrix.inv_def, hBd]; simp
  rw [this]; exact hBc.matrix_adjugate

/-- Birkhoff sums of `g`. -/
def bsum (α : ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, g (x + k * α)

lemma bsum_add (α : ℝ) (g : ℝ → ℝ) (a b : ℕ) (x : ℝ) :
    bsum α g (a + b) x = bsum α g a x + bsum α g b (x + a * α) := by
  simp only [bsum, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; push_cast; ring

lemma bsum_one (α : ℝ) (g : ℝ → ℝ) (x : ℝ) : bsum α g 1 x = g x := by simp [bsum]

lemma continuous_bsum {α : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) :
    Continuous (bsum α g n) :=
  continuous_finsetSum _ fun _ _ => hg.comp (continuous_id.add continuous_const)

lemma periodic_bsum {α : ℝ} {g : ℝ → ℝ} (hg : Periodic g 1) (n : ℕ) :
    Periodic (bsum α g n) 1 := fun x => by
  simp only [bsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_right_comm, hg]

/-- **Adapted frame.**  The diagonalising frame can be rescaled so that the expanding
multiplier has modulus `≥ ρ > 1` at every point. -/
theorem adapt_frame {α : ℝ} {A B : ℝ → M2} (hA : IsSLCocycle A) (hBc : Continuous B)
    (hBp : Periodic B 1) (hBd : ∀ x, (B x).det = 1)
    (hdiag : ∀ x, ((B (x + α))⁻¹ * A x * B x) 0 1 = 0 ∧ ((B (x + α))⁻¹ * A x * B x) 1 0 = 0)
    (hexp : ∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ < ‖iter α A n x *ᵥ (B x *ᵥ ![1, 0])‖) :
    ∃ (B' : ℝ → M2) (l : ℝ → ℂ) (ρ : ℝ), Continuous B' ∧ Periodic B' 1 ∧
      (∀ x, (B' x).det = 1) ∧ Continuous l ∧ Periodic l 1 ∧ 1 < ρ ∧ (∀ x, ρ ≤ ‖l x‖) ∧
      (∀ x, (B' (x + α))⁻¹ * A x * B' x = !![l x, 0; 0, (l x)⁻¹]) ∧
      ∀ x (M : M2), ulc ((B' x)⁻¹ * M * B' x) = ulc ((B x)⁻¹ * M * B x) := by
  obtain ⟨n, hn1, hn⟩ := hexp
  have hBi := continuous_inv_of_det hBc hBd
  have hu : ∀ x, IsUnit (B x).det := fun x => by rw [hBd]; exact isUnit_one
  set D : ℝ → M2 := fun x => (B (x + α))⁻¹ * A x * B x with hDdef
  have hDc : Continuous D :=
    ((hBi.comp (continuous_id.add continuous_const)).mul hA.continuous).mul hBc
  have hDp : Periodic D 1 := fun x => by
    simp only [hDdef]; rw [add_right_comm, hBp, hA.periodic, hBp]
  have hDdet : ∀ x, (D x).det = 1 := fun x => by
    simp [hDdef, Matrix.det_mul, Matrix.det_nonsing_inv, hBd, hA.det_eq_one]
  set l : ℝ → ℂ := fun x => D x 0 0 with hl
  have hlc : Continuous l := hDc.matrix_elem 0 0
  have hlp : Periodic l 1 := fun x => by simp only [hl, hDp x]
  have hdiag' : ∀ x, D x 0 1 = 0 ∧ D x 1 0 = 0 := hdiag
  have hDform : ∀ x, D x = !![l x, 0; 0, (l x)⁻¹] ∧ l x ≠ 0 := by
    intro x
    have h := hDdet x
    rw [Matrix.det_fin_two, (hdiag' x).1, (hdiag' x).2, mul_zero, sub_zero] at h
    have hl0 : l x ≠ 0 := fun h0 => by
      rw [show D x 0 0 = l x from rfl, h0, zero_mul] at h; exact zero_ne_one h
    refine ⟨?_, hl0⟩
    ext i j; fin_cases i <;> fin_cases j
    · rfl
    · exact (hdiag' x).1
    · exact (hdiag' x).2
    · simp only [Fin.mk_one, of_apply, cons_val', cons_val_one, cons_val_fin_one, empty_val']
      exact eq_inv_of_mul_eq_one_right h
  have hl0 : ∀ x, l x ≠ 0 := fun x => (hDform x).2
  have hAB : ∀ x, A x * B x = B (x + α) * D x := fun x => by
    simp only [hDdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu _), Matrix.one_mul]
  set v : ℝ → Fin 2 → ℂ := fun x => B x *ᵥ ![1, 0] with hv
  have hvc : Continuous v := by
    simp only [hv]; exact hBc.matrix_mulVec continuous_const
  have hvp : Periodic v 1 := fun x => by simp only [hv, hBp x]
  have hv0 : ∀ x, v x ≠ 0 := by
    intro x h0
    have := cr_mulVec (B x) ![1, 0] ![0, 1]
    rw [hBd] at this
    simp only [hv] at h0
    rw [h0] at this
    simp [cr] at this
  have hvinv : ∀ x, A x *ᵥ v x = l x • v (x + α) := by
    intro x
    simp only [hv, Matrix.mulVec_mulVec, hAB, (hDform x).1, ← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hiv := iter_mulVec_inv hvinv
  set lg : ℝ → ℝ := fun x => Real.log ‖l x‖ with hlg
  have hlgc : Continuous lg := hlc.norm.log fun x => norm_ne_zero_iff.2 (hl0 x)
  have hlgp : Periodic lg 1 := fun x => by simp only [hlg, hlp x]
  set S := bsum α lg with hS
  have hSlog : ∀ k x, Real.log ‖oprod α l k x‖ = S k x := by
    intro k x
    simp only [oprod, norm_prod, hS, bsum, hlg]
    exact Real.log_prod (fun j _ => norm_ne_zero_iff.2 (hl0 _))
  set f : ℝ → ℝ := fun x => Real.log ‖v x‖ with hf
  have hfc : Continuous f := hvc.norm.log fun x => norm_ne_zero_iff.2 (hv0 x)
  have hfp : Periodic f 1 := fun x => by simp only [hf, hvp x]
  obtain ⟨F, hF⟩ := per_bound hfc hfp
  have hstep : ∀ x, 0 < S n x + f (x + n * α) - f x := by
    intro x
    have h := hn x
    rw [hiv, norm_smul] at h
    have hp1 : 0 < ‖v x‖ := norm_pos_iff.2 (hv0 x)
    have hp2 : 0 < ‖v (x + n * α)‖ := norm_pos_iff.2 (hv0 _)
    have hp3 : 0 < ‖oprod α l n x‖ := by
      by_contra hc
      push Not at hc
      have : ‖oprod α l n x‖ = 0 := le_antisymm hc (norm_nonneg _)
      rw [this, zero_mul] at h; linarith
    have := Real.log_lt_log hp1 h
    rw [Real.log_mul hp3.ne' hp2.ne', hSlog] at this
    linarith
  obtain ⟨η, hη, hηle⟩ := per_pos_min (g := fun x => S n x + f (x + n * α) - f x)
    (((continuous_bsum hlgc n).add (hfc.comp (continuous_id.add continuous_const))).sub hfc)
    (fun x => by
      simp only [hS]
      rw [periodic_bsum hlgp n x, show x + 1 + n * α = x + n * α + 1 by ring, hfp, hfp])
    hstep
  have hmS : ∀ m : ℕ, ∀ x, m * η + f x - f (x + (m * n : ℕ) * α) ≤ S (m * n) x := by
    intro m
    induction m with
    | zero => intro x; simp [hS, bsum]
    | succ m ih =>
      intro x
      have e : (m + 1) * n = m * n + n := by ring
      rw [e, hS, bsum_add, ← hS]
      have h1 := ih x
      have h2 := hηle (x + (m * n : ℕ) * α)
      have e2 : x + ((m * n + n : ℕ) : ℝ) * α = x + ((m * n : ℕ) : ℝ) * α + n * α := by
        push_cast; ring
      rw [e2]
      push_cast at h1 h2 ⊢
      linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((2 * F + 1) / η)
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0)
  have hmη : 2 * F + 1 < m * η := by rwa [div_lt_iff₀ hη] at hm
  set N := m * n with hN
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hmη; simp at hmη; linarith
    · exact h
  have hN0 : 0 < N := Nat.mul_pos hm0 hn1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hSN : ∀ x, 1 ≤ S N x := by
    intro x
    have h1 := hmS m x
    have h2 := hF x
    have h3 := hF (x + (m * n : ℕ) * α)
    rw [Real.norm_eq_abs] at h2 h3
    have := abs_le.1 h2; have := abs_le.1 h3
    rw [hN]; linarith
  -- the adapted rescaling
  set ψ : ℝ → ℝ := fun x => -(∑ k ∈ Finset.range N, S k x) / N with hψ
  have hψc : Continuous ψ := by
    simp only [hψ]
    exact (continuous_finsetSum _ fun k _ => continuous_bsum hlgc k).neg.div_const _
  have hψp : Periodic ψ 1 := fun x => by
    have : ∀ k, S k (x + 1) = S k x := fun k => periodic_bsum hlgp k x
    simp only [hψ, this]
  have hSsucc : ∀ k x, S (k + 1) x = lg x + S k (x + α) := by
    intro k x
    rw [add_comm, hS, bsum_add, bsum_one]
    simp
  have hS0 : ∀ x, S 0 x = 0 := fun x => by simp [hS, bsum]
  have hψshift : ∀ x, ψ x - ψ (x + α) = S N x / N - lg x := by
    intro x
    have e0 := Finset.sum_range_succ' (fun k => S k x) N
    have e1 := Finset.sum_range_succ (fun k => S k x) N
    have e2 : ∑ k ∈ Finset.range N, S k (x + α) =
        ∑ k ∈ Finset.range N, S (k + 1) x - N * lg x := by
      rw [show (N : ℝ) * lg x = ∑ k ∈ Finset.range N, lg x by simp, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hSsucc]; ring
    simp only [hψ]
    rw [hS0, add_zero] at e0
    field_simp
    linarith
  set φ : ℝ → ℝ := fun x => Real.exp (ψ x) with hφ
  have hφc : Continuous φ := Real.continuous_exp.comp hψc
  have hφp : Periodic φ 1 := fun x => by simp only [hφ, hψp x]
  have hφ0 : ∀ x, (φ x : ℂ) ≠ 0 := fun x => by
    exact_mod_cast (Real.exp_pos (ψ x)).ne'
  set l' : ℝ → ℂ := fun x => l x * ((φ x / φ (x + α) : ℝ) : ℂ) with hl'
  set P : ℝ → M2 := fun x => !![(φ x : ℂ), 0; 0, (φ x : ℂ)⁻¹] with hP
  set Q : ℝ → M2 := fun x => !![(φ x : ℂ)⁻¹, 0; 0, (φ x : ℂ)] with hQ
  have hQP : ∀ x, Q x * P x = 1 := fun x => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP, hQ, hφ0 x]
  have hPinv : ∀ x, (P x)⁻¹ = Q x := fun x => Matrix.inv_eq_left_inv (hQP x)
  have hPc : Continuous P := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hc : Continuous fun x => (φ x : ℂ) := Complex.continuous_ofReal.comp hφc
    fin_cases i <;> fin_cases j <;> simp [hP] <;>
      first | exact hc | exact hc.inv₀ hφ0 | exact continuous_const
  refine ⟨fun x => B x * P x, l', Real.exp (1 / N), hBc.mul hPc, fun x => by
    simp only [hBp x, hP, hφp x], fun x => by
    simp [Matrix.det_mul, hBd, hP, Matrix.det_fin_two, hφ0 x], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hl']
    refine hlc.mul (Complex.continuous_ofReal.comp (hφc.div
      (hφc.comp (continuous_id.add continuous_const)) fun x => (Real.exp_pos _).ne'))
  · intro x
    simp only [hl']
    rw [hlp x, hφp x, add_right_comm, hφp]
  · rw [Real.one_lt_exp_iff]; positivity
  · intro x
    have hn' : ‖l' x‖ = Real.exp (S N x / N) := by
      simp only [hl', norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos (Real.exp_pos _) (Real.exp_pos _)), ← Real.exp_sub,
        hψshift, ← Real.exp_log (norm_pos_iff.2 (hl0 x)), ← Real.exp_add]
      congr 1
      simp only [hlg]; ring
    rw [hn']
    exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (hSN x) hNR.le)
  · intro x
    rw [Matrix.mul_inv_rev, hPinv]
    have e : Q (x + α) * (B (x + α))⁻¹ * A x * (B x * P x) = Q (x + α) * D x * P x := by
      simp only [hDdef, Matrix.mul_assoc]
    rw [e, (hDform x).1]
    have h1 := hφ0 x
    have h2 := hφ0 (x + α)
    have h3 := hl0 x
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP, hQ, hl'] <;> field_simp
  · intro x M
    rw [Matrix.mul_inv_rev, hPinv]
    have := ulc_diag_conj ((B x)⁻¹ * M * B x) (hφ0 x) (inv_ne_zero (hφ0 x))
    rw [inv_inv] at this
    rw [← this]
    simp only [hP, hQ, Matrix.mul_assoc]


/-- The Lyapunov exponent of a cocycle conjugated (by `B`) to a cocycle `Nm` that has an
invariant unstable graph `h` and an invariant stable graph `g`. -/
theorem lyap_of_graphs {α : ℝ} {X B Nm : ℝ → M2} (hX : IsSLCocycle X) (hBc : Continuous B)
    (hBp : Periodic B 1) (hBd : ∀ x, (B x).det = 1) (hNc : Continuous Nm) (hNp : Periodic Nm 1)
    (hXB : ∀ x, X x * B x = B (x + α) * Nm x) {h g : ℝ → ℂ} (hhc : Continuous h)
    (hhp : Periodic h 1) (hgc : Continuous g) (hgp : Periodic g 1)
    (hhg : ∀ x, h x * g x ≠ 1)
    (hh : ∀ x, h (x + α) * (Nm x 0 0 + Nm x 0 1 * h x) = Nm x 1 0 + Nm x 1 1 * h x)
    (hg : ∀ x, Nm x 0 0 * g x + Nm x 0 1 = g (x + α) * (Nm x 1 0 * g x + Nm x 1 1))
    (h1 : ∀ x, 1 ≤ ‖Nm x 0 0 + Nm x 0 1 * h x‖) :
    lyapunov α X = ∫ x in (0 : ℝ)..1, Real.log ‖Nm x 0 0 + Nm x 0 1 * h x‖ := by
  have key : ∀ x (v : Fin 2 → ℂ), X x *ᵥ (B x *ᵥ v) = B (x + α) *ᵥ (Nm x *ᵥ v) := by
    intro x v
    rw [Matrix.mulVec_mulVec, hXB, ← Matrix.mulVec_mulVec]
  refine lyap_of_split hX (u := fun x => B x *ᵥ ![1, h x]) (s := fun x => B x *ᵥ ![g x, 1])
    (m := fun x => Nm x 1 0 * g x + Nm x 1 1)
    (hBc.matrix_mulVec (by fun_prop)) (fun x => by simp only [hBp x, hhp x])
    (hBc.matrix_mulVec (by fun_prop)) (fun x => by simp only [hBp x, hgp x])
    ((hNc.matrix_elem 0 0).add ((hNc.matrix_elem 0 1).mul hhc))
    (fun x => by simp only [hNp x, hhp x]) (fun x => ?_) (fun x => ?_) (fun x => ?_) h1
  · rw [key, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [← hh x]; ring
  · rw [key, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hg x]; ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · show cr (B x *ᵥ ![1, h x]) (B x *ᵥ ![g x, 1]) ≠ 0
    rw [cr_mulVec, hBd, one_mul]
    simp only [cr, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    intro h0
    apply hhg x
    linear_combination -h0

/-- Existence of the two invariant graphs, with sup norm `≤ r`. -/
theorem graphs_exist {α : ℝ} {Nm : ℝ → M2} (hNc : Continuous Nm) (hNp : Periodic Nm 1)
    {r : ℝ} (hr : 0 < r)
    (hU : ∀ x, r * ‖Nm x 0 1‖ + ‖Nm x 1 0‖ / r + ‖Nm x 1 1‖ < ‖Nm x 0 0‖)
    (hS : ∀ x, r * ‖Nm x 1 0‖ + ‖Nm x 0 1‖ / r + ‖Nm x 1 1‖ < ‖Nm x 0 0‖)
    (hU2 : ∀ x, ‖(Nm x).det‖ < (‖Nm x 0 0‖ - r * ‖Nm x 0 1‖) ^ 2)
    (hS2 : ∀ x, ‖(Nm x).det‖ < (‖Nm x 0 0‖ - r * ‖Nm x 1 0‖) ^ 2) :
    ∃ h g : ℝ → ℂ, Continuous h ∧ Periodic h 1 ∧ Continuous g ∧ Periodic g 1 ∧
      (∀ x, ‖h x‖ ≤ r) ∧ (∀ x, ‖g x‖ ≤ r) ∧
      (∀ x, h (x + α) * (Nm x 0 0 + Nm x 0 1 * h x) = Nm x 1 0 + Nm x 1 1 * h x) ∧
      (∀ x, Nm x 0 0 * g x + Nm x 0 1 = g (x + α) * (Nm x 1 0 * g x + Nm x 1 1)) := by
  have he : ∀ i j, Continuous fun x => Nm x i j := fun i j => hNc.matrix_elem i j
  have hpe : ∀ i j, Periodic (fun x => Nm x i j) 1 := fun i j x => by simp only [hNp x]
  obtain ⟨h, hc, hp, hb, heq⟩ := graph_scaled (he 0 0) (he 0 1) (he 1 0) (he 1 1)
    (hpe 0 0) (hpe 0 1) (hpe 1 0) (hpe 1 1) α hr hU (fun x => by
      rw [← Matrix.det_fin_two]; exact hU2 x)
  have hsh : Continuous fun x : ℝ => x - α := continuous_id.sub continuous_const
  have hshp : ∀ i j, Periodic (fun x => Nm (x - α) i j) 1 := fun i j x => by
    simp only [show x + 1 - α = x - α + 1 by ring, hNp (x - α)]
  obtain ⟨g, gc, gp, gb, geq⟩ := graph_scaled (a := fun x => Nm (x - α) 0 0)
    (b := fun x => -Nm (x - α) 1 0) (c := fun x => -Nm (x - α) 0 1)
    (d := fun x => Nm (x - α) 1 1)
    ((he 0 0).comp hsh) ((he 1 0).comp hsh).neg ((he 0 1).comp hsh).neg ((he 1 1).comp hsh)
    (hshp 0 0) (fun x => by simp only [hshp 1 0 x]) (fun x => by simp only [hshp 0 1 x])
    (hshp 1 1) (-α) hr
    (fun x => by simp only [norm_neg]; exact hS (x - α))
    (fun x => by
      have := hS2 (x - α)
      rw [Matrix.det_fin_two] at this
      simp only [norm_neg]
      convert this using 2
      ring)
  refine ⟨h, g, hc, hp, gc, gp, hb, gb, heq, fun x => ?_⟩
  have := geq (x + α)
  simp only [add_sub_cancel_right, add_neg_cancel_right] at this
  linear_combination this


lemma adj_eq_conj (M : M2) : M.adjugate = !![0, 1; -1, 0] * Mᵀ * !![0, -1; 1, 0] := by
  rw [adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma det_exp_of_trace_zero {X : M2} (hX : X.trace = 0) : (NormedSpace.exp X).det = 1 := by
  set J : M2 := !![0, 1; -1, 0]
  have hJu : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det]; simp [J, det_fin_two]
  have hJinv : J⁻¹ = !![0, -1; 1, 0] := by
    rw [Matrix.inv_def]; simp [J, det_fin_two, adjugate_fin_two]
  have hadjX : X.adjugate = -X := by
    rw [adjugate_fin_two]
    have h : X 1 1 = - X 0 0 := by
      rw [Matrix.trace_fin_two] at hX; linear_combination hX
    ext i j; fin_cases i <;> fin_cases j <;> simp [h]
  have key : (NormedSpace.exp X).adjugate = NormedSpace.exp (-X) := by
    rw [adj_eq_conj, ← Matrix.exp_transpose, ← hJinv, ← Matrix.exp_conj _ _ hJu, hJinv,
      ← adj_eq_conj, hadjX]
  have h1 : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      NormedSpace.exp_zero]
  have h2 := Matrix.mul_adjugate (NormedSpace.exp X)
  rw [key, h1] at h2
  have := congrFun (congrFun h2 0) 0
  simpa using this.symm



lemma entry_le_norm (M : M2) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  have := row_sum_le_norm M i
  fin_cases j
  · simp only [Fin.zero_eta]; linarith [norm_nonneg (M i 1)]
  · simp only [Fin.mk_one]; linarith [norm_nonneg (M i 0)]

lemma log_est {l z a : ℂ} {t e : ℝ} (hl : l ≠ 0) (hz : ‖z‖ ≤ 1 / 2)
    (hza : ‖z - t * a‖ ≤ e) :
    |Real.log ‖l * (1 + z)‖ - Real.log ‖l‖ - t * a.re| ≤ e + ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have h1z : (1 + z) ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hz; linarith
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hl) (norm_ne_zero_iff.2 h1z),
    show Real.log ‖1 + z‖ = (Complex.log (1 + z)).re from (Complex.log_re _).symm]
  have hlog := Complex.norm_log_one_add_sub_self_le hz1
  have hb : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have := sq_nonneg ‖z‖
    nlinarith
  have e1 : Real.log ‖l‖ + (Complex.log (1 + z)).re - Real.log ‖l‖ - t * a.re =
      (Complex.log (1 + z) - z).re + (z - t * a).re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  have := Complex.abs_re_le_norm (Complex.log (1 + z) - z)
  have := Complex.abs_re_le_norm (z - t * a)
  linarith

/-- **The core estimate**, in an adapted frame. -/
theorem core {α : ℝ} {A B : ℝ → M2} {l : ℝ → ℂ} {ρ : ℝ} (hA : IsSLCocycle A)
    (hBc : Continuous B) (hBp : Periodic B 1) (hBd : ∀ x, (B x).det = 1)
    (hlc : Continuous l) (hlp : Periodic l 1) (hρ : 1 < ρ) (hlρ : ∀ x, ρ ≤ ‖l x‖)
    (hD : ∀ x, (B (x + α))⁻¹ * A x * B x = !![l x, 0; 0, (l x)⁻¹])
    {w : ℝ → M2} (hwc : Continuous w) (hwp : Periodic w 1) (hwt : ∀ x, (w x).trace = 0) :
    HasDerivAt (fun t : ℝ => lyapunov α fun x => A x * NormedSpace.exp ((t : ℂ) • w x))
      (∫ x in (0 : ℝ)..1, (ulc ((B x)⁻¹ * w x * B x)).re) 0 := by
  have hBi := continuous_inv_of_det hBc hBd
  have hu : ∀ x, IsUnit (B x) := fun x =>
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hBd]; exact isUnit_one)
  have hρ0 : 0 < ρ := by linarith
  have hl0 : ∀ x, l x ≠ 0 := fun x h => by
    have := hlρ x; rw [h, norm_zero] at this; linarith
  set W : ℝ → M2 := fun x => (B x)⁻¹ * w x * B x with hW
  have hWc : Continuous W := (hBi.mul hwc).mul hBc
  have hWp : Periodic W 1 := fun x => by simp only [hW, hBp x, hwp x]
  have hWt : ∀ x, (W x).trace = 0 := fun x => by
    simp only [hW]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (hu x)), Matrix.one_mul, hwt]
  set Dg : ℝ → M2 := fun x => !![l x, 0; 0, (l x)⁻¹] with hDg
  have hDgc : Continuous Dg := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hDg] <;>
      first | exact hlc | exact hlc.inv₀ hl0 | exact continuous_const
  have hDgp : Periodic Dg 1 := fun x => by simp only [hDg, hlp x]
  have hDgd : ∀ x, (Dg x).det = 1 := fun x => by
    simp [hDg, Matrix.det_fin_two, hl0 x]
  set Nm : ℝ → ℝ → M2 := fun t x => Dg x * NormedSpace.exp ((t : ℂ) • W x) with hNm
  have hNc : ∀ t, Continuous (Nm t) := fun t =>
    hDgc.mul (by fun_prop)
  have hNp : ∀ t, Periodic (Nm t) 1 := fun t x => by simp only [hNm, hDgp x, hWp x]
  have hNd : ∀ t x, (Nm t x).det = 1 := fun t x => by
    simp only [hNm]
    rw [Matrix.det_mul, hDgd, det_exp_of_trace_zero (by rw [Matrix.trace_smul, hWt, smul_zero]),
      one_mul]
  set At : ℝ → ℝ → M2 := fun t x => A x * NormedSpace.exp ((t : ℂ) • w x) with hAt
  have hAtS : ∀ t, IsSLCocycle (At t) := fun t =>
    ⟨hA.continuous.mul (by fun_prop),
      fun x => by simp only [hAt, hA.periodic x, hwp x],
      fun x => by
        simp only [hAt]
        rw [Matrix.det_mul, hA.det_eq_one,
          det_exp_of_trace_zero (by rw [Matrix.trace_smul, hwt, smul_zero]), one_mul]⟩
  have hAB : ∀ x, A x * B x = B (x + α) * Dg x := fun x => by
    simp only [hDg, ← hD x, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (hu _)), Matrix.one_mul]
  have hXB : ∀ t x, At t x * B x = B (x + α) * Nm t x := by
    intro t x
    have hc := Matrix.exp_conj' (B x) ((t : ℂ) • w x) (hu x)
    have e1 : (B x)⁻¹ * ((t : ℂ) • w x) * B x = (t : ℂ) • W x := by
      simp only [hW, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1] at hc
    have e2 : NormedSpace.exp ((t : ℂ) • w x) * B x = B x * NormedSpace.exp ((t : ℂ) • W x) := by
      rw [hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hu x)), Matrix.one_mul]
    simp only [hAt, hNm]
    rw [Matrix.mul_assoc, e2, ← Matrix.mul_assoc, hAB, Matrix.mul_assoc]
  have hN0 : ∀ x, Nm 0 x = Dg x := fun x => by simp [hNm]
  -- the value at `t = 0`
  have hf0 : lyapunov α (At 0) = ∫ x in (0 : ℝ)..1, Real.log ‖l x‖ := by
    rw [lyap_of_graphs (hAtS 0) hBc hBp hBd (hNc 0) (hNp 0) (hXB 0) (h := fun _ => 0)
      (g := fun _ => 0) continuous_const (fun _ => rfl) continuous_const (fun _ => rfl)
      (fun x => by simp) (fun x => by simp [hN0, hDg]) (fun x => by simp [hN0, hDg])
      (fun x => by simp only [hN0, hDg]; simpa using hρ.le.trans (hlρ x))]
    simp [hN0, hDg]
  -- constants
  obtain ⟨K0, hK0⟩ := per_bound hWc hWp
  set K := max K0 1 with hKdef
  have hK : ∀ x, ‖W x‖ ≤ K := fun x => (hK0 x).trans (le_max_left _ _)
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨L0, hL0⟩ := per_bound hlc hlp
  set Lm := max L0 0 with hLmdef
  have hLm : ∀ x, ‖l x‖ ≤ Lm := fun x => (hL0 x).trans (le_max_left _ _)
  have hLm0 : 0 ≤ Lm := le_max_right _ _
  set γ := ρ - ρ⁻¹ with hγ
  have hρinv : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hγ0 : 0 < γ := by linarith
  set κ := 4 * K * (Lm + 1) / γ + 1 with hκdef
  have hκ : 0 < κ := by positivity
  have hκγ : κ * γ = 4 * K * (Lm + 1) + γ := by
    rw [hκdef]; field_simp
  have hκ0 : 2 * K * (Lm + 1) / κ < γ / 2 := by
    rw [div_lt_iff₀ hκ]; nlinarith
  have hκ1 : 2 * K / κ + 1 / ρ < ρ := by
    have : 2 * K / κ ≤ 2 * K * (Lm + 1) / κ := by
      apply div_le_div_of_nonneg_right _ hκ.le; nlinarith
    rw [one_div]; linarith
  have hκ2 : Lm * (2 * K) / κ + 1 / ρ < ρ := by
    have : Lm * (2 * K) / κ ≤ 2 * K * (Lm + 1) / κ := by
      apply div_le_div_of_nonneg_right _ hκ.le; nlinarith
    rw [one_div]; linarith
  -- the derivative
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hE0⟩ := exp_sub_le 1 one_pos
  obtain ⟨δ₁, hδ₁, hE1⟩ := exp_sub_le (ε / (2 * K)) (by positivity)
  have evl : ∀ {F G : ℝ → ℝ}, Continuous F → Continuous G → F 0 < G 0 →
      ∀ᶠ τ in 𝓝 (0 : ℝ), F τ < G τ := fun hF hG h =>
    hF.continuousAt.eventually_lt hG.continuousAt h
  have ev : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * K < δ₀ ∧ τ * K < δ₁ ∧ 2 * K * τ < 1 ∧ κ * τ < 1 ∧
      κ * τ * (Lm * (2 * K * τ)) + 2 * K / κ + (1 + 2 * K * τ) / ρ < ρ * (1 - 2 * K * τ) ∧
      κ * τ * (2 * K * τ) + Lm * (2 * K) / κ + (1 + 2 * K * τ) / ρ < ρ * (1 - 2 * K * τ) ∧
      1 < ρ * (1 - 2 * K * τ) - κ * τ * ((Lm + 1) * (2 * K * τ)) ∧
      2 * K * τ * (1 + κ * τ) < 1 / 2 ∧
      2 * K * κ * τ + (2 * K * (1 + κ * τ)) ^ 2 * τ < ε / 2 := by
    filter_upwards [
      evl (F := fun τ => τ * K) (G := fun _ => δ₀) (by fun_prop) (by fun_prop) (by simpa using hδ₀),
      evl (F := fun τ => τ * K) (G := fun _ => δ₁) (by fun_prop) (by fun_prop) (by simpa using hδ₁),
      evl (F := fun τ => 2 * K * τ) (G := fun _ => 1) (by fun_prop) (by fun_prop) (by simp),
      evl (F := fun τ => κ * τ) (G := fun _ => 1) (by fun_prop) (by fun_prop) (by simp),
      evl (F := fun τ => κ * τ * (Lm * (2 * K * τ)) + 2 * K / κ + (1 + 2 * K * τ) / ρ)
        (G := fun τ => ρ * (1 - 2 * K * τ)) (by fun_prop) (by fun_prop) (by simpa using hκ1),
      evl (F := fun τ => κ * τ * (2 * K * τ) + Lm * (2 * K) / κ + (1 + 2 * K * τ) / ρ)
        (G := fun τ => ρ * (1 - 2 * K * τ)) (by fun_prop) (by fun_prop) (by simpa using hκ2),
      evl (F := fun _ => 1) (G := fun τ => ρ * (1 - 2 * K * τ) - κ * τ * ((Lm + 1) * (2 * K * τ)))
        (by fun_prop) (by fun_prop) (by simpa using hρ),
      evl (F := fun τ => 2 * K * τ * (1 + κ * τ)) (G := fun _ => 1 / 2) (by fun_prop)
        (by fun_prop) (by simp),
      evl (F := fun τ => 2 * K * κ * τ + (2 * K * (1 + κ * τ)) ^ 2 * τ) (G := fun _ => ε / 2)
        (by fun_prop) (by fun_prop) (by simpa using hε)]
      with τ h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  filter_upwards [habs.eventually ev] with t ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩
  rw [zero_add]
  change ‖(lyapunov α (At t) - lyapunov α (At 0)) - t • ∫ x in (0 : ℝ)..1, (W x 0 0).re‖ ≤
    ε * ‖t‖
  by_cases ht : t = 0
  · subst ht; simp
  rw [hf0]
  set τ := |t| with hτdef
  have hτ : 0 < τ := abs_pos.2 ht
  have hXn : ∀ x, ‖(t : ℂ) • W x‖ ≤ τ * K := fun x => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg t)
  set e : ℝ → M2 := fun x => NormedSpace.exp ((t : ℂ) • W x) with he
  have hE : ∀ x, ‖e x - 1‖ ≤ 2 * K * τ := by
    intro x
    have h1 := hE0 _ ((hXn x).trans_lt q0)
    have h2 : e x - 1 = (e x - 1 - (t : ℂ) • W x) + (t : ℂ) • W x := by abel
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    have := hXn x
    linarith
  have hR : ∀ x, ‖e x - 1 - (t : ℂ) • W x‖ ≤ ε / 2 * τ := by
    intro x
    refine (hE1 _ ((hXn x).trans_lt q1)).trans ?_
    calc ε / (2 * K) * ‖(t : ℂ) • W x‖ ≤ ε / (2 * K) * (τ * K) :=
          mul_le_mul_of_nonneg_left (hXn x) (by positivity)
      _ = ε / 2 * τ := by field_simp
  have e00 : ∀ x, ‖e x 0 0 - 1‖ ≤ 2 * K * τ := fun x => by
    have := (entry_le_norm (e x - 1) 0 0).trans (hE x); simpa using this
  have e01 : ∀ x, ‖e x 0 1‖ ≤ 2 * K * τ := fun x => by
    have := (entry_le_norm (e x - 1) 0 1).trans (hE x); simpa using this
  have e10 : ∀ x, ‖e x 1 0‖ ≤ 2 * K * τ := fun x => by
    have := (entry_le_norm (e x - 1) 1 0).trans (hE x); simpa using this
  have e11 : ∀ x, ‖e x 1 1 - 1‖ ≤ 2 * K * τ := fun x => by
    have := (entry_le_norm (e x - 1) 1 1).trans (hE x); simpa using this
  have n00 : ∀ x, Nm t x 0 0 = l x * e x 0 0 := fun x => by
    show (Dg x * e x) _ _ = _
    simp [hDg, Matrix.mul_apply, Fin.sum_univ_two]
  have n01 : ∀ x, Nm t x 0 1 = l x * e x 0 1 := fun x => by
    show (Dg x * e x) _ _ = _
    simp [hDg, Matrix.mul_apply, Fin.sum_univ_two]
  have n10 : ∀ x, Nm t x 1 0 = (l x)⁻¹ * e x 1 0 := fun x => by
    show (Dg x * e x) _ _ = _
    simp [hDg, Matrix.mul_apply, Fin.sum_univ_two]
  have n11 : ∀ x, Nm t x 1 1 = (l x)⁻¹ * e x 1 1 := fun x => by
    show (Dg x * e x) _ _ = _
    simp [hDg, Matrix.mul_apply, Fin.sum_univ_two]
  have hlinv : ∀ x, ‖(l x)⁻¹‖ ≤ 1 / ρ := fun x => by
    rw [norm_inv, one_div]; exact inv_anti₀ hρ0 (hlρ x)
  have hρi : 1 / ρ ≤ 1 := by rw [one_div]; exact hρinv.le
  have bA : ∀ x, ρ * (1 - 2 * K * τ) ≤ ‖Nm t x 0 0‖ := fun x => by
    rw [n00, norm_mul]
    have h1 : 1 - 2 * K * τ ≤ ‖e x 0 0‖ := by
      have := norm_sub_norm_le (1 : ℂ) (e x 0 0)
      rw [norm_one, norm_sub_rev] at this
      linarith [e00 x]
    exact mul_le_mul (hlρ x) h1 (by linarith) (norm_nonneg _)
  have bB : ∀ x, ‖Nm t x 0 1‖ ≤ Lm * (2 * K * τ) := fun x => by
    rw [n01, norm_mul]; exact mul_le_mul (hLm x) (e01 x) (norm_nonneg _) hLm0
  have bC : ∀ x, ‖Nm t x 1 0‖ ≤ 2 * K * τ := fun x => by
    rw [n10, norm_mul]
    have := mul_le_mul ((hlinv x).trans hρi) (e10 x) (norm_nonneg _) zero_le_one
    linarith
  have bD : ∀ x, ‖Nm t x 1 1‖ ≤ (1 + 2 * K * τ) / ρ := fun x => by
    rw [n11, norm_mul]
    have h1 : ‖e x 1 1‖ ≤ 1 + 2 * K * τ := by
      have := norm_sub_norm_le (e x 1 1) 1
      rw [norm_one] at this; linarith [e11 x]
    calc ‖(l x)⁻¹‖ * ‖e x 1 1‖ ≤ 1 / ρ * (1 + 2 * K * τ) :=
          mul_le_mul (hlinv x) h1 (norm_nonneg _) (by positivity)
      _ = (1 + 2 * K * τ) / ρ := by ring
  set r := κ * τ with hrdef
  have hr : 0 < r := mul_pos hκ hτ
  have hKτ : 0 ≤ 2 * K * τ := by positivity
  have hU : ∀ x, r * ‖Nm t x 0 1‖ + ‖Nm t x 1 0‖ / r + ‖Nm t x 1 1‖ < ‖Nm t x 0 0‖ := by
    intro x
    have a1 : r * ‖Nm t x 0 1‖ ≤ κ * τ * (Lm * (2 * K * τ)) :=
      mul_le_mul_of_nonneg_left (bB x) hr.le
    have a2 : ‖Nm t x 1 0‖ / r ≤ 2 * K / κ := by
      rw [div_le_div_iff₀ hr hκ, hrdef]
      have := mul_le_mul_of_nonneg_left (bC x) hκ.le
      linarith
    linarith [bA x, bD x]
  have hS : ∀ x, r * ‖Nm t x 1 0‖ + ‖Nm t x 0 1‖ / r + ‖Nm t x 1 1‖ < ‖Nm t x 0 0‖ := by
    intro x
    have a1 : r * ‖Nm t x 1 0‖ ≤ κ * τ * (2 * K * τ) :=
      mul_le_mul_of_nonneg_left (bC x) hr.le
    have a2 : ‖Nm t x 0 1‖ / r ≤ Lm * (2 * K) / κ := by
      rw [div_le_div_iff₀ hr hκ, hrdef]
      have := mul_le_mul_of_nonneg_left (bB x) hκ.le
      linarith
    linarith [bA x, bD x]
  have hLe : (Lm + 1) * (2 * K * τ) = Lm * (2 * K * τ) + 2 * K * τ := by ring
  have hLm2 : 0 ≤ Lm * (2 * K * τ) := mul_nonneg hLm0 hKτ
  have hLτ : κ * τ * (Lm * (2 * K * τ)) ≤ κ * τ * ((Lm + 1) * (2 * K * τ)) := by
    apply mul_le_mul_of_nonneg_left _ hr.le; rw [hLe]; linarith
  have hLτ' : κ * τ * (2 * K * τ) ≤ κ * τ * ((Lm + 1) * (2 * K * τ)) := by
    apply mul_le_mul_of_nonneg_left _ hr.le; rw [hLe]; linarith
  have hU2 : ∀ x, ‖(Nm t x).det‖ < (‖Nm t x 0 0‖ - r * ‖Nm t x 0 1‖) ^ 2 := by
    intro x
    rw [hNd, norm_one]
    have a1 : r * ‖Nm t x 0 1‖ ≤ κ * τ * (Lm * (2 * K * τ)) :=
      mul_le_mul_of_nonneg_left (bB x) hr.le
    have : 1 < ‖Nm t x 0 0‖ - r * ‖Nm t x 0 1‖ := by linarith [bA x]
    exact one_lt_pow₀ this (by norm_num)
  have hS2 : ∀ x, ‖(Nm t x).det‖ < (‖Nm t x 0 0‖ - r * ‖Nm t x 1 0‖) ^ 2 := by
    intro x
    rw [hNd, norm_one]
    have a1 : r * ‖Nm t x 1 0‖ ≤ κ * τ * (2 * K * τ) :=
      mul_le_mul_of_nonneg_left (bC x) hr.le
    have : 1 < ‖Nm t x 0 0‖ - r * ‖Nm t x 1 0‖ := by linarith [bA x]
    exact one_lt_pow₀ this (by norm_num)
  obtain ⟨h, g, hhc, hhp, hgc, hgp, hhb, hgb, hheq, hgeq⟩ :=
    graphs_exist (α := α) (hNc t) (hNp t) hr hU hS hU2 hS2
  have hhg : ∀ x, h x * g x ≠ 1 := fun x h1 => by
    have := mul_le_mul (hhb x) (hgb x) (norm_nonneg _) hr.le
    rw [← norm_mul, h1, norm_one] at this
    have h2 := mul_lt_mul_of_pos_left q3 hr
    linarith
  have hlow : ∀ x, 1 < ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ := by
    intro x
    have h1 := norm_add_ge (Nm t x 0 0) (Nm t x 0 1 * h x)
    rw [norm_mul] at h1
    have h2 : ‖Nm t x 0 1‖ * ‖h x‖ ≤ κ * τ * (Lm * (2 * K * τ)) := by
      rw [mul_comm]; exact mul_le_mul (hhb x) (bB x) (norm_nonneg _) hr.le
    linarith [bA x]
  rw [lyap_of_graphs (hAtS t) hBc hBp hBd (hNc t) (hNp t) (hXB t) hhc hhp hgc hgp hhg hheq
    hgeq (fun x => (hlow x).le)]
  -- pointwise estimate
  have hpt : ∀ x, |Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ - Real.log ‖l x‖ -
      t * (W x 0 0).re| ≤ ε * τ := by
    intro x
    set z : ℂ := (e x 0 0 - 1) + e x 0 1 * h x with hz
    have hfac : Nm t x 0 0 + Nm t x 0 1 * h x = l x * (1 + z) := by
      rw [n00, n01, hz]; ring
    have hhe : ‖e x 0 1 * h x‖ ≤ 2 * K * τ * r := by
      rw [norm_mul]; exact mul_le_mul (e01 x) (hhb x) (norm_nonneg _) hKτ
    have hzn : ‖z‖ ≤ 2 * K * τ * (1 + κ * τ) := by
      have := norm_add_le (e x 0 0 - 1) (e x 0 1 * h x)
      rw [← hz] at this
      have : 2 * K * τ * (1 + κ * τ) = 2 * K * τ + 2 * K * τ * r := by rw [hrdef]; ring
      linarith [e00 x]
    have hza : ‖z - (t : ℂ) * W x 0 0‖ ≤ ε / 2 * τ + 2 * K * τ * r := by
      have e1 : z - (t : ℂ) * W x 0 0 = (e x - 1 - (t : ℂ) • W x) 0 0 + e x 0 1 * h x := by
        simp [hz]; ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      have := (entry_le_norm (e x - 1 - (t : ℂ) • W x) 0 0).trans (hR x)
      linarith
    have hl := log_est (hl0 x) (hzn.trans q7.le) hza
    rw [hfac]
    refine hl.trans ?_
    have hsq : ‖z‖ ^ 2 ≤ (2 * K * τ * (1 + κ * τ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
    have hq : τ * (2 * K * κ * τ + (2 * K * (1 + κ * τ)) ^ 2 * τ) ≤ τ * (ε / 2) :=
      mul_le_mul_of_nonneg_left q8.le hτ.le
    have e2 : 2 * K * τ * r + (2 * K * τ * (1 + κ * τ)) ^ 2 =
        τ * (2 * K * κ * τ + (2 * K * (1 + κ * τ)) ^ 2 * τ) := by rw [hrdef]; ring
    linarith
  -- integrate
  have hc1 : Continuous fun x => Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ :=
    (((hNc t).matrix_elem 0 0).add (((hNc t).matrix_elem 0 1).mul hhc)).norm.log
      fun x => by have := hlow x; positivity
  have hc2 : Continuous fun x => Real.log ‖l x‖ :=
    hlc.norm.log fun x => norm_ne_zero_iff.2 (hl0 x)
  have hc3 : Continuous fun x => (W x 0 0).re :=
    Complex.continuous_re.comp (hWc.matrix_elem 0 0)
  have eint : (∫ x in (0 : ℝ)..1, Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖) -
      (∫ x in (0 : ℝ)..1, Real.log ‖l x‖) - t • ∫ x in (0 : ℝ)..1, (W x 0 0).re =
      ∫ x in (0 : ℝ)..1, (Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ - Real.log ‖l x‖ -
        t * (W x 0 0).re) := by
    symm
    rw [intervalIntegral.integral_sub
      (f := fun x => Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ - Real.log ‖l x‖)
      (g := fun x => t * (W x 0 0).re) ((hc1.sub hc2).intervalIntegrable _ _)
      ((continuous_const.mul hc3).intervalIntegrable _ _),
      intervalIntegral.integral_sub (f := fun x => Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖)
      (g := fun x => Real.log ‖l x‖) (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [eint]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ε * τ)
    (f := fun x => Real.log ‖Nm t x 0 0 + Nm t x 0 1 * h x‖ - Real.log ‖l x‖ -
        t * (W x 0 0).re) (fun x _ => by rw [Real.norm_eq_abs]; exact hpt x)
  simpa [Real.norm_eq_abs, hτdef] using this

end DerivFormulaAux

/-- **Lemma (derivative of the Lyapunov exponent at uniformly hyperbolic cocycles)**,
paper §3.2.  Proved directly (no `[Hypotheses]`): after rescaling the frame so that the
expanding multiplier has modulus `≥ ρ > 1` everywhere, the perturbed cocycle has an invariant
unstable graph and an invariant stable graph of size `O(t)` (graph transform), so
`L(α, A e^{tw}) = ∫ log |λ_t|` with `λ_t = λ (1 + t·ulc(B⁻¹wB) + o(t))` uniformly. -/
theorem derivFormula_proof : DerivFormulaClaim := by
  intro α A hA _hUH B hBc hBp hBd hdiag hexp w hwc hwp hwt
  obtain ⟨B', l, ρ, hB'c, hB'p, hB'd, hlc, hlp, hρ, hlρ, hD, hulc⟩ :=
    DerivFormulaAux.adapt_frame hA hBc hBp hBd hdiag hexp
  have h := DerivFormulaAux.core hA hB'c hB'p hB'd hlc hlp hρ hlρ hD hwc hwp hwt
  convert h using 2
  funext x
  rw [hulc, derivCoeffs_sum_eq_ulc (hBd x)]
  congr 4
  have h11 : w x 1 1 = -w x 0 0 := by
    have := hwt x
    rw [Matrix.trace_fin_two] at this
    linear_combination this
  ext i j; fin_cases i <;> fin_cases j <;> simp [h11]

end AvilaGlobal
