import AvilaGlobal.DerivFormula

/-
# Real-analytic dependence of the Lyapunov exponent on `𝒰ℋ`  (Avila, *Global theory I*, §1.2)

`uhAnalytic_proof` proves the field `Hypotheses.uhAnalytic` (no `[Hypotheses]`): for a
real-analytic family `p ↦ A p` of analytic cocycles and `(α, A p₀) ∈ 𝒰ℋ` (any `α`), the map
`p ↦ L(α, A p)` is real-analytic near `p₀`.

* Step 1 (`bcf_analytic`): `p ↦ (x ↦ A p x)` is real-analytic into the Banach space `ℝ →ᵇ M₂`
  (uniform Taylor estimates on a period, from compactness and `changeOrigin`).
* Step 2: in an adapted frame (`DerivFormulaAux.adapt_frame`) the unstable graph `h` solves
  `h(·+α)(a + b h) = c + d h`, a polynomial equation on `ℝ →ᵇ ℂ` whose partial derivative at the
  unperturbed point `k ↦ l·k(·+α) - l⁻¹k` is invertible (`|l| ≥ ρ > 1`, Neumann series); the
  analytic implicit function theorem gives `h` analytic in the coefficients.
* Step 3: `L = ∫ log|a + b h|` (`DerivFormulaAux.lyap_of_graphs`, stable graph from
  `graphs_exist`), and `w ↦ ∫₀¹ log|1 + w|` is analytic at `0` (explicit power series).
-/

noncomputable section
open scoped Matrix.Norms.Operator NNReal ENNReal Nat ContDiff BoundedContinuousFunction
open Matrix Filter Topology Complex Set Function

namespace AvilaGlobal
open AMO
namespace UHAnalyticAux

section Step1
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Uniform Taylor data at a point. -/
def TGood (f : P × ℂ → F) (e : P × ℂ) (ρ M : ℝ) : Prop :=
  (∀ k : ℕ, ‖iteratedFDeriv ℝ k f e‖ ≤ k ! * M * ρ⁻¹ ^ k) ∧
  ∀ w : P × ℂ, ‖w‖ < ρ →
    HasSum (fun n => ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n f e (fun _ => w)) (f (e + w))

omit [CompleteSpace F] in
lemma TGood.nonneg {f : P × ℂ → F} {e : P × ℂ} {ρ M : ℝ} (h : TGood f e ρ M) : 0 ≤ M := by
  have := h.1 0
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

omit [CompleteSpace F] in
lemma TGood.mono {f : P × ℂ → F} {e : P × ℂ} {ρ M ρ' M' : ℝ} (h : TGood f e ρ M)
    (hρ' : 0 < ρ') (hρ : ρ' ≤ ρ) (hM : M ≤ M') : TGood f e ρ' M' := by
  have hM0 : 0 ≤ M := h.nonneg
  refine ⟨fun k => (h.1 k).trans ?_, fun w hw => h.2 w (hw.trans_le hρ)⟩
  have h1 : ρ⁻¹ ≤ ρ'⁻¹ := inv_anti₀ hρ' hρ
  have h0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 (hρ'.le.trans hρ)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _))
    (pow_le_pow_left₀ h0 h1 k) (pow_nonneg h0 k)
    (mul_nonneg (Nat.cast_nonneg _) (hM0.trans hM))

lemma local_tgood {f : P × ℂ → F} {q : FormalMultilinearSeries ℝ (P × ℂ) F} {e₀ : P × ℂ}
    {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f q e₀ R) :
    ∃ ρ > 0, ∃ M, ∀ y : P × ℂ, ‖y‖ < ρ → TGood f (e₀ + y) ρ M := by
  obtain ⟨r', hr'0, hr'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos
  set r : ℝ≥0 := r' / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (by exact_mod_cast hr'0)
  have hrr : ((r : ℝ≥0∞) + r) = r' := by
    rw [← ENNReal.coe_add, hr, add_halves]
  have h2R : ((r : ℝ≥0∞) + r) < R := hrr ▸ hr'R
  have h2rad : ((r : ℝ≥0∞) + r) < q.radius := h2R.trans_le hf.r_le
  have hrR : (r : ℝ≥0∞) < R := lt_of_le_of_lt le_self_add h2R
  have hrrad : (r : ℝ≥0∞) < q.radius := hrR.trans_le hf.r_le
  have hsum := q.changeOriginSeries_summable_aux₁ h2rad
  obtain ⟨-, hslice⟩ := NNReal.summable_sigma.1 hsum
  set M : ℝ≥0 := ∑' k, ∑' t : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
      ‖q (k + t.1)‖₊ * r ^ t.1 * r ^ k with hM
  refine ⟨r, by exact_mod_cast hr0, M, fun y hy => ?_⟩
  have hyr : ‖y‖₊ < r := by rw [← NNReal.coe_lt_coe]; exact hy
  have hyr' : (‖y‖₊ : ℝ≥0∞) < r := by exact_mod_cast hyr
  have hyR : (‖y‖₊ : ℝ≥0∞) < R := hyr'.trans hrR
  have hq' := hf.changeOrigin hyR
  set q' := q.changeOrigin y with hq'def
  have hcoef : ∀ k, ‖q' k‖ ≤ M * (r : ℝ)⁻¹ ^ k := by
    intro k
    have h1 : ‖q' k‖₊ ≤ ∑' t : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
        ‖q (k + t.1)‖₊ * r ^ t.1 := by
      refine (q.nnnorm_changeOrigin_le k (hyr'.trans hrrad)).trans ?_
      refine Summable.tsum_le_tsum (fun t => ?_) ?_ (q.changeOriginSeries_summable_aux₂ hrrad k)
      · gcongr
      · exact NNReal.summable_of_le (fun t => by gcongr)
          (q.changeOriginSeries_summable_aux₂ hrrad k)
    have h2 : ‖q' k‖₊ * r ^ k ≤ M := by
      calc ‖q' k‖₊ * r ^ k ≤ (∑' t : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
          ‖q (k + t.1)‖₊ * r ^ t.1) * r ^ k := by gcongr
        _ = ∑' t : Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
          ‖q (k + t.1)‖₊ * r ^ t.1 * r ^ k := (NNReal.tsum_mul_right _ _).symm
        _ ≤ M := hslice.le_tsum k (fun _ _ => by positivity)
    have h3 : ‖q' k‖ * (r : ℝ) ^ k ≤ M := by exact_mod_cast h2
    have hrk : (0 : ℝ) < (r : ℝ) ^ k := by positivity
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hrk]; exact h3
  refine ⟨fun k => ?_, fun w hw => ?_⟩
  · have hle : ‖iteratedFDeriv ℝ k f (e₀ + y)‖ ≤ k ! * ‖q' k‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
      rw [hq'.iteratedFDeriv_eq_sum_of_completeSpace v]
      calc ‖∑ σ : Equiv.Perm (Fin k), q' k (fun i => v (σ i))‖
          ≤ ∑ σ : Equiv.Perm (Fin k), ‖q' k‖ * ∏ i, ‖v i‖ := by
            refine norm_sum_le_of_le _ fun σ _ => ?_
            refine ((q' k).le_opNorm _).trans_eq ?_
            congr 1
            exact Equiv.prod_comp σ (fun i => ‖v i‖)
        _ = k ! * ‖q' k‖ * ∏ i, ‖v i‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
              nsmul_eq_mul]; ring
    calc _ ≤ k ! * ‖q' k‖ := hle
      _ ≤ k ! * (M * (r : ℝ)⁻¹ ^ k) := by gcongr; exact hcoef k
      _ = _ := by ring
  · have hwr : ‖w‖₊ < r := by rw [← NNReal.coe_lt_coe]; exact hw
    have hw' : w ∈ Metric.eball (0 : P × ℂ) (R - ‖y‖₊) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, lt_tsub_iff_right]
      calc ((‖w‖₊ : ℝ≥0∞) + ‖y‖₊) < r + r :=
            ENNReal.add_lt_add (by exact_mod_cast hwr) hyr'
        _ < R := h2R
    exact hq'.hasSum_iteratedFDeriv hw'

lemma uniform_tgood {f : P × ℂ → F} {p₀ : P} {U : Set P} (hU : U ∈ 𝓝 p₀)
    (han : ∀ x : ℝ, AnalyticAt ℝ f (p₀, (x : ℂ)))
    (hper : ∀ p ∈ U, ∀ z : ℂ, f (p, z + 1) = f (p, z)) :
    ∃ ρ > 0, ∃ M, ∀ x : ℝ, TGood f (p₀, (x : ℂ)) ρ M := by
  have hcpt : ∃ ρ > 0, ∃ M, ∀ x ∈ Icc (0:ℝ) 1, TGood f (p₀, (x : ℂ)) ρ M := by
    refine (isCompact_Icc (a := (0:ℝ)) (b := 1)).induction_on
      (p := fun S : Set ℝ => ∃ ρ > 0, ∃ M, ∀ x ∈ S, TGood f (p₀, (x : ℂ)) ρ M)
      ⟨1, one_pos, 0, fun x hx => hx.elim⟩
      (fun s t hst ⟨ρ, hρ, M, h⟩ => ⟨ρ, hρ, M, fun x hx => h x (hst hx)⟩)
      (fun s t ⟨ρ₁, h₁, M₁, k₁⟩ ⟨ρ₂, h₂, M₂, k₂⟩ => ⟨min ρ₁ ρ₂, lt_min h₁ h₂, max M₁ M₂,
        fun x hx => hx.elim
          (fun hx => (k₁ x hx).mono (lt_min h₁ h₂) (min_le_left _ _) (le_max_left _ _))
          (fun hx => (k₂ x hx).mono (lt_min h₁ h₂) (min_le_right _ _) (le_max_right _ _))⟩) ?_
    intro x _
    obtain ⟨q, R, hq⟩ := han x
    obtain ⟨ρ, hρ, M, hM⟩ := local_tgood hq
    refine ⟨Metric.ball x ρ, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hρ), ρ, hρ, M,
      fun x' hx' => ?_⟩
    have hy : ‖(((0 : P), ((x' - x : ℝ) : ℂ)) : P × ℂ)‖ < ρ := by
      rw [Prod.norm_mk, norm_zero, Complex.norm_real, Real.norm_eq_abs]
      rw [Metric.mem_ball, Real.dist_eq] at hx'
      exact max_lt hρ hx'
    have := hM _ hy
    have he : ((p₀, (x : ℂ)) : P × ℂ) + ((0 : P), ((x' - x : ℝ) : ℂ)) = (p₀, (x' : ℂ)) := by
      ext
      · simp
      · simp only [Prod.snd_add]; push_cast; ring
    rw [he] at this; exact this
  obtain ⟨ρ₀, hρ₀, M, hM⟩ := hcpt
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨min ρ₀ ρ₁, lt_min hρ₀ hρ₁, M, fun x => ?_⟩
  set x' := Int.fract x with hx'def
  set m := ⌊x⌋ with hm
  have hx' : x' ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hG := (hM x' hx').mono (lt_min hρ₀ hρ₁) (min_le_left _ _) le_rfl
  set c : P × ℂ := (0, (m : ℂ)) with hc
  have hxe : ((p₀, (x : ℂ)) : P × ℂ) = (p₀, (x' : ℂ)) + c := by
    have hx : x = x' + m := (Int.fract_add_floor x).symm
    ext
    · simp [c]
    · simp only [c, Prod.snd_add]
      conv_lhs => rw [hx]
      push_cast; ring
  have hperm : ∀ p ∈ U, ∀ z : ℂ, f (p, z + m) = f (p, z) := by
    intro p hp z
    have hP : Periodic (fun z => f (p, z)) 1 := fun z => hper p hp z
    simpa using hP.int_mul m z
  have hev : (fun e => f (e + c)) =ᶠ[𝓝 ((p₀, (x' : ℂ)) : P × ℂ)] f := by
    have hopen : {e : P × ℂ | e.1 ∈ U} ∈ 𝓝 ((p₀, (x' : ℂ)) : P × ℂ) :=
      continuous_fst.continuousAt.preimage_mem_nhds hU
    filter_upwards [hopen] with e he
    have : e + c = (e.1, e.2 + m) := by ext <;> simp [c]
    rw [this]; exact hperm e.1 he e.2
  have hD : ∀ k, iteratedFDeriv ℝ k f (p₀, (x : ℂ)) = iteratedFDeriv ℝ k f (p₀, (x' : ℂ)) := by
    intro k
    rw [hxe, ← iteratedFDeriv_comp_add_right]
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  refine ⟨fun k => by rw [hD]; exact hG.1 k, fun w hw => ?_⟩
  simp_rw [hD]
  have hw1 : p₀ + w.1 ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (norm_fst_le w).trans_lt (hw.trans_le (min_le_right _ _))
  have heq : f ((p₀, (x : ℂ)) + w) = f ((p₀, (x' : ℂ)) + w) := by
    rw [hxe]
    have : (p₀, (x' : ℂ)) + c + w = (p₀ + w.1, ((x' : ℂ) + w.2) + m) := by
      ext
      · simp [c]
      · simp [c]; ring
    rw [this, hperm _ hw1]; rfl
  rw [heq]; exact hG.2 w hw

/-- Packaging a bounded continuous family of multilinear maps. -/
def bcfMulti {k : ℕ} (D : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
    (hD : Continuous D) (K : ℝ) (hK : ∀ x, ‖D x‖ ≤ K) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) (ℝ →ᵇ F) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => BoundedContinuousFunction.ofNormedAddCommGroup (fun x => D x v)
          ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P) F v).continuous.comp hD)
          (K * ∏ i, ‖v i‖) (fun x => ((D x).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (hK x) (by positivity)))
      map_update_add' := by intro _ v i a b; ext x; exact (D x).map_update_add v i a b
      map_update_smul' := by intro _ v i c a; ext x; exact (D x).map_update_smul v i c a }
    K (fun v => (BoundedContinuousFunction.norm_le
        (mul_nonneg ((norm_nonneg _).trans (hK 0)) (by positivity))).2 fun x =>
          ((D x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hK x) (by positivity)))

omit [CompleteSpace F] in
lemma norm_bcfMulti_le {k : ℕ} (D : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
    (hD : Continuous D) (K : ℝ) (hK : ∀ x, ‖D x‖ ≤ K) : ‖bcfMulti D hD K hK‖ ≤ K := by
  unfold bcfMulti
  exact MultilinearMap.mkContinuous_norm_le _ ((norm_nonneg _).trans (hK 0)) _

theorem bcf_analytic {f : P × ℂ → F} {p₀ : P} {U : Set P} (hU : U ∈ 𝓝 p₀)
    (han : ∀ x : ℝ, AnalyticAt ℝ f (p₀, (x : ℂ)))
    (hper : ∀ p ∈ U, ∀ z : ℂ, f (p, z + 1) = f (p, z)) :
    ∃ Φ : P → ℝ →ᵇ F, AnalyticAt ℝ Φ p₀ ∧ ∀ᶠ p in 𝓝 p₀, ∀ x : ℝ, Φ p x = f (p, x) := by
  obtain ⟨ρ, hρ, M, hG⟩ := uniform_tgood hU han hper
  have hM0 : 0 ≤ M := (hG 0).nonneg
  have hA : AnalyticOnNhd ℝ f {e | AnalyticAt ℝ f e} := fun e he => he
  set ι : P →L[ℝ] P × ℂ := ContinuousLinearMap.inl ℝ P ℂ with hι
  set D : ∀ k : ℕ, ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F := fun k x =>
    ((k ! : ℝ)⁻¹) • (iteratedFDeriv ℝ k f (p₀, (x : ℂ))).compContinuousLinearMap
      (fun _ => ι) with hDdef
  have hDc : ∀ k, Continuous (D k) := by
    intro k
    have h1 : Continuous fun x : ℝ => iteratedFDeriv ℝ k f (p₀, (x : ℂ)) := by
      refine continuous_iff_continuousAt.2 fun x => ?_
      exact ContinuousAt.comp (g := iteratedFDeriv ℝ k f)
        (f := fun x : ℝ => ((p₀, (x : ℂ)) : P × ℂ))
        ((hA.iteratedFDeriv k) _ (han x)).continuousAt
        ((by fun_prop : Continuous fun x : ℝ => ((p₀, (x : ℂ)) : P × ℂ)).continuousAt)
    have h2 : Continuous fun x : ℝ =>
        (iteratedFDeriv ℝ k f (p₀, (x : ℂ))).compContinuousLinearMap (fun _ : Fin k => ι) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => ι)).continuous.comp h1
    exact h2.const_smul ((k ! : ℝ)⁻¹)
  have hDb : ∀ k x, ‖D k x‖ ≤ M * ρ⁻¹ ^ k := by
    intro k x
    have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    calc ‖D k x‖ ≤ (k ! : ℝ)⁻¹ * (‖iteratedFDeriv ℝ k f (p₀, (x : ℂ))‖ * ∏ _i : Fin k, ‖ι‖) := by
          rw [hDdef, norm_smul, norm_inv, Real.norm_natCast]
          gcongr
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (k ! : ℝ)⁻¹ * ((k ! * M * ρ⁻¹ ^ k) * 1) := by
          gcongr
          · exact (hG x).1 k
          · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ P ℂ)
      _ = M * ρ⁻¹ ^ k := by field_simp
  set Q : FormalMultilinearSeries ℝ P (ℝ →ᵇ F) := fun k => bcfMulti (D k) (hDc k) _ (hDb k)
    with hQdef
  have hQ : ∀ k, ‖Q k‖ ≤ M * ρ⁻¹ ^ k := fun k => norm_bcfMulti_le _ _ _ _
  set ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩ with hρ'
  have hrad : (ρ' : ℝ≥0∞) ≤ Q.radius := by
    refine Q.le_radius_of_bound M fun n => ?_
    calc ‖Q n‖ * (ρ' : ℝ) ^ n = ‖Q n‖ * ρ ^ n := rfl
      _ ≤ M * ρ⁻¹ ^ n * ρ ^ n := by gcongr; exact hQ n
      _ = M := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hρ.ne', one_pow, mul_one]
  have hpos : (0 : ℝ≥0∞) < ρ' := by
    have : (0 : ℝ≥0) < ρ' := hρ
    exact_mod_cast this
  have hS := Q.hasFPowerSeriesOnBall (hpos.trans_le hrad)
  refine ⟨fun p => Q.sum (p - p₀), ?_, ?_⟩
  · have h0 : AnalyticAt ℝ Q.sum (p₀ - p₀) := by rw [sub_self]; exact hS.analyticAt
    exact AnalyticAt.comp (g := Q.sum) (f := fun p => p - p₀) h0
      (analyticAt_id.sub analyticAt_const)
  · filter_upwards [Metric.ball_mem_nhds p₀ hρ] with p hp x
    have hv : p - p₀ ∈ Metric.eball (0 : P) Q.radius := by
      refine Metric.eball_subset_eball hrad ?_
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
      have : ‖p - p₀‖₊ < ρ' := by
        rw [← NNReal.coe_lt_coe]; show ‖p - p₀‖ < ρ; simpa [dist_eq_norm] using hp
      exact_mod_cast this
    have h1 := (hS.hasSum hv).mapL (BoundedContinuousFunction.evalCLM ℝ x)
    simp only [zero_add] at h1
    have h2 := (hG x).2 ((p - p₀, 0) : P × ℂ) (by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _), ← dist_eq_norm]; exact hp)
    have e1 : ((p₀, (x : ℂ)) : P × ℂ) + (p - p₀, 0) = (p, (x : ℂ)) := by ext <;> simp
    rw [e1] at h2
    refine h1.unique ?_
    convert h2 using 1
    funext n
    rfl

end Step1

local notation "𝔹" => ℝ →ᵇ ℂ

/-- Translation by `β` on bounded continuous functions. -/
def shiftL (β : ℝ) : 𝔹 →L[ℝ] 𝔹 :=
  LinearMap.mkContinuous
    { toFun := fun g => g.compContinuous ⟨fun x => x + β, by fun_prop⟩
      map_add' := fun g h => by ext x; simp
      map_smul' := fun c g => by ext x; simp }
    1 (fun g => by rw [one_mul]; exact BoundedContinuousFunction.norm_compContinuous_le _ _)

@[simp] lemma shiftL_apply (β : ℝ) (g : 𝔹) (x : ℝ) : shiftL β g x = g (x + β) := rfl

lemma norm_shiftL_le (β : ℝ) : ‖shiftL β‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `g ↦ ∫₀¹ Re g`. -/
def intL : 𝔹 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x in (0:ℝ)..1, (g x).re
      map_add' := fun g h => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, Complex.add_re]
        exact intervalIntegral.integral_add
          ((continuous_re.comp g.continuous).intervalIntegrable _ _)
          ((continuous_re.comp h.continuous).intervalIntegrable _ _)
      map_smul' := fun c g => by
        simp only [BoundedContinuousFunction.coe_smul, Complex.real_smul, Complex.re_ofReal_mul,
          RingHom.id_apply, smul_eq_mul]
        exact intervalIntegral.integral_const_mul _ _ }
    1 (fun g => by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖g‖)
        (f := fun x => (g x).re) (fun x _ => by
          rw [Real.norm_eq_abs]
          exact (Complex.abs_re_le_norm _).trans (g.norm_coe_le_norm x))
      simpa using this)

lemma intL_apply (g : 𝔹) : intL g = ∫ x in (0:ℝ)..1, (g x).re := rfl

lemma norm_intL_le : ‖intL‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The power series of `w ↦ ∫₀¹ log |1 + w|`. -/
def logSeries : FormalMultilinearSeries ℝ 𝔹 ℝ := fun n =>
  ((-1 : ℝ) ^ (n + 1) / n) •
    intL.compContinuousMultilinearMap (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n 𝔹)

/-- `Ψ w = ∫₀¹ log |1 + w|`. -/
def Ψ (w : 𝔹) : ℝ := ∫ x in (0:ℝ)..1, Real.log ‖1 + w x‖

lemma hasFPowerSeries_Ψ : HasFPowerSeriesOnBall Ψ logSeries 0 1 := by
  have hc : ∀ n : ℕ, |(-1 : ℝ) ^ (n + 1) / n| ≤ 1 := by
    intro n
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg _)
  have hb : ∀ n, ‖logSeries n‖ ≤ 1 := by
    intro n
    simp only [logSeries]
    rw [norm_smul, Real.norm_eq_abs]
    calc |(-1 : ℝ) ^ (n + 1) / n| * ‖intL.compContinuousMultilinearMap
          (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n 𝔹)‖ ≤ 1 * (1 * 1) := by
          gcongr
          · exact hc n
          · refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
            rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin]
            simpa using norm_intL_le
      _ = 1 := by norm_num
  refine ⟨?_, by norm_num, fun {y} hy => ?_⟩
  · have := logSeries.le_radius_of_bound 1 (r := 1) (fun n => by simpa using hb n)
    simpa using this
  · have hy' : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] at hy
      have : ‖y‖₊ < 1 := by exact_mod_cast hy
      exact_mod_cast this
    set t : ℕ → 𝔹 := fun n => ((-1 : ℝ) ^ (n + 1) / n) • y ^ n with ht
    have hts : Summable t := by
      refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hy')
        (fun n => ?_)
      rw [ht, norm_smul, Real.norm_eq_abs]
      calc |(-1 : ℝ) ^ (n + 1) / n| * ‖y ^ n‖ ≤ 1 * ‖y‖ ^ n := by
            gcongr
            · exact hc n
            · exact norm_pow_le _ _
        _ = ‖y‖ ^ n := one_mul _
    have hT := hts.hasSum
    have hpt : ∀ x, (∑' n, t n) x = Complex.log (1 + y x) := by
      intro x
      have h1 := hT.mapL (BoundedContinuousFunction.evalCLM ℝ x)
      refine h1.unique ?_
      convert hasSum_taylorSeries_log (z := y x) ((y.norm_coe_le_norm x).trans_lt hy') using 1
      funext n
      simp only [ht, BoundedContinuousFunction.evalCLM_apply, BoundedContinuousFunction.coe_smul,
        Pi.smul_apply, BoundedContinuousFunction.coe_pow, Pi.pow_apply, Complex.real_smul]
      push_cast
      ring
    have := hT.mapL intL
    simp only [zero_add]
    convert this using 1
    · funext n
      simp only [logSeries, ht, _root_.smul_apply,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate,
        map_smul]
    · rw [intL_apply, Ψ]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hpt, Complex.log_re]

lemma analyticAt_Ψ : AnalyticAt ℝ Ψ 0 := hasFPowerSeries_Ψ.analyticAt

/-! ### The graph equation -/

/-- `F((a,b,c,d), h) = h(·+α) (a + b h) - c - d h`. -/
def Fn (α : ℝ) (v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) : 𝔹 :=
  shiftL α v.2 * (v.1.1 + v.1.2.1 * v.2) - v.1.2.2.1 - v.1.2.2.2 * v.2

lemma an_fst {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F × G} {x : E}
    (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun y => (f y).1) x :=
  analyticAt_fst.comp hf

lemma an_snd {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F × G} {x : E}
    (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun y => (f y).2) x :=
  analyticAt_snd.comp hf

lemma analyticAt_Fn (α : ℝ) (u : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) : AnalyticAt ℝ (Fn α) u := by
  have hid : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v) u := analyticAt_id
  have h2 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.2) u := an_snd hid
  have h1 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.1) u := an_fst hid
  have h11 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.1.1) u := an_fst h1
  have h12 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.1.2.1) u := an_fst (an_snd h1)
  have h13 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.1.2.2.1) u :=
    an_fst (an_snd (an_snd h1))
  have h14 : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => v.1.2.2.2) u :=
    an_snd (an_snd (an_snd h1))
  have hS : AnalyticAt ℝ (fun v : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 => shiftL α v.2) u :=
    (shiftL α).analyticAt _ |>.comp h2
  exact ((hS.mul (h11.add (h12.mul h2))).sub h13).sub (h14.mul h2)

/-- Multiplication operator. -/
def mulL (g : 𝔹) : 𝔹 →L[ℝ] 𝔹 := ContinuousLinearMap.mul ℝ 𝔹 g

@[simp] lemma mulL_apply (g h : 𝔹) : mulL g h = g * h := rfl

lemma deriv_invertible (α : ℝ) {l li : 𝔹} (hli : li * l = 1) {ρ : ℝ} (hρ : 1 < ρ)
    (hlin : ‖li‖ ≤ ρ⁻¹) : ((mulL l).comp (shiftL α) - mulL li).IsInvertible := by
  have hpt : ∀ x, li x * l x = 1 := fun x => by
    have := congrArg (fun g : 𝔹 => g x) hli; simpa using this
  set K : 𝔹 →L[ℝ] 𝔹 := (shiftL (-α)).comp (mulL (li * li)) with hK
  have hρ0 : 0 < ρ := by linarith
  have hKn : ‖K‖ < 1 := by
    calc ‖K‖ ≤ ‖shiftL (-α)‖ * ‖mulL (li * li)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (ρ⁻¹ * ρ⁻¹) := by
          gcongr
          · exact norm_shiftL_le _
          · refine (ContinuousLinearMap.opNorm_mul_apply_le ℝ 𝔹 _).trans ?_
            refine (norm_mul_le _ _).trans ?_
            gcongr
      _ < 1 := by
          rw [one_mul, ← mul_inv]
          exact inv_lt_one_of_one_lt₀ (by nlinarith)
  set u₁ : (𝔹 →L[ℝ] 𝔹)ˣ :=
    { val := (mulL l).comp (shiftL α)
      inv := (shiftL (-α)).comp (mulL li)
      val_inv := by
        refine ContinuousLinearMap.ext fun g => BoundedContinuousFunction.ext fun x => ?_
        show l x * (li (x + α + -α) * g (x + α + -α)) = g x
        rw [add_neg_cancel_right, ← mul_assoc, mul_comm (l x), hpt, one_mul]
      inv_val := by
        refine ContinuousLinearMap.ext fun g => BoundedContinuousFunction.ext fun x => ?_
        show li (x + -α) * (l (x + -α) * g (x + -α + α)) = g x
        rw [neg_add_cancel_right, ← mul_assoc, hpt, one_mul] }
  set w := u₁ * Units.oneSub K hKn with hw
  have hD : (mulL l).comp (shiftL α) - mulL li = (w : 𝔹 →L[ℝ] 𝔹) := by
    rw [hw, Units.val_mul, Units.val_oneSub]
    refine ContinuousLinearMap.ext fun g => BoundedContinuousFunction.ext fun x => ?_
    show l x * g (x + α) - li x * g x =
      l x * (g (x + α) - li (x + α + -α) * li (x + α + -α) * g (x + α + -α))
    rw [add_neg_cancel_right]
    linear_combination (li x * g x) * hpt x
  rw [hD]
  exact ContinuousLinearMap.IsInvertible.of_inverse (g := ((w⁻¹ : (𝔹 →L[ℝ] 𝔹)ˣ) : 𝔹 →L[ℝ] 𝔹))
    w.mul_inv w.inv_mul

lemma fderiv_Fn_inr (α : ℝ) (l li : 𝔹) :
    fderiv ℝ (Fn α) (((l, 0, 0, li), 0) : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) ∘L
      ContinuousLinearMap.inr ℝ (𝔹 × 𝔹 × 𝔹 × 𝔹) 𝔹 = (mulL l).comp (shiftL α) - mulL li := by
  set u : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 := ((l, 0, 0, li), 0)
  have hd : HasFDerivAt (Fn α) (fderiv ℝ (Fn α) u) u :=
    (analyticAt_Fn α u).differentiableAt.hasFDerivAt
  have h2 := hd.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
  have h3 : HasFDerivAt ((Fn α) ∘ fun k => (u.1, k)) ((mulL l).comp (shiftL α) - mulL li) u.2 := by
    have : ((Fn α) ∘ fun k => (u.1, k)) = ⇑((mulL l).comp (shiftL α) - mulL li) := by
      funext k
      simp only [Function.comp_apply, Fn, u, zero_mul, add_zero, sub_zero,
        _root_.sub_apply, ContinuousLinearMap.comp_apply, mulL_apply]
      ring
    rw [this]; exact ContinuousLinearMap.hasFDerivAt _
  exact h2.unique h3


/-! ### A diagonalizing frame (copied from `Cod1.lean`, which carries `[Hypotheses]`) -/

theorem frame_of_isUH {α : ℝ} {A : ℝ → M2} (h : IsUH α A) :
    ∃ B : ℝ → M2, Continuous B ∧ Function.Periodic B 1 ∧ (∀ x, (B x).det = 1) ∧
      (∀ x, ((B (x + α))⁻¹ * A x * B x) 0 1 = 0 ∧ ((B (x + α))⁻¹ * A x * B x) 1 0 = 0) ∧
      (∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ < ‖iter α A n x *ᵥ (B x *ᵥ ![1, 0])‖) := by
  obtain ⟨u, s, huc, hsc, hup, hsp, hu0, hs0, hui, hsi, n, hn, hexp⟩ := h
  set d : ℝ → ℂ := fun x => u x 0 * s x 1 - u x 1 * s x 0 with hd
  have hd0 : ∀ x, d x ≠ 0 := by
    intro x hdx
    have hpar : ∃ c : ℂ, s x = c • u x := by
      by_cases h0 : u x 0 = 0
      · have h1 : u x 1 ≠ 0 := by
          intro h1; apply hu0 x; ext i; fin_cases i <;> simp [h0, h1]
        have hs0' : s x 0 = 0 := by
          have : u x 1 * s x 0 = 0 := by
            simp only [hd, h0, zero_mul, zero_sub] at hdx; simpa using hdx
          exact (mul_eq_zero.1 this).resolve_left h1
        refine ⟨s x 1 / u x 1, ?_⟩
        ext i; fin_cases i
        · simp [h0, hs0']
        · simp [div_mul_cancel₀ _ h1]
      · refine ⟨s x 0 / u x 0, ?_⟩
        ext i; fin_cases i
        · simp [div_mul_cancel₀ _ h0]
        · show s x 1 = s x 0 / u x 0 * u x 1
          have : u x 0 * s x 1 - u x 1 * s x 0 = 0 := hdx
          field_simp
          linear_combination this
    obtain ⟨c, hc⟩ := hpar
    have hc0 : c ≠ 0 := by rintro rfl; apply hs0 x; rw [hc, zero_smul]
    obtain ⟨h1, h2⟩ := hexp x
    rw [hc, Matrix.mulVec_smul, norm_smul, norm_smul] at h1
    have := (mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc0)).1 h1
    linarith
  set B : ℝ → M2 := fun x => !![u x 0, s x 0 / d x; u x 1, s x 1 / d x] with hB
  have hcol : ∀ x, B x *ᵥ ![1, 0] = u x := by
    intro x; ext i; fin_cases i <;> simp [hB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hdc : Continuous d := by
    simp only [hd]
    have h0 : Continuous fun x => u x 0 := (continuous_apply 0).comp huc
    have h1 : Continuous fun x => u x 1 := (continuous_apply 1).comp huc
    have h2 : Continuous fun x => s x 0 := (continuous_apply 0).comp hsc
    have h3 : Continuous fun x => s x 1 := (continuous_apply 1).comp hsc
    fun_prop
  have hdet : ∀ x, (B x).det = 1 := by
    intro x
    simp only [hB, det_fin_two_of]
    field_simp [hd0 x]
    simp only [hd]; ring
  refine ⟨B, ?_, ?_, hdet, ?_, ⟨n, hn, fun x => ?_⟩⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hB]
    · exact (continuous_apply 0).comp huc
    · exact ((continuous_apply 0).comp hsc).div hdc hd0
    · exact (continuous_apply 1).comp huc
    · exact ((continuous_apply 1).comp hsc).div hdc hd0
  · intro x
    have hdp : d (x + 1) = d x := by simp only [hd, hup x, hsp x]
    simp only [hB, hup x, hsp x, hdp]
  · intro x
    obtain ⟨c, hc⟩ := hui x
    obtain ⟨c', hc'⟩ := hsi x
    set D : M2 := !![c, 0; 0, c' * d (x + α) / d x] with hD
    have hAB : A x * B x = B (x + α) * D := by
      have e0 := congrFun hc 0
      have e1 := congrFun hc 1
      have f0 := congrFun hc' 0
      have f1 := congrFun hc' 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
        at e0 e1 f0 f1
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [hB, hD, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination e0
      · field_simp [hd0 x, hd0 (x + α)]; linear_combination f0
      · linear_combination e1
      · field_simp [hd0 x, hd0 (x + α)]; linear_combination f1
    have hu : IsUnit (B (x + α)).det := by rw [hdet]; exact isUnit_one
    have : (B (x + α))⁻¹ * A x * B x = D := by
      rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]; simp [hD]
  · rw [hcol]; exact (hexp x).2

/-- A bounded continuous function from a continuous periodic one. -/
def ofPer {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hc : Continuous f)
    (hp : Periodic f 1) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hc _
    (Classical.choose_spec (UHOpenAux.per_bound hc hp))

@[simp] lemma ofPer_apply {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hc : Continuous f)
    (hp : Periodic f 1) (x : ℝ) : ofPer f hc hp x = f x := rfl

lemma norm_comp_le4 (v : 𝔹 × 𝔹 × 𝔹 × 𝔹) :
    ‖v.1‖ ≤ ‖v‖ ∧ ‖v.2.1‖ ≤ ‖v‖ ∧ ‖v.2.2.1‖ ≤ ‖v‖ ∧ ‖v.2.2.2‖ ≤ ‖v‖ :=
  ⟨norm_fst_le v, (norm_fst_le _).trans (norm_snd_le v),
    (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le v)),
    (norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le v))⟩

set_option maxHeartbeats 1000000 in
theorem main_local {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ} {U : Set P}
    {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A) (α : ℝ) {p₀ : P} (hp₀ : p₀ ∈ U)
    (hUH : UH α (A p₀)) :
    ∃ G : P → ℝ, AnalyticAt ℝ G p₀ ∧ ∀ᶠ p in 𝓝 p₀, L α (A p) 0 = G p := by
  have hU : U ∈ 𝓝 p₀ := hA.isOpen.mem_nhds hp₀
  have hδ : 0 < δ := (hA.cocycle p₀ hp₀).pos
  have hδ' : |(0:ℝ)| < δ := by simpa using hδ
  -- Step 1: the family as an analytic map into bounded continuous functions
  obtain ⟨Φ, hΦ, hΦe⟩ := bcf_analytic (f := fun q : P × ℂ => A q.1 q.2) hU
    (fun x => hA.analytic _ ⟨hp₀, show ((x : ℂ)) ∈ strip δ by simp [strip, hδ]⟩)
    (fun p hp z => (hA.cocycle p hp).periodic z)
  -- the adapted frame at `p₀`
  have hX₀ : IsSLCocycle (shift (A p₀) 0) := (hA.cocycle p₀ hp₀).isSLCocycle_shift hδ'
  obtain ⟨B, hBc, hBp, hBd, hdiag, hexp⟩ := frame_of_isUH hUH
  obtain ⟨B', l, ρ, hB'c, hB'p, hB'd, hlc, hlp, hρ, hlρ, hD, -⟩ :=
    DerivFormulaAux.adapt_frame hX₀ hBc hBp hBd hdiag hexp
  have hρ0 : 0 < ρ := by linarith
  have hl0 : ∀ x, l x ≠ 0 := fun x h => by
    have := hlρ x; rw [h, norm_zero] at this; linarith
  have hBi_c : Continuous fun x => (B' (x + α))⁻¹ :=
    (DerivFormulaAux.continuous_inv_of_det hB'c hB'd).comp (continuous_id.add continuous_const)
  have hBi_p : Periodic (fun x => (B' (x + α))⁻¹) 1 := fun x => by
    simp only [add_right_comm x 1 α, hB'p (x + α)]
  have hli_c : Continuous fun x => (l x)⁻¹ := hlc.inv₀ hl0
  have hli_p : Periodic (fun x => (l x)⁻¹) 1 := fun x => by simp only [hlp x]
  set Bh : ℝ →ᵇ M2 := ofPer B' hB'c hB'p with hBh
  set Bih : ℝ →ᵇ M2 := ofPer _ hBi_c hBi_p with hBih
  set lh : 𝔹 := ofPer l hlc hlp with hlh
  set lih : 𝔹 := ofPer _ hli_c hli_p with hlih
  have hlil : lih * lh = 1 := by
    ext x; show (l x)⁻¹ * l x = 1; exact inv_mul_cancel₀ (hl0 x)
  have hlin : ‖lih‖ ≤ ρ⁻¹ := (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => by
    show ‖(l x)⁻¹‖ ≤ ρ⁻¹; rw [norm_inv]; exact inv_anti₀ hρ0 (hlρ x)
  -- the conjugated entries as a continuous linear map
  set conjL : (ℝ →ᵇ M2) →L[ℝ] (ℝ →ᵇ M2) :=
    (ContinuousLinearMap.mul ℝ (ℝ →ᵇ M2) Bih).comp
      ((ContinuousLinearMap.mul ℝ (ℝ →ᵇ M2)).flip Bh) with hconjL
  set entL : Fin 2 → Fin 2 → (ℝ →ᵇ M2) →L[ℝ] 𝔹 := fun i j =>
    ContinuousLinearMap.compLeftContinuousBounded ℝ ((entryCLM i j).restrictScalars ℝ)
    with hentL
  set Lb : (ℝ →ᵇ M2) →L[ℝ] (𝔹 × 𝔹 × 𝔹 × 𝔹) :=
    ((entL 0 0).comp conjL).prod (((entL 0 1).comp conjL).prod
      (((entL 1 0).comp conjL).prod ((entL 1 1).comp conjL))) with hLb
  set Nm : P → ℝ → M2 := fun p x => (B' (x + α))⁻¹ * shift (A p) 0 x * B' x with hNm
  have hLbx : ∀ (g : ℝ →ᵇ M2) (x : ℝ), (Lb g).1 x = (Bih x * (g x * Bh x)) 0 0 ∧
      (Lb g).2.1 x = (Bih x * (g x * Bh x)) 0 1 ∧ (Lb g).2.2.1 x = (Bih x * (g x * Bh x)) 1 0 ∧
      (Lb g).2.2.2 x = (Bih x * (g x * Bh x)) 1 1 := fun g x => ⟨rfl, rfl, rfl, rfl⟩
  have hLbe : ∀ p, (∀ x : ℝ, Φ p x = A p x) → ∀ x : ℝ,
      (Lb (Φ p)).1 x = Nm p x 0 0 ∧ (Lb (Φ p)).2.1 x = Nm p x 0 1 ∧
      (Lb (Φ p)).2.2.1 x = Nm p x 1 0 ∧ (Lb (Φ p)).2.2.2 x = Nm p x 1 1 := by
    intro p hp x
    have hs : shift (A p) 0 x = A p x := by simp [shift]
    have e1 : Nm p x = (B' (x + α))⁻¹ * (A p x * B' x) := by
      simp only [hNm, hs, Matrix.mul_assoc]
    have hm : Bih x * (Φ p x * Bh x) = Nm p x := by
      rw [e1, hp x] <;> rfl
    obtain ⟨h1, h2, h3, h4⟩ := hLbx (Φ p) x
    rw [hm] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set e : P → 𝔹 × 𝔹 × 𝔹 × 𝔹 := fun p => Lb (Φ p) with he
  have hea : AnalyticAt ℝ e p₀ := (Lb.analyticAt _).comp hΦ
  have hΦ0 : ∀ x : ℝ, Φ p₀ x = A p₀ x := hΦe.self_of_nhds
  set u₀ : (𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹 := ((lh, 0, 0, lih), 0) with hu₀
  have he0 : e p₀ = u₀.1 := by
    have hN0 : ∀ x, Nm p₀ x = !![l x, 0; 0, (l x)⁻¹] := fun x => hD x
    have h := hLbe p₀ hΦ0
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ext x
    · show (Lb (Φ p₀)).1 x = l x
      rw [(h x).1, hN0]; simp
    · show (Lb (Φ p₀)).2.1 x = 0
      rw [(h x).2.1, hN0]; simp
    · show (Lb (Φ p₀)).2.2.1 x = 0
      rw [(h x).2.2.1, hN0]; simp
    · show (Lb (Φ p₀)).2.2.2 x = (l x)⁻¹
      rw [(h x).2.2.2, hN0]; simp
  -- the implicit function theorem
  have cdf : ContDiffAt ℝ ω (Fn α) u₀ := (analyticAt_Fn α u₀).contDiffAt
  have hinv : (fderiv ℝ (Fn α) u₀ ∘L
      ContinuousLinearMap.inr ℝ (𝔹 × 𝔹 × 𝔹 × 𝔹) 𝔹).IsInvertible := by
    rw [hu₀, fderiv_Fn_inr]; exact deriv_invertible α hlil hρ hlin
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := cdf.implicitFunction pn hinv with hψ
  have hψa : AnalyticAt ℝ ψ u₀.1 := (cdf.contDiffAt_implicitFunction pn hinv).analyticAt
  have hψ0 : ψ u₀.1 = 0 := cdf.implicitFunction_apply_self pn hinv
  have hψeq := cdf.eventually_apply_implicitFunction pn hinv
  have hψuniq := cdf.eventually_apply_eq_iff_implicitFunction pn hinv
  have hFu : Fn α u₀ = 0 := by simp [Fn, hu₀]
  have hψa' : AnalyticAt ℝ ψ (e p₀) := by rw [he0]; exact hψa
  set h : P → 𝔹 := fun p => ψ (e p) with hh
  have hha : AnalyticAt ℝ h p₀ := hψa'.comp hea
  have hh0 : h p₀ = 0 := by simp only [hh, he0, hψ0]
  set lam : P → 𝔹 := fun p => (e p).1 + (e p).2.1 * h p with hlam
  have hlama : AnalyticAt ℝ lam p₀ := (an_fst hea).add ((an_fst (an_snd hea)).mul hha)
  have hlam0 : lam p₀ = lh := by simp [hlam, he0, hh0, hu₀]
  set uu : P → 𝔹 := fun p => (lam p - lh) * lih with huu
  have huua : AnalyticAt ℝ uu p₀ := (hlama.sub analyticAt_const).mul analyticAt_const
  have huu0 : uu p₀ = 0 := by simp [huu, hlam0]
  set c₀ : ℝ := ∫ x in (0:ℝ)..1, Real.log ‖l x‖ with hc₀
  have hΨa : AnalyticAt ℝ Ψ (uu p₀) := by rw [huu0]; exact analyticAt_Ψ
  refine ⟨fun p => c₀ + Ψ (uu p), analyticAt_const.add (hΨa.comp huua), ?_⟩
  -- eventual properties
  set ε : ℝ := (ρ - 1) / 5 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have E3 : ∀ᶠ p in 𝓝 p₀, Fn α (e p, h p) = 0 := by
    rw [← he0] at hψeq
    filter_upwards [hea.continuousAt.tendsto.eventually hψeq] with p hp
    rw [hp, hFu]
  have hc2 : ContinuousAt (fun p => shiftL 1 (h p)) p₀ :=
    (shiftL 1).continuous.continuousAt.comp hha.continuousAt
  have hT : Tendsto (fun p => (e p, shiftL 1 (h p))) (𝓝 p₀) (𝓝 u₀) := by
    have := (hea.continuousAt.prodMk hc2).tendsto
    have hv : (e p₀, shiftL 1 (h p₀)) = u₀ := by rw [he0, hh0, map_zero]
    rwa [hv] at this
  have E4 := hT.eventually hψuniq
  have E5 : ∀ᶠ p in 𝓝 p₀, dist (e p) (e p₀) < ε :=
    Metric.tendsto_nhds.1 hea.continuousAt.tendsto ε hε0
  have E6 : ∀ᶠ p in 𝓝 p₀, dist (h p) (h p₀) < 1 / 2 :=
    Metric.tendsto_nhds.1 hha.continuousAt.tendsto _ (by norm_num)
  have E7 : ∀ᶠ p in 𝓝 p₀, dist (lam p) (lam p₀) < ρ - 1 :=
    Metric.tendsto_nhds.1 hlama.continuousAt.tendsto _ (by linarith)
  have E8 : ∀ᶠ p in 𝓝 p₀, dist (uu p) (uu p₀) < 1 :=
    Metric.tendsto_nhds.1 huua.continuousAt.tendsto _ one_pos
  filter_upwards [hU, hΦe, E3, E4, E5, E6, E7, E8] with p hpU hpΦ hp3 hp4 hp5 hp6 hp7 hp8
  rw [he0, dist_eq_norm] at hp5
  rw [hh0, dist_zero_right] at hp6
  rw [hlam0, dist_eq_norm] at hp7
  rw [huu0, dist_zero_right] at hp8
  have hent := hLbe p hpΦ
  have hent' : ∀ x, (e p).1 x = Nm p x 0 0 ∧ (e p).2.1 x = Nm p x 0 1 ∧
      (e p).2.2.1 x = Nm p x 1 0 ∧ (e p).2.2.2 x = Nm p x 1 1 := hent
  have hX : IsSLCocycle (shift (A p) 0) := (hA.cocycle p hpU).isSLCocycle_shift hδ'
  have hNc : Continuous (Nm p) := (hBi_c.mul hX.continuous).mul hB'c
  have hNp : Periodic (Nm p) 1 := fun x => by
    simp only [hNm, add_right_comm x 1 α, hB'p (x + α), hB'p x, hX.periodic x]
  have hNd : ∀ x, (Nm p x).det = 1 := fun x => by
    simp only [hNm, Matrix.det_mul, hX.det_eq_one, hB'd, Matrix.det_nonsing_inv, mul_one,
      inv_one, Ring.inverse_one]
  -- periodicity of the unstable graph
  have hep : ∀ x, (e p).1 (x + 1) = (e p).1 x ∧ (e p).2.1 (x + 1) = (e p).2.1 x ∧
      (e p).2.2.1 (x + 1) = (e p).2.2.1 x ∧ (e p).2.2.2 (x + 1) = (e p).2.2.2 x := by
    intro x
    obtain ⟨a1, b1, c1, d1⟩ := hent (x + 1)
    obtain ⟨a0, b0, c0, d0⟩ := hent x
    rw [hNp x] at a1 b1 c1 d1
    exact ⟨a1.trans a0.symm, b1.trans b0.symm, c1.trans c0.symm, d1.trans d0.symm⟩
  have hTF : Fn α (e p, shiftL 1 (h p)) = shiftL 1 (Fn α (e p, h p)) := by
    ext x
    obtain ⟨ha, hb, hc, hd⟩ := hep x
    simp only [Fn, shiftL_apply, BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_mul, BoundedContinuousFunction.coe_add, Pi.sub_apply,
      Pi.mul_apply, Pi.add_apply, ha, hb, hc, hd, add_right_comm x 1 α]
  have hper : ψ (e p) = shiftL 1 (h p) := hp4.1 (by rw [hTF, hp3, map_zero, hFu])
  have hhp : Periodic (fun x => h p x) 1 := fun x => by
    have := congrArg (fun g : 𝔹 => g x) hper
    simp only [shiftL_apply] at this
    exact this.symm
  -- pointwise bounds
  have hb4 := norm_comp_le4 (e p - u₀.1)
  have hpt : ∀ (g : 𝔹) (x : ℝ), ‖g x‖ ≤ ‖g‖ := fun g x => g.norm_coe_le_norm x
  have hpa : ∀ x, ‖Nm p x 0 0 - l x‖ < ε := fun x => by
    rw [← (hent x).1]
    calc ‖(e p).1 x - l x‖ = ‖((e p - u₀.1).1) x‖ := by simp [hu₀, hlh]
      _ ≤ ‖e p - u₀.1‖ := (hpt _ x).trans hb4.1
      _ < ε := hp5
  have hpb : ∀ x, ‖Nm p x 0 1‖ < ε := fun x => by
    rw [← (hent x).2.1]
    calc ‖(e p).2.1 x‖ = ‖((e p - u₀.1).2.1) x‖ := by simp [hu₀]
      _ ≤ ‖e p - u₀.1‖ := (hpt _ x).trans hb4.2.1
      _ < ε := hp5
  have hpc : ∀ x, ‖Nm p x 1 0‖ < ε := fun x => by
    rw [← (hent x).2.2.1]
    calc ‖(e p).2.2.1 x‖ = ‖((e p - u₀.1).2.2.1) x‖ := by simp [hu₀]
      _ ≤ ‖e p - u₀.1‖ := (hpt _ x).trans hb4.2.2.1
      _ < ε := hp5
  have hpd : ∀ x, ‖Nm p x 1 1 - (l x)⁻¹‖ < ε := fun x => by
    rw [← (hent x).2.2.2]
    calc ‖(e p).2.2.2 x - (l x)⁻¹‖ = ‖((e p - u₀.1).2.2.2) x‖ := by simp [hu₀, hlih]
      _ ≤ ‖e p - u₀.1‖ := (hpt _ x).trans hb4.2.2.2
      _ < ε := hp5
  have hρinv : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ.le
  have hA0 : ∀ x, ρ - ε < ‖Nm p x 0 0‖ := fun x => by
    have h1 := norm_sub_norm_le (l x) (Nm p x 0 0)
    rw [norm_sub_rev] at h1
    linarith [hlρ x, hpa x]
  have hD1 : ∀ x, ‖Nm p x 1 1‖ < ρ⁻¹ + ε := fun x => by
    have h1 := norm_sub_norm_le (Nm p x 1 1) (l x)⁻¹
    have h2 : ‖(l x)⁻¹‖ ≤ ρ⁻¹ := by rw [norm_inv]; exact inv_anti₀ hρ0 (hlρ x)
    linarith [hpd x]
  obtain ⟨-, g, -, -, hgc, hgp, -, hgb, -, hgeq⟩ := DerivFormulaAux.graphs_exist (α := α)
    hNc hNp (r := 1 / 2) (by norm_num)
    (fun x => by linarith [hpb x, hpc x, hD1 x, hA0 x, norm_nonneg (Nm p x 0 1)])
    (fun x => by linarith [hpb x, hpc x, hD1 x, hA0 x, norm_nonneg (Nm p x 1 0)])
    (fun x => by
      have ht : 1 < ‖Nm p x 0 0‖ - 1 / 2 * ‖Nm p x 0 1‖ := by linarith [hpb x, hA0 x]
      rw [hNd x, norm_one]; nlinarith)
    (fun x => by
      have ht : 1 < ‖Nm p x 0 0‖ - 1 / 2 * ‖Nm p x 1 0‖ := by linarith [hpc x, hA0 x]
      rw [hNd x, norm_one]; nlinarith)
  have hhg : ∀ x, h p x * g x ≠ 1 := fun x heq => by
    have h1 : ‖h p x‖ < 1 / 2 := (hpt _ x).trans_lt hp6
    have h2 := hgb x
    have : ‖h p x * g x‖ < 1 := by
      rw [norm_mul]; nlinarith [norm_nonneg (h p x), norm_nonneg (g x)]
    rw [heq, norm_one] at this; exact lt_irrefl _ this
  have hheq : ∀ x, h p (x + α) * (Nm p x 0 0 + Nm p x 0 1 * h p x) =
      Nm p x 1 0 + Nm p x 1 1 * h p x := by
    intro x
    have := congrArg (fun g : 𝔹 => g x) hp3
    obtain ⟨ha, hb, hc, hd⟩ := hent' x
    simp only [Fn, shiftL_apply, BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_mul, BoundedContinuousFunction.coe_add, Pi.sub_apply,
      Pi.mul_apply, Pi.add_apply, ha, hb, hc, hd, BoundedContinuousFunction.coe_zero,
      Pi.zero_apply] at this
    linear_combination this
  have hlamx : ∀ x, lam p x = Nm p x 0 0 + Nm p x 0 1 * h p x := fun x => by
    simp [hlam, (hent' x).1, (hent' x).2.1]
  have h1 : ∀ x, 1 ≤ ‖Nm p x 0 0 + Nm p x 0 1 * h p x‖ := fun x => by
    rw [← hlamx]
    have h3 : ‖lam p x - l x‖ < ρ - 1 := by
      have := (hpt (lam p - lh) x).trans_lt hp7
      simpa [hlh] using this
    have h4 := norm_sub_norm_le (l x) (lam p x)
    rw [norm_sub_rev] at h4
    linarith [hlρ x]
  have hXB : ∀ x, shift (A p) 0 x * B' x = B' (x + α) * Nm p x := fun x => by
    have hunit : IsUnit (B' (x + α)).det := by rw [hB'd]; exact isUnit_one
    simp only [hNm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
  have hL := DerivFormulaAux.lyap_of_graphs hX hB'c hB'p hB'd hNc hNp hXB
    (h := fun x => h p x) (h p).continuous hhp hgc hgp hhg hheq hgeq h1
  show lyapunov α (shift (A p) 0) = c₀ + Ψ (uu p)
  rw [hL]
  have hux : ∀ x, ‖uu p x‖ < 1 := fun x => (hpt _ x).trans_lt hp8
  have h1u : ∀ x, 1 + uu p x ≠ 0 := fun x h0 => by
    have := hux x
    rw [show uu p x = -1 by linear_combination h0, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  have hfac : ∀ x, Real.log ‖Nm p x 0 0 + Nm p x 0 1 * h p x‖ =
      Real.log ‖l x‖ + Real.log ‖1 + uu p x‖ := by
    intro x
    rw [← hlamx]
    have hlu : lam p x = l x * (1 + uu p x) := by
      simp only [huu, BoundedContinuousFunction.coe_mul, BoundedContinuousFunction.coe_sub,
        Pi.mul_apply, Pi.sub_apply, hlh, hlih, ofPer_apply]
      field_simp [hl0 x]
      ring
    rw [hlu, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hl0 x)) (norm_ne_zero_iff.2 (h1u x))]
  have cont1 : Continuous fun x => Real.log ‖l x‖ :=
    hlc.norm.log (fun x => norm_ne_zero_iff.2 (hl0 x))
  have cont2 : Continuous fun x => Real.log ‖1 + uu p x‖ :=
    (continuous_const.add (uu p).continuous).norm.log (fun x => norm_ne_zero_iff.2 (h1u x))
  rw [intervalIntegral.integral_congr (fun x _ => hfac x),
    intervalIntegral.integral_add (cont1.intervalIntegrable _ _) (cont2.intervalIntegrable _ _)]
  rfl

end UHAnalyticAux

open UHAnalyticAux in
/-- **Real-analytic dependence of `L` on `𝒰ℋ`** (the field `Hypotheses.uhAnalytic`). -/
theorem uhAnalytic_proof : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ}
    {U : Set P} {A : P → ℂ → M2}, IsAnalyticCocycleFamily δ U A → ∀ (α : ℝ) {p₀ : P},
      p₀ ∈ U → UH α (A p₀) → ∃ W ∈ 𝓝 p₀, AnalyticOnNhd ℝ (fun p => L α (A p) 0) W := by
  intro P _ _ δ U A hA α p₀ hp₀ hUH
  obtain ⟨G, hG, hLG⟩ := main_local hA α hp₀ hUH
  refine ⟨_, hG.eventually_analyticAt.and hLG.eventually_nhds, fun p hp => ?_⟩
  exact hp.1.congr (hp.2.mono fun q hq => hq.symm)

/-- Real-analytic dependence on `𝒰ℋ` at fixed frequency. -/
theorem uh_analytic_family {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ}
    {U : Set P} {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A) (α : ℝ) {p₀ : P}
    (hp₀ : p₀ ∈ U) (hUH : UH α (A p₀)) :
    ∃ W ∈ 𝓝 p₀, AnalyticOnNhd ℝ (fun p => L α (A p) 0) W :=
  uhAnalytic_proof hA α hp₀ hUH

end AvilaGlobal
