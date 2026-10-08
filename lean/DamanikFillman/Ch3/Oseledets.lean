/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.2: Oseledets' multiplicative ergodic theorem (Corollary 3.8.8)

Main results:
* `DF.Cocycle.ruelle_orbit` — Ruelle's theorem (`DF.Cocycle.ruelle`) along the orbit of a point
  where the Furstenberg–Kesten limit holds;
* `DF.Cocycle.stVec` — an explicit, measurable choice of a vector spanning the stable line:
  `e₁` if `e₁` is contracted, and otherwise `e₀ + z e₁` with
  `z = lim -⟪Aₙe₁, Aₙe₀⟫ / ‖Aₙe₁‖²`;
* `DF.Cocycle.exists_stable_vec` — the stable direction is measurable, invariant and contracted
  at rate `-L`;
* `DF.Cocycle.oseledets` — **Corollary 3.8.8**: the Statement `DF.Cocycle.OseledetsStatement`;
  the unstable direction is the stable direction of the inverse cocycle `(T⁻¹, A(T⁻¹ ·)⁻¹)`,
  whose Lyapunov exponent is again `L`.

Deviation: the book obtains measurability of the line fields from their construction as limits of
most contracted directions; here measurability comes from the explicit formula for `stVec`
(a limit of measurable functions, plus a measurable case distinction).
-/
import DamanikFillman.Ch3.Ruelle
import DamanikFillman.Ch3.UHStable
import DamanikFillman.Ch1.SL2

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace

namespace DF

namespace Cocycle

variable {Ω : Type*}

/-! ### Preliminaries -/

lemma coe_iter (T : Ω → Ω) (A : Ω → SL2C) (n : ℕ) (ω : Ω) :
    ((iter T A n ω : SL2C) : M2) = iter T (fun ω => (A ω : M2)) n ω := by
  induction n with
  | zero => simp
  | succ n ih => rw [iter_succ, iter_succ, Matrix.SpecialLinearGroup.coe_mul, ih]

lemma norm_adjugate_eq (M : M2) (hM : M.det = 1) : ‖adjugate M‖ = ‖M‖ := by
  rw [← norm_inv_eq_norm M hM, Matrix.inv_def, hM, Ring.inverse_one, one_smul]

lemma norm_coe_inv (g : SL2C) : ‖((g⁻¹ : SL2C) : M2)‖ = ‖(g : M2)‖ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, norm_adjugate_eq _ g.2]

lemma actC_one (x : C2) : actC 1 x = x := by simp [actC]

lemma actC_adjugate_actC {M : M2} (hM : M.det = 1) (x : C2) :
    actC (adjugate M) (actC M x) = x := by
  rw [← actC_mul, adjugate_mul, hM, one_smul, actC_one]

lemma actC_actC_adjugate {M : M2} (hM : M.det = 1) (x : C2) :
    actC M (actC (adjugate M) x) = x := by
  rw [← actC_mul, mul_adjugate, hM, one_smul, actC_one]

lemma actC_ne_zero {M : M2} (hM : M.det = 1) {x : C2} (hx : x ≠ 0) : actC M x ≠ 0 := by
  intro h
  apply hx
  rw [← actC_adjugate_actC hM x, h]
  simp [actC]

lemma continuous_actC_left (e : C2) : Continuous fun M : M2 => actC M e := by
  have : Continuous fun M : M2 => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M :=
    AddMonoidHomClass.continuous_of_bound (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) 1
      fun M => by rw [one_mul]; exact le_of_eq rfl
  exact this.clm_apply continuous_const

lemma exists_smul_of_finrank_eq_one {V : Submodule ℂ C2} (hV : Module.finrank ℂ V = 1)
    {w : C2} (hw : w ∈ V) (hw0 : w ≠ 0) {v : C2} (hv : v ∈ V) : ∃ a : ℂ, v = a • w := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : V) (by simpa using hw0)).1 hV
    ⟨v, hv⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

lemma rate_succ {f : ℕ → ℝ} {c : ℝ} (h : Tendsto (fun n : ℕ => f n / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => f (n + 1) / n) atTop (𝓝 c) := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [add_div, div_self h0]
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1' : (n : ℝ) + 1 ≠ 0 := by positivity
  show f (n + 1) / ((n + 1 : ℕ) : ℝ) * (((n : ℝ) + 1) / n) = f (n + 1) / n
  push_cast
  rw [div_mul_div_comm, mul_comm ((n : ℝ) + 1) (n : ℝ), mul_div_mul_right _ _ h1']

lemma tendsto_ratio_zero {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) {L : ℝ}
    (hL : 0 < L) (h1 : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 L))
    (h2 : Tendsto (fun n : ℕ => Real.log (b n) / n) atTop (𝓝 (-L))) :
    Tendsto (fun n => b n / a n) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * (Real.log (b n) / n - Real.log (a n) / n)) atTop
      atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_neg (by linarith : -L - L < 0) (h2.sub h1)
  refine (Real.tendsto_exp_atBot.comp h3).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : (n : ℝ) * (Real.log (b n) / n - Real.log (a n) / n) =
      Real.log (b n) - Real.log (a n) := by
    field_simp
  rw [Function.comp_apply, e, ← Real.log_div (hb n).ne' (ha n).ne',
    Real.exp_log (div_pos (hb n) (ha n))]

/-! ### Ruelle along orbits -/

/-- Ruelle's theorem along the orbit of `ω`. -/
lemma ruelle_orbit {T : Ω → Ω} {A : Ω → M2} (hdet : ∀ ω, (A ω).det = 1) {M : ℝ}
    (hM : ∀ ω, ‖A ω‖ ≤ M) {L : ℝ} (hL : 0 < L) {ω : Ω}
    (hω : Tendsto (fun n : ℕ => Real.log ‖iter T A n ω‖ / n) atTop (𝓝 L)) :
    ∃ V : Submodule ℂ C2, Module.finrank ℂ V = 1 ∧
      (∀ v ∈ V, v ≠ 0 →
        Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) v‖ / n) atTop (𝓝 (-L))) ∧
      (∀ v ∉ V, Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) v‖ / n) atTop (𝓝 L)) := by
  have hseq : ∀ n, seqProd (fun k => A (T^[k - 1] ω)) n = iter T A n ω := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show A (T^[n + 1 - 1] ω) * seqProd (fun k => A (T^[k - 1] ω)) n = _
      rw [ih, iter_succ, Nat.add_sub_cancel]
  have hA0 : Tendsto (fun n : ℕ => Real.log ‖A (T^[n - 1] ω)‖ / n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => div_nonneg
      (Real.log_nonneg (one_le_norm_of_det_eq_one (hdet _))) (Nat.cast_nonneg n)) (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log M))
    exact div_le_div_of_nonneg_right (Real.log_le_log
      (lt_of_lt_of_le zero_lt_one (one_le_norm_of_det_eq_one (hdet _))) (hM _)) (Nat.cast_nonneg n)
  obtain ⟨V, hV1, hVs, hVu⟩ := ruelle (fun k => A (T^[k - 1] ω)) L (fun n => hdet _) hA0
    (by simp_rw [hseq]; exact hω) hL
  refine ⟨V, hV1, fun v hv hv0 => ?_, fun v hv => ?_⟩
  · have := hVs v hv hv0
    simp_rw [hseq] at this
    exact this
  · have := hVu v hv
    simp_rw [hseq] at this
    exact this

/-! ### A measurable choice of the stable vector -/

/-- `e₀ = (1, 0)`. -/
def e0c : C2 := WithLp.toLp 2 ![1, 0]

/-- `e₁ = (0, 1)`. -/
def e1c : C2 := WithLp.toLp 2 ![0, 1]

@[simp] lemma e0c_zero : e0c 0 = 1 := rfl
@[simp] lemma e0c_one : e0c 1 = 0 := rfl
@[simp] lemma e1c_zero : e1c 0 = 0 := rfl
@[simp] lemma e1c_one : e1c 1 = 1 := rfl

lemma e1c_ne_zero : e1c ≠ 0 := by
  intro h
  have := congrArg (fun v : C2 => v 1) h
  simp at this

/-- `zₙ = -⟪Aₙe₁, Aₙe₀⟫ / ‖Aₙe₁‖²`. -/
def zseq (T : Ω → Ω) (A : Ω → M2) (n : ℕ) (ω : Ω) : ℂ :=
  -(⟪actC (iter T A n ω) e1c, actC (iter T A n ω) e0c⟫_ℂ / (‖actC (iter T A n ω) e1c‖ : ℂ) ^ 2)

open Classical in
/-- The stable vector: `e₁` if `e₁` is contracted at rate `-L`, else `e₀ + (lim zₙ) e₁`. -/
def stVec (T : Ω → Ω) (A : Ω → M2) (L : ℝ) (ω : Ω) : C2 :=
  if Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) e1c‖ / n) atTop (𝓝 (-L)) then e1c
  else e0c + (limUnder atTop fun n => zseq T A n ω) • e1c

lemma measurable_stVec [MeasurableSpace Ω] {T : Ω → Ω} {A : Ω → M2} (hT : Measurable T)
    (hA : Measurable A) (L : ℝ) : Measurable (stVec T A L) := by
  have hB : ∀ n, Measurable (iter T A n) := measurable_iter hT hA
  have hz : ∀ n, Measurable (zseq T A n) := fun n => by
    have h1 := (continuous_actC_left e1c).measurable.comp (hB n)
    have h0 := (continuous_actC_left e0c).measurable.comp (hB n)
    exact ((h1.inner (𝕜 := ℂ) h0).div ((Complex.measurable_ofReal.comp h1.norm).pow_const 2)).neg
  have hS : MeasurableSet {ω | Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) e1c‖ / n)
      atTop (𝓝 (-L))} :=
    measurableSet_tendsto (𝓝 (-L)) fun n =>
      ((continuous_actC_left e1c).measurable.comp (hB n)).norm.log.div_const _
  have hzl : Measurable fun ω => limUnder atTop fun n => zseq T A n ω :=
    (StronglyMeasurable.limUnder fun n => (hz n).stronglyMeasurable).measurable
  unfold stVec
  exact Measurable.ite hS measurable_const (measurable_const.add (hzl.smul measurable_const))

lemma stVec_spec {T : Ω → Ω} {A : Ω → M2} (hdet : ∀ ω, (A ω).det = 1) {M : ℝ}
    (hM : ∀ ω, ‖A ω‖ ≤ M) {L : ℝ} (hL : 0 < L) {ω : Ω}
    (hω : Tendsto (fun n : ℕ => Real.log ‖iter T A n ω‖ / n) atTop (𝓝 L)) :
    ∃ V : Submodule ℂ C2, Module.finrank ℂ V = 1 ∧
      (∀ v ∈ V, v ≠ 0 →
        Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) v‖ / n) atTop (𝓝 (-L))) ∧
      (∀ v ∉ V, Tendsto (fun n : ℕ => Real.log ‖actC (iter T A n ω) v‖ / n) atTop (𝓝 L)) ∧
      stVec T A L ω ∈ V ∧ stVec T A L ω ≠ 0 := by
  obtain ⟨V, hV1, hVs, hVu⟩ := ruelle_orbit hdet hM hL hω
  have hne : L ≠ -L := by linarith
  refine ⟨V, hV1, hVs, hVu, ?_⟩
  unfold stVec
  split_ifs with hS
  · refine ⟨?_, e1c_ne_zero⟩
    by_contra hn
    exact hne (tendsto_nhds_unique (hVu _ hn) hS)
  · have he1V : e1c ∉ V := fun h => hS (hVs _ h e1c_ne_zero)
    have hbot : V ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hV1
      exact zero_ne_one hV1
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hw00 : w 0 ≠ 0 := by
      intro h0
      have hw1 : w 1 ≠ 0 := by
        intro h1
        apply hw0
        ext i
        fin_cases i
        · simpa using h0
        · simpa using h1
      apply he1V
      have : e1c = (w 1)⁻¹ • w := by
        ext i
        fin_cases i
        · simp [h0]
        · simp [hw1]
      rw [this]
      exact V.smul_mem _ hw
    obtain ⟨v, hvdef⟩ : ∃ v : C2, v = (w 0)⁻¹ • w := ⟨_, rfl⟩
    have hvV : v ∈ V := by rw [hvdef]; exact V.smul_mem _ hw
    have hv0 : v 0 = 1 := by rw [hvdef]; simp [hw00]
    have hvne : v ≠ 0 := by
      intro h
      rw [h] at hv0
      simp at hv0
    have hveq : v = e0c + (v 1) • e1c := by
      ext i
      fin_cases i
      · simp [hv0]
      · simp
    have he0 : e0c = v - (v 1) • e1c := by
      ext i
      fin_cases i
      · simp [hv0]
      · simp
    -- convergence of `zₙ`
    have hdetn : ∀ n, (iter T A n ω).det = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [iter_succ, det_mul, hdet, ih, one_mul]
    have ha : ∀ n, 0 < ‖actC (iter T A n ω) e1c‖ := fun n =>
      norm_pos_iff.2 (actC_ne_zero (hdetn n) e1c_ne_zero)
    have hb : ∀ n, 0 < ‖actC (iter T A n ω) v‖ := fun n =>
      norm_pos_iff.2 (actC_ne_zero (hdetn n) hvne)
    have hratio := tendsto_ratio_zero ha hb hL (hVu _ he1V) (hVs _ hvV hvne)
    have hdiff : ∀ n, zseq T A n ω - v 1 = -(⟪actC (iter T A n ω) e1c, actC (iter T A n ω) v⟫_ℂ /
        (‖actC (iter T A n ω) e1c‖ : ℂ) ^ 2) := by
      intro n
      have hne0 : (‖actC (iter T A n ω) e1c‖ : ℂ) ≠ 0 := by exact_mod_cast (ha n).ne'
      unfold zseq
      have hd : (‖actC (iter T A n ω) e1c‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hne0
      rw [he0, actC_sub, actC_smul, inner_sub_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, sub_div, mul_div_assoc, div_self hd, mul_one]
      ring
    have hbound : ∀ n, ‖zseq T A n ω - v 1‖ ≤
        ‖actC (iter T A n ω) v‖ / ‖actC (iter T A n ω) e1c‖ := by
      intro n
      have hpos := ha n
      rw [hdiff, norm_neg, norm_div, norm_pow, Complex.norm_real, norm_norm]
      calc ‖⟪actC (iter T A n ω) e1c, actC (iter T A n ω) v⟫_ℂ‖ / ‖actC (iter T A n ω) e1c‖ ^ 2
          ≤ ‖actC (iter T A n ω) e1c‖ * ‖actC (iter T A n ω) v‖ /
              ‖actC (iter T A n ω) e1c‖ ^ 2 := by
            gcongr
            exact norm_inner_le_norm _ _
        _ = ‖actC (iter T A n ω) v‖ / ‖actC (iter T A n ω) e1c‖ := by
            rw [pow_two, mul_div_mul_left _ _ hpos.ne']
    have hz : Tendsto (fun n => zseq T A n ω) atTop (𝓝 (v 1)) :=
      tendsto_iff_norm_sub_tendsto_zero.2
        (squeeze_zero (fun n => norm_nonneg _) hbound hratio)
    rw [hz.limUnder_eq, ← hveq]
    exact ⟨hvV, hvne⟩

/-! ### The stable direction -/

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The stable direction of an `SL(2, ℂ)` cocycle with positive Lyapunov exponent: measurable,
invariant, and contracted at rate `-L`. -/
theorem exists_stable_vec [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) (A : Ω → SL2C)
    (hT : Ergodic T μ) (hA : Measurable fun ω => (A ω : M2)) {M : ℝ}
    (hM : ∀ ω, ‖(A ω : M2)‖ ≤ M) (hL : 0 < lyap μ T (fun ω => (A ω : M2))) :
    ∃ vs : Ω → C2, Measurable vs ∧ ∀ᵐ ω ∂μ, vs ω ≠ 0 ∧
      (∃ a : ℂ, actC (A ω : M2) (vs ω) = a • vs (T ω)) ∧
      Tendsto (fun n : ℕ => Real.log ‖actC ((iterZ T.toEquiv A n ω : SL2C) : M2) (vs ω)‖ / n)
        atTop (𝓝 (-lyap μ T (fun ω => (A ω : M2)))) := by
  set At : Ω → M2 := fun ω => (A ω : M2) with hAt
  set L := lyap μ T At with hLdef
  have hdet : ∀ ω, (At ω).det = 1 := fun ω => (A ω).2
  obtain ⟨-, -, hFK⟩ := lyapunov_exponent hT hA hdet hM
  refine ⟨stVec T At L, measurable_stVec T.measurable hA L, ?_⟩
  filter_upwards [hFK, hT.toMeasurePreserving.quasiMeasurePreserving.ae hFK] with ω hω hTω
  obtain ⟨V, hV1, hVs, hVu, hmem, hne⟩ := stVec_spec hdet hM hL hω
  obtain ⟨V', hV1', hVs', hVu', hmem', hne'⟩ := stVec_spec hdet hM hL hTω
  have hiterZ : ∀ n : ℕ, ((iterZ T.toEquiv A n ω : SL2C) : M2) = iter T At n ω := fun n => by
    rw [iterZ_natCast, coe_iter]
    try rfl
  refine ⟨hne, ?_, ?_⟩
  · have hrate := hVs _ hmem hne
    have e : ∀ n : ℕ, actC (iter T At n (T ω)) (actC (At ω) (stVec T At L ω)) =
        actC (iter T At (n + 1) ω) (stVec T At L ω) := by
      intro n
      rw [← actC_mul, show n + 1 = 1 + n from add_comm _ _, iter_add, iter_one]
      try rfl
    have hshift : Tendsto (fun n : ℕ =>
        Real.log ‖actC (iter T At n (T ω)) (actC (At ω) (stVec T At L ω))‖ / n) atTop
          (𝓝 (-L)) := by
      simp_rw [e]
      exact rate_succ (f := fun n => Real.log ‖actC (iter T At n ω) (stVec T At L ω)‖) hrate
    have hAv : actC (At ω) (stVec T At L ω) ∈ V' := by
      by_contra hn
      exact (show L ≠ -L by linarith) (tendsto_nhds_unique (hVu' _ hn) hshift)
    exact exists_smul_of_finrank_eq_one hV1' hmem' hne' hAv
  · simp_rw [hiterZ]
    exact hVs _ hmem hne

/-- **Corollary 3.8.8** (Oseledets' multiplicative ergodic theorem). -/
theorem oseledets : OseledetsStatement := by
  intro Ω _ μ _ T A hT hA hMex hL
  obtain ⟨M, hM⟩ := hMex
  obtain ⟨vs, hvsm, hvs⟩ := exists_stable_vec T A hT hA hM hL
  -- the inverse cocycle over `T⁻¹`
  obtain ⟨B, hBdef⟩ : ∃ B : Ω → SL2C, B = fun ω => (A (T.symm ω))⁻¹ := ⟨_, rfl⟩
  have hBcoe : ∀ ω, (B ω : M2) = adjugate (A (T.symm ω) : M2) := fun ω => by
    rw [hBdef]
    exact Matrix.SpecialLinearGroup.coe_inv _
  have hBm : Measurable fun ω => (B ω : M2) := by
    simp_rw [hBcoe]
    exact continuous_id.matrix_adjugate.measurable.comp (hA.comp T.symm.measurable)
  have hMB : ∀ ω, ‖(B ω : M2)‖ ≤ M := fun ω => by
    rw [hBcoe, norm_adjugate_eq _ (A (T.symm ω)).2]
    exact hM _
  have hiter : ∀ (n : ℤ) ω, iterZ T.symm.toEquiv B n ω = iterZ T.toEquiv A (-n) ω := by
    intro n ω
    rw [hBdef]
    exact iterZ_symm T.toEquiv A n ω
  have hnorm : ∀ (k : ℕ) ω, ‖iter T.symm (fun ω => (B ω : M2)) k (T^[k] ω)‖ =
      ‖iter T (fun ω => (A ω : M2)) k ω‖ := by
    intro k ω
    have h1 : iter T.symm (fun ω => (B ω : M2)) k (T^[k] ω) =
        ((iterZ T.symm.toEquiv B k (T^[k] ω) : SL2C) : M2) := by
      rw [iterZ_natCast, coe_iter]
      try rfl
    have h2 : iterZ T.toEquiv A (-(k : ℤ)) (T^[k] ω) = (iter T A k ω)⁻¹ :=
      iterZ_neg_apply (T := T.toEquiv) k ω
    rw [h1, hiter, h2, norm_coe_inv, coe_iter]
  have hlyap : lyap μ T.symm (fun ω => (B ω : M2)) = lyap μ T (fun ω => (A ω : M2)) := by
    unfold lyap
    refine iInf_congr fun n => ?_
    congr 1
    have hmp : MeasurePreserving (T^[n + 1]) μ μ := hT.toMeasurePreserving.iterate (n + 1)
    have hmeas : Measurable fun ω => Real.log ‖iter T.symm (fun ω => (B ω : M2)) (n + 1) ω‖ :=
      (measurable_iter T.symm.measurable hBm (n + 1)).norm.log
    have := integral_map (μ := μ) hmp.measurable.aemeasurable
      (f := fun ω => Real.log ‖iter T.symm (fun ω => (B ω : M2)) (n + 1) ω‖)
      hmeas.aestronglyMeasurable
    rw [hmp.map_eq] at this
    rw [this]
    simp_rw [hnorm]
  obtain ⟨vu, hvum, hvu⟩ := exists_stable_vec T.symm B hT.symm hBm hMB (by rw [hlyap]; exact hL)
  refine ⟨vs, vu, hvsm, hvum, ?_⟩
  filter_upwards [hvs, hvu, hT.toMeasurePreserving.quasiMeasurePreserving.ae hvu]
    with ω h1 h2 h3
  obtain ⟨hs0, ⟨a, ha⟩, hsr⟩ := h1
  obtain ⟨hu0, -, hur⟩ := h2
  obtain ⟨hu0', ⟨b, hb⟩, -⟩ := h3
  refine ⟨hs0, hu0, ⟨a, ha⟩, ?_, hsr, ?_⟩
  · rw [hBcoe] at hb
    simp only [MeasurableEquiv.symm_apply_apply] at hb
    have key := actC_actC_adjugate (A ω).2 (vu (T ω))
    rw [hb, actC_smul] at key
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_smul] at key
      exact hu0' key.symm
    exact ⟨b⁻¹, by rw [← key, smul_smul, inv_mul_cancel₀ hb0, one_smul]⟩
  · rw [hlyap] at hur
    simp_rw [hiter] at hur
    exact hur

end Cocycle

end DF
