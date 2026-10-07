import AvilaGlobal.Background

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Set Function

namespace AvilaGlobal

open AMO

namespace UHOpenAux

/-! ### Elementary linear algebra in `ℂ²` -/

/-- The determinant of the pair `(v, w)`. -/
def cr (v w : Fin 2 → ℂ) : ℂ := v 0 * w 1 - v 1 * w 0

lemma continuous_cr : Continuous (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) => cr p.1 p.2) := by
  have : Continuous (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) => p.1 0 * p.2 1 - p.1 1 * p.2 0) := by
    fun_prop
  exact this

lemma tendsto_cr {ι : Type*} {l : Filter ι} {f g : ι → Fin 2 → ℂ} {a b : Fin 2 → ℂ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun z => cr (f z) (g z)) l (𝓝 (cr a b)) :=
  (continuous_cr.tendsto (a, b)).comp (hf.prodMk_nhds hg)

lemma tendsto_mulVec' {ι : Type*} {l : Filter ι} {M : ι → M2} {v : ι → Fin 2 → ℂ} {M0 : M2}
    {v0 : Fin 2 → ℂ} (hM : Tendsto M l (𝓝 M0)) (hv : Tendsto v l (𝓝 v0)) :
    Tendsto (fun z => M z *ᵥ v z) l (𝓝 (M0 *ᵥ v0)) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hMe : ∀ j, Tendsto (fun z => M z i j) l (𝓝 (M0 i j)) := fun j =>
    (((continuous_id (X := M2)).matrix_elem i j).tendsto M0).comp hM
  have hve : ∀ j, Tendsto (fun z => v z j) l (𝓝 (v0 j)) := fun j => (tendsto_pi_nhds.1 hv) j
  exact ((hMe 0).mul (hve 0)).add ((hMe 1).mul (hve 1))

lemma cr_mulVec (P : M2) (v w : Fin 2 → ℂ) : cr (P *ᵥ v) (P *ᵥ w) = P.det * cr v w := by
  simp [cr, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

lemma cr_self (v : Fin 2 → ℂ) : cr v v = 0 := by simp [cr]; ring

lemma cr_comm (v w : Fin 2 → ℂ) : cr v w = - cr w v := by simp [cr]; ring

lemma cr_smul_left (c : ℂ) (v w : Fin 2 → ℂ) : cr (c • v) w = c * cr v w := by
  simp [cr]; ring

lemma cr_smul_right (c : ℂ) (v w : Fin 2 → ℂ) : cr v (c • w) = c * cr v w := by
  simp [cr]; ring

lemma norm_cr_le (v w : Fin 2 → ℂ) : ‖cr v w‖ ≤ 2 * (‖v‖ * ‖w‖) := by
  have h0 := norm_le_pi_norm v 0
  have h1 := norm_le_pi_norm v 1
  have g0 := norm_le_pi_norm w 0
  have g1 := norm_le_pi_norm w 1
  unfold cr
  calc ‖v 0 * w 1 - v 1 * w 0‖ ≤ ‖v 0‖ * ‖w 1‖ + ‖v 1‖ * ‖w 0‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := by
        gcongr
    _ = 2 * (‖v‖ * ‖w‖) := by ring

lemma parallel_of_cr_eq_zero {v w : Fin 2 → ℂ} (hw : w ≠ 0) (hc : cr v w = 0) :
    ∃ c : ℂ, v = c • w := by
  simp only [cr] at hc
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := fun h1 => hw (by ext i; fin_cases i <;> simp [h0, h1])
    have hv0 : v 0 = 0 := by
      rw [h0, mul_zero, sub_zero] at hc; exact (mul_eq_zero.1 hc).resolve_right h1
    refine ⟨v 1 / w 1, ?_⟩
    ext i; fin_cases i
    · simp [hv0, h0]
    · simp [h1]
  · refine ⟨v 0 / w 0, ?_⟩
    ext i; fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination -hc

/-- Coordinates in a basis `(e, f)`. -/
lemma decomp {e f : Fin 2 → ℂ} (h : cr e f ≠ 0) (v : Fin 2 → ℂ) :
    v = (cr v f / cr e f) • e + (cr e v / cr e f) • f := by
  ext i
  have key : cr v f * e i + cr e v * f i = v i * cr e f := by
    fin_cases i <;> simp [cr] <;> ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, key, mul_div_assoc, div_self h,
    mul_one]

/-- If det-one matrices send two vectors to `0`, the vectors are parallel. -/
lemma parallel_of_tendsto {v w : Fin 2 → ℂ} (hw : w ≠ 0) {P : ℕ → M2}
    (hdet : ∀ k, (P k).det = 1) (hv : Tendsto (fun k => P k *ᵥ v) atTop (𝓝 0))
    (hw' : Tendsto (fun k => P k *ᵥ w) atTop (𝓝 0)) : ∃ c : ℂ, v = c • w := by
  apply parallel_of_cr_eq_zero hw
  have h1 := tendsto_cr hv hw'
  simp only [cr_mulVec, hdet, one_mul, cr_self] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

lemma norm_add_ge (a e : ℂ) : ‖a‖ - ‖e‖ ≤ ‖a + e‖ := by
  have := norm_sub_le (a + e) e
  simp only [add_sub_cancel_right] at this
  linarith

lemma vnorm_add_ge (a e : Fin 2 → ℂ) : ‖a‖ - ‖e‖ ≤ ‖a + e‖ := by
  have := norm_sub_le (a + e) e
  simp only [add_sub_cancel_right] at this
  linarith

/-! ### Compactness on the circle -/

lemma per_bound {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    (hp : Periodic f 1) : ∃ K, ∀ x, ‖f x‖ ≤ K := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 (hp.isBounded_of_continuous one_ne_zero hf)
  exact ⟨K, fun x => hK _ (mem_range_self x)⟩

lemma per_max_lt {g : ℝ → ℝ} (hg : Continuous g) (hp : Periodic g 1) {b : ℝ}
    (hb : ∀ x, g x < b) : ∃ c < b, ∀ x, g x ≤ c := by
  obtain ⟨x0, -, hx0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) hg.continuousOn
  refine ⟨g x0, hb x0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]; exact hx0 (Ico_subset_Icc_self hy)

lemma eventually_forall_of_local {P : ℕ → ℝ → Prop}
    (hP : ∀ x, ∀ᶠ q in atTop ×ˢ 𝓝 x, P q.1 q.2)
    (hper : ∀ᶠ n in atTop, ∀ x, ∃ y ∈ Icc (0:ℝ) 1, P n y → P n x) :
    ∀ᶠ n in atTop, ∀ x, P n x := by
  have h1 : {q : ℕ × ℝ | P q.1 q.2} ∈ atTop ×ˢ 𝓝ˢ (Icc (0:ℝ) 1) :=
    isCompact_Icc.mem_prod_nhdsSet_of_forall (fun y _ => hP y)
  have h2 : ∀ᶠ q in atTop ×ˢ 𝓟 (Icc (0:ℝ) 1), P q.1 q.2 :=
    (Filter.prod_mono le_rfl principal_le_nhdsSet) h1
  rw [eventually_prod_principal_iff] at h2
  filter_upwards [h2, hper] with n h2n hpn x
  obtain ⟨y, hy, h⟩ := hpn x
  exact h (h2n y hy)

/-! ### Iterates -/

lemma iter_one' {α : ℝ} {X : ℝ → M2} (x : ℝ) : iter α X 1 x = X x := by simp [iter]

lemma iter_succ' {α : ℝ} {X : ℝ → M2} (n : ℕ) (x : ℝ) :
    iter α X (n + 1) x = X (x + n * α) * iter α X n x := rfl

lemma iter_inv {α : ℝ} {X : ℝ → M2} {v : ℝ → Fin 2 → ℂ}
    (h : ∀ x, ∃ c : ℂ, X x *ᵥ v x = c • v (x + α)) (n : ℕ) (x : ℝ) :
    ∃ c : ℂ, iter α X n x *ᵥ v x = c • v (x + n * α) := by
  induction n with
  | zero => exact ⟨1, by simp [iter]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := h (x + n * α)
    refine ⟨c' * c, ?_⟩
    rw [iter_succ', ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hc', smul_smul, mul_comm c]
    congr 2; push_cast; ring

lemma iter_kN {α : ℝ} {X : ℝ → M2} {s : ℝ → Fin 2 → ℂ} {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hinv : ∀ y, ∃ σ : ℂ, iter α X N y *ᵥ s y = σ • s (y + N * α))
    (hcon : ∀ y, ‖iter α X N y *ᵥ s y‖ ≤ c * ‖s y‖) (y : ℝ) (k : ℕ) :
    ∃ m : ℂ, iter α X (k * N) y *ᵥ s y = m • s (y + ((k * N : ℕ) : ℝ) * α) ∧
      ‖iter α X (k * N) y *ᵥ s y‖ ≤ c ^ k * ‖s y‖ := by
  induction k with
  | zero => exact ⟨1, by simp [iter], by simp [iter]⟩
  | succ k ih =>
    obtain ⟨m, hm, hn⟩ := ih
    obtain ⟨σ, hσ⟩ := hinv (y + ((k * N : ℕ) : ℝ) * α)
    have hsplit : (k + 1) * N = k * N + N := by ring
    refine ⟨m * σ, ?_, ?_⟩
    · have e : y + ((k * N : ℕ) : ℝ) * α + N * α = y + ((k * N + N : ℕ) : ℝ) * α := by
        push_cast; ring
      rw [hsplit, iter_add, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, hσ, smul_smul, e]
    · rw [hsplit, iter_add, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, norm_smul]
      have := hcon (y + ((k * N : ℕ) : ℝ) * α)
      calc ‖m‖ * ‖iter α X N (y + ((k * N : ℕ) : ℝ) * α) *ᵥ s (y + ((k * N : ℕ) : ℝ) * α)‖
          ≤ ‖m‖ * (c * ‖s (y + ((k * N : ℕ) : ℝ) * α)‖) := by gcongr
        _ = c * ‖m • s (y + ((k * N : ℕ) : ℝ) * α)‖ := by rw [norm_smul]; ring
        _ = c * ‖iter α X (k * N) y *ᵥ s y‖ := by rw [hm]
        _ ≤ c * (c ^ k * ‖s y‖) := by gcongr
        _ = c ^ (k + 1) * ‖s y‖ := by ring

/-- `N`-step contraction along an `N`-step invariant direction gives one-step invariance. -/
lemma invariant_of_contract {α : ℝ} {X : ℝ → M2} (hdet : ∀ x, (X x).det = 1) {K : ℝ}
    (hK : ∀ x, ‖X x‖ ≤ K) {s : ℝ → Fin 2 → ℂ} (hs0 : ∀ x, s x ≠ 0) {C : ℝ}
    (hC : ∀ x, ‖s x‖ ≤ C) {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinv : ∀ y, ∃ σ : ℂ, iter α X N y *ᵥ s y = σ • s (y + N * α))
    (hcon : ∀ y, ‖iter α X N y *ᵥ s y‖ ≤ c * ‖s y‖) (x : ℝ) :
    ∃ σ : ℂ, X x *ᵥ s x = σ • s (x + α) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hgeo : Tendsto (fun k : ℕ => c ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  apply parallel_of_tendsto (hs0 _) (P := fun k => iter α X (k * N) (x + α))
    (fun k => det_iter hdet _ _)
  · have heq : ∀ k : ℕ, iter α X (k * N) (x + α) *ᵥ (X x *ᵥ s x) =
        X (x + ((k * N : ℕ) : ℝ) * α) *ᵥ (iter α X (k * N) x *ᵥ s x) := by
      intro k
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← iter_succ',
        show k * N + 1 = 1 + k * N from add_comm _ _, iter_add, iter_one']
      simp
    simp only [heq]
    apply squeeze_zero_norm (a := fun k : ℕ => K * (c ^ k * C))
    · intro k
      obtain ⟨_, -, hn⟩ := iter_kN hc0 hinv hcon x k
      refine (linfty_opNorm_mulVec _ _).trans ?_
      gcongr
      · exact hK _
      · exact hn.trans (by gcongr; exact hC x)
    · simpa using (hgeo.mul_const C).const_mul K
  · apply squeeze_zero_norm (a := fun k : ℕ => c ^ k * C)
    · intro k
      obtain ⟨_, -, hn⟩ := iter_kN hc0 hinv hcon (x + α) k
      exact hn.trans (by gcongr; exact hC _)
    · simpa using hgeo.mul_const C

lemma iter_adj {α : ℝ} {X : ℝ → M2} (n : ℕ) (y : ℝ) :
    iter α (fun x => adjugate (X (-x))) n y = adjugate (iter α X n (α - y - n * α)) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    rw [iter_succ', ih, ← adjugate_mul_distrib]
    congr 1
    rw [show n + 1 = 1 + n from add_comm _ _, iter_add, iter_one']
    have e1 : α - y - ((1 + n : ℕ) : ℝ) * α + ((1 : ℕ) : ℝ) * α = α - y - n * α := by
      push_cast; ring
    have e2 : -(y + n * α) = α - y - ((1 + n : ℕ) : ℝ) * α := by push_cast; ring
    rw [e1, e2]

/-- **UH from `N`-step data.** -/
theorem isUH_of_iterate {α : ℝ} {X : ℝ → M2} (hX : IsSLCocycle X) {u s : ℝ → Fin 2 → ℂ}
    (hu : Continuous u) (hs : Continuous s) (hup : Periodic u 1) (hsp : Periodic s 1)
    (hu0 : ∀ x, u x ≠ 0) (hs0 : ∀ x, s x ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    (hinvu : ∀ x, ∃ σ : ℂ, iter α X N x *ᵥ u x = σ • u (x + N * α))
    (hinvs : ∀ x, ∃ σ : ℂ, iter α X N x *ᵥ s x = σ • s (x + N * α))
    (hexp : ∀ x, ‖iter α X N x *ᵥ s x‖ < ‖s x‖ ∧ ‖u x‖ < ‖iter α X N x *ᵥ u x‖) :
    IsUH α X := by
  have hitc : Continuous (iter α X N) := continuous_iter hX.continuous N
  have hitp : Periodic (iter α X N) 1 := iter_periodic hX.periodic N
  refine ⟨u, s, hu, hs, hup, hsp, hu0, hs0, ?_, ?_, N, hN, hexp⟩
  · -- unstable direction: use the adjugate cocycle
    set Xh : ℝ → M2 := fun x => adjugate (X (-x)) with hXh
    set uh : ℝ → Fin 2 → ℂ := fun x => u (α - x) with huh
    have hXhc : Continuous Xh := (hX.continuous.comp continuous_neg).matrix_adjugate
    have hXhp : Periodic Xh 1 := by
      intro x
      show adjugate (X (-(x+1))) = adjugate (X (-x))
      rw [show -(x + 1) = -x - 1 by ring, ← hX.periodic (-x - 1), sub_add_cancel]
    obtain ⟨K, hK⟩ := per_bound hXhc hXhp
    obtain ⟨C, hC⟩ := per_bound (f := fun x => u (α - x)) (by fun_prop)
      (fun x => by
        show u (α - (x + 1)) = u (α - x)
        rw [show α - (x + 1) = α - x - 1 by ring, ← hup (α - x - 1), sub_add_cancel])
    -- the ratio
    have hne : ∀ z, iter α X N z *ᵥ u z ≠ 0 := fun z h => by
      have := (hexp z).2; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
    obtain ⟨c, hc1, hc⟩ := per_max_lt (g := fun z => ‖u z‖ / ‖iter α X N z *ᵥ u z‖)
      (hu.norm.div ((hitc.matrix_mulVec hu).norm) (fun z => norm_ne_zero_iff.2 (hne z)))
      (fun z => by simp only; rw [hup z, hitp z])
      (fun z => (div_lt_one (norm_pos_iff.2 (hne z))).2 (hexp z).2)
    have hc0 : 0 ≤ c := (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hc 0)
    have key : ∀ y, ∃ σ : ℂ, iter α Xh N y *ᵥ uh y = σ • uh (y + N * α) ∧
        ‖iter α Xh N y *ᵥ uh y‖ ≤ c * ‖uh y‖ := by
      intro y
      set z := α - y - N * α with hz
      obtain ⟨l, hl⟩ := hinvu z
      have hzN : z + N * α = α - y := by rw [hz]; ring
      rw [hzN] at hl
      have hl0 : l ≠ 0 := by rintro rfl; exact hne z (by rw [hl, zero_smul])
      have hadj : adjugate (iter α X N z) *ᵥ u (α - y) = l⁻¹ • u z := by
        have h1 : adjugate (iter α X N z) *ᵥ (iter α X N z *ᵥ u z) = u z := by
          rw [Matrix.mulVec_mulVec, adjugate_mul, det_iter hX.det_eq_one]; simp
        rw [hl, Matrix.mulVec_smul] at h1
        rw [← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      have hyN : α - (y + N * α) = z := by rw [hz]; ring
      refine ⟨l⁻¹, ?_, ?_⟩
      · simp only [huh, hXh]; rw [iter_adj, hyN, ← hz, hadj]
      · simp only [huh, hXh]; rw [iter_adj, ← hz, hadj, norm_smul, norm_inv]
        have h2 := hc z
        rw [hl, norm_smul] at h2
        have hpos : 0 < ‖l‖ * ‖u (α - y)‖ := mul_pos (norm_pos_iff.2 hl0) (norm_pos_iff.2 (hu0 _))
        rw [div_le_iff₀ hpos] at h2
        rw [inv_mul_le_iff₀ (norm_pos_iff.2 hl0)]
        linarith
    have hdet : ∀ x, (Xh x).det = 1 := fun x => by
      simp only [hXh, det_adjugate, hX.det_eq_one]; simp
    intro y
    obtain ⟨σ, hσ⟩ := invariant_of_contract hdet hK (s := uh) (fun x => hu0 _) (fun x => hC x)
      hc0 hc1 (fun y => (key y).imp fun _ h => h.1) (fun y => (key y).elim fun _ h => h.2) (-y)
    simp only [huh, hXh, neg_neg, show α - -y = y + α by ring,
      show α - (-y + α) = y by ring] at hσ
    have hσ0 : σ ≠ 0 := by
      rintro rfl
      have : X y *ᵥ (adjugate (X y) *ᵥ u (y + α)) = 0 := by rw [hσ, zero_smul, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, mul_adjugate, hX.det_eq_one] at this
      simp at this; exact hu0 _ this
    refine ⟨σ⁻¹, ?_⟩
    have : X y *ᵥ (adjugate (X y) *ᵥ u (y + α)) = σ • (X y *ᵥ u y) := by
      rw [hσ, Matrix.mulVec_smul]
    rw [Matrix.mulVec_mulVec, mul_adjugate, hX.det_eq_one] at this
    simp only [one_smul, Matrix.one_mulVec] at this
    rw [this, smul_smul, inv_mul_cancel₀ hσ0, one_smul]
  · -- stable direction
    obtain ⟨K, hK⟩ := per_bound hX.continuous hX.periodic
    obtain ⟨C, hC⟩ := per_bound hs hsp
    have hpos : ∀ z, 0 < ‖s z‖ := fun z => norm_pos_iff.2 (hs0 z)
    obtain ⟨c, hc1, hc⟩ := per_max_lt (g := fun z => ‖iter α X N z *ᵥ s z‖ / ‖s z‖)
      (((hitc.matrix_mulVec hs).norm).div hs.norm (fun z => (hpos z).ne'))
      (fun z => by simp only; rw [hsp z, hitp z])
      (fun z => (div_lt_one (hpos z)).2 (hexp z).1)
    have hc0 : 0 ≤ c := (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hc 0)
    exact invariant_of_contract hX.det_eq_one hK hs0 hC hc0 hc1 hinvs
      (fun y => (div_le_iff₀ (hpos y)).1 (hc y))


/-! ### Graph transform -/

/-- The Möbius map of the graph transform. -/
def mob (a b c d : ℝ → ℂ) (x : ℝ) (φ : ℂ) : ℂ := (c x + d x * φ) / (a x + b x * φ)

/-- Iterates of the graph transform, starting from the zero section. -/
def gIter (F : ℝ → ℂ → ℂ) (β : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 0
  | k + 1 => fun y => F (y - β) (gIter F β k (y - β))

theorem graph_fixed {a b c d : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hd : Continuous d) (hap : Periodic a 1) (hbp : Periodic b 1) (hcp : Periodic c 1)
    (hdp : Periodic d 1) (β : ℝ)
    (h1 : ∀ x, ‖b x‖ + ‖c x‖ + ‖d x‖ < ‖a x‖)
    (h2 : ∀ x, ‖a x * d x - b x * c x‖ < (‖a x‖ - ‖b x‖) ^ 2) :
    ∃ χ : ℝ → ℂ, Continuous χ ∧ Periodic χ 1 ∧ (∀ x, ‖χ x‖ ≤ 1) ∧
      ∀ x, χ (x + β) * (a x + b x * χ x) = c x + d x * χ x := by
  have hab : ∀ x, 0 < ‖a x‖ - ‖b x‖ := fun x => by
    linarith [h1 x, norm_nonneg (c x), norm_nonneg (d x)]
  obtain ⟨θ, hθ1, hθ⟩ := per_max_lt
    (g := fun x => ‖a x * d x - b x * c x‖ / (‖a x‖ - ‖b x‖) ^ 2)
    (Continuous.div (by fun_prop) (by fun_prop) (fun x => (pow_pos (hab x) 2).ne'))
    (fun x => by simp only; rw [hap x, hbp x, hcp x, hdp x])
    (fun x => (div_lt_one (pow_pos (hab x) 2)).2 (h2 x))
  have hθ0 : 0 ≤ θ := (div_nonneg (norm_nonneg _) (sq_nonneg _)).trans (hθ 0)
  have hden : ∀ x (φ : ℂ), ‖φ‖ ≤ 1 → ‖a x‖ - ‖b x‖ ≤ ‖a x + b x * φ‖ := by
    intro x φ hφ
    refine le_trans ?_ (norm_add_ge _ _)
    rw [norm_mul]
    have := mul_le_of_le_one_right (norm_nonneg (b x)) hφ
    linarith
  have hden0 : ∀ x (φ : ℂ), ‖φ‖ ≤ 1 → a x + b x * φ ≠ 0 := fun x φ hφ h => by
    have := hden x φ hφ; rw [h, norm_zero] at this; linarith [hab x]
  obtain ⟨F, hFeq⟩ : ∃ F : ℝ → ℂ → ℂ, F = mob a b c d := ⟨_, rfl⟩
  have hF : ∀ x φ, F x φ = (c x + d x * φ) / (a x + b x * φ) := fun _ _ => by rw [hFeq]; rfl
  have hFb : ∀ x φ, ‖φ‖ ≤ 1 → ‖F x φ‖ ≤ 1 := by
    intro x φ hφ
    rw [hF, norm_div, div_le_one (lt_of_lt_of_le (hab x) (hden x φ hφ))]
    calc ‖c x + d x * φ‖ ≤ ‖c x‖ + ‖d x‖ * ‖φ‖ := (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ ‖c x‖ + ‖d x‖ := by gcongr; exact mul_le_of_le_one_right (norm_nonneg _) hφ
      _ ≤ ‖a x‖ - ‖b x‖ := by linarith [h1 x]
      _ ≤ _ := hden x φ hφ
  have hFl : ∀ x φ ψ, ‖φ‖ ≤ 1 → ‖ψ‖ ≤ 1 → ‖F x φ - F x ψ‖ ≤ θ * ‖φ - ψ‖ := by
    intro x φ ψ hφ hψ
    have e : F x φ - F x ψ = (a x * d x - b x * c x) * (φ - ψ) /
        ((a x + b x * φ) * (a x + b x * ψ)) := by
      rw [hF, hF, div_sub_div _ _ (hden0 x φ hφ) (hden0 x ψ hψ)]; congr 1; ring
    rw [e, norm_div, norm_mul, norm_mul]
    have hθx := hθ x
    rw [div_le_iff₀ (pow_pos (hab x) 2)] at hθx
    have hp : 0 < ‖a x + b x * φ‖ * ‖a x + b x * ψ‖ :=
      mul_pos (lt_of_lt_of_le (hab x) (hden x φ hφ)) (lt_of_lt_of_le (hab x) (hden x ψ hψ))
    rw [div_le_iff₀ hp]
    have hq : (‖a x‖ - ‖b x‖) ^ 2 ≤ ‖a x + b x * φ‖ * ‖a x + b x * ψ‖ := by
      rw [sq]; exact mul_le_mul (hden x φ hφ) (hden x ψ hψ) (hab x).le (norm_nonneg _)
    calc ‖a x * d x - b x * c x‖ * ‖φ - ψ‖ ≤ θ * (‖a x‖ - ‖b x‖) ^ 2 * ‖φ - ψ‖ := by gcongr
      _ ≤ θ * (‖a x + b x * φ‖ * ‖a x + b x * ψ‖) * ‖φ - ψ‖ := by gcongr
      _ = _ := by ring
  have hFc : ∀ g : ℝ → ℂ, Continuous g → (∀ x, ‖g x‖ ≤ 1) →
      Continuous fun y => F (y - β) (g (y - β)) := by
    intro g hg hg1
    simp only [hF]
    exact Continuous.div (by fun_prop) (by fun_prop) (fun y => hden0 _ _ (hg1 _))
  obtain ⟨φs, hφs⟩ : ∃ φs : ℕ → ℝ → ℂ, φs = gIter F β := ⟨_, rfl⟩
  have φs_succ : ∀ k y, φs (k + 1) y = F (y - β) (φs k (y - β)) := fun k y => by rw [hφs]; rfl
  have φs_zero : φs 0 = fun _ => 0 := by rw [hφs]; rfl
  have hprop : ∀ k, Continuous (φs k) ∧ Periodic (φs k) 1 ∧ ∀ y, ‖φs k y‖ ≤ 1 := by
    intro k
    induction k with
    | zero => rw [φs_zero]; exact ⟨continuous_const, fun _ => rfl, fun _ => by simp⟩
    | succ k ih =>
      obtain ⟨hc', hp', hb'⟩ := ih
      refine ⟨by rw [show φs (k + 1) = fun y => F (y - β) (φs k (y - β)) from funext (φs_succ k)]; exact hFc _ hc' hb', fun y => ?_, fun y => ?_⟩
      · rw [φs_succ, φs_succ, show y + 1 - β = y - β + 1 by ring, hp' (y - β), hF, hF,
          hap, hbp, hcp, hdp]
      · rw [φs_succ]; exact hFb _ _ (hb' _)
  have hstep : ∀ k y, ‖φs (k + 1) y - φs k y‖ ≤ 2 * θ ^ k := by
    intro k
    induction k with
    | zero =>
      intro y
      simp only [pow_zero, mul_one]
      refine (norm_sub_le _ _).trans ?_
      linarith [(hprop (0 + 1)).2.2 y, (hprop 0).2.2 y]
    | succ k ih =>
      intro y
      rw [φs_succ (k + 1) y, φs_succ k y]
      refine (hFl _ _ _ ((hprop _).2.2 _) ((hprop _).2.2 _)).trans ?_
      calc θ * ‖φs (k + 1) (y - β) - φs k (y - β)‖ ≤ θ * (2 * θ ^ k) := by gcongr; exact ih _
        _ = 2 * θ ^ (k + 1) := by ring
  have hstep' : ∀ y k, dist (φs k y) (φs (k + 1) y) ≤ 2 * θ ^ k := fun y k => by
    rw [dist_comm, dist_eq_norm]; exact hstep k y
  have hcauchy : ∀ y, CauchySeq fun k => φs k y := fun y =>
    cauchySeq_of_le_geometric θ 2 hθ1 (hstep' y)
  let χ : ℝ → ℂ := fun y => limUnder atTop fun k => φs k y
  have hlim : ∀ y, Tendsto (fun k => φs k y) atTop (𝓝 (χ y)) := fun y =>
    (hcauchy y).tendsto_limUnder
  have hdist : ∀ k y, dist (φs k y) (χ y) ≤ 2 * θ ^ k / (1 - θ) := fun k y =>
    dist_le_of_le_geometric_of_tendsto θ 2 hθ1 (hstep' y) (hlim y) k
  have hunif : TendstoUniformly φs χ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h0 : Tendsto (fun k : ℕ => 2 * θ ^ k / (1 - θ)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul 2).div_const (1 - θ)
      simpa using this
    filter_upwards [h0.eventually (gt_mem_nhds hε)] with k hk y
    rw [dist_comm]; exact (hdist k y).trans_lt hk
  have hχc : Continuous χ := hunif.continuous (Frequently.of_forall fun k => (hprop k).1)
  have hχb : ∀ y, ‖χ y‖ ≤ 1 := fun y =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hlim y))
      (Eventually.of_forall fun k => (hprop k).2.2 y)
  have hχp : Periodic χ 1 := fun y => by
    show (limUnder atTop fun k => φs k (y + 1)) = limUnder atTop fun k => φs k y
    congr 1; funext k; exact (hprop k).2.1 y
  refine ⟨χ, hχc, hχp, hχb, fun x => ?_⟩
  have h1' : Tendsto (fun k => φs (k + 1) (x + β)) atTop (𝓝 (χ (x + β))) :=
    (hlim (x + β)).comp (tendsto_add_atTop_nat 1)
  have h2' : Tendsto (fun k => φs (k + 1) (x + β)) atTop (𝓝 (F x (χ x))) := by
    have e : (fun k => φs (k + 1) (x + β)) = fun k => F x (φs k x) := by
      funext k; rw [φs_succ, add_sub_cancel_right]
    rw [e]; simp only [hF]
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul (hlim x))).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul (hlim x))) (hden0 x _ (hχb x))
  rw [tendsto_nhds_unique h1' h2', hF]
  exact div_mul_cancel₀ _ (hden0 x _ (hχb x))

/-! ### Normalisation and quantitative data -/

/-- The normalised vector. -/
def nrm (v : Fin 2 → ℂ) : Fin 2 → ℂ := ((‖v‖ : ℂ)⁻¹) • v

lemma norm_nrm {v : Fin 2 → ℂ} (hv : v ≠ 0) : ‖nrm v‖ = 1 := by
  rw [nrm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

lemma smul_nrm {v : Fin 2 → ℂ} (hv : v ≠ 0) : v = (‖v‖ : ℂ) • nrm v := by
  have : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  rw [nrm, smul_smul, mul_inv_cancel₀ this, one_smul]

lemma norm_mulVec_nrm (M : M2) {v : Fin 2 → ℂ} :
    ‖M *ᵥ nrm v‖ = ‖v‖⁻¹ * ‖M *ᵥ v‖ := by
  rw [nrm, Matrix.mulVec_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm]

lemma inv_nrm {M : ℝ → M2} {v : ℝ → Fin 2 → ℂ} {γ : ℝ} (hv : ∀ x, v x ≠ 0)
    (h : ∀ x, ∃ c : ℂ, M x *ᵥ v x = c • v (x + γ)) :
    ∀ x, ∃ c : ℂ, M x *ᵥ nrm (v x) = c • nrm (v (x + γ)) := by
  intro x
  obtain ⟨c, hc⟩ := h x
  refine ⟨(‖v x‖ : ℂ)⁻¹ * c * ‖v (x + γ)‖, ?_⟩
  calc M x *ᵥ nrm (v x) = (‖v x‖ : ℂ)⁻¹ • (c • v (x + γ)) := by
        rw [nrm, Matrix.mulVec_smul, hc]
    _ = _ := by
        conv_lhs => rw [smul_nrm (hv (x + γ))]
        simp only [smul_smul, mul_assoc]

structure UHData (α : ℝ) (X : ℝ → M2) (N : ℕ) (u s : ℝ → Fin 2 → ℂ) : Prop where
  hN : 1 ≤ N
  cu : Continuous u
  cs : Continuous s
  pu : Periodic u 1
  ps : Periodic s 1
  nu : ∀ x, ‖u x‖ = 1
  ns : ∀ x, ‖s x‖ = 1
  crne : ∀ x, cr (u x) (s x) ≠ 0
  iu : ∀ x, ∃ σ : ℂ, iter α X N x *ᵥ u x = σ • u (x + N * α)
  is : ∀ x, ∃ σ : ℂ, iter α X N x *ᵥ s x = σ • s (x + N * α)
  es : ∀ x, ‖iter α X N x *ᵥ s x‖ < 1
  eu : ∀ x, 1 < ‖iter α X N x *ᵥ u x‖

lemma uhData_of_isUH {α : ℝ} {X : ℝ → M2} (h : IsUH α X) : ∃ N u s, UHData α X N u s := by
  obtain ⟨u, s, hu, hs, hup, hsp, hu0, hs0, hiu, his, N, hN, hexp⟩ := h
  have cn : ∀ {v : ℝ → Fin 2 → ℂ}, Continuous v → (∀ x, v x ≠ 0) →
      Continuous fun x => nrm (v x) := by
    intro v hv hv0
    unfold nrm
    exact ((Complex.continuous_ofReal.comp hv.norm).inv₀ (fun x => by simpa using hv0 x)).smul hv
  have es : ∀ x, ‖iter α X N x *ᵥ nrm (s x)‖ < 1 := fun x => by
    rw [norm_mulVec_nrm, inv_mul_lt_iff₀ (norm_pos_iff.2 (hs0 x)), mul_one]; exact (hexp x).1
  have eu : ∀ x, 1 < ‖iter α X N x *ᵥ nrm (u x)‖ := fun x => by
    rw [norm_mulVec_nrm, lt_inv_mul_iff₀ (norm_pos_iff.2 (hu0 x)), mul_one]; exact (hexp x).2
  refine ⟨N, fun x => nrm (u x), fun x => nrm (s x), ⟨hN, cn hu hu0, cn hs hs0,
    fun x => by show nrm (u (x + 1)) = nrm (u x); rw [hup x],
    fun x => by show nrm (s (x + 1)) = nrm (s x); rw [hsp x],
    fun x => norm_nrm (hu0 x), fun x => norm_nrm (hs0 x), ?_,
    inv_nrm hu0 (iter_inv hiu N), inv_nrm hs0 (iter_inv his N), es, eu⟩⟩
  intro x hx
  have hx' : cr (nrm (s x)) (nrm (u x)) = 0 := by rw [cr_comm, hx, neg_zero]
  have hun : nrm (u x) ≠ 0 := fun h0 => by
    have := norm_nrm (hu0 x); rw [h0, norm_zero] at this; exact zero_ne_one this
  obtain ⟨c, hc⟩ := parallel_of_cr_eq_zero hun hx'
  have hc1 : ‖c‖ = 1 := by
    have := norm_nrm (hs0 x); rw [hc, norm_smul, norm_nrm (hu0 x), mul_one] at this; exact this
  have := es x
  rw [hc, Matrix.mulVec_smul, norm_smul, hc1, one_mul] at this
  linarith [eu x]

/-! ### Cone criterion -/

/-- The open conditions on the coefficients `(p, q, r, t)` of `Y_N` in the basis `(u, s)`. -/
def Good (η : ℝ) (p q r t : ℂ) : Prop :=
  ‖q‖ * η + ‖r‖ / η + ‖t‖ < ‖p‖ ∧
  ‖p * t - q * r‖ < (‖p‖ - ‖q‖ * η) ^ 2 ∧
  1 + η < (‖p‖ - ‖q‖ * η) * (1 - η) ∧
  ‖r‖ * η + ‖q‖ / η + ‖t‖ < ‖p‖ ∧
  ‖p * t - q * r‖ < (‖p‖ - ‖r‖ * η) ^ 2 ∧
  ‖p * t - q * r‖ * (1 + η) < (‖p‖ - ‖r‖ * η) * (1 - η)

lemma isOpen_good (η : ℝ) :
    IsOpen {z : ℂ × ℂ × ℂ × ℂ | Good η z.1 z.2.1 z.2.2.1 z.2.2.2} := by
  simp only [Good, Set.ofPred_and]
  repeat' apply IsOpen.inter
  all_goals exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isUH_of_good {a : ℝ} {Y : ℝ → M2} (hY : IsSLCocycle Y) {N : ℕ} (hN : 1 ≤ N)
    {u s : ℝ → Fin 2 → ℂ} (hu : Continuous u) (hs : Continuous s) (hup : Periodic u 1)
    (hsp : Periodic s 1) (hnu : ∀ x, ‖u x‖ = 1) (hns : ∀ x, ‖s x‖ = 1)
    {p q r t : ℝ → ℂ} (hpc : Continuous p) (hqc : Continuous q) (hrc : Continuous r)
    (htc : Continuous t) (hpp : Periodic p 1) (hqp : Periodic q 1) (hrp : Periodic r 1)
    (htp : Periodic t 1)
    (hdu : ∀ x, iter a Y N x *ᵥ u x = p x • u (x + N * a) + r x • s (x + N * a))
    (hds : ∀ x, iter a Y N x *ᵥ s x = q x • u (x + N * a) + t x • s (x + N * a))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hgood : ∀ x, Good η (p x) (q x) (r x) (t x)) :
    IsUH a Y := by
  have hnη : ‖(η : ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη0.ne'
  have fid : ∀ z w : ℂ, z * (η : ℂ) * (w / η) = z * w := fun z w => by field_simp
  -- unstable graph
  obtain ⟨χ, hχc, hχp, hχb, hχe⟩ := graph_fixed (a := p) (b := fun x => q x * η)
    (c := fun x => r x / η) (d := t) hpc (by fun_prop) (by fun_prop) htc hpp
    (fun x => by simp only [hqp x]) (fun x => by simp only [hrp x]) htp (N * a)
    (fun x => by simp only [norm_mul, norm_div, hnη]; exact (hgood x).1)
    (fun x => by simp only [fid, norm_mul, hnη]; exact (hgood x).2.1)
  set u' : ℝ → Fin 2 → ℂ := fun x => u x + ((η : ℂ) * χ x) • s x with hu'
  have hfix : ∀ x, (η : ℂ) * χ (x + N * a) * (p x + q x * η * χ x) = r x + η * t x * χ x := by
    intro x
    have := hχe x
    calc _ = (η : ℂ) * (χ (x + N * a) * (p x + q x * η * χ x)) := by ring
      _ = η * (r x / η + t x * χ x) := by rw [this]
      _ = _ := by rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hηc]; ring
  have hu'inv : ∀ x, iter a Y N x *ᵥ u' x = (p x + q x * η * χ x) • u' (x + N * a) := by
    intro x
    simp only [hu', Matrix.mulVec_add, Matrix.mulVec_smul, hdu x, hds x]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(s (x + N * a) i)) * hfix x
  have hu'n : ∀ x, 1 - η ≤ ‖u' x‖ ∧ ‖u' x‖ ≤ 1 + η := by
    intro x
    have h1 : ‖((η : ℂ) * χ x) • s x‖ ≤ η := by
      rw [norm_smul, norm_mul, hnη, hns x, mul_one]; exact mul_le_of_le_one_right hη0.le (hχb x)
    constructor
    · have := vnorm_add_ge (u x) (((η : ℂ) * χ x) • s x); rw [hnu x] at this
      simp only [hu']; linarith
    · have := norm_add_le (u x) (((η : ℂ) * χ x) • s x); rw [hnu x] at this
      simp only [hu']; linarith
  have hexpu : ∀ x, ‖u' x‖ < ‖iter a Y N x *ᵥ u' x‖ := by
    intro x
    obtain ⟨g1, -, g3, -, -, -⟩ := hgood x
    rw [hu'inv x, norm_smul]
    have hA : ‖p x‖ - ‖q x‖ * η ≤ ‖p x + q x * η * χ x‖ := by
      refine le_trans ?_ (norm_add_ge _ _)
      rw [norm_mul, norm_mul, hnη]
      have := mul_le_of_le_one_right (mul_nonneg (norm_nonneg (q x)) hη0.le) (hχb x)
      linarith
    calc ‖u' x‖ ≤ 1 + η := (hu'n x).2
      _ < (‖p x‖ - ‖q x‖ * η) * (1 - η) := g3
      _ ≤ ‖p x + q x * η * χ x‖ * ‖u' (x + N * a)‖ :=
          mul_le_mul hA (hu'n _).1 (by linarith) (norm_nonneg _)
  -- stable graph
  have shp : ∀ {f : ℝ → ℂ}, Periodic f 1 → ∀ z : ℝ, f (z + 1 - N * a) = f (z - N * a) :=
    fun hf z => by rw [show z + 1 - (N : ℝ) * a = z - N * a + 1 by ring, hf]
  obtain ⟨ω, hωc, hωp, hωb, hωe⟩ := graph_fixed (a := fun z => p (z - N * a))
    (b := fun z => -(r (z - N * a) * η)) (c := fun z => -(q (z - N * a) / η))
    (d := fun z => t (z - N * a)) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by simp only [shp hpp]) (fun z => by simp only [shp hrp])
    (fun z => by simp only [shp hqp]) (fun z => by simp only [shp htp]) (-(N * a))
    (fun z => by simp only [norm_neg, norm_mul, norm_div, hnη]; exact (hgood _).2.2.2.1)
    (fun z => by
      simp only [neg_mul_neg, fid, norm_mul, norm_neg, hnη, mul_comm (r _) (q _)]
      exact (hgood _).2.2.2.2.1)
  set s' : ℝ → Fin 2 → ℂ := fun x => s x + ((η : ℂ) * ω x) • u x with hs'
  have hfix' : ∀ x, (η : ℂ) * ω x * (p x - r x * η * ω (x + N * a)) =
      η * t x * ω (x + N * a) - q x := by
    intro x
    have := hωe (x + N * a)
    simp only [add_neg_cancel_right, add_sub_cancel_right] at this
    calc _ = (η : ℂ) * (ω x * (p x + -(r x * η) * ω (x + N * a))) := by ring
      _ = η * (-(q x / η) + t x * ω (x + N * a)) := by rw [this]
      _ = _ := by rw [mul_add, mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hηc]; ring
  have hP : ∀ x, ‖p x‖ - ‖r x‖ * η ≤ ‖p x - r x * η * ω (x + N * a)‖ := by
    intro x
    rw [sub_eq_add_neg (p x)]
    refine le_trans ?_ (norm_add_ge _ _)
    rw [norm_neg, norm_mul, norm_mul, hnη]
    have := mul_le_of_le_one_right (mul_nonneg (norm_nonneg (r x)) hη0.le) (hωb (x + N * a))
    linarith
  have hPpos : ∀ x, 0 < ‖p x‖ - ‖r x‖ * η := fun x => by
    obtain ⟨-, -, -, g4, -, -⟩ := hgood x
    have : 0 ≤ ‖q x‖ / η := div_nonneg (norm_nonneg _) hη0.le
    linarith [norm_nonneg (t x)]
  have hP0 : ∀ x, p x - r x * η * ω (x + N * a) ≠ 0 := fun x h => by
    have := hP x; rw [h, norm_zero] at this; linarith [hPpos x]
  set σ : ℝ → ℂ := fun x => (p x * t x - q x * r x) / (p x - r x * η * ω (x + N * a)) with hσ
  have hs'inv : ∀ x, iter a Y N x *ᵥ s' x = σ x • s' (x + N * a) := by
    intro x
    have e1 : σ x * (η * ω (x + N * a)) = η * ω x * p x + q x := by
      simp only [hσ]
      rw [div_mul_eq_mul_div, div_eq_iff (hP0 x)]
      linear_combination (-(p x)) * hfix' x
    have e2 : σ x = η * ω x * r x + t x := by
      simp only [hσ]
      rw [div_eq_iff (hP0 x)]
      linear_combination (-(r x)) * hfix' x
    simp only [hs', Matrix.mulVec_add, Matrix.mulVec_smul, hdu x, hds x]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(u (x + N * a) i)) * e1 + (-(s (x + N * a) i)) * e2
  have hs'n : ∀ x, 1 - η ≤ ‖s' x‖ ∧ ‖s' x‖ ≤ 1 + η := by
    intro x
    have h1 : ‖((η : ℂ) * ω x) • u x‖ ≤ η := by
      rw [norm_smul, norm_mul, hnη, hnu x, mul_one]; exact mul_le_of_le_one_right hη0.le (hωb x)
    constructor
    · have := vnorm_add_ge (s x) (((η : ℂ) * ω x) • u x); rw [hns x] at this
      simp only [hs']; linarith
    · have := norm_add_le (s x) (((η : ℂ) * ω x) • u x); rw [hns x] at this
      simp only [hs']; linarith
  have hcons : ∀ x, ‖iter a Y N x *ᵥ s' x‖ < ‖s' x‖ := by
    intro x
    obtain ⟨-, -, -, -, -, g6⟩ := hgood x
    have hσP : ‖σ x‖ * ‖p x - r x * η * ω (x + N * a)‖ = ‖p x * t x - q x * r x‖ := by
      rw [← norm_mul]; simp only [hσ]; rw [div_mul_cancel₀ _ (hP0 x)]
    have k1 : ‖σ x‖ * (1 + η) * (‖p x‖ - ‖r x‖ * η) < (1 - η) * (‖p x‖ - ‖r x‖ * η) := by
      calc ‖σ x‖ * (1 + η) * (‖p x‖ - ‖r x‖ * η)
          ≤ ‖σ x‖ * (1 + η) * ‖p x - r x * η * ω (x + N * a)‖ := by
            exact mul_le_mul_of_nonneg_left (hP x) (mul_nonneg (norm_nonneg _) (by linarith))
        _ = ‖p x * t x - q x * r x‖ * (1 + η) := by rw [← hσP]; ring
        _ < _ := by linarith
    have k2 : ‖σ x‖ * (1 + η) < 1 - η := lt_of_mul_lt_mul_right k1 (hPpos x).le
    rw [hs'inv x, norm_smul]
    calc ‖σ x‖ * ‖s' (x + N * a)‖ ≤ ‖σ x‖ * (1 + η) := by gcongr; exact (hs'n _).2
      _ < 1 - η := k2
      _ ≤ ‖s' x‖ := (hs'n x).1
  exact isUH_of_iterate hY (u := u') (s := s') (by rw [hu']; fun_prop) (by rw [hs']; fun_prop)
    (fun x => by simp only [hu', hup x, hχp x, hsp x])
    (fun x => by simp only [hs', hsp x, hωp x, hup x])
    (fun x h => by have := (hu'n x).1; rw [h, norm_zero] at this; linarith)
    (fun x h => by have := (hs'n x).1; rw [h, norm_zero] at this; linarith)
    hN (fun x => ⟨_, hu'inv x⟩) (fun x => ⟨_, hs'inv x⟩) (fun x => ⟨hcons x, hexpu x⟩)

/-! ### Openness -/

/-- The coefficients of `Y_N` in the bases `(u(x), s(x))` and `(u(x + N a), s(x + N a))`. -/
def coef (N : ℕ) (u s : ℝ → Fin 2 → ℂ) (a : ℝ) (Y : ℝ → M2) (x : ℝ) : ℂ × ℂ × ℂ × ℂ :=
  (cr (iter a Y N x *ᵥ u x) (s (x + N * a)) / cr (u (x + N * a)) (s (x + N * a)),
   cr (iter a Y N x *ᵥ s x) (s (x + N * a)) / cr (u (x + N * a)) (s (x + N * a)),
   cr (u (x + N * a)) (iter a Y N x *ᵥ u x) / cr (u (x + N * a)) (s (x + N * a)),
   cr (u (x + N * a)) (iter a Y N x *ᵥ s x) / cr (u (x + N * a)) (s (x + N * a)))

lemma continuous_coef {N : ℕ} {u s : ℝ → Fin 2 → ℂ} {a : ℝ} {Y : ℝ → M2} (hY : Continuous Y)
    (hu : Continuous u) (hs : Continuous s) (hcr : ∀ x, cr (u x) (s x) ≠ 0) :
    Continuous (coef N u s a Y) := by
  have hI := continuous_iter (α := a) hY N
  have hy : Continuous fun x : ℝ => x + N * a := continuous_id.add continuous_const
  have huy : Continuous fun x => u (x + N * a) := hu.comp hy
  have hsy : Continuous fun x => s (x + N * a) := hs.comp hy
  have c2 : ∀ {f g : ℝ → Fin 2 → ℂ}, Continuous f → Continuous g →
      Continuous fun x => cr (f x) (g x) := fun hf hg => continuous_cr.comp (hf.prodMk hg)
  have hD : Continuous fun x => cr (u (x + N * a)) (s (x + N * a)) := c2 huy hsy
  have hne : ∀ x, cr (u (x + N * a)) (s (x + N * a)) ≠ 0 := fun x => hcr _
  have hIu : Continuous fun x => iter a Y N x *ᵥ u x := hI.matrix_mulVec hu
  have hIs : Continuous fun x => iter a Y N x *ᵥ s x := hI.matrix_mulVec hs
  exact ((c2 hIu hsy).div hD hne).prodMk (((c2 hIs hsy).div hD hne).prodMk
    (((c2 huy hIu).div hD hne).prodMk ((c2 huy hIs).div hD hne)))

lemma periodic_coef {N : ℕ} {u s : ℝ → Fin 2 → ℂ} {a : ℝ} {Y : ℝ → M2} (hY : Periodic Y 1)
    (hup : Periodic u 1) (hsp : Periodic s 1) : Periodic (coef N u s a Y) 1 := fun x => by
  simp only [coef]
  rw [iter_periodic hY N x, hup x, hsp x, show x + 1 + N * a = x + N * a + 1 by ring,
    hup (x + N * a), hsp (x + N * a)]

lemma tendsto_iter {α : ℝ} {X : ℝ → M2} (hXc : Continuous X) {αs : ℕ → ℝ} {Xs : ℕ → ℝ → M2}
    (hαs : Tendsto αs atTop (𝓝 α)) (hconv : TendstoUniformly Xs X atTop) (k : ℕ) (x : ℝ) :
    Tendsto (fun q : ℕ × ℝ => iter (αs q.1) (Xs q.1) k q.2) (atTop ×ˢ 𝓝 x)
      (𝓝 (iter α X k x)) := by
  induction k with
  | zero => simp only [iter]; exact tendsto_const_nhds
  | succ k ih =>
    have hU : TendstoUniformly (fun q : ℕ × ℝ => Xs q.1) X (atTop ×ˢ 𝓝 x) :=
      fun U hU => tendsto_fst.eventually (hconv U hU)
    have hg : Tendsto (fun q : ℕ × ℝ => q.2 + k * αs q.1) (atTop ×ˢ 𝓝 x) (𝓝 (x + k * α)) :=
      tendsto_snd.add ((hαs.comp tendsto_fst).const_mul _)
    exact (hU.tendsto_comp hXc.continuousAt hg).mul ih

lemma good_diag {η m c : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hm : 1 < m) (hc0 : 0 ≤ c)
    (hA : η * (m + 1) < m - 1) (hB : η * (1 + c) < 1 - c) {P T : ℂ} (hP : m ≤ ‖P‖)
    (hT : ‖T‖ ≤ c) : Good η P 0 0 T := by
  have hP0 : 0 < ‖P‖ := by linarith
  have hT0 := norm_nonneg T
  have hc1 : c < 1 := by nlinarith [mul_nonneg hη0.le hc0]
  have k1 : ‖T‖ < ‖P‖ := by linarith
  have k2 : ‖P‖ * ‖T‖ < ‖P‖ ^ 2 := by
    have := mul_lt_mul_of_pos_left k1 hP0; nlinarith
  have k3 : 1 + η < ‖P‖ * (1 - η) := by
    have := mul_le_mul_of_nonneg_right hP (by linarith : (0:ℝ) ≤ 1 - η); nlinarith
  have k4 : ‖P‖ * ‖T‖ * (1 + η) < ‖P‖ * (1 - η) := by
    have h1 := mul_le_mul_of_nonneg_right hT (by linarith : (0:ℝ) ≤ 1 + η)
    have h2 : ‖T‖ * (1 + η) < 1 - η := by nlinarith
    have := mul_lt_mul_of_pos_left h2 hP0; nlinarith
  unfold Good
  simp only [norm_zero, zero_mul, zero_div, mul_zero, sub_zero, add_zero, zero_add, norm_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [k1, k2, k3, k4]

theorem uh_open_aux {α : ℝ} {X : ℝ → M2} (hX : IsSLCocycle X) (hUH : IsUH α X)
    {αs : ℕ → ℝ} {Xs : ℕ → ℝ → M2} (hXs : ∀ᶠ n in atTop, IsSLCocycle (Xs n))
    (hαs : Tendsto αs atTop (𝓝 α)) (hconv : TendstoUniformly Xs X atTop) :
    ∀ᶠ n in atTop, IsUH (αs n) (Xs n) := by
  obtain ⟨N, u, s, hD⟩ := uhData_of_isUH hUH
  have hcc := continuous_coef (N := N) (a := α) hX.continuous hD.cu hD.cs hD.crne
  have hcp := periodic_coef (N := N) (a := α) hX.periodic hD.pu hD.ps
  -- limit values
  have hlim : ∀ x, (coef N u s α X x).2.1 = 0 ∧ (coef N u s α X x).2.2.1 = 0 ∧
      ‖(coef N u s α X x).1‖ = ‖iter α X N x *ᵥ u x‖ ∧
      ‖(coef N u s α X x).2.2.2‖ = ‖iter α X N x *ᵥ s x‖ := by
    intro x
    obtain ⟨σ, hσ⟩ := hD.iu x
    obtain ⟨τ, hτ⟩ := hD.is x
    have hne := hD.crne (x + N * α)
    simp only [coef, hσ, hτ, cr_smul_left, cr_smul_right, cr_self, mul_zero, zero_div,
      true_and, norm_smul, hD.nu, hD.ns, mul_one]
    constructor
    · rw [mul_div_assoc, div_self hne, mul_one]
    · rw [mul_div_assoc, div_self hne, mul_one]
  obtain ⟨c1, hc1, hc1'⟩ := per_max_lt (g := fun x => -‖(coef N u s α X x).1‖)
    (continuous_fst.comp hcc).norm.neg (fun x => by simp only [hcp x]) (b := -1)
    (fun x => by simp only [neg_lt_neg_iff]; rw [(hlim x).2.2.1]; exact hD.eu x)
  obtain ⟨c2, hc2, hc2'⟩ := per_max_lt (g := fun x => ‖(coef N u s α X x).2.2.2‖)
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hcc))).norm
    (fun x => by simp only [hcp x]) (b := 1)
    (fun x => by rw [(hlim x).2.2.2]; exact hD.es x)
  set m := -c1 with hm
  have hm1 : 1 < m := by linarith
  have hc20 : 0 ≤ c2 := (norm_nonneg _).trans (hc2' 0)
  set η := min ((m - 1) / (m + 1)) ((1 - c2) / (1 + c2)) / 2 with hη
  have hA : 0 < (m - 1) / (m + 1) := div_pos (by linarith) (by linarith)
  have hB : 0 < (1 - c2) / (1 + c2) := div_pos (by linarith) (by linarith)
  have hη0 : 0 < η := by rw [hη]; exact half_pos (lt_min hA hB)
  have hηA : η < (m - 1) / (m + 1) := by
    rw [hη]; linarith [min_le_left ((m - 1) / (m + 1)) ((1 - c2) / (1 + c2))]
  have hηB : η < (1 - c2) / (1 + c2) := by
    rw [hη]; linarith [min_le_right ((m - 1) / (m + 1)) ((1 - c2) / (1 + c2))]
  rw [lt_div_iff₀ (by linarith)] at hηA hηB
  have hη1 : η < 1 := by nlinarith
  -- the limit is good
  have hgl : ∀ x, Good η (coef N u s α X x).1 (coef N u s α X x).2.1 (coef N u s α X x).2.2.1
      (coef N u s α X x).2.2.2 := by
    intro x
    obtain ⟨h0, h0', -, -⟩ := hlim x
    rw [h0, h0']
    exact good_diag hη0 hη1 hm1 hc20 hηA hηB (by linarith [hc1' x]) (hc2' x)
  -- convergence of the coefficients
  have hΦ : ∀ x, Tendsto (fun q : ℕ × ℝ => coef N u s (αs q.1) (Xs q.1) q.2) (atTop ×ˢ 𝓝 x)
      (𝓝 (coef N u s α X x)) := by
    intro x
    have hI := tendsto_iter hX.continuous hαs hconv N x
    have hy : Tendsto (fun q : ℕ × ℝ => q.2 + N * αs q.1) (atTop ×ˢ 𝓝 x) (𝓝 (x + N * α)) :=
      tendsto_snd.add ((hαs.comp tendsto_fst).const_mul _)
    have hux : Tendsto (fun q : ℕ × ℝ => u q.2) (atTop ×ˢ 𝓝 x) (𝓝 (u x)) :=
      (hD.cu.tendsto x).comp tendsto_snd
    have hsx : Tendsto (fun q : ℕ × ℝ => s q.2) (atTop ×ˢ 𝓝 x) (𝓝 (s x)) :=
      (hD.cs.tendsto x).comp tendsto_snd
    have huy : Tendsto (fun q : ℕ × ℝ => u (q.2 + N * αs q.1)) (atTop ×ˢ 𝓝 x)
        (𝓝 (u (x + N * α))) := (hD.cu.tendsto _).comp hy
    have hsy : Tendsto (fun q : ℕ × ℝ => s (q.2 + N * αs q.1)) (atTop ×ˢ 𝓝 x)
        (𝓝 (s (x + N * α))) := (hD.cs.tendsto _).comp hy
    have hIu := tendsto_mulVec' hI hux
    have hIs := tendsto_mulVec' hI hsx
    have hDn := tendsto_cr huy hsy
    have hne := hD.crne (x + N * α)
    exact ((tendsto_cr hIu hsy).div hDn hne).prodMk_nhds (((tendsto_cr hIs hsy).div hDn
      hne).prodMk_nhds (((tendsto_cr huy hIu).div hDn hne).prodMk_nhds
      ((tendsto_cr huy hIs).div hDn hne)))
  have hloc : ∀ x, ∀ᶠ q in atTop ×ˢ 𝓝 x, (fun n y => IsSLCocycle (Xs n) →
      Good η (coef N u s (αs n) (Xs n) y).1 (coef N u s (αs n) (Xs n) y).2.1
        (coef N u s (αs n) (Xs n) y).2.2.1 (coef N u s (αs n) (Xs n) y).2.2.2) q.1 q.2 := by
    intro x
    filter_upwards [(hΦ x).eventually ((isOpen_good η).mem_nhds (hgl x))] with q hq _
    exact hq
  have hper : ∀ᶠ n in atTop, ∀ x, ∃ y ∈ Icc (0:ℝ) 1, ((fun n y => IsSLCocycle (Xs n) →
      Good η (coef N u s (αs n) (Xs n) y).1 (coef N u s (αs n) (Xs n) y).2.1
        (coef N u s (αs n) (Xs n) y).2.2.1 (coef N u s (αs n) (Xs n) y).2.2.2) n y →
      (fun n y => IsSLCocycle (Xs n) →
      Good η (coef N u s (αs n) (Xs n) y).1 (coef N u s (αs n) (Xs n) y).2.1
        (coef N u s (αs n) (Xs n) y).2.2.1 (coef N u s (αs n) (Xs n) y).2.2.2) n x) := by
    filter_upwards [hXs] with n hn x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_coef (N := N) (a := αs n) hn.periodic hD.pu hD.ps).exists_mem_Ico₀ one_pos x
    exact ⟨y, Ico_subset_Icc_self hy, fun h _ => by rw [hxy]; exact h hn⟩
  filter_upwards [eventually_forall_of_local hloc hper, hXs] with n h hn
  have hcn := continuous_coef (N := N) (a := αs n) hn.continuous hD.cu hD.cs hD.crne
  have hpn := periodic_coef (N := N) (a := αs n) hn.periodic hD.pu hD.ps
  exact isUH_of_good hn hD.hN hD.cu hD.cs hD.pu hD.ps hD.nu hD.ns
    (p := fun x => (coef N u s (αs n) (Xs n) x).1)
    (q := fun x => (coef N u s (αs n) (Xs n) x).2.1)
    (r := fun x => (coef N u s (αs n) (Xs n) x).2.2.1)
    (t := fun x => (coef N u s (αs n) (Xs n) x).2.2.2)
    (continuous_fst.comp hcn) (continuous_fst.comp (continuous_snd.comp hcn))
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hcn)))
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hcn)))
    (fun x => by simp only [hpn x]) (fun x => by simp only [hpn x])
    (fun x => by simp only [hpn x]) (fun x => by simp only [hpn x])
    (fun x => decomp (hD.crne _) _) (fun x => decomp (hD.crne _) _)
    hη0 hη1 (fun x => h x hn)

end UHOpenAux

open UHOpenAux in
/-- **Openness of uniform hyperbolicity** (the field `Hypotheses.uhOpen`). -/
theorem uhOpen_proof : ∀ {α : ℝ} {A : ℂ → M2}, IsSLCocycle (shift A 0) → UH α A →
    ∀ {αs : ℕ → ℝ} {As : ℕ → ℂ → M2}, (∀ᶠ n in atTop, IsSLCocycle (shift (As n) 0)) →
      Tendsto αs atTop (𝓝 α) →
      TendstoUniformly (fun n => shift (As n) 0) (shift A 0) atTop →
        ∀ᶠ n in atTop, UH (αs n) (As n) :=
  fun hA hUH _ _ hAs hαs hconv => uh_open_aux hA hUH hAs hαs hconv

/-- `𝒰ℋ` is open (for all frequencies, with `C⁰` convergence on the real line). -/
theorem uh_open {α : ℝ} {A : ℂ → M2} (hA : IsSLCocycle (shift A 0)) (hUH : UH α A)
    {αs : ℕ → ℝ} {As : ℕ → ℂ → M2} (hAs : ∀ᶠ n in atTop, IsSLCocycle (shift (As n) 0))
    (hαs : Tendsto αs atTop (𝓝 α))
    (hconv : TendstoUniformly (fun n => shift (As n) 0) (shift A 0) atTop) :
    ∀ᶠ n in atTop, UH (αs n) (As n) :=
  uhOpen_proof hA hUH hAs hαs hconv

end AvilaGlobal
